// Tiny stack VM for make.fun's tiny stack ISA v1: runs every program in a set
// and writes each one's stdout + exit code. Node 22, stdlib only. 32-bit wrapping
// ints, 256-value stack, 64-deep call stack, 256 words of memory, 1,000,000 steps,
// 65,536 output bytes. Traps: 2 underflow, 3 overflow, 4 div-by-zero, 5 bad opcode,
// 6 bad address, 7 call depth, 8 empty RET, 9 pc outside / cut-off immediate,
// 10 step limit, 11 output limit.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

// Per-opcode [pops, pushes, immediate bytes]; imm 255 = unknown opcode.
const POPS = new Uint8Array(256);
const PUSHES = new Uint8Array(256);
const IMM = new Uint8Array(256).fill(255);
for (const [op, pops, pushes, imm] of [
  [0x00,0,0,0],[0x01,0,1,1],[0x02,0,1,4],[0x03,1,0,0],
  [0x04,1,2,0],[0x05,2,2,0],[0x06,2,3,0],[0x07,3,3,0],
  [0x10,2,1,0],[0x11,2,1,0],[0x12,2,1,0],[0x13,2,1,0],
  [0x14,2,1,0],[0x15,2,1,0],[0x16,2,1,0],[0x17,1,1,0],
  [0x18,2,1,0],[0x19,2,1,0],[0x1a,2,1,0],[0x1b,1,1,0],
  [0x1c,2,1,0],[0x1d,2,1,0],[0x1e,2,1,0],[0x20,2,1,0],
  [0x21,2,1,0],[0x22,2,1,0],[0x30,0,0,2],[0x31,1,0,2],
  [0x32,1,0,2],[0x33,0,0,2],[0x34,0,0,0],[0x40,1,1,0],
  [0x41,2,0,0],[0x50,1,0,0],[0x51,1,0,0],[0x52,0,1,0],
  [0x53,1,0,0],
]) {
  POPS[op] = pops; PUSHES[op] = pushes; IMM[op] = imm;
}

// Runs one program on its input, returning [output bytes, exit code];
// a trap keeps prior output and exits with the trap's code.
function run(prog, input) {
  const n = prog.length;
  const st = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = [];
  let pc = 0, sp = 0, csp = 0, ip = 0, steps = 0;
  for (;;) {
    if (steps === 1000000) return [out, 10];
    if (pc < 0 || pc >= n) return [out, 9];
    const op = prog[pc];
    const imm = IMM[op];
    if (imm === 255) return [out, 5];
    if (pc + imm >= n) return [out, 9];
    steps++;
    const nx = pc + 1 + imm;
    const pops = POPS[op], pushes = PUSHES[op];
    if (sp < pops) return [out, 2];
    if (sp - pops + pushes > 256) return [out, 3];
    pc = nx;
    switch (op) {
      case 0x00:
        return [out, 0];
      case 0x01:
        st[sp++] = (prog[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = t;
        break;
      }
      case 0x06:
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = a;
        break;
      }
      case 0x17:
        st[sp - 1] = (-st[sp - 1]) | 0;
        break;
      case 0x1b:
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return [out, 4];
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return [out, 4];
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return [out, 4];
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return [out, 4];
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30) pc = nx + rel;
        else {
          const v = st[--sp];
          if ((op === 0x31) === (v === 0)) pc = nx + rel;
        }
        break;
      }
      case 0x33:
        if (csp === 64) return [out, 7];
        calls[csp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return [out, 8];
        pc = calls[--csp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return [out, 6];
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return [out, 6];
        mem[addr] = st[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(st[sp - 1]);
        if (out.length + s.length > 65536) return [out, 11];
        sp--;
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        break;
      }
      case 0x51:
        if (out.length + 1 > 65536) return [out, 11];
        out.push(st[--sp] & 255);
        break;
      case 0x52:
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return [out, st[--sp] & 255];
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
for (const id of readdirSync(IN_DIR).sort()) {
  const prog = new Uint8Array(readFileSync(join(IN_DIR, id, "program.bin")));
  const input = new Uint8Array(readFileSync(join(IN_DIR, id, "input.bin")));
  const [out, code] = run(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, "stdout.bin"), Uint8Array.from(out));
  writeFileSync(join(OUT_DIR, id, "exit.txt"), `${code}\n`);
}
