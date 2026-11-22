// A tiny stack VM for make.fun's tiny stack ISA: 32-bit wrapping integers, a
// 256-value data stack, a 64-deep call stack, 256 words of memory, and every
// trap of the spec with its own exit code. Answers each /input/<id> program
// with the bytes it wrote and the exit code it ended with. Each step checks,
// in the spec's order: the step limit, pc in bounds, a known opcode, the
// immediate in bounds, the stack's needs, and only then the instruction's
// own traps (division by zero, a full call stack, a bad memory address, the
// output limit) before its effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(p, inp) {
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  const n = p.length;
  let sp = 0, csp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (c) => [out.subarray(0, ol), c];
  for (;;) {
    if (st === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const o = p[pc];
    let im = -1, pp = 0, pu = 0;
    if (o < 8) {
      im = o === 1 ? 1 : o === 2 ? 4 : 0;
      pp = [0, 0, 0, 1, 1, 2, 2, 3][o];
      pu = [0, 1, 1, 0, 2, 2, 3, 3][o];
    } else if (o >= 0x10 && o <= 0x22 && o !== 0x1f) {
      im = 0;
      pp = o === 0x17 || o === 0x1b ? 1 : 2;
      pu = 1;
    } else if (o >= 0x30 && o <= 0x34) {
      im = o === 0x34 ? 0 : 2;
      pp = o === 0x31 || o === 0x32 ? 1 : 0;
    } else if (o === 0x40) { im = 0; pp = 1; pu = 1; }
    else if (o === 0x41) { im = 0; pp = 2; }
    else if (o === 0x50 || o === 0x51 || o === 0x53) { im = 0; pp = 1; }
    else if (o === 0x52) { im = 0; pu = 1; }
    if (im < 0) return end(5);
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < pp) return end(2);
    if (sp - pp + pu > 256) return end(3);
    pc = nx;
    switch (o) {
      case 0x00:
        return end(0);
      case 0x01:
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17:
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (o !== 0x30) {
          const v = D[--sp];
          take = o === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return end(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol === 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(D[--sp] & 255);
      default: {
        // The binary operators: 0x10-0x16, 0x18-0x1a, 0x1c-0x1e, 0x20-0x22.
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (o === 0x10) r = (a + b) | 0;
        else if (o === 0x11) r = (a - b) | 0;
        else if (o === 0x12) r = Math.imul(a, b);
        else if (o === 0x13) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (o === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (o === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (o === 0x16) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (o === 0x18) r = a & b;
        else if (o === 0x19) r = a | b;
        else if (o === 0x1a) r = a ^ b;
        else if (o === 0x1c) r = a << (b & 31);
        else if (o === 0x1d) r = a >> (b & 31);
        else if (o === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (o === 0x20) r = a === b ? 1 : 0;
        else if (o === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [so, code] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), so);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
