// Tests for utility functions: reciprocal, link, invertMatrix, removeFromArray, nameToFancyName, etc.

import { assert, assertEquals, assertThrows } from "$std/assert/mod.ts";
import { link, reciprocal } from "./graph.ts";
import {
  fancyNameToName,
  invertMatrix,
  minMax,
  nameToFancyName,
  removeFromArray,
  removeFromArrayIf,
} from "./util.ts";
import type { Node } from "./types.ts";

function makeNode(type: string, numPorts: number): Node {
  const node: Node = { type, ports: [], label: type };
  for (let i = 0; i < numPorts; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
}

// ─── reciprocal ────────────────────────────────────────────────────

Deno.test("reciprocal: returns opposite end of a link", () => {
  const a = makeNode("abs", 2);
  const b = makeNode("app", 2);
  link({ node: a, port: 0 }, { node: b, port: 0 });
  const r = reciprocal({ node: a, port: 0 });
  assertEquals(r.node, b);
  assertEquals(r.port, 0);
});

Deno.test("reciprocal: self-loop returns same port", () => {
  const a = makeNode("var", 1);
  // Self-loop: port 0 points to itself
  const r = reciprocal({ node: a, port: 0 });
  assertEquals(r.node, a);
  assertEquals(r.port, 0);
});

Deno.test("reciprocal: auxiliary port linkage", () => {
  const a = makeNode("abs", 3);
  const b = makeNode("var", 1);
  link({ node: a, port: 2 }, { node: b, port: 0 });
  const r = reciprocal({ node: a, port: 2 });
  assertEquals(r.node, b);
  assertEquals(r.port, 0);
  // Verify reverse
  const r2 = reciprocal({ node: b, port: 0 });
  assertEquals(r2.node, a);
  assertEquals(r2.port, 2);
});

// ─── link ──────────────────────────────────────────────────────────

Deno.test("link: establishes bidirectional connection", () => {
  const a = makeNode("abs", 2);
  const b = makeNode("app", 2);
  link({ node: a, port: 1 }, { node: b, port: 1 });
  assertEquals(a.ports[1].node, b);
  assertEquals(a.ports[1].port, 1);
  assertEquals(b.ports[1].node, a);
  assertEquals(b.ports[1].port, 1);
});

// ─── invertMatrix ──────────────────────────────────────────────────

Deno.test("invertMatrix: identity matrix returns identity", () => {
  const I = [[1, 0], [0, 1]];
  const inv = invertMatrix(I);
  assertEquals(inv.length, 2);
  for (let i = 0; i < 2; i++) {
    for (let j = 0; j < 2; j++) {
      const expected = i === j ? 1 : 0;
      assert(
        Math.abs(inv[i][j] - expected) < 1e-10,
        `inv[${i}][${j}] should be ${expected}`,
      );
    }
  }
});

Deno.test("invertMatrix: simple 2x2", () => {
  // [[2, 1], [7, 4]] — inverse is [[4, -1], [-7, 2]]
  const M = [[2, 1], [7, 4]];
  const inv = invertMatrix(M);
  assert(Math.abs(inv[0][0] - 4) < 1e-10);
  assert(Math.abs(inv[0][1] - (-1)) < 1e-10);
  assert(Math.abs(inv[1][0] - (-7)) < 1e-10);
  assert(Math.abs(inv[1][1] - 2) < 1e-10);
});

Deno.test("invertMatrix: 3x3 matrix", () => {
  const M = [[1, 2, 3], [0, 1, 4], [5, 6, 0]];
  const inv = invertMatrix(M);
  // Verify M * inv ≈ I
  for (let i = 0; i < 3; i++) {
    for (let j = 0; j < 3; j++) {
      let sum = 0;
      for (let k = 0; k < 3; k++) sum += M[i][k] * inv[k][j];
      const expected = i === j ? 1 : 0;
      assert(
        Math.abs(sum - expected) < 1e-10,
        `(M*inv)[${i}][${j}] should be ${expected}, got ${sum}`,
      );
    }
  }
});

Deno.test("invertMatrix: singular matrix throws", () => {
  const M = [[1, 2], [2, 4]]; // det = 0
  assertThrows(() => invertMatrix(M), Error, "not invertible");
});

Deno.test("invertMatrix: non-square matrix throws", () => {
  const M = [[1, 2, 3], [4, 5, 6]];
  assertThrows(() => invertMatrix(M), Error, "not square");
});

// ─── removeFromArray / removeFromArrayIf ───────────────────────────

Deno.test("removeFromArray: removes specified elements", () => {
  const arr = [1, 2, 3, 4, 5];
  removeFromArray(arr, [2, 4]);
  assertEquals(arr, [1, 3, 5]);
});

Deno.test("removeFromArray: no-op for absent elements", () => {
  const arr = [1, 2, 3];
  removeFromArray(arr, [99]);
  assertEquals(arr, [1, 2, 3]);
});

Deno.test("removeFromArray: empty removal list", () => {
  const arr = [1, 2];
  removeFromArray(arr, []);
  assertEquals(arr, [1, 2]);
});

Deno.test("removeFromArrayIf: removes matching elements", () => {
  const arr = [1, 2, 3, 4, 5];
  removeFromArrayIf(arr, (e) => e % 2 === 0);
  assertEquals(arr, [1, 3, 5]);
});

Deno.test("removeFromArrayIf: no matches leaves array intact", () => {
  const arr = [1, 3, 5];
  removeFromArrayIf(arr, (e) => e > 10);
  assertEquals(arr, [1, 3, 5]);
});

// ─── nameToFancyName / fancyNameToName ─────────────────────────────

Deno.test("nameToFancyName: converts lowercase letters", () => {
  assertEquals(nameToFancyName("abc"), "𝑎𝑏𝑐");
});

Deno.test("nameToFancyName: converts uppercase letters", () => {
  assertEquals(nameToFancyName("ABC"), "𝐴𝐵𝐶");
});

Deno.test("nameToFancyName: converts digits to subscripts", () => {
  assertEquals(nameToFancyName("x1"), "𝑥₁");
  assertEquals(nameToFancyName("x02"), "𝑥₀₂");
});

Deno.test("nameToFancyName: passes through non-mapped chars", () => {
  assertEquals(nameToFancyName("λ"), "λ");
  assertEquals(nameToFancyName("."), ".");
});

Deno.test("fancyNameToName: roundtrips with nameToFancyName", () => {
  const names = ["x", "abc", "A1", "foo42", "x0"];
  for (const name of names) {
    assertEquals(fancyNameToName(nameToFancyName(name)), name);
  }
});

Deno.test("fancyNameToName: passes through unknown chars", () => {
  assertEquals(fancyNameToName("λ→"), "λ→");
});

// ─── minMax ────────────────────────────────────────────────────────

Deno.test("minMax: returns sorted pair", () => {
  assertEquals(minMax(5, 3), [3, 5]);
  assertEquals(minMax(2, 7), [2, 7]);
  assertEquals(minMax(4, 4), [4, 4]);
});
