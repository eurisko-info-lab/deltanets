// Tests for the universal interaction net reduction primitives.

import { assertEquals, assertThrows } from "$std/assert/mod.ts";
import { reduceAnnihilate, reduceCommute, reduceErase } from "./reductions.ts";
import { link } from "./graph.ts";
import type { Graph, Node } from "./types.ts";
import { asMut } from "./util.ts";

/** Create a node with the given type and number of ports (unlinked). */
function makeNode(type: string, numPorts: number): Node {
  const node: Node = { type, ports: [] };
  for (let i = 0; i < numPorts; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
}

// ─── reduceAnnihilate ──────────────────────────────────────────────

Deno.test("annihilate: two binary nodes rewires aux ports", () => {
  const a = makeNode("abs", 3);
  const b = makeNode("abs", 3);
  const extA1 = makeNode("var", 1);
  const extA2 = makeNode("var", 1);
  const extB1 = makeNode("var", 1);
  const extB2 = makeNode("var", 1);

  link({ node: a, port: 0 }, { node: b, port: 0 });
  link({ node: a, port: 1 }, { node: extA1, port: 0 });
  link({ node: a, port: 2 }, { node: extA2, port: 0 });
  link({ node: b, port: 1 }, { node: extB1, port: 0 });
  link({ node: b, port: 2 }, { node: extB2, port: 0 });

  const graph: Graph = [a, b, extA1, extA2, extB1, extB2];
  reduceAnnihilate(a, asMut(graph));

  assertEquals(graph.includes(a), false);
  assertEquals(graph.includes(b), false);
  assertEquals(graph.length, 4);
  assertEquals(extA1.ports[0].node, extB1);
  assertEquals(extB1.ports[0].node, extA1);
  assertEquals(extA2.ports[0].node, extB2);
  assertEquals(extB2.ports[0].node, extA2);
});

Deno.test("annihilate: unequal port counts creates erasers", () => {
  const a = makeNode("abs", 3);
  const b = makeNode("app", 2);
  const extA1 = makeNode("var", 1);
  const extA2 = makeNode("var", 1);
  const extB1 = makeNode("var", 1);

  link({ node: a, port: 0 }, { node: b, port: 0 });
  link({ node: a, port: 1 }, { node: extA1, port: 0 });
  link({ node: a, port: 2 }, { node: extA2, port: 0 });
  link({ node: b, port: 1 }, { node: extB1, port: 0 });

  const graph: Graph = [a, b, extA1, extA2, extB1];
  reduceAnnihilate(a, asMut(graph));

  assertEquals(graph.includes(a), false);
  assertEquals(graph.includes(b), false);
  assertEquals(extA1.ports[0].node, extB1);
  assertEquals(extA2.ports[0].node.type, "era");
  assertEquals(graph.includes(extA2.ports[0].node), true);
});

// ─── reduceErase ───────────────────────────────────────────────────

Deno.test("erase: binary node propagates erasers to aux ports", () => {
  const node = makeNode("abs", 3);
  const eraser = makeNode("era", 1);
  const ext1 = makeNode("var", 1);
  const ext2 = makeNode("var", 1);

  link({ node: node, port: 0 }, { node: eraser, port: 0 });
  link({ node: node, port: 1 }, { node: ext1, port: 0 });
  link({ node: node, port: 2 }, { node: ext2, port: 0 });

  const graph: Graph = [node, eraser, ext1, ext2];
  reduceErase(node, asMut(graph));

  assertEquals(graph.includes(node), false);
  assertEquals(graph.includes(eraser), false);
  assertEquals(ext1.ports[0].node.type, "era");
  assertEquals(ext2.ports[0].node.type, "era");
  assertEquals(ext1.ports[0].node !== ext2.ports[0].node, true);
  assertEquals(graph.length, 4);
});

Deno.test("erase: unary node leaves empty graph", () => {
  const node = makeNode("var", 1);
  const eraser = makeNode("era", 1);

  link({ node: node, port: 0 }, { node: eraser, port: 0 });

  const graph: Graph = [node, eraser];
  reduceErase(node, asMut(graph));

  assertEquals(graph.includes(node), false);
  assertEquals(graph.includes(eraser), false);
  assertEquals(graph.length, 0);
});

// ─── reduceCommute ─────────────────────────────────────────────────

Deno.test("commute: binary nodes produce 2x2 cross-copy", () => {
  const node = makeNode("abs", 3);
  const other = makeNode("app", 3);
  const extN1 = makeNode("var", 1);
  const extN2 = makeNode("var", 1);
  const extO1 = makeNode("var", 1);
  const extO2 = makeNode("var", 1);

  link({ node: node, port: 0 }, { node: other, port: 0 });
  link({ node: node, port: 1 }, { node: extN1, port: 0 });
  link({ node: node, port: 2 }, { node: extN2, port: 0 });
  link({ node: other, port: 1 }, { node: extO1, port: 0 });
  link({ node: other, port: 2 }, { node: extO2, port: 0 });

  const graph: Graph = [node, other, extN1, extN2, extO1, extO2];
  const { nodeClones, otherClones } = reduceCommute(node, asMut(graph));

  assertEquals(graph.includes(node), false);
  assertEquals(graph.includes(other), false);
  assertEquals(nodeClones.length, 2);
  assertEquals(otherClones.length, 2);
  assertEquals(otherClones[0].ports[0].node, extN1);
  assertEquals(otherClones[1].ports[0].node, extN2);
  assertEquals(nodeClones[0].ports[0].node, extO1);
  assertEquals(nodeClones[1].ports[0].node, extO2);
  assertEquals(nodeClones[0].ports[1].node, otherClones[0]);
  assertEquals(nodeClones[0].ports[2].node, otherClones[1]);
  assertEquals(nodeClones[1].ports[1].node, otherClones[0]);
  assertEquals(nodeClones[1].ports[2].node, otherClones[1]);
});

Deno.test("commute: preserves levelDeltas", () => {
  const node = makeNode("abs", 2);
  node.levelDeltas = [1, -1];
  const other = makeNode("app", 2);

  link({ node: node, port: 0 }, { node: other, port: 0 });
  const extN = makeNode("var", 1);
  const extO = makeNode("var", 1);
  link({ node: node, port: 1 }, { node: extN, port: 0 });
  link({ node: other, port: 1 }, { node: extO, port: 0 });

  const graph: Graph = [node, other, extN, extO];
  const { nodeClones } = reduceCommute(node, asMut(graph));

  assertEquals(nodeClones[0].levelDeltas !== node.levelDeltas, true);
  assertEquals(JSON.stringify(nodeClones[0].levelDeltas), "[1,-1]");
});

Deno.test("annihilate/commute: throw for non-interacting nodes", () => {
  const a = makeNode("abs", 2);
  const b = makeNode("abs", 2);
  a.ports[0] = { node: b, port: 0 };

  assertThrows(() => reduceAnnihilate(a, asMut([a, b])));
  assertThrows(() => reduceCommute(a, asMut([a, b])));
});
