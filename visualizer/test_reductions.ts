// Tests for the universal interaction net reduction primitives.
// Run: deno run test_reductions.ts

import { reduceAnnihilate, reduceErase, reduceCommute } from "./lib/core/reductions.ts";
import { link } from "./lib/core/graph.ts";
import type { Node, Graph } from "./lib/core/types.ts";

let passed = 0;
let failed = 0;

function assert(condition: boolean, msg: string) {
  if (condition) {
    console.log(`  ✓ ${msg}`);
    passed++;
  } else {
    console.error(`  ✗ ${msg}`);
    failed++;
  }
}

// Helper: create a node with the given type and number of ports (unlinked).
function makeNode(type: string, numPorts: number): Node {
  const node: Node = { type, ports: [] };
  // Pre-allocate port slots pointing to self (will be overwritten by link)
  for (let i = 0; i < numPorts; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
}

// ─── reduceAnnihilate ──────────────────────────────────────────────

console.log("\n=== reduceAnnihilate ===\n");

{
  console.log("Two binary nodes (e.g. abs-abs) with aux wires:");
  // A(0, 1, 2) <> B(0, 1, 2) with external nodes extA1, extA2, extB1, extB2
  const a = makeNode("abs", 3);
  const b = makeNode("abs", 3);
  const extA1 = makeNode("var", 1);
  const extA2 = makeNode("var", 1);
  const extB1 = makeNode("var", 1);
  const extB2 = makeNode("var", 1);

  // Wire principal ports together
  link({ node: a, port: 0 }, { node: b, port: 0 });
  // Wire aux ports to externals
  link({ node: a, port: 1 }, { node: extA1, port: 0 });
  link({ node: a, port: 2 }, { node: extA2, port: 0 });
  link({ node: b, port: 1 }, { node: extB1, port: 0 });
  link({ node: b, port: 2 }, { node: extB2, port: 0 });

  const graph: Graph = [a, b, extA1, extA2, extB1, extB2];
  reduceAnnihilate(a, graph);

  assert(!graph.includes(a), "node a removed");
  assert(!graph.includes(b), "node b removed");
  assert(graph.length === 4, `graph has 4 nodes (got ${graph.length})`);
  // extA1 <-> extB1, extA2 <-> extB2
  assert(extA1.ports[0].node === extB1, "extA1 linked to extB1");
  assert(extB1.ports[0].node === extA1, "extB1 linked to extA1");
  assert(extA2.ports[0].node === extB2, "extA2 linked to extB2");
  assert(extB2.ports[0].node === extA2, "extB2 linked to extA2");
}

{
  console.log("Unequal port counts (3 vs 2) creates erasers:");
  const a = makeNode("abs", 3); // 1 principal + 2 aux
  const b = makeNode("app", 2); // 1 principal + 1 aux
  const extA1 = makeNode("var", 1);
  const extA2 = makeNode("var", 1);
  const extB1 = makeNode("var", 1);

  link({ node: a, port: 0 }, { node: b, port: 0 });
  link({ node: a, port: 1 }, { node: extA1, port: 0 });
  link({ node: a, port: 2 }, { node: extA2, port: 0 });
  link({ node: b, port: 1 }, { node: extB1, port: 0 });

  const graph: Graph = [a, b, extA1, extA2, extB1];
  reduceAnnihilate(a, graph);

  assert(!graph.includes(a), "node a removed");
  assert(!graph.includes(b), "node b removed");
  // Matching aux: a[1]<->b[1] → extA1 <-> extB1
  assert(extA1.ports[0].node === extB1, "matching aux ports connected");
  // Excess aux a[2] → extA2 should be connected to an eraser
  const eraserForA2 = extA2.ports[0].node;
  assert(eraserForA2.type === "era", "excess port gets an eraser");
  assert(graph.includes(eraserForA2), "eraser added to graph");
}

// ─── reduceErase ───────────────────────────────────────────────────

console.log("\n=== reduceErase ===\n");

{
  console.log("Erase a binary node:");
  const node = makeNode("abs", 3);
  const eraser = makeNode("era", 1);
  const ext1 = makeNode("var", 1);
  const ext2 = makeNode("var", 1);

  link({ node: node, port: 0 }, { node: eraser, port: 0 });
  link({ node: node, port: 1 }, { node: ext1, port: 0 });
  link({ node: node, port: 2 }, { node: ext2, port: 0 });

  const graph: Graph = [node, eraser, ext1, ext2];
  reduceErase(node, graph);

  assert(!graph.includes(node), "node removed");
  assert(!graph.includes(eraser), "original eraser removed");
  // Each aux port gets its own new eraser
  const era1 = ext1.ports[0].node;
  const era2 = ext2.ports[0].node;
  assert(era1.type === "era", "ext1 connected to new eraser");
  assert(era2.type === "era", "ext2 connected to new eraser");
  assert(era1 !== era2, "each aux port gets a distinct eraser");
  assert(graph.length === 4, `graph has 4 nodes (2 ext + 2 new erasers, got ${graph.length})`);
}

{
  console.log("Erase a unary node (no aux ports):");
  const node = makeNode("var", 1);
  const eraser = makeNode("era", 1);

  link({ node: node, port: 0 }, { node: eraser, port: 0 });

  const graph: Graph = [node, eraser];
  reduceErase(node, graph);

  assert(!graph.includes(node), "node removed");
  assert(!graph.includes(eraser), "eraser removed");
  assert(graph.length === 0, `graph is empty (got ${graph.length})`);
}

// ─── reduceCommute ─────────────────────────────────────────────────

console.log("\n=== reduceCommute ===\n");

{
  console.log("Commute two binary nodes (2x2 cross-copy):");
  // node(3 ports) <> other(3 ports) → creates 2 clones of each, with 2x2 cross-links
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
  const { nodeClones, otherClones } = reduceCommute(node, graph);

  assert(!graph.includes(node), "original node removed");
  assert(!graph.includes(other), "original other removed");
  assert(nodeClones.length === 2, "2 clones of node");
  assert(otherClones.length === 2, "2 clones of other");
  // otherClones[0] principal → extN1, otherClones[1] principal → extN2
  assert(otherClones[0].ports[0].node === extN1, "otherClone[0] principal → extN1");
  assert(otherClones[1].ports[0].node === extN2, "otherClone[1] principal → extN2");
  // nodeClones[0] principal → extO1, nodeClones[1] principal → extO2
  assert(nodeClones[0].ports[0].node === extO1, "nodeClone[0] principal → extO1");
  assert(nodeClones[1].ports[0].node === extO2, "nodeClone[1] principal → extO2");
  // Cross-links: nodeClones[i].ports[j+1] <-> otherClones[j].ports[i+1]
  assert(nodeClones[0].ports[1].node === otherClones[0], "cross-link nodeClone[0][1] <-> otherClone[0]");
  assert(nodeClones[0].ports[2].node === otherClones[1], "cross-link nodeClone[0][2] <-> otherClone[1]");
  assert(nodeClones[1].ports[1].node === otherClones[0], "cross-link nodeClone[1][1] <-> otherClone[0]");
  assert(nodeClones[1].ports[2].node === otherClones[1], "cross-link nodeClone[1][2] <-> otherClone[1]");
}

{
  console.log("Commute preserves levelDeltas:");
  const node = makeNode("abs", 2);
  node.levelDeltas = [1, -1];
  const other = makeNode("app", 2);

  link({ node: node, port: 0 }, { node: other, port: 0 });
  const extN = makeNode("var", 1);
  const extO = makeNode("var", 1);
  link({ node: node, port: 1 }, { node: extN, port: 0 });
  link({ node: other, port: 1 }, { node: extO, port: 0 });

  const graph: Graph = [node, other, extN, extO];
  const { nodeClones } = reduceCommute(node, graph);

  assert(nodeClones[0].levelDeltas !== node.levelDeltas, "levelDeltas is a distinct array (not shared ref)");
  assert(JSON.stringify(nodeClones[0].levelDeltas) === "[1,-1]", "levelDeltas values preserved");
}

{
  console.log("Sanity check: non-interacting nodes throw:");
  const a = makeNode("abs", 2);
  const b = makeNode("abs", 2);
  // a[0] → b but b[0] → b (not pointing back at a)
  a.ports[0] = { node: b, port: 0 };

  let threw = false;
  try { reduceAnnihilate(a, [a, b]); } catch { threw = true; }
  assert(threw, "reduceAnnihilate throws for non-interacting pair");

  threw = false;
  try { reduceCommute(a, [a, b]); } catch { threw = true; }
  assert(threw, "reduceCommute throws for non-interacting pair");
}

// ─── Summary ───────────────────────────────────────────────────────

console.log(`\n${passed} passed, ${failed} failed\n`);
if (failed > 0) Deno.exit(1);
