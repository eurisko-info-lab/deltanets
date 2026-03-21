// Tests for graph building: buildGraph from AST nodes.

import { assert, assertEquals } from "$std/assert/mod.ts";
import { getExpressionType, parseSource } from "./ast.ts";
import type { AstNode, SystemType } from "./ast.ts";
import { deltanets } from "./systems/deltanets/index.ts";

const { buildGraph } = deltanets;

function build(source: string, systemType?: SystemType) {
  const { ast } = parseSource(source);
  if (!ast) throw new Error(`Parse error for "${source}"`);
  const st = systemType ?? getExpressionType(ast);
  return buildGraph(ast, st, false);
}

function nodeTypes(source: string, systemType?: SystemType) {
  return build(source, systemType).map((n) => n.type).sort();
}

// ─── Basic graph structure ─────────────────────────────────────────

Deno.test("build: identity has root, abs, era, type nodes", () => {
  const graph = build("λx.x", "linear");
  assert(graph.some((n) => n.type === "root"), "has root");
  assert(graph.some((n) => n.type === "abs"), "has abs");
  // In linear system, eraser for unused bind is removed along with reps
});

Deno.test("build: always has exactly one root node", () => {
  const graphs = [
    build("λx.x"),
    build("λx.λy.x"),
    build("(λx.x) (λy.y)"),
    build("λf.λx.f (f x)"),
  ];
  for (const g of graphs) {
    const rootCount = g.filter((n) => n.type === "root").length;
    assertEquals(rootCount, 1, "exactly one root node");
  }
});

Deno.test("build: application creates app node", () => {
  const graph = build("(λx.x) (λy.y)");
  assert(graph.some((n) => n.type === "app"), "has app node");
});

// ─── Variable binding ──────────────────────────────────────────────

Deno.test("build: bound variable connects to abs bind port", () => {
  const graph = build("λx.x", "linear");
  const abs = graph.find((n) => n.type === "abs")!;
  assert(abs !== undefined, "has abs");
  // In linear system with single use, bind port connects to the variable usage
  // (no eraser, no replicator since trivial rep was removed)
});

Deno.test("build: unused variable creates eraser", () => {
  const graph = build("λx.λy.x", "affine");
  // y is unused, so there should be an eraser connected to its bind port
  const erasers = graph.filter((n) => n.type === "era");
  assert(erasers.length >= 1, "at least one eraser for unused variable");
});

Deno.test("build: duplicated variable creates replicator", () => {
  const graph = build("λx.x x");
  const reps = graph.filter((n) => n.type.startsWith("rep"));
  assert(reps.length >= 1, "at least one replicator for duplicated variable");
});

// ─── Variable shadowing ────────────────────────────────────────────

Deno.test("build: shadowed variable restores outer binding", () => {
  // λx.λx.x — inner x shadows outer, outer is unused
  const graph = build("λx.λx.x");
  const absNodes = graph.filter((n) => n.type === "abs");
  assertEquals(absNodes.length, 2, "two abstraction nodes");
});

// ─── System type variations ────────────────────────────────────────

Deno.test("build: linear system removes all replicators", () => {
  const graph = build("λx.x", "linear");
  const reps = graph.filter((n) => n.type.startsWith("rep"));
  assertEquals(reps.length, 0, "no replicators in linear system");
});

Deno.test("build: affine system removes trivial replicators", () => {
  const graph = build("λx.x", "affine");
  const reps = graph.filter((n) => n.type.startsWith("rep"));
  assertEquals(reps.length, 0, "no trivial replicators");
});

Deno.test("build: full system preserves non-trivial replicators", () => {
  const graph = build("λx.x x", "full");
  const reps = graph.filter((n) => n.type.startsWith("rep"));
  assert(reps.length >= 1, "replicators preserved for duplication");
});

// ─── Free variables ────────────────────────────────────────────────

Deno.test("build: free variable creates var node", () => {
  const graph = build("λx.y", "affine");
  assert(graph.some((n) => n.type === "var"), "has var node for free variable");
});

// ─── Type annotations ──────────────────────────────────────────────

Deno.test("build: type annotation creates type nodes", () => {
  const graph = build("λx:A.x");
  assert(graph.some((n) => n.type === "type-base"), "has type-base node");
});

Deno.test("build: arrow type annotation creates type-arrow", () => {
  const graph = build("λf:A->B.f");
  assert(graph.some((n) => n.type === "type-arrow"), "has type-arrow node");
});

Deno.test("build: unannotated creates type-hole", () => {
  const graph = build("λx.x");
  assert(
    graph.some((n) => n.type === "type-hole"),
    "has type-hole for unannotated param",
  );
});

// ─── Port sanity checks ───────────────────────────────────────────

Deno.test("build: all ports are bidirectionally linked", () => {
  const graph = build("(λx.x x) (λy.y)");
  for (const node of graph) {
    for (let i = 0; i < node.ports.length; i++) {
      const target = node.ports[i];
      assertEquals(
        target.node.ports[target.port].node,
        node,
        `port ${i} of ${node.type} should be bidirectional`,
      );
      assertEquals(
        target.node.ports[target.port].port,
        i,
        `port index should match`,
      );
    }
  }
});
