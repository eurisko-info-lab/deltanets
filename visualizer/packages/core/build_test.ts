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
  assertEquals(
    graph.filter((n) => n.type === "abs").length,
    1,
    "exactly one abs node",
  );
  assertEquals(
    graph.filter((n) => n.type === "root").length,
    1,
    "exactly one root node",
  );
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
  assertEquals(
    graph.filter((n) => n.type === "app").length,
    1,
    "exactly one app node",
  );
  assertEquals(
    graph.filter((n) => n.type === "abs").length,
    2,
    "two abs nodes for two lambdas",
  );
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
  // y is unused, so there should be exactly one eraser connected to its bind port
  const erasers = graph.filter((n) => n.type === "era");
  assertEquals(erasers.length, 1, "exactly one eraser for one unused variable");
  // The eraser should be connected to something (the abs node's bind port)
  assertEquals(erasers[0].ports[0].node.type, "abs");
});

Deno.test("build: duplicated variable creates replicator", () => {
  const graph = build("λx.x x");
  const reps = graph.filter((n) => n.type.startsWith("rep"));
  assertEquals(reps.length, 1, "exactly one replicator for one duplication");
  // Replicator should have 3 ports (principal + 2 aux)
  assertEquals(reps[0].ports.length, 3);
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
  assertEquals(reps.length, 1, "exactly one replicator for one duplication");
});

// ─── Free variables ────────────────────────────────────────────────

Deno.test("build: free variable creates var node", () => {
  const graph = build("λx.y", "affine");
  assert(graph.some((n) => n.type === "var"), "has var node for free variable");
});

// ─── Type annotations ──────────────────────────────────────────────

Deno.test("build: type annotation creates type nodes", () => {
  const graph = build("λx:A.x");
  assertEquals(
    graph.filter((n) => n.type === "type-base").length,
    1,
    "exactly one type-base node",
  );
});

Deno.test("build: arrow type annotation creates type-arrow", () => {
  const graph = build("λf:A->B.f");
  assertEquals(
    graph.filter((n) => n.type === "type-arrow").length,
    1,
    "exactly one type-arrow node",
  );
  // Arrow type must also have two type-base children for A and B
  assertEquals(
    graph.filter((n) => n.type === "type-base").length,
    2,
    "two type-base nodes for A and B",
  );
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

// ─── Deeper structure tests ────────────────────────────────────────

Deno.test("build: root principal port connects to top-level node", () => {
  const graph = build("λx.x");
  const root = graph.find((n) => n.type === "root")!;
  // Root's principal port should connect to the top-level abs
  assertEquals(root.ports[0].node.type, "abs");
});

Deno.test("build: bidirectionality holds for all system types", () => {
  const exprs = ["λx.x", "λx.λy.x", "λx.x x", "λx.λy.x x"];
  const systemTypes: Array<"linear" | "affine" | "relevant" | "full"> = [
    "linear",
    "affine",
    "relevant",
    "full",
  ];
  for (const st of systemTypes) {
    for (const expr of exprs) {
      const graph = build(expr, st);
      for (const node of graph) {
        for (let i = 0; i < node.ports.length; i++) {
          const target = node.ports[i];
          assertEquals(
            target.node.ports[target.port].node,
            node,
            `[${st}] "${expr}": port ${i} of ${node.type} should be bidirectional`,
          );
        }
      }
    }
  }
});

Deno.test("build: multiple erasures in full system", () => {
  // λx.λy.λz.x — both y and z are unused
  const graph = build("λx.λy.λz.x", "full");
  const erasers = graph.filter((n) => n.type === "era");
  assertEquals(erasers.length, 2, "two erasers for two unused variables");
});

Deno.test("build: triple duplication creates replicator with extra aux port", () => {
  // λx.x x x – single fan-out node with 4 ports (1 principal + 3 aux)
  const graph = build("λx.x x x", "full");
  const reps = graph.filter((n) => n.type.startsWith("rep"));
  assertEquals(reps.length, 1, "one replicator for triple use");
  assertEquals(reps[0].ports.length, 4, "replicator has 4 ports for 3-way fan-out");
});
