// Tests for redex detection: getRedex, getRedexes across system types.

import { assert, assertEquals } from "$std/assert/mod.ts";
import { getExpressionType, parseSource } from "./ast.ts";
import { deltanets } from "./systems/deltanets/index.ts";
import { getRedex, getRedexes } from "./systems/deltanets/redexes.ts";

const { buildGraph } = deltanets;

function buildAndGetRedexes(
  source: string,
  systemType?: "linear" | "affine" | "relevant" | "full",
) {
  const { ast } = parseSource(source);
  if (!ast) throw new Error(`Parse error for "${source}"`);
  const st = systemType ?? getExpressionType(ast);
  const graph = buildGraph(ast, st, false);
  const redexes = getRedexes(graph, st, false);
  return { graph, redexes, ast };
}

// ─── getRedex ──────────────────────────────────────────────────────

Deno.test("getRedex: finds existing redex", () => {
  const { graph, redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  assert(redexes.length > 0, "should have at least one redex");
  const r = redexes[0];
  const found = getRedex(r.a, r.b, redexes);
  assertEquals(found, r);
});

Deno.test("getRedex: returns undefined for non-redex pair", () => {
  const { graph, redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  const root = graph.find((n) => n.type === "root")!;
  const found = getRedex(root, root, redexes);
  assertEquals(found, undefined);
});

Deno.test("getRedex: order-independent matching", () => {
  const { redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  assert(redexes.length > 0);
  const r = redexes[0];
  // Reversed order should still find the same redex
  const found = getRedex(r.b, r.a, redexes);
  assertEquals(found, r);
});

// ─── Linear system ─────────────────────────────────────────────────

Deno.test("redexes: linear identity application has one redex", () => {
  const { redexes } = buildAndGetRedexes("(λx.x) (λy.y)", "linear");
  assertEquals(redexes.length, 1);
  assertEquals(redexes[0].optimal, true);
  // Verify the redex connects abs ↔ app via principal ports
  const types = [redexes[0].a.type, redexes[0].b.type].sort();
  assertEquals(types, ["abs", "app"]);
  assertEquals(redexes[0].a.ports[0].node, redexes[0].b);
  assertEquals(redexes[0].b.ports[0].node, redexes[0].a);
});

Deno.test("redexes: linear normal form has no redexes", () => {
  const { redexes } = buildAndGetRedexes("λx.x", "linear");
  assertEquals(redexes.length, 0);
});

Deno.test("redexes: linear nested application", () => {
  const { redexes } = buildAndGetRedexes("(λf.λx.f x) (λy.y)", "linear");
  assertEquals(redexes.length, 1, "exactly one beta-redex");
  assertEquals(redexes[0].optimal, true);
  const types = [redexes[0].a.type, redexes[0].b.type].sort();
  assertEquals(types, ["abs", "app"]);
});

// ─── Full system ───────────────────────────────────────────────────

Deno.test("redexes: full system with duplication", () => {
  const { redexes } = buildAndGetRedexes("(λx.x x) (λy.y)");
  assert(redexes.length >= 1, "should have at least one redex");
  // Must include an abs-app annihilation
  const absApp = redexes.find((r) => {
    const ts = [r.a.type, r.b.type].sort();
    return ts[0] === "abs" && ts[1] === "app";
  });
  assert(absApp !== undefined, "should include abs-app redex");
  assertEquals(absApp.a.ports[0].node, absApp.b, "redex pair via principal ports");
});

Deno.test("redexes: full system with erasure", () => {
  const { redexes } = buildAndGetRedexes("(λx.λy.x) (λz.z)");
  assert(redexes.length >= 1);
  // Must contain abs-app annihilation
  const absApp = redexes.find((r) => {
    const ts = [r.a.type, r.b.type].sort();
    return ts[0] === "abs" && ts[1] === "app";
  });
  assert(absApp !== undefined, "should include abs-app redex");
  assertEquals(absApp.optimal, true, "abs-app should be optimal");
});

Deno.test("redexes: Church numeral application", () => {
  const { redexes } = buildAndGetRedexes("(λf.λx.f (f x)) (λy.y)");
  assert(redexes.length >= 1);
  assert(redexes.some((r) => r.optimal));
  // All redex pairs should interact via principal ports (port 0)
  for (const r of redexes) {
    assertEquals(r.a.ports[0].node, r.b);
    assertEquals(r.b.ports[0].node, r.a);
  }
});

Deno.test("redexes: omega combinator (self-application)", () => {
  const { redexes } = buildAndGetRedexes("(λx.x x) (λx.x x)");
  assert(redexes.length >= 1);
  // Verify principal port interaction invariant
  for (const r of redexes) {
    assertEquals(r.a.ports[0].node, r.b);
  }
});

// ─── Optimal marking ──────────────────────────────────────────────

Deno.test("redexes: multiple redexes marks at least one optimal", () => {
  // K I I = (λx.λy.x) (λz.z) (λw.w) — has two potential redexes
  const { redexes } = buildAndGetRedexes("(λx.λy.x) (λz.z) (λw.w)");
  assert(redexes.length >= 1, "K I I should have at least one redex");
  assert(
    redexes.some((r) => r.optimal),
    "at least one redex should be optimal",
  );
  // All redexes interact on principal ports
  for (const r of redexes) {
    assertEquals(r.a.ports[0].node, r.b);
  }
});

Deno.test("redexes: optimal redex is sorted first", () => {
  const { redexes } = buildAndGetRedexes("(λx.λy.x) (λz.z) (λw.w)");
  if (redexes.length > 1) {
    assertEquals(redexes[0].optimal, true, "first redex should be optimal");
    // Verify the first redex is an abs-app pair (the outermost application)
    const types = [redexes[0].a.type, redexes[0].b.type].sort();
    assertEquals(types, ["abs", "app"]);
  }
});

// ─── System type variations ────────────────────────────────────────

Deno.test("redexes: affine system with erasure", () => {
  const { redexes } = buildAndGetRedexes("(λx.λy.y) (λz.z)", "affine");
  assert(redexes.length >= 1);
  // Should include at least an abs-app pair
  const absApp = redexes.find((r) => {
    const ts = [r.a.type, r.b.type].sort();
    return ts[0] === "abs" && ts[1] === "app";
  });
  assert(absApp !== undefined, "affine system should detect abs-app redex");
  assertEquals(absApp.a.ports[0].node, absApp.b, "connected via principal ports");
});

Deno.test("redexes: relevant system with sharing", () => {
  const { redexes } = buildAndGetRedexes("(λx.x x) (λy.y)", "relevant");
  assert(redexes.length >= 1);
  // Should include abs-app interaction
  const absApp = redexes.find((r) => {
    const ts = [r.a.type, r.b.type].sort();
    return ts[0] === "abs" && ts[1] === "app";
  });
  assert(absApp !== undefined, "relevant system should detect abs-app redex");
  assertEquals(absApp.a.ports[0].node, absApp.b, "connected via principal ports");
});

// ─── Reduce closure ────────────────────────────────────────────────

Deno.test("redexes: reduce closure executes without error", () => {
  const { graph, redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  assertEquals(redexes.length, 1);
  const absAppTypes = [redexes[0].a.type, redexes[0].b.type].sort();
  assertEquals(absAppTypes, ["abs", "app"]);
  // Should not throw
  redexes[0].reduce();
});

Deno.test("redexes: reduce removes the redex nodes from graph", () => {
  const { graph, redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  const before = graph.length;
  const a = redexes[0].a;
  const b = redexes[0].b;
  redexes[0].reduce();
  assert(graph.length < before, "graph should shrink after reduction");
  assert(!graph.includes(a), "redex node a should be removed");
  assert(!graph.includes(b), "redex node b should be removed");
});

Deno.test("redexes: reduce preserves graph bidirectionality", () => {
  const { graph, redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  redexes[0].reduce();
  for (const node of graph) {
    for (let i = 0; i < node.ports.length; i++) {
      const target = node.ports[i];
      assertEquals(
        target.node.ports[target.port].node,
        node,
        `after reduce: port ${i} of ${node.type} should be bidirectional`,
      );
    }
  }
});
