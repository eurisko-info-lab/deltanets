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
});

Deno.test("redexes: linear normal form has no redexes", () => {
  const { redexes } = buildAndGetRedexes("λx.x", "linear");
  assertEquals(redexes.length, 0);
});

Deno.test("redexes: linear nested application", () => {
  const { redexes } = buildAndGetRedexes("(λf.λx.f x) (λy.y)", "linear");
  assert(redexes.length >= 1, "at least one redex");
  assert(redexes.some((r) => r.optimal), "at least one is optimal");
});

// ─── Full system ───────────────────────────────────────────────────

Deno.test("redexes: full system with duplication", () => {
  const { redexes } = buildAndGetRedexes("(λx.x x) (λy.y)");
  assert(redexes.length >= 1, "should have at least one redex");
});

Deno.test("redexes: full system with erasure", () => {
  const { redexes } = buildAndGetRedexes("(λx.λy.x) (λz.z)");
  assert(redexes.length >= 1);
});

Deno.test("redexes: Church numeral application", () => {
  const { redexes } = buildAndGetRedexes("(λf.λx.f (f x)) (λy.y)");
  assert(redexes.length >= 1);
  assert(redexes.some((r) => r.optimal));
});

Deno.test("redexes: omega combinator (self-application)", () => {
  const { redexes } = buildAndGetRedexes("(λx.x x) (λx.x x)");
  assert(redexes.length >= 1);
});

// ─── Optimal marking ──────────────────────────────────────────────

Deno.test("redexes: multiple redexes marks at least one optimal", () => {
  // K I I = (λx.λy.x) (λz.z) (λw.w) — has two potential redexes
  const { redexes } = buildAndGetRedexes("(λx.λy.x) (λz.z) (λw.w)");
  assert(redexes.length >= 1);
  assert(
    redexes.some((r) => r.optimal),
    "at least one redex should be optimal",
  );
});

Deno.test("redexes: optimal redex is sorted first", () => {
  const { redexes } = buildAndGetRedexes("(λx.λy.x) (λz.z) (λw.w)");
  if (redexes.length > 1) {
    assertEquals(redexes[0].optimal, true, "first redex should be optimal");
  }
});

// ─── System type variations ────────────────────────────────────────

Deno.test("redexes: affine system with erasure", () => {
  const { redexes } = buildAndGetRedexes("(λx.λy.y) (λz.z)", "affine");
  assert(redexes.length >= 1);
});

Deno.test("redexes: relevant system with sharing", () => {
  const { redexes } = buildAndGetRedexes("(λx.x x) (λy.y)", "relevant");
  assert(redexes.length >= 1);
});

// ─── Reduce closure ────────────────────────────────────────────────

Deno.test("redexes: reduce closure executes without error", () => {
  const { redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  assert(redexes.length >= 1);
  // Should not throw
  redexes[0].reduce();
});

Deno.test("redexes: reduce removes the redex nodes from graph", () => {
  const { graph, redexes } = buildAndGetRedexes("(λx.x) (λy.y)");
  const before = graph.length;
  redexes[0].reduce();
  assert(graph.length < before, "graph should shrink after reduction");
});
