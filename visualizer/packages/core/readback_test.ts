// Tests for readback: compile lambda terms to delta-net graphs, then read them back.

import { assertEquals } from "$std/assert/mod.ts";
import { astToString, getExpressionType, parseSource } from "./ast.ts";
import { deltanets } from "./systems/deltanets/index.ts";
import { readbackGraph, readbackGraphToString } from "./systems/deltanets/readback.ts";

const { buildGraph } = deltanets;

function roundtrip(source: string, expected?: string) {
  const { ast, errs } = parseSource(source);
  if (!ast || (errs && errs.length > 0)) {
    throw new Error(`Parse error for "${source}": ${JSON.stringify(errs)}`);
  }
  const systemType = getExpressionType(ast);
  const graph = buildGraph(ast, systemType, false);
  const rbStr = readbackGraphToString(graph);
  const exp = expected ?? astToString(ast);
  assertEquals(rbStr, exp, `readback of "${source}"`);
}

Deno.test("readback: identity", () => roundtrip("λx.x"));
Deno.test("readback: constant function", () => roundtrip("λx.λy.x"));
Deno.test("readback: simple application", () => roundtrip("λf.λx.f x"));
Deno.test("readback: non-linear duplication", () => roundtrip("λx.x x"));
Deno.test("readback: Church numeral 2", () => roundtrip("λf.λx.f (f x)"));
Deno.test("readback: erasure", () => roundtrip("λx.λy.y"));
Deno.test("readback: application of terms", () => roundtrip("(λx.x) (λy.y)"));
Deno.test("readback: free variable", () => roundtrip("λx.y"));

// ─── Edge cases ────────────────────────────────────────────────────

Deno.test("readback: Church numeral 3 (deeper nesting)", () =>
  roundtrip("λf.λx.f (f (f x))"));

Deno.test("readback: triple abstraction with erasure", () =>
  roundtrip("λx.λy.λz.x"));

Deno.test("readback: nested application left-associated", () =>
  roundtrip("λf.λx.f x x"));

Deno.test("readback: K combinator applied", () =>
  roundtrip("(λx.λy.x) (λa.a)"));

// ─── AST readback (readbackGraph) ──────────────────────────────────

function buildAndReadbackAST(source: string) {
  const { ast } = parseSource(source);
  if (!ast) throw new Error(`Parse error for "${source}"`);
  const systemType = getExpressionType(ast);
  const graph = buildGraph(ast, systemType, false);
  return readbackGraph(graph);
}

Deno.test("readbackGraph: identity returns abs→var", () => {
  const ast = buildAndReadbackAST("λx.x");
  assertEquals(ast?.type, "abs");
  if (ast?.type === "abs") {
    assertEquals(ast.name, "x");
    assertEquals(ast.body.type, "var");
    if (ast.body.type === "var") assertEquals(ast.body.name, "x");
  }
});

Deno.test("readbackGraph: application structure", () => {
  const ast = buildAndReadbackAST("λf.λx.f x");
  assertEquals(ast?.type, "abs");
  if (ast?.type === "abs") {
    assertEquals(ast.body.type, "abs");
    if (ast.body.type === "abs") {
      assertEquals(ast.body.body.type, "app");
    }
  }
});

Deno.test("readbackGraph: constant function erases second param", () => {
  const ast = buildAndReadbackAST("λx.λy.x");
  assertEquals(ast?.type, "abs");
  if (ast?.type === "abs") {
    assertEquals(ast.name, "x");
    assertEquals(ast.body.type, "abs");
    if (ast.body.type === "abs") {
      assertEquals(ast.body.body.type, "var");
      if (ast.body.body.type === "var") assertEquals(ast.body.body.name, "x");
    }
  }
});
