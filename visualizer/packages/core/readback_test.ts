// Tests for readback: compile lambda terms to delta-net graphs, then read them back.

import { assertEquals } from "$std/assert/mod.ts";
import { astToString, getExpressionType, parseSource } from "./ast.ts";
import { deltanets } from "./systems/deltanets/index.ts";
import { readbackGraphToString } from "./systems/deltanets/readback.ts";

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
