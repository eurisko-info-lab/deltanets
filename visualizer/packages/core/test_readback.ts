// Test readback: compile lambda terms to delta-net graphs, then read them back.

import { parseSource, astToString, getExpressionType } from "./ast.ts";
import { deltanets } from "./systems/deltanets/index.ts";
import { readbackGraph, readbackGraphToString } from "./systems/deltanets/readback.ts";

const { buildGraph } = deltanets;

let passed = 0;
let failed = 0;

function check(source: string, expected?: string) {
  const { ast, errs } = parseSource(source);
  if (errs && errs.length > 0) {
    console.error(`Parse error for "${source}":`, errs);
    failed++;
    return;
  }
  if (!ast) {
    console.error(`No AST for "${source}"`);
    failed++;
    return;
  }

  const systemType = getExpressionType(ast);
  const graph = buildGraph(ast, systemType, false);

  const rbAst = readbackGraph(graph);
  const rbAstStr = rbAst ? astToString(rbAst) : "(null)";
  const rbStr = readbackGraphToString(graph);

  const origStr = astToString(ast);
  const exp = expected ?? origStr;

  const pass = rbStr === exp;
  const icon = pass ? "✓" : "✗";
  console.log(`${icon} "${source}" → rb="${rbStr}", ast="${rbAstStr}"${pass ? "" : ` (expected "${exp}")`}`);
  if (pass) passed++;
  else failed++;
}

console.log("=== Readback Tests ===\n");

// Identity
check("λx.x");

// Constant function
check("λx.λy.x");

// Simple application
check("λf.λx.f x");

// Non-linear: duplication
check("λx.x x");

// Church numeral 2
check("λf.λx.f (f x)");

// Erasure
check("λx.λy.y");

// Application of terms
check("(λx.x) (λy.y)");

// Free variable
check("λx.y");

console.log(`\n${passed} passed, ${failed} failed`);
if (failed > 0) Deno.exit(1);
