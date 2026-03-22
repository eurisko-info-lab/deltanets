// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Public API
// compile(source) → { systems, graphs, definitions, errors }
// ═══════════════════════════════════════════════════════════════════

import { LexError, tokenize } from "./lexer.ts";
import { parse, ParseError } from "./parser.ts";
import { EvalError, evaluate } from "./evaluator.ts";
import type { CoreResult, IncludeResolver } from "./evaluator.ts";

export { LexError, tokenize } from "./lexer.ts";
export { parse, ParseError } from "./parser.ts";
export { EvalError, evaluate } from "./evaluator.ts";
export type {
  AgentDef,
  CoreResult,
  GraphDef,
  IncludeResolver,
  LaneViewDef,
  ModeDef,
  RuleDef,
  SystemDef,
} from "./evaluator.ts";
export type { ProofNode, ProofTree } from "./typecheck-prove.ts";
export { exportProofJSON, exportProofText, exportProofTerm } from "./proof-export.ts";
export type * from "./types.ts";

export function compile(
  source: string,
  resolver?: IncludeResolver,
): CoreResult {
  try {
    const tokens = tokenize(source);
    const ast = parse(tokens);
    return evaluate(ast, resolver);
  } catch (e) {
    if (
      e instanceof LexError || e instanceof ParseError || e instanceof EvalError
    ) {
      return {
        systems: new Map(),
        graphs: new Map(),
        laneViews: new Map(),
        proofTrees: new Map(),
        definitions: new Map(),
        errors: [e.message],
      };
    }
    return {
      systems: new Map(),
      graphs: new Map(),
      laneViews: new Map(),
      proofTrees: new Map(),
      definitions: new Map(),
      errors: [`Internal error: ${(e as Error).message}`],
    };
  }
}
