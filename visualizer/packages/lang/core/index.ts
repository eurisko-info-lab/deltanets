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
  TacticDef,
} from "./evaluator.ts";
export type { ProofNode, ProofTree } from "./typecheck-prove.ts";
export { universeLevel, typeUniverse, typeSubsumes } from "./typecheck-prove.ts";
export { exportProofJSON, exportProofText, exportProofTerm } from "./proof-export.ts";
export {
  quoteExpr, unquoteStatements, buildGoalStatements,
  registerQuotationAgents, containsQuote, containsUnquote,
  QUOTE_AGENTS, TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
  Q_GOAL, CTX_NIL, CTX_CONS,
} from "./quotation.ts";
export type { QuoteResult } from "./quotation.ts";
export {
  registerMetaAgents, createNormalizeHandler, createApplyRuleHandler,
  readTermFromGraph, writeTermToGraph, collectTermTree,
  META_AGENTS, META_MATCH_GOAL, META_APPLY_RULE, META_NORMALIZE,
  META_AGENT_DECLS,
} from "./meta-agents.ts";
export { normalize, computeGoalType } from "./typecheck-prove.ts";
export {
  registerBuiltinTactics, compileTactic, resolveUserTactics,
  createSimpHandler, createDecideHandler, createOmegaHandler, createAutoHandler,
  TACTIC_AGENTS, TACTIC_SIMP, TACTIC_DECIDE, TACTIC_OMEGA, TACTIC_AUTO,
  TACTIC_AGENT_DECLS, BUILTIN_TACTIC_NAMES,
} from "./tactics.ts";
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
