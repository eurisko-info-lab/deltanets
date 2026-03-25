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
  FunctorDef,
  GraphDef,
  IncludeResolver,
  LaneViewDef,
  ModeDef,
  ModuleTypeDef,
  RuleDef,
  SystemDef,
  TacticDef,
} from "./evaluator.ts";
export type { ProofNode, ProofTree, ConversionResult } from "./typecheck-prove.ts";
export { universeLevel, typeUniverse, typeSubsumes, isPropSort, sortOf } from "./typecheck-prove.ts";
export { exportProofJSON, exportProofText, exportProofTerm } from "./proof-export.ts";
export { extractSystem, renderTypeScript, renderJavaScript } from "./extract.ts";
export type { ExtractionResult, ExtractedType, ExtractedFunction } from "./extract.ts";
export {
  quoteExpr, unquoteStatements, buildGoalStatements,
  registerQuotationAgents, containsQuote, containsUnquote,
  QUOTE_AGENTS, TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
  Q_GOAL, CTX_NIL, CTX_CONS,
} from "./quotation.ts";
export type { QuoteResult } from "./quotation.ts";
export {
  registerMetaAgents, createNormalizeHandler, createApplyRuleHandler,
  createCtxSearchHandler, createEqCheckHandler,
  readTermFromGraph, writeTermToGraph, collectTermTree,
  META_AGENTS, META_MATCH_GOAL, META_APPLY_RULE, META_NORMALIZE,
  META_CTX_SEARCH, META_EQ_CHECK,
  META_AGENT_DECLS,
} from "./meta-agents.ts";
export { normalize, computeGoalType, exprEqual, convertible, checkConvertible, searchProofContext, makeStrategyContext, primConv, primCtxSearch, primRewrite, primGround, primCong, primSearch } from "./typecheck-prove.ts";
export type { StrategyContext } from "./typecheck-prove.ts";
export {
  compileTactic, resolveAllTactics, runStrategy,
  BUILTIN_TACTIC_NAMES,
} from "./tactics.ts";
export {
  startProofSession, getSession, getGoals,
  applyTactic as applySessionTactic,
  applyProofTerm, applyProofString,
  undoTactic, redoTactic,
  closeSession, listSessions,
  exportSessionText, createSessionsForSystem,
} from "./interactive-proof.ts";
export type {
  ProofGoal, GoalBinding, TacticResult, ProofSession,
} from "./interactive-proof.ts";
export {
  enableVM, disableVM, isVMEnabled,
  vmNormalize, vmConvertible, vmCheckConvertible,
  getVMStats, resetVMStats, clearVMCache,
  compileExpr, exprHash, withVMContext, precompile,
} from "./vm-normalize.ts";
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
        moduleTypes: new Map(),
        functors: new Map(),
        errors: [e.message],
      };
    }
    return {
      systems: new Map(),
      graphs: new Map(),
      laneViews: new Map(),
      proofTrees: new Map(),
      definitions: new Map(),
      moduleTypes: new Map(),
      functors: new Map(),
      errors: [`Internal error: ${(e as Error).message}`],
    };
  }
}
