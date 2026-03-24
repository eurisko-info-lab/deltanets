// @deltanets/lang — INet language parser, evaluator, and bridge.

export { compileCore, compileView } from "./index.ts";
export { exportProofJSON, exportProofText, exportProofTerm } from "./core/proof-export.ts";
export { universeLevel, typeUniverse, typeSubsumes, isPropSort, isSPropSort, sortOf, convertibleInSort } from "./core/typecheck-prove.ts";
export type { ConversionResult } from "./core/typecheck-prove.ts";
export {
  quoteExpr, unquoteStatements, buildGoalStatements,
  registerQuotationAgents, QUOTE_AGENTS,
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
  Q_GOAL, CTX_NIL, CTX_CONS,
} from "./core/quotation.ts";
export type { QuoteResult } from "./core/quotation.ts";
export {
  registerMetaAgents, createNormalizeHandler, createApplyRuleHandler,
  createCtxSearchHandler, createEqCheckHandler,
  readTermFromGraph, writeTermToGraph, collectTermTree,
  META_AGENTS, META_MATCH_GOAL, META_APPLY_RULE, META_NORMALIZE,
  META_CTX_SEARCH, META_EQ_CHECK,
  META_AGENT_DECLS,
} from "./core/meta-agents.ts";
export { normalize, computeGoalType, exprEqual, convertible, checkConvertible, searchProofContext, makeStrategyContext, primConv, primCtxSearch, primRewrite, primGround, primCong, primSearch } from "./core/typecheck-prove.ts";
export type { StrategyContext } from "./core/typecheck-prove.ts";
export {
  compileTactic, resolveAllTactics, runStrategy,
  BUILTIN_TACTIC_NAMES,
} from "./core/tactics.ts";
export * as core from "./core/index.ts";
export * as view from "./view/index.ts";
export type {
  AgentDef,
  CoreResult,
  GraphDef,
  IncludeResolver,
  LaneViewDef,
  ModeDef,
  ProofNode,
  ProofTree,
  RuleDef,
  Sort,
  SystemDef,
  TacticDef,
} from "./core/index.ts";
export type { AgentRole, AgentStyleDef } from "./view/evaluator.ts";
export {
  type BridgeResult,
  compileINet,
  type ExtractedGraph,
  extractGraph,
  isINetSource,
  LANE_VIEW_PREFIX,
  PROOF_TREE_PREFIX,
  resolveAgentStyles,
} from "./bridge.ts";
export { DEFAULT_IVIEW } from "./defaults.ts";
