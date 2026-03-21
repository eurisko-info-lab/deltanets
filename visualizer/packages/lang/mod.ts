// @deltanets/lang — INet language parser, evaluator, and bridge.

export { compileCore, compileView } from "./index.ts";
export * as core from "./core/index.ts";
export * as view from "./view/index.ts";
export type {
  AgentDef,
  CoreResult,
  GraphDef,
  ModeDef,
  RuleDef,
  SystemDef,
} from "./core/index.ts";
export type { AgentRole, AgentStyleDef } from "./view/evaluator.ts";
export {
  type BridgeResult,
  compileINet,
  type ExtractedGraph,
  extractGraph,
  isINetSource,
  resolveAgentStyles,
} from "./bridge.ts";
export { DEFAULT_IVIEW } from "./defaults.ts";
