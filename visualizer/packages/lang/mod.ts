// @deltanets/lang — INet language parser, evaluator, and bridge.

export { compileCore, compileView } from "./index.ts";
export * as core from "./core/index.ts";
export * as view from "./view/index.ts";
export type { CoreResult, SystemDef, AgentDef, RuleDef, ModeDef, GraphDef } from "./core/index.ts";
export type { AgentStyleDef, AgentRole } from "./view/evaluator.ts";
export {
  isINetSource, compileINet, extractGraph, resolveAgentStyles,
  type BridgeResult, type ExtractedGraph,
} from "./bridge.ts";
export { DEFAULT_IVIEW } from "./defaults.ts";
