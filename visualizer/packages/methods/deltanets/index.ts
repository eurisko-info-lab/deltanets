import { signal } from "@preact/signals";
import { AstNode, type InteractionRule, SystemType } from "@deltanets/core";
import { deltanets, type Graph } from "@deltanets/core";
import { type Method, type MethodState } from "../index.ts";
import { type Data } from "./config.ts";
import { render } from "./render.ts";

export {
  agentStyles,
  getRole,
  isExprAgentFromStyles,
  typeReductionMode,
} from "./config.ts";
export { applyReduction } from "./reduction.ts";

type State = MethodState<Graph, Data>;

function init(
  ast: AstNode,
  systemType: SystemType,
  relativeLevel: boolean,
  rules?: InteractionRule[],
): State {
  const graph = deltanets.buildGraph(ast, systemType, relativeLevel);
  return {
    back: undefined,
    forward: undefined,
    idx: 0,
    stack: [graph],
    data: { appliedFinalStep: false, isFinalStep: false, rules },
  };
}

function initFromGraph(graph: Graph, rules?: InteractionRule[]): State {
  return {
    back: undefined,
    forward: undefined,
    idx: 0,
    stack: [graph],
    data: { appliedFinalStep: false, isFinalStep: false, rules },
  };
}

// Δ-Nets (absolute indexes)
const method: Method<Graph, Data> = {
  name: "Δ-Nets (2025)",
  state: signal(null),
  init,
  initFromGraph,
  render,
};
export default method;
