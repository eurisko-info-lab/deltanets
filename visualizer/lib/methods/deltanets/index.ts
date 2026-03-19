import { signal } from "@preact/signals";
import { AstNode, SystemType } from "../../ast.ts";
import { type Graph, deltanets } from "../../core/index.ts";
import { type Method, type MethodState } from "../index.ts";
import { type Data } from "./config.ts";
import { render } from "./render.ts";

export { agentStyles, isExprAgentFromStyles, getRole, typeReductionMode } from "./config.ts";
export { applyReduction } from "./reduction.ts";

type State = MethodState<Graph, Data>;

function init(ast: AstNode, systemType: SystemType, relativeLevel: boolean): State {
  const graph = deltanets.buildGraph(ast, systemType, relativeLevel);
  return {
    back: undefined,
    forward: undefined,
    idx: 0,
    stack: [graph],
    data: { appliedFinalStep: false, isFinalStep: false },
  };
}

function initFromGraph(graph: Graph): State {
  return {
    back: undefined,
    forward: undefined,
    idx: 0,
    stack: [graph],
    data: { appliedFinalStep: false, isFinalStep: false },
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
