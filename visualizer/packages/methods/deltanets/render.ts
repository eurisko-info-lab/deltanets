import { Signal } from "@preact/signals";
import { AstNode, SystemType } from "@deltanets/core";
import {
  D,
  Eraser,
  Node2D,
  Root,
  SUBOPTIMAL_HIGHLIGHT_COLOR,
  Wire,
} from "@deltanets/render";
import { MethodState } from "../index.ts";
import {
  type Graph,
  deltanets,
  readbackGraphToString,
} from "@deltanets/core";
import { isExprAgentFromStyles, typeReductionMode, type Data } from "./config.ts";
import { applyReduction } from "./reduction.ts";
import { renderNodePort } from "./render-dispatch.ts";
import { renderWires } from "./render-wires.ts";

const { cleanupGraph, findReachableNodes, getRedex, getRedexes, isConnectedToAllErasers, isParentPort, levelColor } = deltanets;

type State = MethodState<Graph, Data>;

// Renders the current state of the reduction process
export function render(
  state: Signal<State>,
  expression: Signal<string>,
  systemType: SystemType,
  relativeLevel: boolean,
): Node2D {
  const currState = state.peek()!;
  const graph = currState.stack[currState.idx];
  const node2D = new Node2D();

  // Reset flags
  graph.forEach((node) => {
    node.isCreated = false;
  });

  // Get redexes, filtered by reduction mode
  const allRedexes = getRedexes(graph, systemType, relativeLevel);
  const redexes = typeReductionMode.value
    ? allRedexes.filter((r) => !isExprAgentFromStyles(r.a.type) || !isExprAgentFromStyles(r.b.type))
    : allRedexes.filter((r) => isExprAgentFromStyles(r.a.type) && isExprAgentFromStyles(r.b.type));

  // In type reduction mode, the optimal traversal doesn't cover lambda cube agents,
  // so mark the first available redex as optimal if none are
  if (typeReductionMode.value && redexes.length > 0 && !redexes.some((r) => r.optimal)) {
    redexes[0].optimal = true;
  }

  // Render graph
  const rootNode = graph.find((node) => node.type === "root")!;
  const { node2D: mainTreeNode2D, endpoints } = renderNodePort(
    rootNode.ports[0],
    state,
    redexes,
  );
  rootNode.isCreated = true;
  mainTreeNode2D.pos.y = 2 * D;
  node2D.add(mainTreeNode2D);

  // Render root and root wire
  const root = new Root();
  node2D.add(root);
  const rootWire = new Wire(root, mainTreeNode2D, 0, undefined, levelColor(0));
  rootWire.startOffset.y = Root.RADIUS;
  node2D.add(rootWire);

  // Filter not-created erasers connected to parent ports
  const notCreatedParentErasers = graph.filter((node) =>
    node.type === "era" && !node.isCreated && isParentPort(node.ports[0])
  );

  // Prioritize erasers which are the only parents of a node
  const sortedNotCreatedErasers = notCreatedParentErasers.sort((a, b) => {
    // Deprioritize replicators, and among replicators prioritize those with only aux erasers
    if (a.ports[0].node.type.startsWith("rep")) {
      if (b.ports[0].node.type.startsWith("rep")) {
        // check if one has only aux erasers, if so, then prioritize that one
        if (
          isConnectedToAllErasers(a.ports[0].node) &&
          !isConnectedToAllErasers(b.ports[0].node)
        ) {
          return -1;
        } else if (
          !isConnectedToAllErasers(a.ports[0].node) &&
          isConnectedToAllErasers(b.ports[0].node)
        ) {
          return 1;
        } else {
          return 0;
        }
      } else {
        // A is rep, B is non-rep - swap i.e. prioritize B (non-rep)
        return 1;
      }
    } else {
      if (b.ports[0].node.type.startsWith("rep")) {
        // A is non-rep, B is rep - don't swap i.e. prioritize A (non-rep)
        return -1;
      } else {
        // Both are non-rep nodes - no need to prioritize
        return 0;
      }
    }
  });

  // Render eraser roots that are connected to parent ports
  let lastX = mainTreeNode2D.bounds.max.x;
  sortedNotCreatedErasers.forEach((node) => {
    if (node.isCreated) {
      return;
    }

    // Render eraser tree
    const { node2D: eraTree, endpoints: eraEndpoints } = renderNodePort(
      node.ports[0],
      state,
      redexes,
    );
    lastX -= eraTree.bounds.min.x;
    eraTree.pos.x = lastX;
    eraTree.pos.y = 2 * D;
    node2D.add(eraTree);
    endpoints.push(...eraEndpoints);
    // Render eraser and wire
    const era = new Eraser();
    era.pos.x = lastX;
    node2D.add(era);

    // const redex = getRedex(node, node.ports[0].node, currState.stack[currState.idx].redexes);
    const redex = getRedex(
      node,
      node.ports[0].node,
      redexes,
    );

    const wire = new Wire(
      era,
      eraTree,
      0,
      redex?.reduce && (() => applyReduction(state, redex.reduce)),
    );
    if (redex?.optimal === false) {
      wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
    }
    node2D.add(wire);
    lastX += eraTree.bounds.max.x;
    node.isCreated = true;
  });

  // Render auxiliary wires
  renderWires(node2D, endpoints, state);

  // Check if any nodes are not created
  const nodesNotCreated = graph.filter((node) => !node.isCreated);
  if (nodesNotCreated.length > 0) {
    console.warn("Nodes not rendered: ", nodesNotCreated);
  }

  // Get optimal redexes
  const optimalRedexes = redexes.filter((redex) => redex.optimal);
  if (optimalRedexes.length > 0) {
    // If forward is undefined, set it to reduce a random redex
    if (currState.forward === undefined) {
      currState.forward = () => {
        applyReduction(state, () => {
          optimalRedexes[0].reduce();
        });
      };
    }
    // Set forwardParallel
    currState.forwardParallel = () => {
      applyReduction(state, () => {
        optimalRedexes.forEach((redex) => {
          redex.reduce();
        });
      });
    };
  } else if (!currState.data.appliedFinalStep) {
    const reachable = findReachableNodes(graph);
    const nodesToErase = graph.filter((node) => !reachable.has(node));
    if (nodesToErase.length > 0) {
      currState.data.isFinalStep = true;
      const finalStep = () => {
        applyReduction(state, () => {
          currState.data.appliedFinalStep = true;
          cleanupGraph(currState.stack[currState.idx]);
        });
      }
      currState.forward = finalStep;
      currState.forwardParallel = finalStep;
    } else {
      currState.data.appliedFinalStep = true;
    }
  }

  // Update expression display with readback
  expression.value = readbackGraphToString(graph);

  return node2D;
}
