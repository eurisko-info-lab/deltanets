import { batch, Signal, signal } from "@preact/signals";
import { AstNode, SystemType } from "../ast.ts";
import {
  D,
  Eraser,
  Fan,
  Label,
  Node2D,
  Replicator,
  Root,
  SUBOPTIMAL_HIGHLIGHT_COLOR,
  TYPECHECK_ACTIVE_COLOR,
  TYPECHECK_DONE_COLOR,
  TYPECHECK_ERROR_COLOR,
  Wire,
} from "../render.ts";
import { Method, MethodState } from "./index.ts";
import {
  type Graph,
  type Node,
  type NodePort,
  type Redex,
  Ports,
  reciprocal,
  deltanets,
} from "../core/index.ts";

const { buildGraph, cleanupGraph, countAuxErasers, findReachableNodes, getRedex, getRedexes, isConnectedToAllErasers, isParentPort, levelColor, isExprAgent } = deltanets;

// Type reduction mode: when true, only type-level redexes are active
export const typeReductionMode = signal(false);

// Δ-Nets (absolute indexes)
const method: Method<Graph, Data> = {
  name: "Δ-Nets (2025)",
  state: signal(null),
  init,
  initFromGraph,
  render,
};
export default method;

type Data = { appliedFinalStep: boolean, isFinalStep: boolean };

type State = MethodState<Graph, Data>;

function init(ast: AstNode, systemType: SystemType, relativeLevel: boolean): State {
  const graph = buildGraph(ast, systemType, relativeLevel);
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

// Renders the current state of the reduction process
function render(
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
    ? allRedexes.filter((r) => !isExprAgent(r.a.type) || !isExprAgent(r.b.type))
    : allRedexes.filter((r) => isExprAgent(r.a.type) && isExprAgent(r.b.type));

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

  return node2D;
}

// The type of a graph endpoint
type Endpoint = {
  nodePort: NodePort;
  node2D: Node2D;
  level?: number;
  used?: boolean;
  redex?: Redex;
};

// Renders a node port
const renderNodePort = (
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number = 0,
): { node2D: Node2D; endpoints: Endpoint[] } => {
  const node2D = new Node2D();
  let endpoints: Endpoint[] = [];
  if (nodePort.node.isCreated) {
    // Node has been created already - create a wire endpoint
    const endpoint = new Node2D();
    endpoint.bounds = { min: { x: -D, y: 0 }, max: { x: D, y: D } };
    node2D.add(endpoint);
    (node2D as any).isWireEndpoint = true;
    endpoints.push({ nodePort, node2D, level });
  } else if (nodePort.node.type === "var") {
    nodePort.node.isCreated = true;
    const label = new Label(nodePort.node.label);
    if (nodePort.node.typeCheckState === "checking") label.highlightColor = TYPECHECK_ACTIVE_COLOR;
    else if (nodePort.node.typeCheckState === "checked") label.highlightColor = TYPECHECK_DONE_COLOR;
    else if (nodePort.node.typeCheckState === "error") label.highlightColor = TYPECHECK_ERROR_COLOR;
    label.pos.y = D;
    node2D.add(label);
    endpoints.push({ nodePort, node2D });
  } else if (nodePort.node.type === "era") {
    nodePort.node.isCreated = true;
    const era = new Eraser();
    node2D.add(era);
    endpoints.push({ nodePort, node2D });
  } else if ((nodePort.node.type === "abs" || nodePort.node.type === "tyabs" || nodePort.node.type === "type-abs") && nodePort.port === 0) {
    nodePort.node.isCreated = true;
    const fan = new Fan("up", nodePort.node.label);
    if (nodePort.node.typeCheckState === "checking") fan.highlightColor = TYPECHECK_ACTIVE_COLOR;
    else if (nodePort.node.typeCheckState === "checked") fan.highlightColor = TYPECHECK_DONE_COLOR;
    else if (nodePort.node.typeCheckState === "error") fan.highlightColor = TYPECHECK_ERROR_COLOR;

    const { node2D: body, endpoints: bodyEndpoints } = renderNodePort(
      nodePort.node.ports[Ports.abs.body],
      state,
      redexes,
      level,
    );
    body.pos.x = Math.max(Fan.PORT_DELTA, -body.bounds.min.x - D);
    body.pos.y = (body as any).isWireEndpoint
      ? Fan.HEIGHT
      : fan.bounds.max.y - body.bounds.min.y;


    const redex = getRedex(
      nodePort.node,
      nodePort.node.ports[Ports.abs.body].node,
      redexes,
    );

    if (!(body as any).isWireEndpoint) {
      const funcWire = new Wire(fan, body, D, redex?.reduce && (() => applyReduction(state, redex.reduce)), levelColor(level));
      if (redex?.optimal === false) {
        funcWire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      }
      funcWire.startOffset.x = Fan.PORT_DELTA;
      funcWire.startOffset.y = Fan.HEIGHT;
      node2D.add(funcWire);
    } else {
      // Add redex to the appropriate endpoint
      const childEndpoint = bodyEndpoints.find((endpoint) => endpoint.nodePort === nodePort.node.ports[Ports.abs.body]);
      if (childEndpoint) {
        childEndpoint.redex = redex;
      }
    }

    // Create eraser or wire endpoint for bind port
    if (nodePort.node.ports[Ports.abs.bind].node.type === "era") {
      nodePort.node.ports[Ports.abs.bind].node.isCreated = true;
      const era = new Eraser();
      era.pos.x = -Fan.PORT_DELTA;
      era.pos.y = fan.bounds.max.y - era.bounds.min.y;
      node2D.add(era);
      endpoints.push({ nodePort: nodePort.node.ports[Ports.abs.bind], node2D: era, level });
      const wire = new Wire(fan, era, 0, undefined, levelColor(level + 1));
      wire.startOffset.x = -Fan.PORT_DELTA;
      wire.startOffset.y = Fan.HEIGHT;
      wire.endOffset.y = -Eraser.RADIUS;
      node2D.add(wire);
    } else {
      // Render bind subgraph (or wire endpoint if already created)
      const { node2D: bindTree, endpoints: bindEndpoints } = renderNodePort(
        nodePort.node.ports[Ports.abs.bind], state, redexes, level + 1,
      );
      bindTree.pos.x = -Fan.PORT_DELTA;
      bindTree.pos.y = (bindTree as any).isWireEndpoint
        ? Fan.HEIGHT
        : fan.bounds.max.y - bindTree.bounds.min.y;

      if (!(bindTree as any).isWireEndpoint) {
        const bindWire = new Wire(fan, bindTree, 0, undefined, levelColor(level + 1));
        bindWire.startOffset.x = -Fan.PORT_DELTA;
        bindWire.startOffset.y = Fan.HEIGHT;
        node2D.add(bindWire);
      }
      node2D.add(bindTree);
      endpoints.push(...bindEndpoints);
    }

    // Handle type port (only abs has 4 ports; tyabs/type-abs have 3)
    let typeEndpoints: Endpoint[] = [];
    if (nodePort.node.ports.length > 3) {
      const typePortRef = nodePort.node.ports[Ports.abs.type];
      if (typePortRef.node.type === "type-hole") {
        // Mark type-hole as created (invisible for unannotated lambdas)
        typePortRef.node.isCreated = true;
      } else {
        // Render type subgraph inline
        const { node2D: typeTree, endpoints: tEndpoints } = renderNodePort(
          typePortRef, state, redexes, level,
        );
        typeEndpoints = tEndpoints;
        typeTree.pos.x = -2 * Fan.PORT_DELTA;
        typeTree.pos.y = (typeTree as any).isWireEndpoint
          ? Fan.HEIGHT
          : fan.bounds.max.y - typeTree.bounds.min.y;

        if (!(typeTree as any).isWireEndpoint) {
          const typeWire = new Wire(fan, typeTree, 0);
          typeWire.startOffset.x = -Fan.PORT_DELTA;
          typeWire.startOffset.y = Fan.HEIGHT;
          node2D.add(typeWire);
        }
        node2D.add(typeTree);
      }
    }

    node2D.add(fan);
    node2D.add(body);

    endpoints = [...endpoints, ...bodyEndpoints, ...typeEndpoints];
  } else if ((nodePort.node.type === "app" || nodePort.node.type === "tyapp" || nodePort.node.type === "type-app") && nodePort.port === 1) {
    nodePort.node.isCreated = true;
    const fan = new Fan("down", nodePort.node.label);
    if (nodePort.node.typeCheckState === "checking") fan.highlightColor = TYPECHECK_ACTIVE_COLOR;
    else if (nodePort.node.typeCheckState === "checked") fan.highlightColor = TYPECHECK_DONE_COLOR;
    else if (nodePort.node.typeCheckState === "error") fan.highlightColor = TYPECHECK_ERROR_COLOR;
    fan.pos.x = Fan.PORT_DELTA;

    const { node2D: func, endpoints: funcEndpoints } = renderNodePort(
      nodePort.node.ports[Ports.app.func],
      state,
      redexes,
      level,
    );
    func.pos.x = Fan.PORT_DELTA;
    func.pos.y = (func as any).isWireEndpoint
      ? Fan.HEIGHT
      : fan.bounds.max.y - func.bounds.min.y;


    const redex = getRedex(
      nodePort.node,
      nodePort.node.ports[Ports.app.func].node,
      redexes,
    );

    if (!(func as any).isWireEndpoint) {
      const funcWire = new Wire(
        fan,
        func,
        0,
        redex?.reduce && (() => applyReduction(state, redex.reduce)),
        levelColor(level),
      );
      if (redex?.optimal === false) {
        funcWire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      }
      funcWire.startOffset.y = Fan.HEIGHT;
      node2D.add(funcWire);
    } else {
      // Add redex to the appropriate endpoint
      const childEndpoint = funcEndpoints.find((endpoint) => endpoint.nodePort === nodePort.node.ports[Ports.app.func]);
      if (childEndpoint) {
        childEndpoint.redex = redex;
      }
    }

    const { node2D: arg, endpoints: argEndpoints } = renderNodePort(
      nodePort.node.ports[Ports.app.arg],
      state,
      redexes,
      level + 1,
    );
    arg.pos.x = nodePort.node.ports[Ports.app.arg].node.type === "var"
      ? fan.bounds.max.x - arg.bounds.min.x + 2 * D
      : Fan.PORT_DELTA + Math.max(func.bounds.max.x, fan.bounds.max.x) -
        arg.bounds.min.x;

    const argWire = new Wire(fan, arg, -D, undefined, levelColor(level + 1));
    argWire.startOffset.x = Fan.PORT_DELTA;
    node2D.add(argWire);

    node2D.add(fan);
    node2D.add(func);
    node2D.add(arg);

    endpoints = [...funcEndpoints, ...argEndpoints];
  } else if (nodePort.node.type.startsWith("rep") && nodePort.port !== 0) {
    if (nodePort.node.type !== "rep-in") {
      console.error("WRONG REP TYPE - EXPECTED rep-in", nodePort.node.type);
    }
    nodePort.node.isCreated = true;
    const rep = new Replicator(
      "down",
      nodePort.node.label,
      nodePort.node.levelDeltas!,
    );
    const parentPortDelta = rep.portDelta(nodePort.port - 1);
    rep.pos.x = -parentPortDelta;
    const eraCount = countAuxErasers(nodePort.node)
    const relevantAuxPortsMinus1 = Math.max((eraCount > 0) && (eraCount !== nodePort.node.ports.length - 1) ? 1.5 : 0, nodePort.node.ports.length - 2 - eraCount)
    rep.pos.y = relevantAuxPortsMinus1 * 2 * D;
    rep.bounds.min.y -= relevantAuxPortsMinus1 * 2 * D;
    node2D.add(rep);

    // parent wire extender
    const parWire = new Wire(node2D, rep, 0, undefined, levelColor(level));
    parWire.endOffset.x = parentPortDelta;
    node2D.add(parWire);

    const childLevel = level - nodePort.node.levelDeltas![nodePort.port - 1];
    const { node2D: child, endpoints: childEndpoints } = renderNodePort(
      nodePort.node.ports[0],
      state,
      redexes,
      childLevel,
    );
    child.pos.x = -parentPortDelta;
    child.pos.y = rep.pos.y +
      ((child as any).isWireEndpoint
        ? Replicator.HEIGHT
        : rep.bounds.max.y - child.bounds.min.y);
    node2D.add(child);
    endpoints.push(...childEndpoints);

    const redex = getRedex(
      nodePort.node,
      nodePort.node.ports[0].node,
      redexes,
    );

    // Draw child wire
    if (!(child as any).isWireEndpoint) {
      const childWire = new Wire(
        rep,
        child,
        0,
        redex?.reduce && (() => applyReduction(state, redex.reduce)),
        levelColor(childLevel),
      );
      if (redex?.optimal === false) {
        childWire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      }
      childWire.startOffset.y = Replicator.HEIGHT;
      rep.add(childWire);
    } else {
      // Add redex to the appropriate endpoint
      const childEndpoint = childEndpoints.find((endpoint) => endpoint.nodePort === nodePort.node.ports[0]);
      if (childEndpoint) {
        childEndpoint.redex = redex;
      }
    }

    // Draw aux wires to the right and down
    const lastX = node2D.bounds.max.x; // Math.max(child.bounds.max.x, rep.bounds.max.x);
    let i2 = 2;
    for (let i = 1; i < nodePort.node.ports.length; i++) {
      if (i === nodePort.port) {
        // Skip the current port
        continue;
      }
      const auxLevel = childLevel + nodePort.node.levelDeltas![i - 1];
      // Create eraser or wire endpoint
      if (nodePort.node.ports[i].node.type === "era") {
        nodePort.node.ports[i].node.isCreated = true;
        const era = new Eraser();
        era.pos.x = rep.pos.x + rep.portDelta(i - 1);
        era.pos.y = rep.pos.y - 2 * D;
        node2D.add(era);
        const redex = getRedex(
          nodePort.node,
          nodePort.node.ports[i].node,
          redexes,
        );
        const wire = new Wire(
          rep,
          era,
          0,
          redex?.reduce && (() => applyReduction(state, redex.reduce)),
          levelColor(auxLevel),
        );
        if (redex?.optimal === false) {
          wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
        }
        wire.startOffset.x = rep.portDelta(i - 1);
        rep.add(wire);
      } else {
        // Create wire endpoint
        const endpoint = new Node2D();
        endpoint.bounds = { min: { x: -D, y: 0 }, max: { x: D, y: D } };
        endpoint.pos.x = lastX +
          (nodePort.node.ports.length - i2 - 0.5) * 2 * D;
        endpoint.pos.y = rep.pos.y;
        node2D.add(endpoint);
        (endpoint as any).isWireEndpoint = true;
        endpoints.push({
          nodePort: nodePort.node.ports[i],
          node2D: endpoint,
          level: auxLevel,
        });
        // Create wire to endpoint
        const wire = new Wire(
          rep,
          endpoint,
          (i2 - nodePort.node.ports.length + 0.5) * 2 * D,
          undefined,
          levelColor(auxLevel),
        );
        wire.startOffset.x = rep.portDelta(i - 1);
        rep.add(wire);
      }
      i2++;
    }
  } else if (nodePort.node.type.startsWith("rep") && nodePort.port === 0) {
    if (nodePort.node.type !== "rep-out") {
      console.error("WRONG REP TYPE, EXPECTED rep-out", nodePort.node.type);
    }
    nodePort.node.isCreated = true;
    const rep = new Replicator(
      "up",
      nodePort.node.label,
      nodePort.node.levelDeltas!,
    );
    node2D.add(rep);

    // Render children
    const children: Node2D[] = [];
    let allChildrenAreWireEndpoints = true;
    for (let i = nodePort.node.ports.length - 1; i > 0; i--) {
      const childLevel = level + nodePort.node.levelDeltas![i - 1];
      const { node2D: child, endpoints: childEndpoints } = renderNodePort(
        nodePort.node.ports[i],
        state,
        redexes,
        childLevel,
      );
      if (allChildrenAreWireEndpoints && !(child as any).isWireEndpoint) {
        allChildrenAreWireEndpoints = false;
      }
      children.push(child);
      endpoints.push(...childEndpoints);
    }

    // Position children
    if (allChildrenAreWireEndpoints) {
      // If all children are wire endpoints, render them inline
      children.forEach((child, i) => {
        child.pos.x = rep.portDelta(i);
        child.pos.y = Replicator.HEIGHT;
        node2D.add(child);
      });
    } else {
      let lastX = rep.portDelta(0) + children[0].bounds.min.x;
      children.forEach((child, i) => {
        lastX -= child.bounds.min.x;
        child.pos.x = lastX;
        lastX += child.bounds.max.x;
        child.pos.y = Replicator.HEIGHT +
          Math.max(children.length - 1, 1) * 2 * D +
          (nodePort.node.ports[nodePort.node.ports.length - 1 - i].node.type ===
              "app"
            ? 2 * D
            : 0);
        node2D.add(child);

        const childLevel = level +
          nodePort.node.levelDeltas![children.length - i - 1];
        const childWire = new Wire(
          rep,
          child,
          (children.length - i - 0.5) * 2 * D,
          undefined,
          levelColor(childLevel),
        );
        childWire.startOffset.x = rep.portDelta(i);
        childWire.startOffset.y = Replicator.HEIGHT;
        node2D.add(childWire);
      });
    }
  } else if (nodePort.node.type === "type-base" || nodePort.node.type === "kind-star") {
    nodePort.node.isCreated = true;
    const label = new Label(nodePort.node.label);
    label.pos.y = D;
    node2D.add(label);
    endpoints.push({ nodePort, node2D });
  } else if (nodePort.node.type === "type-hole") {
    nodePort.node.isCreated = true;
    const label = new Label("?");
    label.pos.y = D;
    node2D.add(label);
    endpoints.push({ nodePort, node2D });
  } else if ((nodePort.node.type === "type-arrow" || nodePort.node.type === "pi" || nodePort.node.type === "sigma" || nodePort.node.type === "kind-arrow" || nodePort.node.type === "pair") && nodePort.port === 0) {
    nodePort.node.isCreated = true;
    const fan = new Fan("up", nodePort.node.label || "\u2192");

    let codomEndpoints: Endpoint[] = [];
    let domEndpoints: Endpoint[] = [];

    // Render codomain / right child (port 2) if wired
    const codomPort = nodePort.node.ports[Ports.typeArrow.codomain];
    if (codomPort) {
      const { node2D: codom, endpoints: cEP } = renderNodePort(
        codomPort, state, redexes, level,
      );
      codomEndpoints = cEP;
      codom.pos.x = Math.max(Fan.PORT_DELTA, -codom.bounds.min.x - D);
      codom.pos.y = (codom as any).isWireEndpoint
        ? Fan.HEIGHT
        : fan.bounds.max.y - codom.bounds.min.y;

      if (!(codom as any).isWireEndpoint) {
        const wire = new Wire(fan, codom, D);
        wire.startOffset.x = Fan.PORT_DELTA;
        wire.startOffset.y = Fan.HEIGHT;
        node2D.add(wire);
      }
      node2D.add(codom);
    }

    // Render domain / left child (port 1) if wired
    const domPort = nodePort.node.ports[Ports.typeArrow.domain];
    if (domPort) {
      const { node2D: dom, endpoints: dEP } = renderNodePort(
        domPort, state, redexes, level,
      );
      domEndpoints = dEP;
      dom.pos.x = -Fan.PORT_DELTA;
      dom.pos.y = (dom as any).isWireEndpoint
        ? Fan.HEIGHT
        : fan.bounds.max.y - dom.bounds.min.y;

      if (!(dom as any).isWireEndpoint) {
        const wire = new Wire(fan, dom, 0);
        wire.startOffset.x = -Fan.PORT_DELTA;
        wire.startOffset.y = Fan.HEIGHT;
        node2D.add(wire);
      }
      node2D.add(dom);
    }

    node2D.add(fan);

    endpoints = [...endpoints, ...codomEndpoints, ...domEndpoints];
  } else if ((nodePort.node.type === "fst" || nodePort.node.type === "snd") && nodePort.port === 1) {
    // 2-port destructor: fan "down" with single principal child
    nodePort.node.isCreated = true;
    const fan = new Fan("down", nodePort.node.label || nodePort.node.type);

    const { node2D: child, endpoints: childEndpoints } = renderNodePort(
      nodePort.node.ports[0], state, redexes, level,
    );
    child.pos.y = (child as any).isWireEndpoint
      ? Fan.HEIGHT
      : fan.bounds.max.y - child.bounds.min.y;

    const redex = getRedex(nodePort.node, nodePort.node.ports[0].node, redexes);

    if (!(child as any).isWireEndpoint) {
      const wire = new Wire(
        fan, child, 0,
        redex?.reduce && (() => applyReduction(state, redex.reduce)),
        levelColor(level),
      );
      if (redex?.optimal === false) {
        wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      }
      wire.startOffset.y = Fan.HEIGHT;
      node2D.add(wire);
    } else {
      const childEndpoint = childEndpoints.find((ep) => ep.nodePort === nodePort.node.ports[0]);
      if (childEndpoint) childEndpoint.redex = redex;
    }

    node2D.add(fan);
    node2D.add(child);
    endpoints = [...endpoints, ...childEndpoints];
  } else {
    // Node has not been created but will be in the future - create a wire endpoint
    const endpoint = new Node2D();
    endpoint.bounds = { min: { x: -D, y: 0 }, max: { x: D, y: D } };
    node2D.add(endpoint);
    (node2D as any).isWireEndpoint = true;
    endpoints.push({ nodePort, node2D, level });
  }
  return { node2D, endpoints };
};

// Renders wires between paired endpoints, and returns the remaining endpoints
const renderWires = (node2D: Node2D, endpoints: Endpoint[], state: Signal<MethodState<any, Data>>) => {
  // Sort endpoints by x position
  endpoints.sort((a, b) =>
    a.node2D.globalPosition().x - b.node2D.globalPosition().x
  );

  // Compile pairs of endpoints that are connected
  const wiresToCreate: { i: number; j: number, redex?: Redex }[] = [];
  for (let i = 0; i < endpoints.length; i++) {
    for (let j = i + 1; j < endpoints.length; j++) {
      if (endpoints[i].used || endpoints[j].used) {
        continue;
      }
      if (
        reciprocal(endpoints[i].nodePort).node === endpoints[j].nodePort.node &&
        reciprocal(endpoints[i].nodePort).port === endpoints[j].nodePort.port
      ) {
        endpoints[i].used = true;
        endpoints[j].used = true;
        wiresToCreate.push({ i, j, redex: endpoints[i].redex || endpoints[j].redex });
      }
    }
  }

  // Sort wiresToCreate by length
  wiresToCreate.sort((a, b) => {
    const horizontalDist = (i: number, j: number) =>
      endpoints[j].node2D.globalPosition().x -
      endpoints[i].node2D.globalPosition().x;
    return horizontalDist(a.i, a.j) - horizontalDist(b.i, b.j);
  });

  // Create wires
  const wires: Wire[] = [];
  wiresToCreate.forEach(({ i, j, redex }) => {
    const leftX = endpoints[i].node2D.globalPosition().x;
    const rightX = endpoints[j].node2D.globalPosition().x;
    // Find wires between the left and right endpoints
    const wiresBetween = wires.filter((wire) =>
      !(
        wire.start.globalPosition().x > rightX ||
        wire.end.globalPosition().x < leftX
      )
    );
    // Get max height of endpoints in between i and j
    const maxH = Math.max(
      endpoints[i].node2D.globalPosition().y +
        endpoints[i].node2D.bounds.max.y + D,
      endpoints[j].node2D.globalPosition().y +
        endpoints[j].node2D.bounds.max.y + D,
      ...endpoints.slice(i + 1, j).map((endpoint) =>
        endpoint.node2D.globalPosition().y + endpoint.node2D.bounds.max.y + D
      ),
      ...wiresBetween.map((w) => w.start.globalPosition().y + w.viaY + 2 * D),
    );
    // Create wire
    // Set level as undefined if conflicting to indicate issue
    const level = (endpoints[i].level === endpoints[j].level &&
        endpoints[i].level !== undefined)
      ? endpoints[i].level
      : undefined;

    // TODO: show level even if one side? Would sill need to fix levels out of eraser "roots". And if those are fixed, then probably don't need this.
    // Set level. Pick the non-undefined level if it exists. if both are defined, then make sure they are equal
    // const level = endpoints[i].level === undefined ? endpoints[j].level : endpoints[j].level === undefined ? endpoints[i].level : endpoints[i].level// (endpoints[i].level === endpoints[j].level) ? endpoints[i].level : undefined;

    const wire = new Wire(
      endpoints[i].node2D,
      endpoints[j].node2D,
      maxH - endpoints[i].node2D.globalPosition().y,
      redex ? (() => applyReduction(state, redex.reduce)) : undefined,
      level !== undefined ? levelColor(level) : undefined,
    );
    wires.push(wire);
    node2D.add(wire);
    // Update bounds of node2D
    node2D.bounds.max.y = Math.max(node2D.bounds.max.y, maxH + D);
  });
};

// Applies a reduction to the current state, and updates the navigation functions
export function applyReduction(
  state: Signal<MethodState<any, Data>>,
  reduce: () => void,
) {
  // Deep clone current state and insert it into the stack below the
  // curent state, and delete all states after the current one
  const currState = state.peek()!;
  const stateClone = structuredClone(currState.stack[currState.idx]);
  currState.stack = currState.stack.slice(0, currState.idx + 1);
  currState.stack.splice(currState.idx, 0, stateClone);
  currState.idx = currState.idx + 1;
  currState.forward = undefined;
  currState.forwardParallel = undefined;

  reduce();

  // Function to go forward to the next state
  const forward = () => {
    const currState = state.peek()!;
    // Move forward one step
    currState.idx = currState.idx + 1;
    // Update other functions
    if (currState.stack.length - 1 === currState.idx) {
      currState.forward = undefined;
      currState.forwardParallel = undefined;
      currState.last = undefined;
    }
    currState.back = back;
    currState.reset = reset;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Function to go back to the previous state
  const back = () => {
    const currState = state.peek()!;
    // Move back one step
    currState.idx = currState.idx - 1;
    // Update other functions
    if (currState.idx === 0) {
      currState.back = undefined;
      currState.reset = undefined;
    }
    currState.forward = forward;
    currState.last = last;
    currState.data.appliedFinalStep = false;
    currState.data.isFinalStep = false;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Function to reset to the initial state
  const reset = () => {
    const currState = state.peek()!;
    // Move back all the way to the beginning
    currState.idx = 0;
    // Update other functions
    currState.back = undefined;
    currState.reset = undefined;
    currState.forward = forward;
    currState.last = last;
    currState.data.appliedFinalStep = false;
    currState.data.isFinalStep = false;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Function to go to the last state
  const last = () => {
    const currState = state.peek()!;
    // Move forward all the way to the end
    currState.idx = currState.stack.length - 1;
    // Update other functions
    currState.forward = undefined;
    currState.forwardParallel = undefined;
    currState.last = undefined;
    currState.back = back;
    currState.reset = reset;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Update functions that are also set to defined values inside `forward` defined above, assuming that `currState.stack.length - 1 === currState.idx`
  currState.back = back;
  currState.reset = reset;

  state.value = { ...currState };
}
