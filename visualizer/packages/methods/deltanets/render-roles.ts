// ═══════════════════════════════════════════════════════════════════
// Role-based Agent Renderers
// Each function renders a specific agent role (leaf, binder,
// applicator, type-constructor, destructor, replicator).
// ═══════════════════════════════════════════════════════════════════

import { Signal } from "@preact/signals";
import {
  D,
  Eraser,
  Fan,
  Label,
  Node2D,
  Replicator,
  SUBOPTIMAL_HIGHLIGHT_COLOR,
  TYPECHECK_ACTIVE_COLOR,
  TYPECHECK_DONE_COLOR,
  TYPECHECK_ERROR_COLOR,
  Wire,
} from "@deltanets/render";
import { MethodState } from "../index.ts";
import {
  deltanets,
  type Graph,
  type Node,
  type NodePort,
  type Redex,
} from "@deltanets/core";
import { agentStyles, type Data, getRole } from "./config.ts";
import { applyReduction } from "./reduction.ts";
import type { Endpoint } from "./render-wires.ts";
import { renderNodePort } from "./render-dispatch.ts";

const { countAuxErasers, getRedex, levelColor } = deltanets;

type State = MethodState<Graph, Data>;

// ─── Shared helpers ────────────────────────────────────────────────

// Apply typecheck highlight to a node
function applyTypeCheckHighlight(
  shape: { highlightColor?: string },
  node: Node,
) {
  const map: Record<string, string> = {
    checking: TYPECHECK_ACTIVE_COLOR,
    checked: TYPECHECK_DONE_COLOR,
    error: TYPECHECK_ERROR_COLOR,
  };
  if (node.typeCheckState && node.typeCheckState in map) {
    shape.highlightColor = map[node.typeCheckState];
  }
}

type ChildResult = {
  child: Node2D;
  endpoints: Endpoint[];
  redex: Redex | undefined;
};

/** Render a child port, look up its redex, and optionally create a connecting wire. */
function renderChild(
  parentNode: Node,
  portIdx: number,
  parent: Node2D | Fan | Label | Replicator,
  wireContainer: Node2D,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
  wireOpts?: { viaD?: number; startOffsetX?: number; startOffsetY?: number; color?: string },
): ChildResult {
  const portRef = parentNode.ports[portIdx];
  const { node2D: child, endpoints } = renderNodePort(portRef, state, redexes, level);
  const redex = getRedex(parentNode, portRef.node, redexes);

  if (!child.isWireEndpoint && wireOpts !== undefined) {
    const wire = new Wire(
      parent, child, wireOpts.viaD ?? 0,
      redex?.reduce && (() => applyReduction(state, redex.reduce)),
      wireOpts.color ?? levelColor(level),
    );
    if (redex?.optimal === false) wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
    if (wireOpts.startOffsetX !== undefined) wire.startOffset.x = wireOpts.startOffsetX;
    if (wireOpts.startOffsetY !== undefined) wire.startOffset.y = wireOpts.startOffsetY;
    wireContainer.add(wire);
  } else if (child.isWireEndpoint && redex) {
    const ep = endpoints.find((ep) => ep.nodePort === portRef);
    if (ep) ep.redex = redex;
  }

  return { child, endpoints, redex };
}

// Render a leaf agent (var, era, type-base, kind-star, type-hole, or any 1-port agent)
export function renderLeafAgent(
  nodePort: NodePort,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  nodePort.node.isCreated = true;
  const style = agentStyles.peek().get(nodePort.node.type);

  if (
    style?.shape.kind === "eraser" || (!style && nodePort.node.type === "era")
  ) {
    const era = new Eraser();
    node2D.add(era);
  } else {
    const labelText = nodePort.node.type === "type-hole"
      ? "?"
      : nodePort.node.label;
    const label = new Label(labelText);
    applyTypeCheckHighlight(label, nodePort.node);
    label.pos.y = D;
    node2D.add(label);
  }

  return { node2D, endpoints: [{ nodePort, node2D }] };
}

// Render a binder agent (abs, tyabs, type-abs, forall — entered at port 0)
// Port layout: 0=principal(entry), 1=body, 2=bind, 3=type(optional)
export function renderBinderAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  let endpoints: Endpoint[] = [];
  nodePort.node.isCreated = true;

  const fan = new Fan("up", nodePort.node.label);
  applyTypeCheckHighlight(fan, nodePort.node);

  // Body (port 1)
  const { child: body, endpoints: bodyEndpoints } = renderChild(
    nodePort.node, 1, fan, node2D, state, redexes, level,
    { viaD: D, startOffsetX: Fan.PORT_DELTA, startOffsetY: Fan.HEIGHT, color: levelColor(level) },
  );
  body.pos.x = Math.max(Fan.PORT_DELTA, -body.bounds.min.x - D);
  body.pos.y = body.isWireEndpoint
    ? Fan.HEIGHT
    : fan.bounds.max.y - body.bounds.min.y;

  // Bind (port 2)
  const bindPortRef = nodePort.node.ports[2];
  if (bindPortRef.node.type === "era") {
    bindPortRef.node.isCreated = true;
    const era = new Eraser();
    era.pos.x = -Fan.PORT_DELTA;
    era.pos.y = fan.bounds.max.y - era.bounds.min.y;
    node2D.add(era);
    endpoints.push({ nodePort: bindPortRef, node2D: era, level });
    const wire = new Wire(fan, era, 0, undefined, levelColor(level + 1));
    wire.startOffset.x = -Fan.PORT_DELTA;
    wire.startOffset.y = Fan.HEIGHT;
    wire.endOffset.y = -Eraser.RADIUS;
    node2D.add(wire);
  } else {
    const { child: bindTree, endpoints: bindEndpoints } = renderChild(
      nodePort.node, 2, fan, node2D, state, redexes, level + 1,
      { viaD: 0, startOffsetX: -Fan.PORT_DELTA, startOffsetY: Fan.HEIGHT, color: levelColor(level + 1) },
    );
    bindTree.pos.x = -Fan.PORT_DELTA;
    bindTree.pos.y = bindTree.isWireEndpoint
      ? Fan.HEIGHT
      : fan.bounds.max.y - bindTree.bounds.min.y;
    node2D.add(bindTree);
    endpoints.push(...bindEndpoints);
  }

  // Type (port 3, optional — only abs has 4 ports)
  let typeEndpoints: Endpoint[] = [];
  if (nodePort.node.ports.length > 3) {
    const typePortRef = nodePort.node.ports[3];
    if (typePortRef.node.type === "type-hole") {
      typePortRef.node.isCreated = true;
    } else {
      const { child: typeTree, endpoints: tEndpoints } = renderChild(
        nodePort.node, 3, fan, node2D, state, redexes, level,
        { viaD: 0, startOffsetX: -Fan.PORT_DELTA, startOffsetY: Fan.HEIGHT },
      );
      typeEndpoints = tEndpoints;
      typeTree.pos.x = -2 * Fan.PORT_DELTA;
      typeTree.pos.y = typeTree.isWireEndpoint
        ? Fan.HEIGHT
        : fan.bounds.max.y - typeTree.bounds.min.y;
      node2D.add(typeTree);
    }
  }

  node2D.add(fan);
  node2D.add(body);
  endpoints = [...endpoints, ...bodyEndpoints, ...typeEndpoints];
  return { node2D, endpoints };
}

// Render an applicator agent (app, tyapp, type-app — entered at port 1)
// Port layout: 0=func/principal, 1=result(entry), 2=arg
export function renderApplicatorAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  nodePort.node.isCreated = true;

  const fan = new Fan("down", nodePort.node.label);
  applyTypeCheckHighlight(fan, nodePort.node);
  fan.pos.x = Fan.PORT_DELTA;

  // Func/principal (port 0)
  const { child: func, endpoints: funcEndpoints } = renderChild(
    nodePort.node, 0, fan, node2D, state, redexes, level,
    { viaD: 0, startOffsetY: Fan.HEIGHT, color: levelColor(level) },
  );
  func.pos.x = Fan.PORT_DELTA;
  func.pos.y = func.isWireEndpoint
    ? Fan.HEIGHT
    : fan.bounds.max.y - func.bounds.min.y;

  // Arg (port 2)
  const { child: arg, endpoints: argEndpoints } = renderChild(
    nodePort.node, 2, fan, node2D, state, redexes, level + 1,
    { viaD: -D, startOffsetX: Fan.PORT_DELTA, color: levelColor(level + 1) },
  );
  const argPortRef = nodePort.node.ports[2];
  arg.pos.x = argPortRef.node.type === "var"
    ? fan.bounds.max.x - arg.bounds.min.x + 2 * D
    : Fan.PORT_DELTA + Math.max(func.bounds.max.x, fan.bounds.max.x) -
      arg.bounds.min.x;

  node2D.add(fan);
  node2D.add(func);
  node2D.add(arg);

  return { node2D, endpoints: [...funcEndpoints, ...argEndpoints] };
}

// Render a type-constructor agent (type-arrow, pi, sigma, kind-arrow, pair — entered at port 0)
// Port layout: 0=principal(entry), 1=domain/left, 2=codomain/right
export function renderTypeConstructorAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  let endpoints: Endpoint[] = [];
  nodePort.node.isCreated = true;

  const fan = new Fan("up", nodePort.node.label || "\u2192");

  // Codomain / right child (port 2)
  let codomEndpoints: Endpoint[] = [];
  const codomPort = nodePort.node.ports[2];
  if (codomPort) {
    const { child: codom, endpoints: cEP } = renderChild(
      nodePort.node, 2, fan, node2D, state, redexes, level,
      { viaD: D, startOffsetX: Fan.PORT_DELTA, startOffsetY: Fan.HEIGHT },
    );
    codomEndpoints = cEP;
    codom.pos.x = Math.max(Fan.PORT_DELTA, -codom.bounds.min.x - D);
    codom.pos.y = codom.isWireEndpoint
      ? Fan.HEIGHT
      : fan.bounds.max.y - codom.bounds.min.y;
    node2D.add(codom);
  }

  // Domain / left child (port 1)
  let domEndpoints: Endpoint[] = [];
  const domPort = nodePort.node.ports[1];
  if (domPort) {
    const { child: dom, endpoints: dEP } = renderChild(
      nodePort.node, 1, fan, node2D, state, redexes, level,
      { viaD: 0, startOffsetX: -Fan.PORT_DELTA, startOffsetY: Fan.HEIGHT },
    );
    domEndpoints = dEP;
    dom.pos.x = -Fan.PORT_DELTA;
    dom.pos.y = dom.isWireEndpoint
      ? Fan.HEIGHT
      : fan.bounds.max.y - dom.bounds.min.y;
    node2D.add(dom);
  }

  node2D.add(fan);
  endpoints = [...endpoints, ...codomEndpoints, ...domEndpoints];
  return { node2D, endpoints };
}

// Render a destructor agent (fst, snd — entered at port 1)
// Port layout: 0=principal, 1=result(entry)
export function renderDestructorAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  nodePort.node.isCreated = true;

  const fan = new Fan("down", nodePort.node.label || nodePort.node.type);

  // Principal child (port 0)
  const { child, endpoints } = renderChild(
    nodePort.node, 0, fan, node2D, state, redexes, level,
    { viaD: 0, startOffsetY: Fan.HEIGHT, color: levelColor(level) },
  );
  child.pos.y = child.isWireEndpoint
    ? Fan.HEIGHT
    : fan.bounds.max.y - child.bounds.min.y;

  node2D.add(fan);
  node2D.add(child);
  return { node2D, endpoints };
}

// Render a replicator-in agent (rep-in — entered at non-0 port)
export function renderReplicatorInAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  const endpoints: Endpoint[] = [];
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
  const eraCount = countAuxErasers(nodePort.node);
  const relevantAuxPortsMinus1 = Math.max(
    (eraCount > 0) && (eraCount !== nodePort.node.ports.length - 1) ? 1.5 : 0,
    nodePort.node.ports.length - 2 - eraCount,
  );
  rep.pos.y = relevantAuxPortsMinus1 * 2 * D;
  rep.bounds.min.y -= relevantAuxPortsMinus1 * 2 * D;
  node2D.add(rep);

  // Parent wire extender
  const parWire = new Wire(node2D, rep, 0, undefined, levelColor(level));
  parWire.endOffset.x = parentPortDelta;
  node2D.add(parWire);

  const childLevel = level - nodePort.node.levelDeltas![nodePort.port - 1];
  const { child, endpoints: childEndpoints } = renderChild(
    nodePort.node, 0, rep, rep, state, redexes, childLevel,
    { viaD: 0, startOffsetY: Replicator.HEIGHT, color: levelColor(childLevel) },
  );
  child.pos.x = -parentPortDelta;
  child.pos.y = rep.pos.y +
    (child.isWireEndpoint
      ? Replicator.HEIGHT
      : rep.bounds.max.y - child.bounds.min.y);
  node2D.add(child);
  endpoints.push(...childEndpoints);

  // Aux wires
  const lastX = node2D.bounds.max.x;
  let i2 = 2;
  for (let i = 1; i < nodePort.node.ports.length; i++) {
    if (i === nodePort.port) continue;
    const auxLevel = childLevel + nodePort.node.levelDeltas![i - 1];
    if (nodePort.node.ports[i].node.type === "era") {
      nodePort.node.ports[i].node.isCreated = true;
      const era = new Eraser();
      era.pos.x = rep.pos.x + rep.portDelta(i - 1);
      era.pos.y = rep.pos.y - 2 * D;
      node2D.add(era);
      const auxRedex = getRedex(
        nodePort.node,
        nodePort.node.ports[i].node,
        redexes,
      );
      const wire = new Wire(
        rep,
        era,
        0,
        auxRedex?.reduce && (() => applyReduction(state, auxRedex.reduce)),
        levelColor(auxLevel),
      );
      if (auxRedex?.optimal === false) {
        wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      }
      wire.startOffset.x = rep.portDelta(i - 1);
      rep.add(wire);
    } else {
      const endpoint = new Node2D();
      endpoint.bounds = { min: { x: -D, y: 0 }, max: { x: D, y: D } };
      endpoint.pos.x = lastX + (nodePort.node.ports.length - i2 - 0.5) * 2 * D;
      endpoint.pos.y = rep.pos.y;
      node2D.add(endpoint);
      endpoint.isWireEndpoint = true;
      endpoints.push({
        nodePort: nodePort.node.ports[i],
        node2D: endpoint,
        level: auxLevel,
      });
      const auxViaY = (i2 - nodePort.node.ports.length + 0.5) * 2 * D;
      const wire = new Wire(
        rep,
        endpoint,
        auxViaY,
        undefined,
        levelColor(auxLevel),
      );
      wire.startOffset.x = rep.portDelta(i - 1);
      rep.add(wire);
    }
    i2++;
  }

  return { node2D, endpoints };
}

// Render a replicator-out agent (rep-out — entered at port 0)
export function renderReplicatorOutAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  const endpoints: Endpoint[] = [];
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
    if (allChildrenAreWireEndpoints && !child.isWireEndpoint) {
      allChildrenAreWireEndpoints = false;
    }
    children.push(child);
    endpoints.push(...childEndpoints);
  }

  if (allChildrenAreWireEndpoints) {
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

  return { node2D, endpoints };
}

// Render a generic agent — fallback for custom/unknown agent types.
// Draws a label and renders all non-entry ports as child subtrees.
export function renderGenericAgent(
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  let endpoints: Endpoint[] = [];
  nodePort.node.isCreated = true;

  const label = new Label(nodePort.node.label || nodePort.node.type);
  applyTypeCheckHighlight(label, nodePort.node);

  const entryPort = nodePort.port;
  const auxPorts = nodePort.node.ports
    .map((p, i) => ({ ref: p, idx: i }))
    .filter((p) => p.idx !== entryPort);

  // Render all children first so we know their bounds
  const renderedChildren = auxPorts.map((aux) => {
    const childPortRef = aux.ref;
    const { node2D: child, endpoints: childEPs } = renderNodePort(
      childPortRef,
      state,
      redexes,
      level,
    );
    return { childPortRef, child, childEPs };
  });

  // Compute horizontal positions based on actual subtree widths
  const positions: number[] = [];
  if (renderedChildren.length <= 1) {
    positions.push(0);
  } else {
    let x = 0;
    positions.push(0);
    for (let i = 1; i < renderedChildren.length; i++) {
      const prev = renderedChildren[i - 1].child;
      const curr = renderedChildren[i].child;
      const gap = Math.max(
        Fan.PORT_DELTA,
        prev.bounds.max.x - curr.bounds.min.x + Fan.PORT_DELTA,
      );
      x += gap;
      positions.push(x);
    }
    // Center the group
    const center = (positions[0] + positions[positions.length - 1]) / 2;
    for (let i = 0; i < positions.length; i++) {
      positions[i] -= center;
    }
  }

  renderedChildren.forEach(({ childPortRef, child, childEPs }, i) => {
    const xPos = positions[i];
    child.pos.x = xPos;
    child.pos.y = child.isWireEndpoint
      ? Label.SIZE * 2
      : label.bounds.max.y - child.bounds.min.y + Fan.PORT_DELTA;

    const redex = getRedex(nodePort.node, childPortRef.node, redexes);

    if (!child.isWireEndpoint) {
      const wire = new Wire(
        label,
        child,
        0,
        redex?.reduce && (() => applyReduction(state, redex.reduce)),
        levelColor(level),
      );
      if (redex?.optimal === false) {
        wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      }
      wire.startOffset.x = xPos;
      wire.startOffset.y = Label.SIZE;
      node2D.add(wire);
    } else {
      const childEndpoint = childEPs.find((ep) =>
        ep.nodePort === childPortRef
      );
      if (childEndpoint) childEndpoint.redex = redex;
    }

    node2D.add(child);
    endpoints.push(...childEPs);
  });

  node2D.add(label);
  return { node2D, endpoints };
}
