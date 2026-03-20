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
} from "../../render.ts";
import { MethodState } from "../index.ts";
import {
  type Node,
  type NodePort,
  type Redex,
  deltanets,
} from "../../core/index.ts";
import { agentStyles, getRole, type Data } from "./config.ts";
import { applyReduction } from "./reduction.ts";
import type { Endpoint } from "./render-wires.ts";
import { renderNodePort } from "./render-dispatch.ts";

const { countAuxErasers, getRedex, levelColor } = deltanets;

type State = MethodState<any, Data>;

// Apply typecheck highlight to a node
function applyTypeCheckHighlight(shape: { highlightColor?: string }, node: Node) {
  if (node.typeCheckState === "checking") shape.highlightColor = TYPECHECK_ACTIVE_COLOR;
  else if (node.typeCheckState === "checked") shape.highlightColor = TYPECHECK_DONE_COLOR;
  else if (node.typeCheckState === "error") shape.highlightColor = TYPECHECK_ERROR_COLOR;
}

// Render a leaf agent (var, era, type-base, kind-star, type-hole, or any 1-port agent)
export function renderLeafAgent(
  nodePort: NodePort,
): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  nodePort.node.isCreated = true;
  const style = agentStyles.peek().get(nodePort.node.type);

  if (style?.shape.kind === "eraser" || (!style && nodePort.node.type === "era")) {
    const era = new Eraser();
    node2D.add(era);
  } else {
    const labelText = nodePort.node.type === "type-hole" ? "?" : nodePort.node.label;
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
  const bodyPortRef = nodePort.node.ports[1];
  const { node2D: body, endpoints: bodyEndpoints } = renderNodePort(bodyPortRef, state, redexes, level);
  body.pos.x = Math.max(Fan.PORT_DELTA, -body.bounds.min.x - D);
  body.pos.y = (body as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - body.bounds.min.y;

  const redex = getRedex(nodePort.node, bodyPortRef.node, redexes);

  if (!(body as any).isWireEndpoint) {
    const funcWire = new Wire(fan, body, D, redex?.reduce && (() => applyReduction(state, redex.reduce)), levelColor(level));
    if (redex?.optimal === false) funcWire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
    funcWire.startOffset.x = Fan.PORT_DELTA;
    funcWire.startOffset.y = Fan.HEIGHT;
    node2D.add(funcWire);
  } else {
    const childEndpoint = bodyEndpoints.find((ep) => ep.nodePort === bodyPortRef);
    if (childEndpoint) childEndpoint.redex = redex;
  }

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
    const { node2D: bindTree, endpoints: bindEndpoints } = renderNodePort(bindPortRef, state, redexes, level + 1);
    bindTree.pos.x = -Fan.PORT_DELTA;
    bindTree.pos.y = (bindTree as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - bindTree.bounds.min.y;
    if (!(bindTree as any).isWireEndpoint) {
      const bindWire = new Wire(fan, bindTree, 0, undefined, levelColor(level + 1));
      bindWire.startOffset.x = -Fan.PORT_DELTA;
      bindWire.startOffset.y = Fan.HEIGHT;
      node2D.add(bindWire);
    }
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
      const { node2D: typeTree, endpoints: tEndpoints } = renderNodePort(typePortRef, state, redexes, level);
      typeEndpoints = tEndpoints;
      typeTree.pos.x = -2 * Fan.PORT_DELTA;
      typeTree.pos.y = (typeTree as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - typeTree.bounds.min.y;
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
  const funcPortRef = nodePort.node.ports[0];
  const { node2D: func, endpoints: funcEndpoints } = renderNodePort(funcPortRef, state, redexes, level);
  func.pos.x = Fan.PORT_DELTA;
  func.pos.y = (func as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - func.bounds.min.y;

  const redex = getRedex(nodePort.node, funcPortRef.node, redexes);

  if (!(func as any).isWireEndpoint) {
    const funcWire = new Wire(fan, func, 0, redex?.reduce && (() => applyReduction(state, redex.reduce)), levelColor(level));
    if (redex?.optimal === false) funcWire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
    funcWire.startOffset.y = Fan.HEIGHT;
    node2D.add(funcWire);
  } else {
    const childEndpoint = funcEndpoints.find((ep) => ep.nodePort === funcPortRef);
    if (childEndpoint) childEndpoint.redex = redex;
  }

  // Arg (port 2)
  const argPortRef = nodePort.node.ports[2];
  const { node2D: arg, endpoints: argEndpoints } = renderNodePort(argPortRef, state, redexes, level + 1);
  arg.pos.x = argPortRef.node.type === "var"
    ? fan.bounds.max.x - arg.bounds.min.x + 2 * D
    : Fan.PORT_DELTA + Math.max(func.bounds.max.x, fan.bounds.max.x) - arg.bounds.min.x;

  const argWire = new Wire(fan, arg, -D, undefined, levelColor(level + 1));
  argWire.startOffset.x = Fan.PORT_DELTA;
  node2D.add(argWire);

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
    const { node2D: codom, endpoints: cEP } = renderNodePort(codomPort, state, redexes, level);
    codomEndpoints = cEP;
    codom.pos.x = Math.max(Fan.PORT_DELTA, -codom.bounds.min.x - D);
    codom.pos.y = (codom as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - codom.bounds.min.y;
    if (!(codom as any).isWireEndpoint) {
      const wire = new Wire(fan, codom, D);
      wire.startOffset.x = Fan.PORT_DELTA;
      wire.startOffset.y = Fan.HEIGHT;
      node2D.add(wire);
    }
    node2D.add(codom);
  }

  // Domain / left child (port 1)
  let domEndpoints: Endpoint[] = [];
  const domPort = nodePort.node.ports[1];
  if (domPort) {
    const { node2D: dom, endpoints: dEP } = renderNodePort(domPort, state, redexes, level);
    domEndpoints = dEP;
    dom.pos.x = -Fan.PORT_DELTA;
    dom.pos.y = (dom as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - dom.bounds.min.y;
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
  const { node2D: child, endpoints: childEndpoints } = renderNodePort(nodePort.node.ports[0], state, redexes, level);
  child.pos.y = (child as any).isWireEndpoint ? Fan.HEIGHT : fan.bounds.max.y - child.bounds.min.y;

  const redex = getRedex(nodePort.node, nodePort.node.ports[0].node, redexes);

  if (!(child as any).isWireEndpoint) {
    const wire = new Wire(fan, child, 0, redex?.reduce && (() => applyReduction(state, redex.reduce)), levelColor(level));
    if (redex?.optimal === false) wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
    wire.startOffset.y = Fan.HEIGHT;
    node2D.add(wire);
  } else {
    const childEndpoint = childEndpoints.find((ep) => ep.nodePort === nodePort.node.ports[0]);
    if (childEndpoint) childEndpoint.redex = redex;
  }

  node2D.add(fan);
  node2D.add(child);
  return { node2D, endpoints: childEndpoints };
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
  const rep = new Replicator("down", nodePort.node.label, nodePort.node.levelDeltas!);
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
  const { node2D: child, endpoints: childEndpoints } = renderNodePort(nodePort.node.ports[0], state, redexes, childLevel);
  child.pos.x = -parentPortDelta;
  child.pos.y = rep.pos.y + ((child as any).isWireEndpoint ? Replicator.HEIGHT : rep.bounds.max.y - child.bounds.min.y);
  node2D.add(child);
  endpoints.push(...childEndpoints);

  const redex = getRedex(nodePort.node, nodePort.node.ports[0].node, redexes);

  if (!(child as any).isWireEndpoint) {
    const childWire = new Wire(rep, child, 0, redex?.reduce && (() => applyReduction(state, redex.reduce)), levelColor(childLevel));
    if (redex?.optimal === false) childWire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
    childWire.startOffset.y = Replicator.HEIGHT;
    rep.add(childWire);
  } else {
    const childEndpoint = childEndpoints.find((ep) => ep.nodePort === nodePort.node.ports[0]);
    if (childEndpoint) childEndpoint.redex = redex;
  }

  // Aux wires
  const lastX = node2D.bounds.max.x;
  let i2 = 2;
  for (let i = 1; i < nodePort.node.ports.length; i++) {
    if (i === nodePort.port) { continue; }
    const auxLevel = childLevel + nodePort.node.levelDeltas![i - 1];
    if (nodePort.node.ports[i].node.type === "era") {
      nodePort.node.ports[i].node.isCreated = true;
      const era = new Eraser();
      era.pos.x = rep.pos.x + rep.portDelta(i - 1);
      era.pos.y = rep.pos.y - 2 * D;
      node2D.add(era);
      const auxRedex = getRedex(nodePort.node, nodePort.node.ports[i].node, redexes);
      const wire = new Wire(rep, era, 0, auxRedex?.reduce && (() => applyReduction(state, auxRedex.reduce)), levelColor(auxLevel));
      if (auxRedex?.optimal === false) wire.highlightColor = SUBOPTIMAL_HIGHLIGHT_COLOR;
      wire.startOffset.x = rep.portDelta(i - 1);
      rep.add(wire);
    } else {
      const endpoint = new Node2D();
      endpoint.bounds = { min: { x: -D, y: 0 }, max: { x: D, y: D } };
      endpoint.pos.x = lastX + (nodePort.node.ports.length - i2 - 0.5) * 2 * D;
      endpoint.pos.y = rep.pos.y;
      node2D.add(endpoint);
      (endpoint as any).isWireEndpoint = true;
      endpoints.push({ nodePort: nodePort.node.ports[i], node2D: endpoint, level: auxLevel });
      const auxViaY = (i2 - nodePort.node.ports.length + 0.5) * 2 * D;
      const wire = new Wire(rep, endpoint, auxViaY, undefined, levelColor(auxLevel));
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
  const rep = new Replicator("up", nodePort.node.label, nodePort.node.levelDeltas!);
  node2D.add(rep);

  const children: Node2D[] = [];
  let allChildrenAreWireEndpoints = true;
  for (let i = nodePort.node.ports.length - 1; i > 0; i--) {
    const childLevel = level + nodePort.node.levelDeltas![i - 1];
    const { node2D: child, endpoints: childEndpoints } = renderNodePort(nodePort.node.ports[i], state, redexes, childLevel);
    if (allChildrenAreWireEndpoints && !(child as any).isWireEndpoint) allChildrenAreWireEndpoints = false;
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
        (nodePort.node.ports[nodePort.node.ports.length - 1 - i].node.type === "app" ? 2 * D : 0);
      node2D.add(child);
      const childLevel = level + nodePort.node.levelDeltas![children.length - i - 1];
      const childWire = new Wire(rep, child, (children.length - i - 0.5) * 2 * D, undefined, levelColor(childLevel));
      childWire.startOffset.x = rep.portDelta(i);
      childWire.startOffset.y = Replicator.HEIGHT;
      node2D.add(childWire);
    });
  }

  return { node2D, endpoints };
}
