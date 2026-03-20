// ═══════════════════════════════════════════════════════════════════
// Render Dispatch — main renderNodePort entry point
// Dispatches to role-based renderers and provides the wire endpoint
// fallback for already-created or unknown nodes.
// ═══════════════════════════════════════════════════════════════════

import { Signal } from "@preact/signals";
import {
  D,
  Node2D,
} from "../../render.ts";
import { MethodState } from "../index.ts";
import {
  type NodePort,
  type Redex,
  type Graph,
} from "../../core/index.ts";
import { getRole, type Data } from "./config.ts";
import type { Endpoint } from "./render-wires.ts";
import {
  renderLeafAgent,
  renderBinderAgent,
  renderApplicatorAgent,
  renderTypeConstructorAgent,
  renderDestructorAgent,
  renderReplicatorInAgent,
  renderReplicatorOutAgent,
} from "./render-roles.ts";

type State = MethodState<Graph, Data>;

// Create a wire endpoint node for already-created or unknown nodes
function makeWireEndpoint(nodePort: NodePort, level: number): { node2D: Node2D; endpoints: Endpoint[] } {
  const node2D = new Node2D();
  const endpoint = new Node2D();
  endpoint.bounds = { min: { x: -D, y: 0 }, max: { x: D, y: D } };
  node2D.add(endpoint);
  node2D.isWireEndpoint = true;
  return { node2D, endpoints: [{ nodePort, node2D, level }] };
}

// ─── Main renderNodePort — dispatches by role ──────────────────

// Renders a node port
export const renderNodePort = (
  nodePort: NodePort,
  state: Signal<State>,
  redexes: Redex[],
  level: number = 0,
): { node2D: Node2D; endpoints: Endpoint[] } => {
  // Already created — wire endpoint
  if (nodePort.node.isCreated) {
    return makeWireEndpoint(nodePort, level);
  }

  // Look up role from style or infer from type name
  const role = getRole(nodePort.node.type);

  // Dispatch by role
  switch (role) {
    case "leaf":
      return renderLeafAgent(nodePort);
    case "binder":
      if (nodePort.port === 0) return renderBinderAgent(nodePort, state, redexes, level);
      break;
    case "applicator":
      if (nodePort.port === 1) return renderApplicatorAgent(nodePort, state, redexes, level);
      break;
    case "type-constructor":
      if (nodePort.port === 0) return renderTypeConstructorAgent(nodePort, state, redexes, level);
      break;
    case "destructor":
      if (nodePort.port === 1) return renderDestructorAgent(nodePort, state, redexes, level);
      break;
    case "replicator":
      if (nodePort.port !== 0) return renderReplicatorInAgent(nodePort, state, redexes, level);
      if (nodePort.port === 0) return renderReplicatorOutAgent(nodePort, state, redexes, level);
      break;
  }

  // Unknown agent or wrong entry port — wire endpoint (will be connected later)
  return makeWireEndpoint(nodePort, level);
};
