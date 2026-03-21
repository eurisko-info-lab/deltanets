// Custom rule body interpreter for data-driven δ-net reductions.
//
// Executes the RuleStmt[] body of an InteractionRule when two agents interact.
// The "left" node is the one whose type matches rule.agentA, and "right"
// matches rule.agentB.  If both agents have the same type AND both types
// match rule.agentA, we keep the canonical order from the call site.

import { removeFromArrayIf } from "../../util.ts";
import type {
  AgentPortDefs,
  Graph,
  InteractionRule,
  Node,
  RulePortRef,
} from "../../types.ts";
import { link } from "../../graph.ts";

/**
 * Resolve a RulePortRef to a concrete { node, port } index pair.
 *
 * Named ports (e.g. "body", "bind") are resolved via AgentPortDefs using the
 * node's type. Numeric port strings (e.g. "0", "1") are parsed directly.
 */
function resolvePort(
  ref: RulePortRef,
  env: Map<string, Node>,
  agentPorts: AgentPortDefs,
): { node: Node; port: number } {
  const node = env.get(ref.node);
  if (!node) {
    throw new Error(`Custom rule: unknown node "${ref.node}"`);
  }

  // Try numeric parse first
  const numeric = parseInt(ref.port, 10);
  if (!isNaN(numeric)) {
    return { node, port: numeric };
  }

  // Named port — look up from agentPorts by the node's type
  const portMap = agentPorts.get(node.type);
  if (portMap) {
    const idx = portMap.get(ref.port);
    if (idx !== undefined) return { node, port: idx };
  }

  throw new Error(
    `Custom rule: cannot resolve port "${ref.port}" on node "${ref.node}" (type "${node.type}")`,
  );
}

/**
 * Execute a custom interaction rule body against two interacting nodes.
 *
 * @param left       The node whose type matches `rule.agentA`.
 * @param right      The node whose type matches `rule.agentB`.
 * @param graph      The mutable graph array.
 * @param rule       The interaction rule (must have `action.kind === "custom"`).
 * @param agentPorts Port-name → index maps for all agent types.
 */
export function reduceCustomRule(
  left: Node,
  right: Node,
  graph: Graph,
  rule: InteractionRule,
  agentPorts: AgentPortDefs,
) {
  if (rule.action.kind !== "custom") {
    throw new Error("reduceCustomRule called with non-custom rule");
  }

  // Environment maps node names to actual Node objects
  const env = new Map<string, Node>();
  env.set("left", left);
  env.set("right", right);

  for (const stmt of rule.action.body) {
    switch (stmt.kind) {
      case "let": {
        // Create a new agent node with the specified type
        const portCount = getPortCount(stmt.agentType, agentPorts);
        const newNode: Node = {
          type: stmt.agentType,
          label: stmt.label ?? stmt.agentType,
          ports: new Array(portCount),
        };
        // Initialize ports to self-loops (disconnected)
        for (let i = 0; i < portCount; i++) {
          newNode.ports[i] = { node: newNode, port: i };
        }
        graph.push(newNode);
        env.set(stmt.varName, newNode);
        break;
      }
      case "wire": {
        // Connect two ports with a new wire
        const a = resolvePort(stmt.portA, env, agentPorts);
        const b = resolvePort(stmt.portB, env, agentPorts);
        link(a, b);
        break;
      }
      case "relink": {
        // Reconnect: the neighbor of portA gets connected to the neighbor of portB.
        // For new self-looped nodes, neighbor == self, so this also handles new↔old.
        const a = resolvePort(stmt.portA, env, agentPorts);
        const neighborA = a.node.ports[a.port];
        const b = resolvePort(stmt.portB, env, agentPorts);
        const neighborB = b.node.ports[b.port];
        link(neighborA, neighborB);
        break;
      }
      case "erase-stmt": {
        // Insert an eraser at the given port
        const p = resolvePort(stmt.port, env, agentPorts);
        const neighbor = p.node.ports[p.port];
        const eraser: Node = { type: "era", label: "era", ports: [] };
        graph.push(eraser);
        link({ node: eraser, port: 0 }, neighbor);
        break;
      }
    }
  }

  // Remove the original interacting nodes (left and right)
  removeFromArrayIf(graph, (n) => n === left || n === right);
}

/** Get the port count for an agent type from AgentPortDefs, defaulting to 1. */
function getPortCount(agentType: string, agentPorts: AgentPortDefs): number {
  const portMap = agentPorts.get(agentType);
  return portMap ? portMap.size : 1;
}
