// Δ-Nets specific types and helper functions.

import { removeFromArrayIf } from "../../util.ts";
import { Ports } from "../../types.ts";
import type { Graph, InteractionRule, Node, NodePort } from "../../types.ts";
import { link, reciprocal } from "../../graph.ts";
import { reduceCommute } from "../../reductions.ts";

// --- Delta-nets specific types ---

export type NodeType =
  | "abs" // Abstraction (3 auxiliary ports: body, bind, type)
  | "app" // Application (2 auxiliary ports: func, arg)
  | "rep-in" // Replicator Fan-In (any number of auxiliary ports)
  | "rep-out" // Replicator Fan-Out (any number of auxiliary ports)
  | "era" // Eraser (0 auxiliary ports)
  | "var" // Variable (0 auxiliary ports)
  | "root" // Root (0 auxiliary ports)
  | "type-base" // Base type (0 auxiliary ports)
  | "type-arrow" // Arrow type (2 auxiliary ports: domain, codomain)
  | "type-hole"; // Unknown/hole type (0 auxiliary ports)

export type RepStatus = "unpaired" | "unknown";

export type DeltaData = { appliedFinalStep: boolean; isFinalStep: boolean };

// --- Delta-nets specific helpers ---

export function parseRepLabel(
  label: string,
): { level: number; status: RepStatus } {
  let level: number;
  let status: RepStatus;
  const marker = label[label.length - 1];
  if (marker === "*") {
    level = parseInt(label.slice(0, -1));
    status = "unknown";
  } else {
    level = parseInt(label);
    status = "unpaired";
  }
  return { level, status };
}

export function formatRepLabel(level: number, status: RepStatus): string {
  if (status === "unknown") {
    return level + "*";
  } else {
    return level.toString();
  }
}

export function isParentPort(nodePort: NodePort): boolean {
  const { type, ports } = nodePort.node;
  const port = nodePort.port;

  // Replicators: special handling
  if (type === "rep-out") return port === 0;
  if (type === "rep-in") return port !== 0;

  // For all other agents, determine entry port from port count and naming convention:
  // - 1-port agents (leaf): entry = port 0
  // - Applicators/destructors (app, tyapp, type-app, fst, snd): entry = port 1
  // - Everything else (binders, type-constructors): entry = port 0
  if (ports.length === 1) return port === 0;
  if (
    type === "app" || type === "tyapp" || type === "type-app" ||
    type === "fst" || type === "snd"
  ) return port === 1;
  return port === 0;
}

export function isConnectedToAllErasers(node: Node): boolean {
  return node.ports.every((p, i) => i > 0 ? p.node.type === "era" : true);
}

export function countAuxErasers(node: Node): number {
  return node.ports.reduce((count, p, i) => {
    if (i > 0 && p.node.type === "era") {
      count++;
    }
    return count;
  }, 0);
}

// --- Delta-nets specific reduction ---

export function reduceAuxFan(node: Node, graph: Graph, relativeLevel: boolean) {
  // node is an app node
  const firstAuxNode = node.ports[Ports.app.result].node;

  if (firstAuxNode.type === "era") {
    const newEraser0: Node = { type: "era", ports: [] };
    graph.push(newEraser0);
    link({ node: newEraser0, port: 0 }, node.ports[Ports.app.func]);

    const newEraser1: Node = { type: "era", ports: [] };
    graph.push(newEraser1);
    link({ node: newEraser1, port: 0 }, node.ports[Ports.app.arg]);

    removeFromArrayIf(graph, (n) => (n === node) || (n === firstAuxNode));
  } else if (firstAuxNode.type.startsWith("rep")) {
    // Rotate ports: func(0)→2, result(1)→0, arg(2)→1
    const origPorts = [...node.ports];
    link({ node, port: 0 }, origPorts[Ports.app.result]);
    link({ node, port: 1 }, origPorts[Ports.app.arg]);
    link({ node, port: 2 }, origPorts[Ports.app.func]);

    const { nodeClones, otherClones } = reduceCommute(node, graph);

    if (relativeLevel) {
      const repLevel = parseRepLabel(otherClones[1].label!).level;
      otherClones[0].label = formatRepLabel(repLevel + 1, "unknown");
    }

    nodeClones.forEach((nodeClone) => {
      const origPorts = [...nodeClone.ports];
      link({ node: nodeClone, port: 0 }, origPorts[2]);
      link({ node: nodeClone, port: 1 }, origPorts[0]);
      link({ node: nodeClone, port: 2 }, origPorts[1]);
    });
  }
}

// --- Type graph helpers ---

export function isTypeNode(node: Node): boolean {
  return node.type === "type-base" || node.type === "type-arrow" ||
    node.type === "type-hole";
}

// Whether a node type is an expression-level agent (vs type/lambda-cube agent)
const EXPR_AGENT_TYPES = new Set(["abs", "app", "var", "era", "root"]);
export function isExprAgent(type: string): boolean {
  return EXPR_AGENT_TYPES.has(type) || type.startsWith("rep");
}

// Cross-rule erasure: both agents are erased (all aux ports get erasers)
export function reduceEraseRule(nodeA: Node, nodeB: Node, graph: Graph) {
  for (let i = 1; i < nodeA.ports.length; i++) {
    const newEraser: Node = { type: "era", label: "era", ports: [] };
    graph.push(newEraser);
    link({ node: newEraser, port: 0 }, nodeA.ports[i]);
  }
  for (let i = 1; i < nodeB.ports.length; i++) {
    const newEraser: Node = { type: "era", label: "era", ports: [] };
    graph.push(newEraser);
    link({ node: newEraser, port: 0 }, nodeB.ports[i]);
  }
  removeFromArrayIf(graph, (n) => n === nodeA || n === nodeB);
}

// Default interaction rules for lambda cube agents (used when no .inet rules are provided).
// These mirror the rules defined in lambda-cube.inet but are available for raw lambda terms.

const annihilate = { kind: "builtin", name: "annihilate" } as const;
const erase = { kind: "builtin", name: "erase" } as const;

export const DEFAULT_RULES: InteractionRule[] = [
  // Lambda cube annihilation rules
  { agentA: "tyabs", agentB: "tyapp", action: annihilate },
  { agentA: "type-abs", agentB: "type-app", action: annihilate },
  { agentA: "fst", agentB: "pair", action: annihilate },
  { agentA: "snd", agentB: "pair", action: annihilate },
  { agentA: "tyapp", agentB: "type-abs", action: annihilate }, // λω cross-rule
  // Lambda cube cross-rule erasure
  { agentA: "tyabs", agentB: "fst", action: erase }, // λP2
  { agentA: "tyabs", agentB: "snd", action: erase }, // λP2
  { agentA: "type-abs", agentB: "fst", action: erase }, // λPω
  { agentA: "type-abs", agentB: "snd", action: erase }, // λPω
];
