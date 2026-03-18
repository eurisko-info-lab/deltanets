// Universal types and interface for interaction net systems.
// Any interaction net implementation (Δ-Nets, HVM, etc.) should conform to InteractionSystem.

import type { AstNode, SystemType } from "../ast.ts";

// A port of a particular node.
export type NodePort = { node: Node; port: number };

// A node in an interaction net graph.
// Port 0 is the principal port. Ports >= 1 are auxiliary ports (left to right, clockwise from principal).
export type Node = {
  type: string;
  ports: NodePort[];
  label?: string;
  isCreated?: boolean;
  levelDeltas?: number[];
};

// A graph is a list of nodes.
export type Graph = Node[];

// A reducible pair of interacting nodes.
export type Redex = { a: Node; b: Node; optimal: boolean; reduce: () => void };

// The interface that any interaction net system must implement.
// This enables swapping between different implementations (e.g., Δ-Nets, HVM).
export interface InteractionSystem {
  name: string;
  buildGraph(ast: AstNode, systemType: SystemType, relativeLevel: boolean): Graph;
  getRedexes(graph: Graph, systemType: SystemType, relativeLevel: boolean): Redex[];
  getRedex(a: Node, b: Node, redexes: Redex[]): Redex | undefined;
  findReachableNodes(graph: Graph): Set<Node>;
  cleanupGraph(graph: Graph): void;
  isParentPort(nodePort: NodePort): boolean;
  isConnectedToAllErasers(node: Node): boolean;
  countAuxErasers(node: Node): number;
  levelColor(level: number): string | undefined;
}
