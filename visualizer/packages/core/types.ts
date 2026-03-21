// Universal types and interfaces for interaction net systems and tree-based calculi.

import type {
  Abstraction,
  AstNode,
  SystemType,
  Type,
  Variable,
} from "./ast.ts";
import type { TypeEnv, TypeResult } from "./typechecker.ts";

// A port of a particular node.
export type NodePort = { node: Node; port: number; erase?: boolean };

// A node in an interaction net graph.
// Port 0 is the principal port. Ports >= 1 are auxiliary ports (left to right, clockwise from principal).
export type Node = {
  type: string;
  ports: NodePort[];
  label?: string;
  isCreated?: boolean;
  levelDeltas?: number[];
  // Reference to the source AST node (for type check highlighting)
  astRef?: AstNode;
  // Type check visual state (set during type check stepping)
  typeCheckState?: "checking" | "checked" | "error";
  // Used during graph traversal to mark visited nodes
  traversed?: boolean;
  traversed2?: boolean;
  // Used to mark replicators that should be merged
  isToBeMerged?: boolean;
};

// A graph is a list of nodes.
export type Graph = Node[];

// Named port indices for each node type.
// Port 0 is always the principal port for all interaction net agents.
export const Ports = {
  abs: { principal: 0, body: 1, bind: 2, type: 3 },
  app: { func: 0, result: 1, arg: 2 },
  repIn: { principal: 0 },
  repOut: { principal: 0 },
  era: { principal: 0 },
  var: { principal: 0 },
  root: { principal: 0 },
  typeBase: { principal: 0 },
  typeArrow: { principal: 0, domain: 1, codomain: 2 },
  typeHole: { principal: 0 },
  // Lambda cube agents
  tyabs: { principal: 0, body: 1, bind: 2 },
  tyapp: { principal: 0, result: 1, arg: 2 },
  pi: { principal: 0, domain: 1, codomain: 2 },
  sigma: { principal: 0, fstType: 1, sndType: 2 },
  pair: { principal: 0, fst: 1, snd: 2 },
  fst: { principal: 0, result: 1 },
  snd: { principal: 0, result: 1 },
  typeAbs: { principal: 0, body: 1, bind: 2 },
  typeApp: { principal: 0, result: 1, arg: 2 },
  kindStar: { principal: 0 },
  kindArrow: { principal: 0, domain: 1, codomain: 2 },
} as const;

// A reducible pair of interacting nodes.
export type Redex = { a: Node; b: Node; optimal: boolean; reduce: () => void };

// ─── Data-driven interaction rules ─────────────────────────────────
// These are core-level mirrors of the lang-level RuleDef/RuleStmt types,
// kept minimal to avoid a circular dependency between @deltanets/core and
// @deltanets/lang.

/** Port reference inside a custom rule body. */
export type RulePortRef = {
  node: string; // "left" | "right" | variable name introduced by let
  port: string; // named port or numeric index (as string)
};

/** Statements that form the body of a custom interaction rule. */
export type RuleStmt =
  | { kind: "let"; varName: string; agentType: string; label?: string }
  | { kind: "wire"; portA: RulePortRef; portB: RulePortRef }
  | { kind: "relink"; portA: RulePortRef; portB: RulePortRef }
  | { kind: "erase-stmt"; port: RulePortRef };

/** A declared interaction rule between two agent types. */
export type InteractionRule = {
  agentA: string;
  agentB: string;
  action:
    | { kind: "builtin"; name: "annihilate" | "erase" | "commute" | "aux-fan" }
    | { kind: "custom"; body: RuleStmt[] };
};

/**
 * Port-name → index maps for all agents in a system.
 * Passed alongside InteractionRule[] to resolve named ports in custom rules.
 */
export type AgentPortDefs = Map<string, Map<string, number>>;

// The interface that any interaction net system must implement.
// This enables swapping between different graph implementations (e.g., Δ-Nets, HVM).
export interface InteractionSystem {
  name: string;
  buildGraph(
    ast: AstNode,
    systemType: SystemType,
    relativeLevel: boolean,
  ): Graph;
  getRedexes(
    graph: Graph,
    systemType: SystemType,
    relativeLevel: boolean,
    rules?: InteractionRule[],
    agentPorts?: AgentPortDefs,
  ): Redex[];
  getRedex(a: Node, b: Node, redexes: Redex[]): Redex | undefined;
  findReachableNodes(graph: Graph): Set<Node>;
  cleanupGraph(graph: Graph): void;
  isParentPort(nodePort: NodePort): boolean;
  isConnectedToAllErasers(node: Node): boolean;
  countAuxErasers(node: Node): number;
  levelColor(level: number): string | undefined;
  typeCheck?(ast: AstNode, env?: TypeEnv): TypeResult;
  isExprAgent(type: string): boolean;
}

// The interface that any tree-based lambda calculus must implement.
// This enables swapping between different reduction strategies and calculi.
export interface TreeSystem {
  name: string;
  clone(ast: AstNode, parent?: AstNode): AstNode;
  substitute(
    tree: AstNode,
    varName: string,
    replacement: AstNode,
    freeVarsInArg: string[],
  ): AstNode;
  replace(astNode: AstNode, newNode: AstNode): boolean;
  freeVars(node: AstNode): string[];
  boundVars(node: AstNode, name: string): Variable[];
  isAbstractionClosed(node: Abstraction): boolean;
  astToString(ast: AstNode): string;
  typeCheck?(ast: AstNode, env?: TypeEnv): TypeResult;
}
