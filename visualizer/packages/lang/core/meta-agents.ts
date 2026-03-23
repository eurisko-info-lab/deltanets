// ═══════════════════════════════════════════════════════════════════
// Meta-Agents — Phase 18
// Built-in agents that inspect/construct/transform quoted terms
// at INet reduction time using procedural (TypeScript) handlers.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, RuleDef } from "./evaluator.ts";
import { evalAgent } from "./eval-system.ts";
import type { ComputeRule } from "./typecheck-prove.ts";
import { withNormTable, normalize } from "./typecheck-prove.ts";
import {
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
} from "./quotation.ts";
import type { Node, Graph, AgentPortDefs, MetaHandler } from "@deltanets/core";
import { link } from "@deltanets/core";
import { removeFromArrayIf } from "@deltanets/core";

// ─── Meta-agent names ──────────────────────────────────────────────

export const META_MATCH_GOAL = "MatchGoal";
export const META_APPLY_RULE = "ApplyRule";
export const META_NORMALIZE = "NormalizeTerm";

export const META_AGENTS = [
  META_MATCH_GOAL, META_APPLY_RULE, META_NORMALIZE,
] as const;

// ─── Agent declarations ────────────────────────────────────────────

function mkAgent(name: string, portNames: string[]): AST.AgentDecl {
  return {
    kind: "agent",
    name,
    ports: portNames.map((p) => ({ name: p, variadic: false })),
  };
}

export const META_AGENT_DECLS: AST.AgentDecl[] = [
  mkAgent(META_MATCH_GOAL, [
    "principal", "on_var", "on_app", "on_pi", "on_sigma", "on_lam", "on_other",
  ]),
  mkAgent(META_APPLY_RULE, ["principal", "result"]),
  mkAgent(META_NORMALIZE, ["principal", "result"]),
];

// ─── Term type helpers ─────────────────────────────────────────────

const TM_TERM_AGENTS = new Set([
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
]);

function isTmAgent(type: string): boolean {
  return TM_TERM_AGENTS.has(type);
}

// ─── Graph-level term read/write ───────────────────────────────────

/**
 * Read a Tm* agent tree from the live graph into a ProveExpr.
 * Follows aux ports (1+) to read children.
 */
export function readTermFromGraph(node: Node, visited?: Set<Node>): AST.ProveExpr {
  if (!visited) visited = new Set();
  if (visited.has(node)) return { kind: "ident", name: "?" };
  visited.add(node);

  switch (node.type) {
    case TM_VAR:
      return { kind: "ident", name: node.label ?? "?" };

    case TM_APP: {
      const argsHead = node.ports[1]?.node;
      const args = argsHead ? readListFromGraph(argsHead, visited) : [];
      return { kind: "call", name: node.label ?? "?", args };
    }

    case TM_PI: {
      const domain = node.ports[1]?.node
        ? readTermFromGraph(node.ports[1].node, visited)
        : { kind: "ident" as const, name: "?" };
      const codomain = node.ports[2]?.node
        ? readTermFromGraph(node.ports[2].node, visited)
        : { kind: "ident" as const, name: "?" };
      return { kind: "pi", param: "_", domain, codomain };
    }

    case TM_SIGMA: {
      const domain = node.ports[1]?.node
        ? readTermFromGraph(node.ports[1].node, visited)
        : { kind: "ident" as const, name: "?" };
      const codomain = node.ports[2]?.node
        ? readTermFromGraph(node.ports[2].node, visited)
        : { kind: "ident" as const, name: "?" };
      return { kind: "sigma", param: "_", domain, codomain };
    }

    case TM_LAM: {
      const paramType = node.ports[1]?.node
        ? readTermFromGraph(node.ports[1].node, visited)
        : { kind: "ident" as const, name: "?" };
      const body = node.ports[2]?.node
        ? readTermFromGraph(node.ports[2].node, visited)
        : { kind: "ident" as const, name: "?" };
      return { kind: "lambda", param: "_", paramType, body };
    }

    default:
      return { kind: "ident", name: node.label ?? node.type };
  }
}

function readListFromGraph(node: Node, visited: Set<Node>): AST.ProveExpr[] {
  if (visited.has(node)) return [];
  visited.add(node);

  if (node.type === TM_NIL) return [];
  if (node.type === TM_CONS) {
    const head = node.ports[1]?.node
      ? readTermFromGraph(node.ports[1].node, visited)
      : { kind: "ident" as const, name: "?" };
    const tail = node.ports[2]?.node
      ? readListFromGraph(node.ports[2].node, visited)
      : [];
    return [head, ...tail];
  }
  return [];
}

/**
 * Write a ProveExpr as Tm* agents into the graph.
 * Returns the root node (caller wires its principal port).
 */
export function writeTermToGraph(expr: AST.ProveExpr, graph: Graph): Node {
  switch (expr.kind) {
    case "ident": {
      const node = mkNode(TM_VAR, expr.name, 1);
      graph.push(node);
      return node;
    }

    case "call": {
      const node = mkNode(TM_APP, expr.name, 2);
      graph.push(node);
      const args = writeListToGraph(expr.args, graph);
      link({ node, port: 1 }, { node: args, port: 0 });
      return node;
    }

    case "pi": {
      const node = mkNode(TM_PI, undefined, 3);
      graph.push(node);
      const domain = writeTermToGraph(expr.domain, graph);
      const codomain = writeTermToGraph(expr.codomain, graph);
      link({ node, port: 1 }, { node: domain, port: 0 });
      link({ node, port: 2 }, { node: codomain, port: 0 });
      return node;
    }

    case "sigma": {
      const node = mkNode(TM_SIGMA, undefined, 3);
      graph.push(node);
      const domain = writeTermToGraph(expr.domain, graph);
      const codomain = writeTermToGraph(expr.codomain, graph);
      link({ node, port: 1 }, { node: domain, port: 0 });
      link({ node, port: 2 }, { node: codomain, port: 0 });
      return node;
    }

    case "lambda": {
      const node = mkNode(TM_LAM, undefined, 3);
      graph.push(node);
      const paramType = writeTermToGraph(expr.paramType, graph);
      const body = writeTermToGraph(expr.body, graph);
      link({ node, port: 1 }, { node: paramType, port: 0 });
      link({ node, port: 2 }, { node: body, port: 0 });
      return node;
    }

    default: {
      // Fallback: encode as TmVar with the expression kind
      const node = mkNode(TM_VAR, "?", 1);
      graph.push(node);
      return node;
    }
  }
}

function writeListToGraph(exprs: AST.ProveExpr[], graph: Graph): Node {
  if (exprs.length === 0) {
    const nil = mkNode(TM_NIL, TM_NIL, 1);
    graph.push(nil);
    return nil;
  }
  const cons = mkNode(TM_CONS, TM_CONS, 3);
  graph.push(cons);
  const head = writeTermToGraph(exprs[0], graph);
  const tail = writeListToGraph(exprs.slice(1), graph);
  link({ node: cons, port: 1 }, { node: head, port: 0 });
  link({ node: cons, port: 2 }, { node: tail, port: 0 });
  return cons;
}

/** Create a node with self-looped ports. */
function mkNode(type: string, label: string | undefined, portCount: number): Node {
  const node: Node = { type, label: label ?? type, ports: [] };
  for (let i = 0; i < portCount; i++) {
    node.ports[i] = { node, port: i };
  }
  return node;
}

/**
 * Collect all Tm* nodes in a subtree rooted at `root`.
 * Follows aux ports (1+) into Tm* children.
 */
export function collectTermTree(root: Node): Set<Node> {
  const nodes = new Set<Node>();
  function walk(node: Node) {
    if (nodes.has(node)) return;
    if (!isTmAgent(node.type)) return;
    nodes.add(node);
    for (let i = 1; i < node.ports.length; i++) {
      if (node.ports[i]?.node) walk(node.ports[i].node);
    }
  }
  walk(root);
  return nodes;
}

// ─── MatchGoal handler ─────────────────────────────────────────────

/**
 * MatchGoal × Tm*: dispatches to the branch corresponding to the Tm type.
 * Recreates the Tm agent at the chosen branch output; erases unused branches.
 */
function matchGoalHandler(
  left: Node,
  right: Node,
  graph: Graph,
  _agentPorts: AgentPortDefs,
): void {
  const matchGoal = left.type === META_MATCH_GOAL ? left : right;
  const tmAgent = left.type === META_MATCH_GOAL ? right : left;

  // Map Tm types to branch port indices
  const branchMap: Record<string, number> = {
    [TM_VAR]: 1,   // on_var
    [TM_APP]: 2,   // on_app
    [TM_PI]: 3,    // on_pi
    [TM_SIGMA]: 4, // on_sigma
    [TM_LAM]: 5,   // on_lam
  };
  const branchPort = branchMap[tmAgent.type] ?? 6; // on_other

  // Clone the Tm agent
  const clone = mkNode(tmAgent.type, tmAgent.label, tmAgent.ports.length);
  graph.push(clone);

  // Connect clone's principal to the chosen branch's neighbor
  link({ node: clone, port: 0 }, matchGoal.ports[branchPort]);

  // Wire clone's aux ports to the original's aux port neighbors
  for (let i = 1; i < tmAgent.ports.length; i++) {
    link({ node: clone, port: i }, tmAgent.ports[i]);
  }

  // Erase all other branches
  for (let i = 1; i < matchGoal.ports.length; i++) {
    if (i !== branchPort) {
      const eraser: Node = { type: "era", label: "era", ports: [] };
      graph.push(eraser);
      link({ node: eraser, port: 0 }, matchGoal.ports[i]);
    }
  }

  // Remove the original interacting agents
  removeFromArrayIf(graph, (n) => n === matchGoal || n === tmAgent);
}

// ─── NormalizeTerm handler ─────────────────────────────────────────

/**
 * Create a NormalizeTerm handler that captures compute rules.
 * When NormalizeTerm × Tm*: reads the Tm tree, normalizes, rebuilds.
 */
export function createNormalizeHandler(computeRules: ComputeRule[]): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const normAgent = left.type === META_NORMALIZE ? left : right;
    const tmAgent = left.type === META_NORMALIZE ? right : left;

    // Read the term tree into a ProveExpr
    const expr = readTermFromGraph(tmAgent);

    // Normalize using compute rules
    const normalized = withNormTable(computeRules, () => normalize(expr));

    // Remove old term tree from graph
    const oldNodes = collectTermTree(tmAgent);
    removeFromArrayIf(graph, (n) => oldNodes.has(n));

    // Build new normalized term tree
    const newRoot = writeTermToGraph(normalized, graph);

    // Connect new root's principal to the result port's neighbor
    link({ node: newRoot, port: 0 }, normAgent.ports[1]);

    // Remove the NormalizeTerm agent
    removeFromArrayIf(graph, (n) => n === normAgent);
  };
}

// ─── ApplyRule handler ─────────────────────────────────────────────

/**
 * Create an ApplyRule handler that captures the agent registry.
 * When ApplyRule × TmVar/TmApp: reads the agent name from the label,
 * creates an instance of that agent, and wires its principal to result.
 */
export function createApplyRuleHandler(agents: Map<string, AgentDef>): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const applyAgent = left.type === META_APPLY_RULE ? left : right;
    const tmAgent = left.type === META_APPLY_RULE ? right : left;

    // Read the agent name from the Tm label
    const name = tmAgent.label ?? tmAgent.type;
    const agentDef = agents.get(name);

    if (!agentDef) {
      // Unknown agent — erase the result port
      const eraser: Node = { type: "era", label: "era", ports: [] };
      graph.push(eraser);
      link({ node: eraser, port: 0 }, applyAgent.ports[1]);
      removeFromArrayIf(graph, (n) => n === applyAgent || n === tmAgent);
      return;
    }

    // Create the named agent
    const newNode = mkNode(agentDef.name, agentDef.name, agentDef.ports.length);
    graph.push(newNode);

    // Wire the new agent's principal to the result port's neighbor
    link({ node: newNode, port: 0 }, applyAgent.ports[1]);

    // If TmApp had args, erase the args list (not wired to the new agent)
    if (tmAgent.type === TM_APP && tmAgent.ports.length > 1) {
      const eraser: Node = { type: "era", label: "era", ports: [] };
      graph.push(eraser);
      link({ node: eraser, port: 0 }, tmAgent.ports[1]);
    }

    // Remove original interacting agents
    removeFromArrayIf(graph, (n) => n === applyAgent || n === tmAgent);
  };
}

// ─── Registration ──────────────────────────────────────────────────

/**
 * Register meta-agents and their interaction rules.
 * The handlers for NormalizeTerm and ApplyRule capture the provided context.
 */
export function registerMetaAgents(
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  computeRules?: ComputeRule[],
): void {
  // Register agent declarations
  for (const decl of META_AGENT_DECLS) {
    if (!agents.has(decl.name)) {
      agents.set(decl.name, evalAgent(decl));
    }
  }

  // MatchGoal × Tm* rules (pure routing, no captured context)
  const matchTmTypes = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS];
  for (const tm of matchTmTypes) {
    rules.push({
      agentA: META_MATCH_GOAL,
      agentB: tm,
      action: { kind: "meta", handler: matchGoalHandler },
    });
  }

  // NormalizeTerm × Tm* rules
  const normHandler = createNormalizeHandler(computeRules ?? []);
  const normTmTypes = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM];
  for (const tm of normTmTypes) {
    rules.push({
      agentA: META_NORMALIZE,
      agentB: tm,
      action: { kind: "meta", handler: normHandler },
    });
  }

  // ApplyRule × TmVar/TmApp rules
  const applyHandler = createApplyRuleHandler(agents);
  for (const tm of [TM_VAR, TM_APP]) {
    rules.push({
      agentA: META_APPLY_RULE,
      agentB: tm,
      action: { kind: "meta", handler: applyHandler },
    });
  }
}
