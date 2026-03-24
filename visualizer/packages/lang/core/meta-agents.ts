// ═══════════════════════════════════════════════════════════════════
// Meta-Agents — Phase 18 + Phase 20 (CtxSearch, EqCheck)
// Built-in agents that inspect/construct/transform quoted terms
// at INet reduction time using procedural (TypeScript) handlers.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, RuleDef } from "./evaluator.ts";
import { evalAgent } from "./eval-system.ts";
import type { ComputeRule, ProvedContext, StrategyContext } from "./typecheck-prove.ts";
import {
  withNormTable, normalize, exprEqual, searchProofContext, convertible,
  makeStrategyContext, extractEq,
  primRewrite, primSearch, primCong,
} from "./typecheck-prove.ts";
import {
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
} from "./quotation.ts";
import type { Node, Graph, AgentPortDefs, MetaHandler, InteractionRule } from "@deltanets/core";
import { link, getRedexes } from "@deltanets/core";
import { removeFromArrayIf } from "@deltanets/core";

// ─── Meta-agent names ──────────────────────────────────────────────

export const META_MATCH_GOAL = "MatchGoal";
export const META_APPLY_RULE = "ApplyRule";
export const META_NORMALIZE = "NormalizeTerm";
export const META_CTX_SEARCH = "CtxSearch";
export const META_EQ_CHECK = "EqCheck";

export const META_AGENTS = [
  META_MATCH_GOAL, META_APPLY_RULE, META_NORMALIZE,
  META_CTX_SEARCH, META_EQ_CHECK,
] as const;

// ─── Strategy protocol agent names ─────────────────────────────────

export const STRAT_OK = "Ok";
export const STRAT_FAIL = "Fail";
export const STRAT_GATE = "Gate";
export const STRAT_DUP_TERM = "DupTerm";
export const STRAT_CONV = "StratConv";
export const STRAT_CTX_LOOKUP = "StratCtxLookup";
export const STRAT_REWRITE = "StratRewrite";
export const STRAT_GROUND = "StratGround";
export const STRAT_SEARCH = "StratSearch";
export const STRAT_CONG = "StratCong";

export const STRAT_AGENTS = [
  STRAT_OK, STRAT_FAIL, STRAT_GATE, STRAT_DUP_TERM,
  STRAT_CONV, STRAT_CTX_LOOKUP, STRAT_REWRITE, STRAT_GROUND, STRAT_SEARCH, STRAT_CONG,
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
  mkAgent(META_CTX_SEARCH, ["principal", "result"]),
  mkAgent(META_EQ_CHECK, ["principal", "second", "on_eq", "on_neq"]),
];

// ─── Strategy protocol agent declarations ──────────────────────────
// Ok/Fail/Gate form a pure backtracking protocol.
// Ok(principal, result) — success, carries proof term on result port
// Fail(principal) — failure signal
// Gate(principal, on_ok, on_fail) — routes based on Ok/Fail

export const STRAT_AGENT_DECLS: AST.AgentDecl[] = [
  mkAgent(STRAT_OK, ["principal", "result"]),
  mkAgent(STRAT_FAIL, ["principal"]),
  mkAgent(STRAT_GATE, ["principal", "on_ok", "on_fail"]),
  mkAgent(STRAT_DUP_TERM, ["principal", "copy1", "copy2"]),
  // Judgment agents: principal receives Tm* goal, output is Ok/Fail
  mkAgent(STRAT_CONV, ["principal", "output"]),
  mkAgent(STRAT_CTX_LOOKUP, ["principal", "output"]),
  mkAgent(STRAT_REWRITE, ["principal", "output"]),
  mkAgent(STRAT_GROUND, ["principal", "output"]),
  mkAgent(STRAT_SEARCH, ["principal", "output", "depth"]),
  mkAgent(STRAT_CONG, ["principal", "output", "inner"]),
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

// ─── CtxSearch handler ─────────────────────────────────────────────

/**
 * Create a CtxSearch handler that captures proof context.
 * When CtxSearch × Tm*: reads goal, searches proof context for a proof,
 * writes proof term (or original goal on failure) to result port.
 */
export function createCtxSearchHandler(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const ctxAgent = left.type === META_CTX_SEARCH ? left : right;
    const tmAgent = left.type === META_CTX_SEARCH ? right : left;

    const goal = readTermFromGraph(tmAgent);
    const proof = withNormTable(computeRules, () =>
      searchProofContext(prove, caseArm, provedCtx, goal)
    );

    // Remove old term tree
    const oldNodes = collectTermTree(tmAgent);
    removeFromArrayIf(graph, (n) => oldNodes.has(n));

    // Write proof (or original goal if not found) to result
    const newRoot = writeTermToGraph(proof ?? goal, graph);
    link({ node: newRoot, port: 0 }, ctxAgent.ports[1]);
    removeFromArrayIf(graph, (n) => n === ctxAgent);
  };
}

// ─── EqCheck handler ───────────────────────────────────────────────

/**
 * Create an EqCheck handler.
 * When EqCheck × Tm*: reads term A (from principal interaction) and
 * term B (from `second` port). If structurally equal, wires on_eq
 * with TmVar("refl") and erases on_neq. Otherwise, wires on_neq
 * with the original goal and erases on_eq.
 */
export function createEqCheckHandler(): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const eqAgent = left.type === META_EQ_CHECK ? left : right;
    const tmAgent = left.type === META_EQ_CHECK ? right : left;

    // Read term A from the principal interaction
    const termA = readTermFromGraph(tmAgent);

    // Read term B from the second port
    const secondNode = eqAgent.ports[1]?.node;
    const termB = (secondNode && secondNode !== eqAgent && isTmAgent(secondNode.type))
      ? readTermFromGraph(secondNode)
      : { kind: "ident" as const, name: "?" };

    const equal = exprEqual(termA, termB);

    // Remove both input Tm* trees
    const oldA = collectTermTree(tmAgent);
    removeFromArrayIf(graph, (n) => oldA.has(n));
    if (secondNode && secondNode !== eqAgent && isTmAgent(secondNode.type)) {
      const oldB = collectTermTree(secondNode);
      removeFromArrayIf(graph, (n) => oldB.has(n));
    }

    if (equal) {
      // Wire TmVar("refl") to on_eq; erase on_neq
      const refl = writeTermToGraph({ kind: "ident", name: "refl" }, graph);
      link({ node: refl, port: 0 }, eqAgent.ports[2]); // on_eq
      const eraser = mkNode("era", "era", 1);
      graph.push(eraser);
      link({ node: eraser, port: 0 }, eqAgent.ports[3]); // on_neq
    } else {
      // Wire original goal back to on_neq; erase on_eq
      const goalBack = writeTermToGraph(termA, graph);
      link({ node: goalBack, port: 0 }, eqAgent.ports[3]); // on_neq
      const eraser = mkNode("era", "era", 1);
      graph.push(eraser);
      link({ node: eraser, port: 0 }, eqAgent.ports[2]); // on_eq
    }

    removeFromArrayIf(graph, (n) => n === eqAgent);
  };
}

// ─── Strategy protocol: Gate rules (pure routing) ──────────────────
// Gate × Ok → wire ok.result to gate.on_ok, erase gate.on_fail
// Gate × Fail → wire to gate.on_fail, erase gate.on_ok

function gateOkHandler(
  left: Node,
  right: Node,
  graph: Graph,
  _agentPorts: AgentPortDefs,
): void {
  const gate = left.type === STRAT_GATE ? left : right;
  const ok = left.type === STRAT_GATE ? right : left;
  // Success: wire Ok's result (port 1) neighbor to Gate's on_ok (port 1) neighbor
  link(ok.ports[1], gate.ports[1]);
  // Erase Gate's on_fail (port 2) neighbor
  const eraser = mkNode("era", "era", 1);
  graph.push(eraser);
  link({ node: eraser, port: 0 }, gate.ports[2]);
  // Remove both interacting agents
  removeFromArrayIf(graph, (n) => n === gate || n === ok);
}

function gateFailHandler(
  left: Node,
  right: Node,
  graph: Graph,
  _agentPorts: AgentPortDefs,
): void {
  const gate = left.type === STRAT_GATE ? left : right;
  const fail = left.type === STRAT_GATE ? right : left;
  // Failure: connect on_ok neighbor ↔ on_fail neighbor
  // on_ok neighbor = final output (root), on_fail neighbor = fallback result (B)
  link(gate.ports[1], gate.ports[2]);
  removeFromArrayIf(graph, (n) => n === gate || n === fail);
}

// ─── Strategy protocol: DupTerm handler ────────────────────────────
// DupTerm × Tm*: reads the Tm* tree, writes two copies to copy1/copy2

function dupTermHandler(
  left: Node,
  right: Node,
  graph: Graph,
  _agentPorts: AgentPortDefs,
): void {
  const dup = left.type === STRAT_DUP_TERM ? left : right;
  const tm = left.type === STRAT_DUP_TERM ? right : left;
  const expr = readTermFromGraph(tm);
  const old = collectTermTree(tm);
  removeFromArrayIf(graph, (n) => old.has(n));
  const copy1 = writeTermToGraph(expr, graph);
  const copy2 = writeTermToGraph(expr, graph);
  link({ node: copy1, port: 0 }, dup.ports[1]); // copy1
  link({ node: copy2, port: 0 }, dup.ports[2]); // copy2
  removeFromArrayIf(graph, (n) => n === dup);
}

// ─── Strategy protocol: Judgment agent handlers ────────────────────
// Each reads a Tm* goal, tries a proof strategy, outputs Ok(proof) or Fail.

function mkOk(proof: AST.ProveExpr, graph: Graph): Node {
  const ok = mkNode(STRAT_OK, STRAT_OK, 2);
  graph.push(ok);
  const tm = writeTermToGraph(proof, graph);
  link({ node: ok, port: 1 }, { node: tm, port: 0 });
  return ok;
}

function mkFail(graph: Graph): Node {
  const fail = mkNode(STRAT_FAIL, STRAT_FAIL, 1);
  graph.push(fail);
  return fail;
}

/** StratConv × Tm*: normalize both sides of Eq, check convertible → Ok(refl) or Fail */
export function createStratConvHandler(computeRules: ComputeRule[]): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const agent = left.type === STRAT_CONV ? left : right;
    const tm = left.type === STRAT_CONV ? right : left;
    const goal = readTermFromGraph(tm);
    const old = collectTermTree(tm);
    removeFromArrayIf(graph, (n) => old.has(n));
    const result = withNormTable(computeRules, () => {
      const eq = extractEq(normalize(goal));
      if (!eq) return null;
      if (convertible(eq.left, eq.right)) return { kind: "ident" as const, name: "refl" };
      return null;
    });
    const out = result ? mkOk(result, graph) : mkFail(graph);
    link({ node: out, port: 0 }, agent.ports[1]);
    removeFromArrayIf(graph, (n) => n === agent);
  };
}

/** StratCtxLookup × Tm*: search proof context → Ok(proof) or Fail */
export function createStratCtxLookupHandler(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const agent = left.type === STRAT_CTX_LOOKUP ? left : right;
    const tm = left.type === STRAT_CTX_LOOKUP ? right : left;
    const goal = readTermFromGraph(tm);
    const old = collectTermTree(tm);
    removeFromArrayIf(graph, (n) => old.has(n));
    const proof = withNormTable(computeRules, () =>
      searchProofContext(prove, caseArm, provedCtx, goal)
    );
    const out = proof ? mkOk(proof, graph) : mkFail(graph);
    link({ node: out, port: 0 }, agent.ports[1]);
    removeFromArrayIf(graph, (n) => n === agent);
  };
}

/** StratRewrite × Tm*: try lemma rewrite → Ok(proof) or Fail */
export function createStratRewriteHandler(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const agent = left.type === STRAT_REWRITE ? left : right;
    const tm = left.type === STRAT_REWRITE ? right : left;
    const goal = readTermFromGraph(tm);
    const old = collectTermTree(tm);
    removeFromArrayIf(graph, (n) => old.has(n));
    const result = withNormTable(computeRules, () => {
      const sctx = makeStrategyContext(prove, caseArm, provedCtx);
      sctx.goal = goal; // override with graph-read goal
      return primRewrite(sctx);
    });
    const out = result ? mkOk(result, graph) : mkFail(graph);
    link({ node: out, port: 0 }, agent.ports[1]);
    removeFromArrayIf(graph, (n) => n === agent);
  };
}

/** StratGround × Tm*: check ground equality → Ok(refl) or Fail */
export function createStratGroundHandler(computeRules: ComputeRule[]): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const agent = left.type === STRAT_GROUND ? left : right;
    const tm = left.type === STRAT_GROUND ? right : left;
    const goal = readTermFromGraph(tm);
    const old = collectTermTree(tm);
    removeFromArrayIf(graph, (n) => old.has(n));
    const result = withNormTable(computeRules, () => {
      const eq = extractEq(normalize(goal));
      if (!eq) return null;
      const lhs = normalize(eq.left);
      const rhs = normalize(eq.right);
      if (exprEqual(lhs, rhs)) return { kind: "ident" as const, name: "refl" };
      return null;
    });
    const out = result ? mkOk(result, graph) : mkFail(graph);
    link({ node: out, port: 0 }, agent.ports[1]);
    removeFromArrayIf(graph, (n) => n === agent);
  };
}

/** StratSearch × Tm*: depth-bounded proof search → Ok(proof) or Fail */
export function createStratSearchHandler(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const agent = left.type === STRAT_SEARCH ? left : right;
    const tm = left.type === STRAT_SEARCH ? right : left;
    const goal = readTermFromGraph(tm);
    const old = collectTermTree(tm);
    removeFromArrayIf(graph, (n) => old.has(n));
    // Read depth from port 2 (encoded as TmVar label)
    const depthNode = agent.ports[2]?.node;
    const depth = (depthNode && depthNode !== agent && depthNode.type === TM_VAR)
      ? parseInt(depthNode.label ?? "3", 10) || 3
      : 3;
    if (depthNode && depthNode !== agent) {
      removeFromArrayIf(graph, (n) => n === depthNode);
    }
    const result = withNormTable(computeRules, () => {
      const sctx = makeStrategyContext(prove, caseArm, provedCtx);
      sctx.goal = goal; // override with graph-read goal
      return primSearch(sctx, depth);
    });
    const out = result ? mkOk(result, graph) : mkFail(graph);
    link({ node: out, port: 0 }, agent.ports[1]);
    removeFromArrayIf(graph, (n) => n === agent);
  };
}

/** StratCong × Tm*: congruence decomposition → Ok(wrapped proof) or Fail
 *  Reads constructor name from `inner` port's label.
 *  Decomposes goal into subgoal, creates sub-strategy graph, reduces, wraps. */
export function createStratCongHandler(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const agent = left.type === STRAT_CONG ? left : right;
    const tm = left.type === STRAT_CONG ? right : left;
    const goal = readTermFromGraph(tm);
    const old = collectTermTree(tm);
    removeFromArrayIf(graph, (n) => old.has(n));
    const ctor = agent.label !== STRAT_CONG ? agent.label : undefined;
    const decomp = withNormTable(computeRules, () => {
      const sctx = makeStrategyContext(prove, caseArm, provedCtx);
      sctx.goal = goal; // override with graph-read goal
      return primCong(ctor, sctx);
    });
    if (!decomp) {
      const fail = mkFail(graph);
      link({ node: fail, port: 0 }, agent.ports[1]); // output
      // Erase inner port neighbor
      const eraser = mkNode("era", "era", 1);
      graph.push(eraser);
      link({ node: eraser, port: 0 }, agent.ports[2]); // inner
      removeFromArrayIf(graph, (n) => n === agent);
      return;
    }
    // Decomposition succeeded: write subgoal Tm*, wire to inner strategy,
    // place CongWrap on the output to wrap the result.
    const subGoalNode = writeTermToGraph(decomp.subGoal, graph);
    link({ node: subGoalNode, port: 0 }, agent.ports[2]); // inner strategy input
    const wrapper = mkNode("CongWrap", "CongWrap", 2);
    (wrapper as any)._wrap = decomp.wrap;
    graph.push(wrapper);
    link({ node: wrapper, port: 0 }, agent.ports[1]); // output
    removeFromArrayIf(graph, (n) => n === agent);
  };
}



// ─── CongWrap handler ──────────────────────────────────────────────
// CongWrap × Ok → wrap the proof term, emit Ok(wrapped)
// CongWrap × Fail → pass through Fail

function congWrapOkHandler(
  left: Node,
  right: Node,
  graph: Graph,
  _agentPorts: AgentPortDefs,
): void {
  const wrapper = left.type === "CongWrap" ? left : right;
  const ok = left.type === "CongWrap" ? right : left;
  const wrapFn = (wrapper as any)._wrap as ((p: AST.ProveExpr) => AST.ProveExpr) | undefined;
  // Read the proof from Ok's result port
  const proofNode = ok.ports[1]?.node;
  const proof = (proofNode && proofNode !== ok && proofNode.type.startsWith("Tm"))
    ? readTermFromGraph(proofNode)
    : { kind: "ident" as const, name: "?" };
  // Clean up old proof tree
  if (proofNode && proofNode !== ok && proofNode.type.startsWith("Tm")) {
    const old = collectTermTree(proofNode);
    removeFromArrayIf(graph, (n) => old.has(n));
  }
  const wrapped = wrapFn ? wrapFn(proof) : proof;
  const newOk = mkOk(wrapped, graph);
  link({ node: newOk, port: 0 }, wrapper.ports[1]); // output
  removeFromArrayIf(graph, (n) => n === wrapper || n === ok);
}

function congWrapFailHandler(
  left: Node,
  right: Node,
  graph: Graph,
  _agentPorts: AgentPortDefs,
): void {
  const wrapper = left.type === "CongWrap" ? left : right;
  const fail = left.type === "CongWrap" ? right : left;
  const newFail = mkFail(graph);
  link({ node: newFail, port: 0 }, wrapper.ports[1]); // output
  removeFromArrayIf(graph, (n) => n === wrapper || n === fail);
}

// ─── Strategy graph builder ────────────────────────────────────────
// Compiles a StrategyExpr into an INet agent wiring graph.
// Returns the root node whose principal port receives the goal Tm*,
// and whose output port emits the Ok/Fail result.

/**
 * Build an INet graph that implements a strategy expression.
 * @param expr       The strategy expression to compile
 * @param strategies Map of strategy name → expression (for self-reference)
 * @param graph      The mutable graph to add nodes to
 * @param depth      Recursion depth limit for self-referential strategies
 * @returns { input, output } — wire goal Tm* to input, read Ok/Fail from output
 */
export function buildStrategyGraph(
  expr: AST.StrategyExpr,
  strategies: Map<string, AST.StrategyExpr>,
  graph: Graph,
  depth: number = 10,
): { input: { node: Node; port: number }; output: { node: Node; port: number } } | null {
  if (depth <= 0) return null;

  switch (expr.kind) {
    case "ident": {
      // Check for primitive judgment agents
      const agentType = STRAT_PRIMITIVE_MAP[expr.name];
      if (agentType) {
        const agent = mkNode(agentType, agentType, agentType === STRAT_SEARCH ? 3 : 2);
        graph.push(agent);
        return {
          input: { node: agent, port: 0 },    // principal receives goal
          output: { node: agent, port: 1 },    // output emits Ok/Fail
        };
      }
      // Named strategy reference — expand inline
      const ref = strategies.get(expr.name);
      if (ref) return buildStrategyGraph(ref, strategies, graph, depth - 1);
      return null;
    }

    case "first": {
      if (expr.alts.length === 0) return null;
      if (expr.alts.length === 1) {
        return buildStrategyGraph(expr.alts[0], strategies, graph, depth);
      }
      // first(A, B, ...) = DupTerm + A + Gate + B (both run in parallel)
      // Gate × Ok  → pass A's proof to output, erase B's result
      // Gate × Fail → pass B's result to output
      const altA = buildStrategyGraph(expr.alts[0], strategies, graph, depth);
      if (!altA) return buildStrategyGraph(
        { kind: "first", alts: expr.alts.slice(1) }, strategies, graph, depth);
      const rest = expr.alts.length === 2
        ? buildStrategyGraph(expr.alts[1], strategies, graph, depth)
        : buildStrategyGraph({ kind: "first", alts: expr.alts.slice(1) }, strategies, graph, depth);
      if (!rest) return altA;

      const dup = mkNode(STRAT_DUP_TERM, STRAT_DUP_TERM, 3);
      graph.push(dup);
      const gate = mkNode(STRAT_GATE, STRAT_GATE, 3);
      graph.push(gate);

      // dup.copy1 → A.input, dup.copy2 → B.input (both branches run)
      link(altA.input, { node: dup, port: 1 });
      link(rest.input, { node: dup, port: 2 });
      // A.output → gate.principal
      link(altA.output, { node: gate, port: 0 });
      // gate.on_fail → B.output (fallback = B's result)
      link({ node: gate, port: 2 }, rest.output);

      return {
        input: { node: dup, port: 0 },    // goal enters here
        output: { node: gate, port: 1 },   // on_ok = final result
      };
    }

    case "cong": {
      // Cong compiles to a StratCong agent with the inner strategy on port 2
      const agent = mkNode(STRAT_CONG, expr.ctor ?? STRAT_CONG, 3);
      graph.push(agent);
      const inner = buildStrategyGraph(expr.inner, strategies, graph, depth - 1);
      if (inner) {
        link({ node: agent, port: 2 }, inner.input); // inner strategy input
      }
      return {
        input: { node: agent, port: 0 },
        output: { node: agent, port: 1 },
      };
    }

    case "search": {
      const agent = mkNode(STRAT_SEARCH, STRAT_SEARCH, 3);
      graph.push(agent);
      // Encode depth as a TmVar label on port 2
      const depthNode = mkNode(TM_VAR, String(expr.depth), 1);
      graph.push(depthNode);
      link({ node: agent, port: 2 }, { node: depthNode, port: 0 });
      return {
        input: { node: agent, port: 0 },
        output: { node: agent, port: 1 },
      };
    }
  }
}

const STRAT_PRIMITIVE_MAP: Record<string, string> = {
  conv: STRAT_CONV,
  ctx_search: STRAT_CTX_LOOKUP,
  rewrite: STRAT_REWRITE,
  ground: STRAT_GROUND,
};

/**
 * Run a strategy by building an INet graph, reducing it, and reading the result.
 * This replaces the TypeScript interpreter with real INet reduction.
 */
export function runStrategyGraph(
  expr: AST.StrategyExpr,
  goal: AST.ProveExpr,
  strategies: Map<string, AST.StrategyExpr>,
  allRules: InteractionRule[],
  agentPorts: AgentPortDefs,
): AST.ProveExpr | null {
  const graph: Graph = [];

  // Build the strategy agent graph
  const strat = buildStrategyGraph(expr, strategies, graph);
  if (!strat) return null;

  // Write the goal as Tm* agents and wire to strategy input
  const goalNode = writeTermToGraph(goal, graph);
  link({ node: goalNode, port: 0 }, strat.input);

  // Create root to capture output
  const root = mkNode("root", "root", 1);
  graph.push(root);
  link({ node: root, port: 0 }, strat.output);

  // Reduce
  const MAX_STEPS = 200;
  for (let i = 0; i < MAX_STEPS; i++) {
    const redexes = getRedexes(graph, "full", false, allRules, agentPorts);
    if (redexes.length === 0) break;
    redexes[0].reduce();
  }

  // Read result: expect Ok node with proof on result port
  const resultNode = root.ports[0]?.node;
  if (!resultNode || resultNode === root) return null;
  if (resultNode.type === STRAT_OK) {
    const proofNode = resultNode.ports[1]?.node;
    if (proofNode && proofNode !== resultNode && proofNode.type.startsWith("Tm")) {
      return readTermFromGraph(proofNode);
    }
  }
  // If result is a Tm* node directly (from pass-through), read it
  if (resultNode.type.startsWith("Tm")) {
    return readTermFromGraph(resultNode);
  }
  return null;
}

/**
 * Collect all strategy protocol interaction rules for a given proof context.
 * These are injected alongside meta-agent rules when running strategies.
 */
export function collectStrategyRules(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): InteractionRule[] {
  const rules: InteractionRule[] = [];
  const tmTypes = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM];

  // Gate × Ok, Gate × Fail (pure routing)
  rules.push({ agentA: STRAT_GATE, agentB: STRAT_OK, action: { kind: "meta", handler: gateOkHandler } });
  rules.push({ agentA: STRAT_GATE, agentB: STRAT_FAIL, action: { kind: "meta", handler: gateFailHandler } });

  // DupTerm × Tm*
  for (const tm of tmTypes) {
    rules.push({ agentA: STRAT_DUP_TERM, agentB: tm, action: { kind: "meta", handler: dupTermHandler } });
  }

  // CongWrap × Ok, CongWrap × Fail
  rules.push({ agentA: "CongWrap", agentB: STRAT_OK, action: { kind: "meta", handler: congWrapOkHandler } });
  rules.push({ agentA: "CongWrap", agentB: STRAT_FAIL, action: { kind: "meta", handler: congWrapFailHandler } });

  // Judgment agent handlers (context-dependent)
  const convHandler = createStratConvHandler(computeRules);
  const ctxHandler = createStratCtxLookupHandler(prove, caseArm, provedCtx, computeRules);
  const rwHandler = createStratRewriteHandler(prove, caseArm, provedCtx, computeRules);
  const groundHandler = createStratGroundHandler(computeRules);
  const searchHandler = createStratSearchHandler(prove, caseArm, provedCtx, computeRules);
  const congHandler = createStratCongHandler(prove, caseArm, provedCtx, computeRules);

  for (const tm of tmTypes) {
    rules.push({ agentA: STRAT_CONV, agentB: tm, action: { kind: "meta", handler: convHandler } });
    rules.push({ agentA: STRAT_CTX_LOOKUP, agentB: tm, action: { kind: "meta", handler: ctxHandler } });
    rules.push({ agentA: STRAT_REWRITE, agentB: tm, action: { kind: "meta", handler: rwHandler } });
    rules.push({ agentA: STRAT_GROUND, agentB: tm, action: { kind: "meta", handler: groundHandler } });
    rules.push({ agentA: STRAT_SEARCH, agentB: tm, action: { kind: "meta", handler: searchHandler } });
    rules.push({ agentA: STRAT_CONG, agentB: tm, action: { kind: "meta", handler: congHandler } });
  }

  return rules;
}

// ─── Registration ──────────────────────────────────────────────────

/**
 * Register meta-agents and their interaction rules.
 * The handlers for NormalizeTerm and ApplyRule capture the provided context.
 */
/** Upsert a rule: replace an existing rule for the same pair, or push. */
function upsertRule(rules: RuleDef[], rule: RuleDef): void {
  const idx = rules.findIndex(
    (r) =>
      (r.agentA === rule.agentA && r.agentB === rule.agentB) ||
      (r.agentA === rule.agentB && r.agentB === rule.agentA),
  );
  if (idx >= 0) rules[idx] = rule;
  else rules.push(rule);
}

export function registerMetaAgents(
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  computeRules?: ComputeRule[],
): void {
  // Register meta-agent declarations (idempotent for agent defs)
  for (const decl of META_AGENT_DECLS) {
    if (!agents.has(decl.name)) agents.set(decl.name, evalAgent(decl));
  }

  // Register strategy protocol agent declarations
  for (const decl of STRAT_AGENT_DECLS) {
    if (!agents.has(decl.name)) agents.set(decl.name, evalAgent(decl));
  }

  // MatchGoal × Tm* rules (pure routing, no captured context)
  const matchTmTypes = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS];
  for (const tm of matchTmTypes) {
    upsertRule(rules, {
      agentA: META_MATCH_GOAL,
      agentB: tm,
      action: { kind: "meta", handler: matchGoalHandler },
    });
  }

  // NormalizeTerm × Tm* rules
  const normHandler = createNormalizeHandler(computeRules ?? []);
  const normTmTypes = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM];
  for (const tm of normTmTypes) {
    upsertRule(rules, {
      agentA: META_NORMALIZE,
      agentB: tm,
      action: { kind: "meta", handler: normHandler },
    });
  }

  // ApplyRule × TmVar/TmApp rules
  const applyHandler = createApplyRuleHandler(agents);
  for (const tm of [TM_VAR, TM_APP]) {
    upsertRule(rules, {
      agentA: META_APPLY_RULE,
      agentB: tm,
      action: { kind: "meta", handler: applyHandler },
    });
  }

  // EqCheck × Tm* rules (structural equality, no captured context)
  const eqHandler = createEqCheckHandler();
  for (const tm of normTmTypes) {
    upsertRule(rules, {
      agentA: META_EQ_CHECK,
      agentB: tm,
      action: { kind: "meta", handler: eqHandler },
    });
  }
}
