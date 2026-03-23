// ═══════════════════════════════════════════════════════════════════
// Tactics — Phase 19 + Phase 20 (meta-agent primitives in user tactics)
// Built-in tactic agents (Simp, Decide, Omega, Auto) as INet
// meta-handlers, and user-definable tactics via
// `tactic name { agents... rules... }`.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, RuleDef, TacticDef } from "./evaluator.ts";
import { evalAgent } from "./eval-system.ts";
import type { ComputeRule, ProvedContext } from "./typecheck-prove.ts";
import {
  withNormTable, normalize, computeGoalType,
  tryResolveAssumption, tryResolveSimp, tryResolveDecide, tryResolveOmega, tryResolveAuto,
} from "./typecheck-prove.ts";
import {
  readTermFromGraph, writeTermToGraph, collectTermTree,
  createCtxSearchHandler, createNormalizeHandler, createEqCheckHandler,
  META_CTX_SEARCH, META_NORMALIZE, META_EQ_CHECK,
  META_AGENT_DECLS,
} from "./meta-agents.ts";
import {
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM,
} from "./quotation.ts";
import type { Node, Graph, AgentPortDefs, MetaHandler, InteractionRule } from "@deltanets/core";
import { link, removeFromArrayIf, getRedexes } from "@deltanets/core";

// ─── Tactic agent names ────────────────────────────────────────────

export const TACTIC_SIMP = "TacSimp";
export const TACTIC_DECIDE = "TacDecide";
export const TACTIC_OMEGA = "TacOmega";
export const TACTIC_AUTO = "TacAuto";

export const TACTIC_AGENTS = [
  TACTIC_SIMP, TACTIC_DECIDE, TACTIC_OMEGA, TACTIC_AUTO,
] as const;

// Map from prove-level tactic name → INet agent name
const BUILTIN_TACTIC_MAP: Record<string, string> = {
  simp: TACTIC_SIMP,
  decide: TACTIC_DECIDE,
  omega: TACTIC_OMEGA,
  auto: TACTIC_AUTO,
};

export const BUILTIN_TACTIC_NAMES = new Set([...Object.keys(BUILTIN_TACTIC_MAP), "assumption"]);

/** AST-level resolver for each built-in tactic keyword. */
type BuiltinResolver = (
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
) => AST.ProveExpr | null;

const BUILTIN_RESOLVERS = new Map<string, BuiltinResolver>([
  ["assumption", tryResolveAssumption],
  ["simp", tryResolveSimp],
  ["decide", tryResolveDecide],
  ["omega", tryResolveOmega],
  ["auto", tryResolveAuto],
]);

// ─── Agent declarations ────────────────────────────────────────────

function mkAgent(name: string, portNames: string[]): AST.AgentDecl {
  return {
    kind: "agent",
    name,
    ports: portNames.map((p) => ({ name: p, variadic: false })),
  };
}

export const TACTIC_AGENT_DECLS: AST.AgentDecl[] = [
  mkAgent(TACTIC_SIMP, ["principal", "result"]),
  mkAgent(TACTIC_DECIDE, ["principal", "result"]),
  mkAgent(TACTIC_OMEGA, ["principal", "result"]),
  mkAgent(TACTIC_AUTO, ["principal", "result"]),
];

// ─── Simplified proof helpers ──────────────────────────────────────

function extractEq(
  type: AST.ProveExpr,
): { left: AST.ProveExpr; right: AST.ProveExpr } | null {
  if (type.kind === "call" && type.name === "Eq" && type.args.length === 2) {
    return { left: type.args[0], right: type.args[1] };
  }
  return null;
}

function exprEqual(a: AST.ProveExpr, b: AST.ProveExpr): boolean {
  if (a.kind === "ident" && b.kind === "ident") return a.name === b.name;
  if (a.kind === "call" && b.kind === "call") {
    if (a.name !== b.name || a.args.length !== b.args.length) return false;
    return a.args.every((arg, i) => exprEqual(arg, b.args[i]));
  }
  if (a.kind === "pi" && b.kind === "pi") {
    return exprEqual(a.domain, b.domain) && exprEqual(a.codomain, b.codomain);
  }
  if (a.kind === "sigma" && b.kind === "sigma") {
    return exprEqual(a.domain, b.domain) && exprEqual(a.codomain, b.codomain);
  }
  if (a.kind === "lambda" && b.kind === "lambda") {
    return exprEqual(a.paramType, b.paramType) && exprEqual(a.body, b.body);
  }
  if (a.kind === "let" && b.kind === "let") {
    return a.name === b.name && exprEqual(a.value, b.value) && exprEqual(a.body, b.body);
  }
  return false;
}

// ─── Graph helpers ─────────────────────────────────────────────────

function mkNode(type: string, label: string | undefined, portCount: number): Node {
  const node: Node = { type, label, ports: [] };
  for (let i = 0; i < portCount; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
}

/** Common tactic pattern: read goal, try to prove, write result back. */
function tacticResolve(
  tacAgent: Node,
  tmAgent: Node,
  graph: Graph,
  tryProve: (goal: AST.ProveExpr) => AST.ProveExpr | null,
): void {
  const goal = readTermFromGraph(tmAgent);
  const proof = tryProve(goal);

  // Remove old term tree
  const oldNodes = collectTermTree(tmAgent);
  removeFromArrayIf(graph, (n) => oldNodes.has(n));

  // Write proof (or original goal if no proof found)
  const newRoot = writeTermToGraph(proof ?? goal, graph);
  link({ node: newRoot, port: 0 }, tacAgent.ports[1]);
  removeFromArrayIf(graph, (n) => n === tacAgent);
}

// ─── Built-in tactic MetaHandlers ──────────────────────────────────

/** Simp: normalize both sides of Eq, check equality → refl. */
export function createSimpHandler(
  _provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const tacAgent = left.type === TACTIC_SIMP ? left : right;
    const tmAgent = left.type === TACTIC_SIMP ? right : left;
    tacticResolve(tacAgent, tmAgent, graph, (goal) =>
      withNormTable(computeRules, () => {
        const eq = extractEq(normalize(goal));
        if (!eq) return null;
        if (exprEqual(normalize(eq.left), normalize(eq.right))) {
          return { kind: "ident", name: "refl" };
        }
        return null;
      })
    );
  };
}

/** Decide: ground-term equality via normalization → refl. */
export function createDecideHandler(
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const tacAgent = left.type === TACTIC_DECIDE ? left : right;
    const tmAgent = left.type === TACTIC_DECIDE ? right : left;
    tacticResolve(tacAgent, tmAgent, graph, (goal) =>
      withNormTable(computeRules, () => {
        const eq = extractEq(normalize(goal));
        if (!eq) return null;
        if (exprEqual(normalize(eq.left), normalize(eq.right))) {
          return { kind: "ident", name: "refl" };
        }
        return null;
      })
    );
  };
}

/** Omega: normalize + congruence on Succ. */
export function createOmegaHandler(
  _provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const tacAgent = left.type === TACTIC_OMEGA ? left : right;
    const tmAgent = left.type === TACTIC_OMEGA ? right : left;
    tacticResolve(tacAgent, tmAgent, graph, (goal) =>
      withNormTable(computeRules, () => {
        const eq = extractEq(normalize(goal));
        if (!eq) return null;
        const lhs = normalize(eq.left);
        const rhs = normalize(eq.right);
        if (exprEqual(lhs, rhs)) return { kind: "ident", name: "refl" };
        // Congruence on Succ
        if (
          lhs.kind === "call" && lhs.name === "Succ" && lhs.args.length === 1 &&
          rhs.kind === "call" && rhs.name === "Succ" && rhs.args.length === 1
        ) {
          if (exprEqual(normalize(lhs.args[0]), normalize(rhs.args[0]))) {
            return { kind: "call", name: "cong_succ", args: [{ kind: "ident", name: "refl" }] };
          }
        }
        return null;
      })
    );
  };
}

/** Auto: conv + congruence (simplified depth-1 search). */
export function createAutoHandler(
  _provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): MetaHandler {
  return (left, right, graph, _agentPorts) => {
    const tacAgent = left.type === TACTIC_AUTO ? left : right;
    const tmAgent = left.type === TACTIC_AUTO ? right : left;
    tacticResolve(tacAgent, tmAgent, graph, (goal) =>
      withNormTable(computeRules, () => {
        const eq = extractEq(normalize(goal));
        if (!eq) return null;
        const lhs = normalize(eq.left);
        const rhs = normalize(eq.right);
        if (exprEqual(lhs, rhs)) return { kind: "ident", name: "refl" };
        // Congruence on matching constructors
        if (
          lhs.kind === "call" && rhs.kind === "call" &&
          lhs.name === rhs.name && lhs.args.length === rhs.args.length
        ) {
          if (lhs.args.every((a, i) => exprEqual(normalize(a), normalize(rhs.args[i])))) {
            return { kind: "ident", name: "refl" };
          }
        }
        return null;
      })
    );
  };
}

// ─── Built-in tactics registration ─────────────────────────────────

const TACTIC_TM_TYPES = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM];

export function registerBuiltinTactics(
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): void {
  for (const decl of TACTIC_AGENT_DECLS) {
    if (!agents.has(decl.name)) {
      agents.set(decl.name, evalAgent(decl));
    }
  }

  const handlers: [string, MetaHandler][] = [
    [TACTIC_SIMP, createSimpHandler(provedCtx, computeRules)],
    [TACTIC_DECIDE, createDecideHandler(computeRules)],
    [TACTIC_OMEGA, createOmegaHandler(provedCtx, computeRules)],
    [TACTIC_AUTO, createAutoHandler(provedCtx, computeRules)],
  ];

  for (const [agentName, handler] of handlers) {
    for (const tm of TACTIC_TM_TYPES) {
      rules.push({
        agentA: agentName,
        agentB: tm,
        action: { kind: "meta", handler },
      });
    }
  }
}

// ─── User tactic compilation ───────────────────────────────────────

export function compileTactic(
  decl: AST.TacticDecl,
  agents: Map<string, AgentDef>,
): TacticDef {
  const tacAgents = new Map<string, AgentDef>();
  const tacRules: RuleDef[] = [];

  // Auto-declare tactic agent with (principal, result) ports
  const autoDecl = mkAgent(decl.name, ["principal", "result"]);
  const tacAgent = evalAgent(autoDecl);
  tacAgents.set(decl.name, tacAgent);
  agents.set(decl.name, tacAgent);

  for (const item of decl.body) {
    if (item.kind === "agent") {
      const agent = evalAgent(item);
      tacAgents.set(agent.name, agent);
      agents.set(agent.name, agent);
    } else if (item.kind === "rule") {
      tacRules.push({
        agentA: item.agentA,
        agentB: item.agentB,
        action: item.action,
      });
    }
  }

  return { name: decl.name, agents: tacAgents, rules: tacRules };
}

// ─── User tactic resolution ────────────────────────────────────────

export function resolveAllTactics(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
  tactics: Map<string, TacticDef>,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveUserTacticExpr(
      caseArm.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules,
    );
    if (resolved !== caseArm.body) {
      changed = true;
      return { ...caseArm, body: resolved };
    }
    return caseArm;
  });
  return changed ? { ...prove, cases: newCases } : prove;
}

function resolveUserTacticExpr(
  expr: AST.ProveExpr,
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
  tactics: Map<string, TacticDef>,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
): AST.ProveExpr {
  if (expr.kind === "ident") {
    // Built-in tactic resolvers (assumption, simp, decide, omega, auto)
    const builtinResolver = BUILTIN_RESOLVERS.get(expr.name);
    if (builtinResolver) {
      const result = builtinResolver(prove, caseArm, provedCtx);
      return result ?? expr;
    }
    // User-defined tactics
    if (tactics.has(expr.name)) {
      const tactic = tactics.get(expr.name)!;
      const goal = computeGoalType(prove, caseArm, provedCtx);
      return withNormTable(computeRules, () => {
        const result = runUserTactic(tactic, goal, agents, rules, prove, caseArm, provedCtx, computeRules);
        return result ?? expr;
      });
    }
  }
  if (expr.kind === "let") {
    const nv = resolveUserTacticExpr(expr.value, prove, caseArm, provedCtx, computeRules, tactics, agents, rules);
    const nb = resolveUserTacticExpr(expr.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules);
    if (nv !== expr.value || nb !== expr.body) return { kind: "let", name: expr.name, value: nv, body: nb };
    return expr;
  }
  if (expr.kind === "lambda") {
    const nb = resolveUserTacticExpr(expr.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules);
    if (nb !== expr.body) return { kind: "lambda", param: expr.param, paramType: expr.paramType, body: nb };
    return expr;
  }
  if (expr.kind === "match") {
    let ch = false;
    const nc = expr.cases.map((c) => {
      const r = resolveUserTacticExpr(c.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules);
      if (r !== c.body) ch = true;
      return { ...c, body: r };
    });
    return ch ? { kind: "match", scrutinee: expr.scrutinee, cases: nc } : expr;
  }
  if (expr.kind === "call") {
    let ch = false;
    const na = expr.args.map((a) => {
      const r = resolveUserTacticExpr(a, prove, caseArm, provedCtx, computeRules, tactics, agents, rules);
      if (r !== a) ch = true;
      return r;
    });
    return ch ? { kind: "call", name: expr.name, args: na } : expr;
  }
  return expr;
}

/** Run a user-defined tactic by creating a temporary INet graph,
 *  reducing it, and reading back the proof term.
 *  Phase 20: CtxSearch/NormalizeTerm/EqCheck meta-agents are injected
 *  so user tactics can normalize, search context, and compare terms. */
function runUserTactic(
  tactic: TacticDef,
  goal: AST.ProveExpr,
  systemAgents: Map<string, AgentDef>,
  systemRules: RuleDef[],
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): AST.ProveExpr | null {
  const graph: Graph = [];

  // Write quoted goal into graph
  const goalNode = writeTermToGraph(goal, graph);

  // Create tactic agent
  const tacNode = mkNode(tactic.name, tactic.name, 2);
  graph.push(tacNode);

  // Wire tactic principal to goal's principal
  link({ node: tacNode, port: 0 }, { node: goalNode, port: 0 });

  // Create a root to hold the result
  const root = mkNode("root", "root", 1);
  graph.push(root);
  link({ node: root, port: 0 }, { node: tacNode, port: 1 });

  // Collect all rules
  const allRules: InteractionRule[] = [
    ...tactic.rules.map((r) => ({
      agentA: r.agentA, agentB: r.agentB, action: r.action,
    })),
    ...systemRules.map((r) => ({
      agentA: r.agentA, agentB: r.agentB, action: r.action,
    })),
  ];

  // Phase 20: inject CtxSearch rules (per-invocation, captures proof context)
  const ctxHandler = createCtxSearchHandler(prove, caseArm, provedCtx, computeRules);
  const normHandler = createNormalizeHandler(computeRules);
  const eqHandler = createEqCheckHandler();
  const tmTypes = [TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM];
  for (const tm of tmTypes) {
    allRules.push({ agentA: META_CTX_SEARCH, agentB: tm, action: { kind: "meta", handler: ctxHandler } });
    // Ensure NormalizeTerm and EqCheck are always available
    if (!allRules.some((r) =>
      (r.agentA === META_NORMALIZE && r.agentB === tm) ||
      (r.agentB === META_NORMALIZE && r.agentA === tm)
    )) {
      allRules.push({ agentA: META_NORMALIZE, agentB: tm, action: { kind: "meta", handler: normHandler } });
    }
    if (!allRules.some((r) =>
      (r.agentA === META_EQ_CHECK && r.agentB === tm) ||
      (r.agentB === META_EQ_CHECK && r.agentA === tm)
    )) {
      allRules.push({ agentA: META_EQ_CHECK, agentB: tm, action: { kind: "meta", handler: eqHandler } });
    }
  }

  // Build agent port defs — include meta-agents
  const agentPorts: AgentPortDefs = new Map();
  for (const [name, agent] of tactic.agents) {
    agentPorts.set(name, agent.portIndex);
  }
  for (const [name, agent] of systemAgents) {
    if (!agentPorts.has(name)) agentPorts.set(name, agent.portIndex);
  }
  // Ensure meta-agent port defs are registered
  for (const decl of META_AGENT_DECLS) {
    if (!agentPorts.has(decl.name)) {
      const portIndex = new Map<string, number>();
      decl.ports.forEach((p, i) => portIndex.set(p.name, i));
      agentPorts.set(decl.name, portIndex);
    }
  }

  // Reduce
  const MAX_STEPS = 100;
  for (let i = 0; i < MAX_STEPS; i++) {
    const redexes = getRedexes(graph, "full", false, allRules, agentPorts);
    if (redexes.length === 0) break;
    redexes[0].reduce();
  }

  // Read result from root's port 0
  const resultNode = root.ports[0]?.node;
  if (!resultNode || resultNode.type === "root" || resultNode === tacNode) {
    return null;
  }
  if (resultNode.type.startsWith("Tm")) {
    return readTermFromGraph(resultNode);
  }
  return null;
}
