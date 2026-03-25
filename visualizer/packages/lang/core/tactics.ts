// ═══════════════════════════════════════════════════════════════════
// Tactics — Strategy-based tactic resolution + user-definable tactics
// via `tactic name { agents... rules... }`.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, RuleDef, TacticDef, InstanceDef } from "./evaluator.ts";
import { evalAgent } from "./eval-system.ts";
import type { ComputeRule, ProvedContext, StrategyContext } from "./typecheck-prove.ts";
import {
  withNormTable, normalize, computeGoalType,
  makeStrategyContext, primConv, primCtxSearch, primRewrite, primGround, primCong, primSearch, primEauto,
} from "./typecheck-prove.ts";
import {
  readTermFromGraph, writeTermToGraph, collectTermTree,
  createCtxSearchHandler, createNormalizeHandler, createEqCheckHandler,
  META_CTX_SEARCH, META_NORMALIZE, META_EQ_CHECK,
  META_AGENT_DECLS,
  STRAT_AGENT_DECLS, collectStrategyRules, runStrategyGraph,
} from "./meta-agents.ts";
import {
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM,
} from "./quotation.ts";
import type { Node, Graph, AgentPortDefs, MetaHandler, InteractionRule } from "@deltanets/core";
import { link, removeFromArrayIf, getRedexes } from "@deltanets/core";

/** Built-in tactic keyword names. */
export const BUILTIN_TACTIC_NAMES = new Set(["assumption", "simp", "decide", "omega", "auto", "eauto"]);

/** Tactic combinator keywords (Phase 34). */
export const TACTIC_COMBINATORS = new Set(["try", "first", "repeat", "then", "seq", "all"]);

// ─── Strategy interpreter (Phase 38) ──────────────────────────────
// Evaluates strategy expressions by composing proof primitives.

const STRATEGY_PRIMITIVES = new Set(["conv", "ctx_search", "rewrite", "ground"]);

/** Check if a strategy expression is recursive (references itself via the strategies map). */
function isRecursiveStrategy(
  expr: AST.StrategyExpr,
  strategies: Map<string, AST.StrategyExpr>,
  visited: Set<string> = new Set(),
): boolean {
  switch (expr.kind) {
    case "ident": {
      if (STRATEGY_PRIMITIVES.has(expr.name)) return false;
      if (visited.has(expr.name)) return true;
      const ref = strategies.get(expr.name);
      if (!ref) return false;
      visited.add(expr.name);
      return isRecursiveStrategy(ref, strategies, visited);
    }
    case "first":
      return expr.alts.some(a => isRecursiveStrategy(a, strategies, visited));
    case "cong":
      return isRecursiveStrategy(expr.inner, strategies, visited);
    case "search":
      return false;
    case "eauto":
      return true; // eauto requires TS interpreter (hint-DB backtracking)
  }
}

/**
 * Run a strategy expression as an INet graph reduction.
 * Builds the strategy agent graph, injects judgment rules, reduces, reads result.
 * Falls back to the TS interpreter for recursive strategies (which can't be
 * statically unrolled into a finite graph).
 */
export function runStrategy(
  expr: AST.StrategyExpr,
  sctx: StrategyContext,
  strategies: Map<string, AST.StrategyExpr>,
  depth: number = 20,
  _extra?: {
    prove: AST.ProveDecl;
    caseArm: AST.ProveCase;
    provedCtx: ProvedContext;
    computeRules: ComputeRule[];
  },
): AST.ProveExpr | null {
  if (depth <= 0) return null;

  // If full context is available AND strategy is non-recursive, use INet graph-based reduction
  if (_extra && !isRecursiveStrategy(expr, strategies)) {
    const { prove, caseArm, provedCtx, computeRules } = _extra;
    // Build agentPorts for strategy agents + Tm* agents
    const agentPorts: AgentPortDefs = new Map();
    for (const decl of STRAT_AGENT_DECLS) {
      const portIndex = new Map<string, number>();
      decl.ports.forEach((p, i) => portIndex.set(p.name, i));
      agentPorts.set(decl.name, portIndex);
    }
    for (const decl of META_AGENT_DECLS) {
      if (!agentPorts.has(decl.name)) {
        const portIndex = new Map<string, number>();
        decl.ports.forEach((p, i) => portIndex.set(p.name, i));
        agentPorts.set(decl.name, portIndex);
      }
    }
    // Add CongWrap port defs
    agentPorts.set("CongWrap", new Map([["principal", 0], ["output", 1]]));
    // Add root/era port defs
    agentPorts.set("root", new Map([["principal", 0]]));
    agentPorts.set("era", new Map([["principal", 0]]));

    const allRules = collectStrategyRules(prove, caseArm, provedCtx, computeRules);
    return runStrategyGraph(expr, sctx.goal, strategies, allRules, agentPorts);
  }

  // Fallback: TypeScript interpreter (for recursive strategies or callers without full context)
  return runStrategyTS(expr, sctx, strategies, depth);
}

/** TypeScript-interpreted strategy fallback. */
function runStrategyTS(
  expr: AST.StrategyExpr,
  sctx: StrategyContext,
  strategies: Map<string, AST.StrategyExpr>,
  depth: number,
): AST.ProveExpr | null {
  if (depth <= 0) return null;

  switch (expr.kind) {
    case "ident": {
      switch (expr.name) {
        case "conv": return primConv(sctx);
        case "ctx_search": return primCtxSearch(sctx);
        case "rewrite": return primRewrite(sctx);
        case "ground": return primGround(sctx);
        default: {
          const ref = strategies.get(expr.name);
          if (ref) return runStrategyTS(ref, sctx, strategies, depth - 1);
          return null;
        }
      }
    }
    case "first": {
      for (const alt of expr.alts) {
        const result = runStrategyTS(alt, sctx, strategies, depth);
        if (result) return result;
      }
      return null;
    }
    case "cong": {
      const decomp = primCong(expr.ctor, sctx);
      if (!decomp) return null;
      const subSctx: StrategyContext = { ...sctx, goal: decomp.subGoal };
      const subProof = runStrategyTS(expr.inner, subSctx, strategies, depth - 1);
      if (!subProof) return null;
      return decomp.wrap(subProof);
    }
    case "search": {
      return primSearch(sctx, expr.depth);
    }
    case "eauto": {
      return primEauto(sctx, expr.depth);
    }
  }
}

// ─── Graph helpers ─────────────────────────────────────────────────

function mkAgent(name: string, portNames: string[]): AST.AgentDecl {
  return {
    kind: "agent",
    name,
    ports: portNames.map((p) => ({ name: p, variadic: false })),
  };
}

function mkNode(type: string, label: string | undefined, portCount: number): Node {
  const node: Node = { type, label, ports: [] };
  for (let i = 0; i < portCount; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
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
  hints?: Map<string, Set<string>>,
  instances?: InstanceDef[],
  strategies?: Map<string, AST.StrategyExpr>,
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveUserTacticExpr(
      caseArm.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies,
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
  hints?: Map<string, Set<string>>,
  instances?: InstanceDef[],
  strategies?: Map<string, AST.StrategyExpr>,
): AST.ProveExpr {
  if (expr.kind === "ident") {
    // Strategy-based resolution: user strategies override built-in defaults
    const allStrategies = strategies ?? new Map<string, AST.StrategyExpr>();
    const strategy = allStrategies.get(expr.name);
    if (strategy) {
      const sctx = makeStrategyContext(prove, caseArm, provedCtx, hints, instances);
      const result = runStrategy(strategy, sctx, allStrategies, 20, {
        prove, caseArm, provedCtx, computeRules,
      });
      if (result) return result;
    }
    // User-defined INet tactics
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
    const nv = resolveUserTacticExpr(expr.value, prove, caseArm, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies);
    const nb = resolveUserTacticExpr(expr.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies);
    if (nv !== expr.value || nb !== expr.body) return { kind: "let", name: expr.name, value: nv, body: nb };
    return expr;
  }
  if (expr.kind === "lambda") {
    const nb = resolveUserTacticExpr(expr.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies);
    if (nb !== expr.body) return { kind: "lambda", param: expr.param, paramType: expr.paramType, body: nb };
    return expr;
  }
  if (expr.kind === "match") {
    let ch = false;
    const nc = expr.cases.map((c) => {
      const r = resolveUserTacticExpr(c.body, prove, caseArm, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies);
      if (r !== c.body) ch = true;
      return { ...c, body: r };
    });
    return ch ? { kind: "match", scrutinee: expr.scrutinee, cases: nc } : expr;
  }
  if (expr.kind === "call") {
    // ─── Tactic combinators (Phase 34) ────────────────────────────
    const resolve = (e: AST.ProveExpr) =>
      resolveUserTacticExpr(e, prove, caseArm, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies);

    // try(t) — attempt t; if it doesn't resolve, return hole (no error)
    if (expr.name === "try" && expr.args.length === 1) {
      const result = resolve(expr.args[0]);
      return result !== expr.args[0] ? result : { kind: "hole" };
    }

    // first(t1, t2, ...) — try each alternative until one resolves
    if (expr.name === "first" && expr.args.length >= 1) {
      for (const arg of expr.args) {
        const result = resolve(arg);
        if (result !== arg) return result;
      }
      return expr; // none resolved — leave for error reporting
    }

    // repeat(t) — iterate t until no change (max 100 iterations)
    if (expr.name === "repeat" && expr.args.length === 1) {
      let current: AST.ProveExpr = expr.args[0];
      for (let i = 0; i < 100; i++) {
        const next = resolve(current);
        if (next === current) break;
        current = next;
      }
      return current !== expr.args[0] ? current : expr;
    }

    // then(t1, t2) / seq(t1, t2) — resolve t1, then resolve t2 on result
    if ((expr.name === "then" || expr.name === "seq") && expr.args.length === 2) {
      const first = resolve(expr.args[0]);
      return resolve(first !== expr.args[0] ? first : expr.args[1]);
    }

    // all(t) — apply t recursively to all sub-expressions
    if (expr.name === "all" && expr.args.length === 1) {
      const tac = expr.args[0];
      // First try resolving the tactic itself
      const top = resolve(tac);
      if (top !== tac) return top;
      // Otherwise return unchanged
      return expr;
    }

    // ─── Generic call: resolve arguments ──────────────────────────
    let ch = false;
    const na = expr.args.map((a) => {
      const r = resolve(a);
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
