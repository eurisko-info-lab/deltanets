// ═══════════════════════════════════════════════════════════════════
// Quotation & Reflection — Phase 17
// Represents ProveExpr as INet agents; provides quote/unquote bridge.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, RuleDef } from "./evaluator.ts";
import { evalAgent } from "./eval-system.ts";

// ─── Term-encoding agent names ─────────────────────────────────────

/** Agent names for the quoted term representation. */
export const TM_VAR = "TmVar";
export const TM_APP = "TmApp";
export const TM_PI = "TmPi";
export const TM_SIGMA = "TmSigma";
export const TM_LAM = "TmLam";
export const TM_NIL = "TmNil";
export const TM_CONS = "TmCons";

/** Agent names for proof goals. */
export const Q_GOAL = "QGoal";
export const CTX_NIL = "CtxNil";
export const CTX_CONS = "CtxCons";

/** All quotation agent names. */
export const QUOTE_AGENTS = [
  TM_VAR, TM_APP, TM_PI, TM_SIGMA, TM_LAM, TM_NIL, TM_CONS,
  Q_GOAL, CTX_NIL, CTX_CONS,
] as const;

// ─── Agent definitions ─────────────────────────────────────────────

function mkAgent(name: string, portNames: string[]): AST.AgentDecl {
  return {
    kind: "agent",
    name,
    ports: portNames.map((p) => ({ name: p, variadic: false })),
  };
}

const QUOTE_AGENT_DECLS: AST.AgentDecl[] = [
  // Term constructors
  mkAgent(TM_VAR,   ["principal"]),                        // label carries ident name
  mkAgent(TM_APP,   ["principal", "args"]),                // label carries fn name
  mkAgent(TM_PI,    ["principal", "domain", "codomain"]),
  mkAgent(TM_SIGMA, ["principal", "domain", "codomain"]),
  mkAgent(TM_LAM,   ["principal", "paramType", "body"]),
  mkAgent(TM_NIL,   ["principal"]),
  mkAgent(TM_CONS,  ["principal", "head", "tail"]),
  // Goal & context
  mkAgent(Q_GOAL,   ["principal", "prop", "ctx"]),
  mkAgent(CTX_NIL,  ["principal"]),
  mkAgent(CTX_CONS, ["principal", "name_term", "type_term", "tail"]),
];

// Annihilation rules for same-type Tm* agents (structural equality)
function annihilateRule(agentName: string): RuleDef {
  return { agentA: agentName, agentB: agentName, action: { kind: "builtin", name: "annihilate" } };
}

const QUOTE_RULES: RuleDef[] = QUOTE_AGENTS.map(annihilateRule);

// ─── Registration ──────────────────────────────────────────────────

/**
 * Register quotation agents and rules into a system's agent/rule maps.
 * Called when a system uses `open "Quote"` or contains `quote(...)`.
 */
export function registerQuotationAgents(
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
): void {
  for (const decl of QUOTE_AGENT_DECLS) {
    if (!agents.has(decl.name)) {
      agents.set(decl.name, evalAgent(decl));
    }
  }
  for (const rule of QUOTE_RULES) {
    rules.push(rule);
  }
}

// ─── Quote: ProveExpr → INet statements ────────────────────────────

export type QuoteResult = {
  stmts: AST.RuleStmt[];
  root: AST.PortRef;
};

/**
 * Convert a ProveExpr into INet agent instantiation statements.
 * Returns the root port ref (principal of the top-level Tm* agent).
 * The `counter` is mutated to generate unique variable names.
 */
export function quoteExpr(
  expr: AST.ProveExpr,
  counter: { value: number },
): QuoteResult {
  const stmts: AST.RuleStmt[] = [];

  function emit(agentType: string, label?: string): string {
    const varName = `_q${counter.value++}`;
    const stmt: AST.LetStmt = { kind: "let", varName, agentType };
    if (label) stmt.label = label;
    stmts.push(stmt);
    return varName;
  }

  function wire(a: AST.PortRef, b: AST.PortRef): void {
    stmts.push({ kind: "wire", portA: a, portB: b });
  }

  function quoteRec(e: AST.ProveExpr): AST.PortRef {
    switch (e.kind) {
      case "ident": {
        const v = emit(TM_VAR, e.name);
        return { node: v, port: "principal" };
      }
      case "call": {
        // Quote function name as TmApp, args as TmCons/TmNil list
        const v = emit(TM_APP, e.name);
        const argsPort = quoteList(e.args);
        wire({ node: v, port: "args" }, argsPort);
        return { node: v, port: "principal" };
      }
      case "pi": {
        const v = emit(TM_PI);
        wire({ node: v, port: "domain" }, quoteRec(e.domain));
        wire({ node: v, port: "codomain" }, quoteRec(e.codomain));
        return { node: v, port: "principal" };
      }
      case "sigma": {
        const v = emit(TM_SIGMA);
        wire({ node: v, port: "domain" }, quoteRec(e.domain));
        wire({ node: v, port: "codomain" }, quoteRec(e.codomain));
        return { node: v, port: "principal" };
      }
      case "lambda": {
        const v = emit(TM_LAM);
        wire({ node: v, port: "paramType" }, quoteRec(e.paramType));
        wire({ node: v, port: "body" }, quoteRec(e.body));
        return { node: v, port: "principal" };
      }
      case "hole": {
        // Quote a hole as TmVar with special label
        const v = emit(TM_VAR, "?");
        return { node: v, port: "principal" };
      }
      case "metavar": {
        const v = emit(TM_VAR, `?${e.id}`);
        return { node: v, port: "principal" };
      }
      case "let": {
        // Encode let as a call: TmApp("let", [name, value, body])
        const v = emit(TM_APP, "let");
        const nameRef = quoteRec({ kind: "ident", name: e.name });
        const valRef = quoteRec(e.value);
        const bodyRef = quoteRec(e.body);
        const argsPort = buildList([nameRef, valRef, bodyRef]);
        wire({ node: v, port: "args" }, argsPort);
        return { node: v, port: "principal" };
      }
      case "match": {
        // Encode match as TmApp("match", [scrutinee, ...cases])
        const v = emit(TM_APP, "match");
        const items: AST.PortRef[] = [quoteRec({ kind: "ident", name: e.scrutinee })];
        for (const c of e.cases) {
          items.push(quoteRec(c.body));
        }
        wire({ node: v, port: "args" }, buildList(items));
        return { node: v, port: "principal" };
      }
    }
  }

  function quoteList(exprs: AST.ProveExpr[]): AST.PortRef {
    const items = exprs.map(quoteRec);
    return buildList(items);
  }

  function buildList(items: AST.PortRef[]): AST.PortRef {
    let tail: AST.PortRef = { node: emit(TM_NIL), port: "principal" };
    for (let i = items.length - 1; i >= 0; i--) {
      const cons = emit(TM_CONS);
      wire({ node: cons, port: "head" }, items[i]);
      wire({ node: cons, port: "tail" }, tail);
      tail = { node: cons, port: "principal" };
    }
    return tail;
  }

  const root = quoteRec(expr);
  return { stmts, root };
}

// ─── Unquote: reconstruct ProveExpr from Tm* agent labels ─────────

/**
 * Reconstruct a ProveExpr from a tree described by quoteExpr statements.
 * This is a compile-time operation — reads the statements back.
 */
export function unquoteStatements(stmts: AST.RuleStmt[]): AST.ProveExpr | null {
  // Build a map of variable → agent info
  const agents = new Map<string, { type: string; label?: string }>();
  const wires = new Map<string, Map<string, AST.PortRef>>(); // node → port → target

  for (const s of stmts) {
    if (s.kind === "let") {
      agents.set(s.varName, { type: s.agentType, label: s.label });
    } else if (s.kind === "wire") {
      setWire(wires, s.portA.node, s.portA.port, s.portB);
      setWire(wires, s.portB.node, s.portB.port, s.portA);
    }
  }

  // Find the root: the agent whose principal port isn't wired to another Tm* port
  const rootVar = findRoot(agents, wires);
  if (!rootVar) return null;

  return readNode(rootVar, agents, wires);
}

function setWire(
  wires: Map<string, Map<string, AST.PortRef>>,
  node: string,
  port: string,
  target: AST.PortRef,
): void {
  if (!wires.has(node)) wires.set(node, new Map());
  wires.get(node)!.set(port, target);
}

function findRoot(
  agents: Map<string, { type: string; label?: string }>,
  wires: Map<string, Map<string, AST.PortRef>>,
): string | null {
  // The root is the first TM agent whose principal port is not targeted by another wire
  const targeted = new Set<string>();
  for (const [, portMap] of wires) {
    for (const [, target] of portMap) {
      if (target.port === "principal") targeted.add(target.node);
    }
  }
  for (const [varName, info] of agents) {
    if (info.type.startsWith("Tm") && !targeted.has(varName)) return varName;
  }
  // Fallback: first Tm agent
  for (const [varName, info] of agents) {
    if (info.type.startsWith("Tm")) return varName;
  }
  return null;
}

function readNode(
  varName: string,
  agents: Map<string, { type: string; label?: string }>,
  wires: Map<string, Map<string, AST.PortRef>>,
): AST.ProveExpr {
  const info = agents.get(varName);
  if (!info) return { kind: "ident", name: "?" };

  const portMap = wires.get(varName) ?? new Map<string, AST.PortRef>();

  function follow(portName: string): AST.ProveExpr {
    const target = portMap.get(portName);
    if (!target) return { kind: "ident", name: "?" };
    return readNode(target.node, agents, wires);
  }

  function followList(portName: string): AST.ProveExpr[] {
    const target = portMap.get(portName);
    if (!target) return [];
    return readList(target.node, agents, wires);
  }

  switch (info.type) {
    case TM_VAR:
      return { kind: "ident", name: info.label ?? "?" };
    case TM_APP: {
      const args = followList("args");
      if (info.label === "let" && args.length === 3) {
        const nameExpr = args[0];
        return {
          kind: "let",
          name: nameExpr.kind === "ident" ? nameExpr.name : "?",
          value: args[1],
          body: args[2],
        };
      }
      return { kind: "call", name: info.label ?? "?", args };
    }
    case TM_PI:
      return { kind: "pi", param: "_", domain: follow("domain"), codomain: follow("codomain") };
    case TM_SIGMA:
      return { kind: "sigma", param: "_", domain: follow("domain"), codomain: follow("codomain") };
    case TM_LAM:
      return { kind: "lambda", param: "_", paramType: follow("paramType"), body: follow("body") };
    default:
      return { kind: "ident", name: "?" };
  }
}

function readList(
  varName: string,
  agents: Map<string, { type: string; label?: string }>,
  wires: Map<string, Map<string, AST.PortRef>>,
): AST.ProveExpr[] {
  const info = agents.get(varName);
  if (!info) return [];
  if (info.type === TM_NIL) return [];
  if (info.type === TM_CONS) {
    const portMap = wires.get(varName) ?? new Map<string, AST.PortRef>();
    const headTarget = portMap.get("head");
    const tailTarget = portMap.get("tail");
    const head = headTarget ? readNode(headTarget.node, agents, wires) : { kind: "ident" as const, name: "?" };
    const tail = tailTarget ? readList(tailTarget.node, agents, wires) : [];
    return [head, ...tail];
  }
  return [];
}

// ─── Goal construction ─────────────────────────────────────────────

/**
 * Build INet statements representing a proof goal.
 * The goal has a proposition (type to prove) and a context (available hypotheses).
 */
export function buildGoalStatements(
  proposition: AST.ProveExpr,
  context: Array<{ name: string; type: AST.ProveExpr }>,
  counter: { value: number },
): QuoteResult {
  const stmts: AST.RuleStmt[] = [];

  function emit(agentType: string, label?: string): string {
    const varName = `_q${counter.value++}`;
    const stmt: AST.LetStmt = { kind: "let", varName, agentType };
    if (label) stmt.label = label;
    stmts.push(stmt);
    return varName;
  }

  function wire(a: AST.PortRef, b: AST.PortRef): void {
    stmts.push({ kind: "wire", portA: a, portB: b });
  }

  // Quote the proposition
  const propResult = quoteExpr(proposition, counter);
  stmts.push(...propResult.stmts);

  // Build context list
  let ctxPort: AST.PortRef = { node: emit(CTX_NIL), port: "principal" };
  for (let i = context.length - 1; i >= 0; i--) {
    const entry = context[i];
    const nameResult = quoteExpr({ kind: "ident", name: entry.name }, counter);
    stmts.push(...nameResult.stmts);
    const typeResult = quoteExpr(entry.type, counter);
    stmts.push(...typeResult.stmts);

    const cons = emit(CTX_CONS);
    wire({ node: cons, port: "name_term" }, nameResult.root);
    wire({ node: cons, port: "type_term" }, typeResult.root);
    wire({ node: cons, port: "tail" }, ctxPort);
    ctxPort = { node: cons, port: "principal" };
  }

  // Build goal agent
  const goal = emit(Q_GOAL);
  wire({ node: goal, port: "prop" }, propResult.root);
  wire({ node: goal, port: "ctx" }, ctxPort);

  return { stmts, root: { node: goal, port: "principal" } };
}

// ─── Utilities ─────────────────────────────────────────────────────

/** Check if a ProveExpr contains a quote(...) call. */
export function containsQuote(expr: AST.ProveExpr): boolean {
  if (expr.kind === "call" && expr.name === "quote") return true;
  if (expr.kind === "call") return expr.args.some(containsQuote);
  if (expr.kind === "let") return containsQuote(expr.value) || containsQuote(expr.body);
  if (expr.kind === "pi" || expr.kind === "sigma") return containsQuote(expr.domain) || containsQuote(expr.codomain);
  if (expr.kind === "lambda") return containsQuote(expr.paramType) || containsQuote(expr.body);
  if (expr.kind === "match") return expr.cases.some((c) => containsQuote(c.body));
  return false;
}

/** Check if a ProveExpr contains an unquote(...) call. */
export function containsUnquote(expr: AST.ProveExpr): boolean {
  if (expr.kind === "call" && expr.name === "unquote") return true;
  if (expr.kind === "call") return expr.args.some(containsUnquote);
  if (expr.kind === "let") return containsUnquote(expr.value) || containsUnquote(expr.body);
  if (expr.kind === "pi" || expr.kind === "sigma") return containsUnquote(expr.domain) || containsUnquote(expr.codomain);
  if (expr.kind === "lambda") return containsUnquote(expr.paramType) || containsUnquote(expr.body);
  if (expr.kind === "match") return expr.cases.some((c) => containsUnquote(c.body));
  return false;
}
