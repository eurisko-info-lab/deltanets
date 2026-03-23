// Tests for meta-agents (Phase 18 + Phase 20).
// Verifies MatchGoal, NormalizeTerm, ApplyRule, CtxSearch, EqCheck agents,
// graph read/write, and integration with `open "Meta"`.

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  META_AGENTS, META_MATCH_GOAL, META_APPLY_RULE, META_NORMALIZE,
  META_CTX_SEARCH, META_EQ_CHECK,
  META_AGENT_DECLS,
  registerMetaAgents,
  readTermFromGraph, writeTermToGraph, collectTermTree,
  createNormalizeHandler, createApplyRuleHandler,
  createCtxSearchHandler, createEqCheckHandler,
  exprEqual, searchProofContext,
  TM_VAR, TM_APP, TM_PI, TM_NIL, TM_CONS,
} from "@deltanets/lang";
import { link } from "@deltanets/core";
import type { Node, Graph, AgentPortDefs } from "@deltanets/core";
import { NATEQ_SYSTEM, compileAndAssert, collectRules, collectAgentPorts, reduceAll } from "./helpers.ts";
import type { ProveExpr } from "../lang/core/types.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// Helper constructors
const ident = (name: string): ProveExpr => ({ kind: "ident", name });
const call = (name: string, ...args: ProveExpr[]): ProveExpr => ({ kind: "call", name, args });

// Helper: create a node with self-looped ports
function mkNode(type: string, label: string, portCount: number): Node {
  const node: Node = { type, label, ports: [] };
  for (let i = 0; i < portCount; i++) {
    node.ports[i] = { node, port: i };
  }
  return node;
}

// ─── META_AGENTS constant ──────────────────────────────────────────

Deno.test("meta-agents: META_AGENTS contains 5 agents", () => {
  assertEquals(META_AGENTS.length, 5);
  assertEquals(META_AGENTS[0], META_MATCH_GOAL);
  assertEquals(META_AGENTS[1], META_APPLY_RULE);
  assertEquals(META_AGENTS[2], META_NORMALIZE);
  assertEquals(META_AGENTS[3], META_CTX_SEARCH);
  assertEquals(META_AGENTS[4], META_EQ_CHECK);
});

Deno.test("meta-agents: META_AGENT_DECLS matches META_AGENTS", () => {
  const names = META_AGENT_DECLS.map((d) => d.name);
  for (const m of META_AGENTS) {
    assertEquals(names.includes(m), true, `${m} not in META_AGENT_DECLS`);
  }
});

// ─── readTermFromGraph ─────────────────────────────────────────────

Deno.test("meta-agents: readTermFromGraph — TmVar", () => {
  const node = mkNode(TM_VAR, "x", 1);
  const expr = readTermFromGraph(node);
  assertEquals(expr, { kind: "ident", name: "x" });
});

Deno.test("meta-agents: readTermFromGraph — TmApp with args", () => {
  const app = mkNode(TM_APP, "Succ", 2);
  const cons = mkNode(TM_CONS, TM_CONS, 3);
  const headVar = mkNode(TM_VAR, "n", 1);
  const nil = mkNode(TM_NIL, TM_NIL, 1);

  link({ node: app, port: 1 }, { node: cons, port: 0 });
  link({ node: cons, port: 1 }, { node: headVar, port: 0 });
  link({ node: cons, port: 2 }, { node: nil, port: 0 });

  const expr = readTermFromGraph(app);
  assertEquals(expr.kind, "call");
  if (expr.kind === "call") {
    assertEquals(expr.name, "Succ");
    assertEquals(expr.args.length, 1);
    assertEquals(expr.args[0], { kind: "ident", name: "n" });
  }
});

Deno.test("meta-agents: readTermFromGraph — TmPi", () => {
  const node = mkNode(TM_PI, TM_PI, 3);
  const dom = mkNode(TM_VAR, "Nat", 1);
  const cod = mkNode(TM_VAR, "Bool", 1);
  link({ node: node, port: 1 }, { node: dom, port: 0 });
  link({ node: node, port: 2 }, { node: cod, port: 0 });

  const expr = readTermFromGraph(node);
  assertEquals(expr.kind, "pi");
  if (expr.kind === "pi") {
    assertEquals(expr.domain, { kind: "ident", name: "Nat" });
    assertEquals(expr.codomain, { kind: "ident", name: "Bool" });
  }
});

// ─── writeTermToGraph ──────────────────────────────────────────────

Deno.test("meta-agents: writeTermToGraph — ident", () => {
  const graph: Graph = [];
  const root = writeTermToGraph(ident("x"), graph);
  assertEquals(root.type, TM_VAR);
  assertEquals(root.label, "x");
  assertEquals(graph.length, 1);
});

Deno.test("meta-agents: writeTermToGraph — call", () => {
  const graph: Graph = [];
  const root = writeTermToGraph(call("Succ", ident("n")), graph);
  assertEquals(root.type, TM_APP);
  assertEquals(root.label, "Succ");
  // app(principal, args) — args is a TmCons
  assertEquals(root.ports[1].node.type, TM_CONS);
  // Graph should have: TmApp, TmCons, TmVar(n), TmNil
  assertEquals(graph.length, 4);
});

Deno.test("meta-agents: writeTermToGraph roundtrip", () => {
  const expr: ProveExpr = call("add", ident("x"), ident("y"));
  const graph: Graph = [];
  const root = writeTermToGraph(expr, graph);
  const readBack = readTermFromGraph(root);
  assertEquals(readBack.kind, "call");
  if (readBack.kind === "call") {
    assertEquals(readBack.name, "add");
    assertEquals(readBack.args.length, 2);
    assertEquals(readBack.args[0], { kind: "ident", name: "x" });
    assertEquals(readBack.args[1], { kind: "ident", name: "y" });
  }
});

// ─── collectTermTree ───────────────────────────────────────────────

Deno.test("meta-agents: collectTermTree collects all Tm nodes", () => {
  const graph: Graph = [];
  const root = writeTermToGraph(call("f", ident("a"), ident("b")), graph);
  const collected = collectTermTree(root);
  assertEquals(collected.size, graph.length);
});

// ─── open "Meta" registration ──────────────────────────────────────

Deno.test("meta-agents: open Meta registers agents", () => {
  const result = compile(`
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T")!;
  for (const m of META_AGENTS) {
    assertEquals(sys.agents.has(m), true, `${m} not registered`);
  }
});

Deno.test("meta-agents: open Meta registers interaction rules for MatchGoal", () => {
  const result = compile(`
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T")!;
  const matchRules = sys.rules.filter(
    (r) => r.agentA === META_MATCH_GOAL || r.agentB === META_MATCH_GOAL,
  );
  // Should have rules for TmVar, TmApp, TmPi, TmSigma, TmLam, TmNil, TmCons
  assertEquals(matchRules.length >= 7, true, `only ${matchRules.length} MatchGoal rules`);
  for (const r of matchRules) {
    assertEquals(r.action.kind, "meta");
  }
});

Deno.test("meta-agents: open Meta registers NormalizeTerm rules", () => {
  const result = compile(`
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T")!;
  const normRules = sys.rules.filter(
    (r) => r.agentA === META_NORMALIZE || r.agentB === META_NORMALIZE,
  );
  assertEquals(normRules.length >= 5, true, `only ${normRules.length} NormalizeTerm rules`);
});

Deno.test("meta-agents: open Meta registers ApplyRule rules", () => {
  const result = compile(`
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T")!;
  const applyRules = sys.rules.filter(
    (r) => r.agentA === META_APPLY_RULE || r.agentB === META_APPLY_RULE,
  );
  assertEquals(applyRules.length >= 2, true, `only ${applyRules.length} ApplyRule rules`);
});

// ─── MatchGoal graph-level reduction ───────────────────────────────

Deno.test("meta-agents: MatchGoal routes TmVar to on_var", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  // Build: MatchGoal -- TmVar("x")
  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  const mg = mkNode(META_MATCH_GOAL, META_MATCH_GOAL, 7);
  graph.push(mg);

  const tmVar = mkNode(TM_VAR, "x", 1);
  graph.push(tmVar);

  // Wire MatchGoal's principal <-> TmVar's principal (they interact)
  link({ node: mg, port: 0 }, { node: tmVar, port: 0 });

  // Wire root to mg's on_var port (branch 1)
  link({ node: root, port: 0 }, { node: mg, port: 1 });

  // Create erasers for the other branch ports (on_app through on_other)
  for (let i = 2; i <= 6; i++) {
    const era = mkNode("era", "era", 1);
    graph.push(era);
    link({ node: era, port: 0 }, { node: mg, port: i });
  }

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  // After reduction, root should be connected to a TmVar clone
  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, TM_VAR);
  assertEquals(rootTarget.label, "x");
});

Deno.test("meta-agents: MatchGoal routes TmApp to on_app", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  const mg = mkNode(META_MATCH_GOAL, META_MATCH_GOAL, 7);
  graph.push(mg);

  const tmApp = mkNode(TM_APP, "f", 2);
  graph.push(tmApp);
  const tmNil = mkNode(TM_NIL, TM_NIL, 1);
  graph.push(tmNil);
  link({ node: tmApp, port: 1 }, { node: tmNil, port: 0 });

  link({ node: mg, port: 0 }, { node: tmApp, port: 0 });

  // on_var → eraser
  const eraVar = mkNode("era", "era", 1);
  graph.push(eraVar);
  link({ node: eraVar, port: 0 }, { node: mg, port: 1 });

  // on_app → root
  link({ node: root, port: 0 }, { node: mg, port: 2 });

  // on_pi, on_sigma, on_lam, on_other → erasers
  for (let i = 3; i <= 6; i++) {
    const era = mkNode("era", "era", 1);
    graph.push(era);
    link({ node: era, port: 0 }, { node: mg, port: i });
  }

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  // After reduction, root should be connected to a TmApp clone
  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, TM_APP);
  assertEquals(rootTarget.label, "f");
});

// ─── NormalizeTerm graph-level reduction ───────────────────────────

Deno.test("meta-agents: NormalizeTerm normalizes add(Zero, x) → x", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  // Build NormalizeTerm agent
  const norm = mkNode(META_NORMALIZE, META_NORMALIZE, 2);
  graph.push(norm);

  // Build quoted term: add(Zero, x)
  const addExpr: ProveExpr = call("add", ident("Zero"), ident("x"));
  const tmRoot = writeTermToGraph(addExpr, graph);

  // Wire: NormalizeTerm.principal <-> tmRoot.principal
  link({ node: norm, port: 0 }, { node: tmRoot, port: 0 });
  // Wire: root <-> NormalizeTerm.result
  link({ node: root, port: 0 }, { node: norm, port: 1 });

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  // After reduction, root should be connected to normalized term
  // add(Zero, x) normalizes to x
  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, TM_VAR);
  assertEquals(rootTarget.label, "x");
});

Deno.test("meta-agents: NormalizeTerm normalizes add(Succ(Zero), y)", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  const norm = mkNode(META_NORMALIZE, META_NORMALIZE, 2);
  graph.push(norm);

  // add(Succ(Zero), y) should normalize to Succ(add(Zero, y)) = Succ(y)
  const addExpr: ProveExpr = call("add", call("Succ", ident("Zero")), ident("y"));
  const tmRoot = writeTermToGraph(addExpr, graph);

  link({ node: norm, port: 0 }, { node: tmRoot, port: 0 });
  link({ node: root, port: 0 }, { node: norm, port: 1 });

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  // Result should be Succ(y)
  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, TM_APP);
  assertEquals(rootTarget.label, "Succ");
  // Succ has args list: Cons(y, Nil)
  const argsList = rootTarget.ports[1].node;
  assertEquals(argsList.type, TM_CONS);
  const head = argsList.ports[1].node;
  assertEquals(head.type, TM_VAR);
  assertEquals(head.label, "y");
});

// ─── ApplyRule graph-level reduction ───────────────────────────────

Deno.test("meta-agents: ApplyRule creates agent from TmVar name", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  const applyRule = mkNode(META_APPLY_RULE, META_APPLY_RULE, 2);
  graph.push(applyRule);

  // TmVar("Zero") — should create a Zero agent
  const tmVar = mkNode(TM_VAR, "Zero", 1);
  graph.push(tmVar);

  link({ node: applyRule, port: 0 }, { node: tmVar, port: 0 });
  link({ node: root, port: 0 }, { node: applyRule, port: 1 });

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  // After reduction, root should point to a Zero agent
  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, "Zero");
});

Deno.test("meta-agents: ApplyRule creates agent from TmApp name", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  const applyRule = mkNode(META_APPLY_RULE, META_APPLY_RULE, 2);
  graph.push(applyRule);

  // TmApp("Succ") with args
  const tmApp = mkNode(TM_APP, "Succ", 2);
  graph.push(tmApp);
  const tmNil = mkNode(TM_NIL, TM_NIL, 1);
  graph.push(tmNil);
  link({ node: tmApp, port: 1 }, { node: tmNil, port: 0 });

  link({ node: applyRule, port: 0 }, { node: tmApp, port: 0 });
  link({ node: root, port: 0 }, { node: applyRule, port: 1 });

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, "Succ");
});

Deno.test("meta-agents: ApplyRule erases for unknown agent", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const rules = collectRules(result);
  const agentPorts = collectAgentPorts(result);

  const graph: Graph = [];
  const root = mkNode("root", "root", 1);
  graph.push(root);

  const applyRule = mkNode(META_APPLY_RULE, META_APPLY_RULE, 2);
  graph.push(applyRule);

  // TmVar("Nonexistent") — unknown agent, should erase
  const tmVar = mkNode(TM_VAR, "Nonexistent", 1);
  graph.push(tmVar);

  link({ node: applyRule, port: 0 }, { node: tmVar, port: 0 });
  link({ node: root, port: 0 }, { node: applyRule, port: 1 });

  const steps = reduceAll(graph, rules, agentPorts);
  assertEquals(steps > 0, true, "should reduce");

  // Root should point to an eraser
  const rootTarget = root.ports[0].node;
  assertEquals(rootTarget.type, "era");
});

// ─── Meta action type in rules ─────────────────────────────────────

Deno.test("meta-agents: meta rules have kind 'meta'", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  const metaRules = sys.rules.filter((r) => r.action.kind === "meta");
  assertEquals(metaRules.length > 0, true, "should have meta rules");
  for (const r of metaRules) {
    assertEquals(typeof (r.action as { handler: unknown }).handler, "function");
  }
});

// ─── Integration: prove blocks using meta-agents ───────────────────

Deno.test("meta-agents: prove block with quote + Meta system compiles", () => {
  const result = compile(`
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"

  prove add_comm(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(add_comm(k))
  }
}
`);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("meta-agents: MatchGoal port structure is correct", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  const mg = sys.agents.get(META_MATCH_GOAL)!;
  assertEquals(mg.ports.length, 7);
  assertEquals(mg.ports[0].name, "principal");
  assertEquals(mg.ports[1].name, "on_var");
  assertEquals(mg.ports[2].name, "on_app");
  assertEquals(mg.ports[3].name, "on_pi");
  assertEquals(mg.ports[4].name, "on_sigma");
  assertEquals(mg.ports[5].name, "on_lam");
  assertEquals(mg.ports[6].name, "on_other");
});

Deno.test("meta-agents: NormalizeTerm port structure is correct", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  const nt = sys.agents.get(META_NORMALIZE)!;
  assertEquals(nt.ports.length, 2);
  assertEquals(nt.ports[0].name, "principal");
  assertEquals(nt.ports[1].name, "result");
});

Deno.test("meta-agents: ApplyRule port structure is correct", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  const ar = sys.agents.get(META_APPLY_RULE)!;
  assertEquals(ar.ports.length, 2);
  assertEquals(ar.ports[0].name, "principal");
  assertEquals(ar.ports[1].name, "result");
});

// ═══════════════════════════════════════════════════════════════════
// Phase 20 — CtxSearch, EqCheck, exprEqual, searchProofContext
// ═══════════════════════════════════════════════════════════════════

// ─── Constants ─────────────────────────────────────────────────────

Deno.test("meta-agents: META_CTX_SEARCH is 'CtxSearch'", () => {
  assertEquals(META_CTX_SEARCH, "CtxSearch");
});

Deno.test("meta-agents: META_EQ_CHECK is 'EqCheck'", () => {
  assertEquals(META_EQ_CHECK, "EqCheck");
});

Deno.test("meta-agents: META_AGENT_DECLS includes CtxSearch", () => {
  const decl = META_AGENT_DECLS.find((d) => d.name === META_CTX_SEARCH);
  assertNotEquals(decl, undefined);
  assertEquals(decl!.ports.length, 2);
  assertEquals(decl!.ports[0].name, "principal");
  assertEquals(decl!.ports[1].name, "result");
});

Deno.test("meta-agents: META_AGENT_DECLS includes EqCheck", () => {
  const decl = META_AGENT_DECLS.find((d) => d.name === META_EQ_CHECK);
  assertNotEquals(decl, undefined);
  assertEquals(decl!.ports.length, 4);
  assertEquals(decl!.ports[0].name, "principal");
  assertEquals(decl!.ports[1].name, "second");
  assertEquals(decl!.ports[2].name, "on_eq");
  assertEquals(decl!.ports[3].name, "on_neq");
});

// ─── exprEqual ─────────────────────────────────────────────────────

Deno.test("meta-agents: exprEqual — identical idents", () => {
  assertEquals(exprEqual({ kind: "ident", name: "x" }, { kind: "ident", name: "x" }), true);
});

Deno.test("meta-agents: exprEqual — different idents", () => {
  assertEquals(exprEqual({ kind: "ident", name: "x" }, { kind: "ident", name: "y" }), false);
});

Deno.test("meta-agents: exprEqual — identical calls", () => {
  const a = { kind: "call" as const, name: "Succ", args: [{ kind: "ident" as const, name: "n" }] };
  const b = { kind: "call" as const, name: "Succ", args: [{ kind: "ident" as const, name: "n" }] };
  assertEquals(exprEqual(a, b), true);
});

Deno.test("meta-agents: exprEqual — different calls", () => {
  const a = { kind: "call" as const, name: "Succ", args: [{ kind: "ident" as const, name: "n" }] };
  const b = { kind: "call" as const, name: "Succ", args: [{ kind: "ident" as const, name: "m" }] };
  assertEquals(exprEqual(a, b), false);
});

Deno.test("meta-agents: exprEqual — pi with α-renaming", () => {
  const a: ProveExpr = { kind: "pi", param: "x", domain: { kind: "ident", name: "Nat" }, codomain: { kind: "ident", name: "x" } };
  const b: ProveExpr = { kind: "pi", param: "y", domain: { kind: "ident", name: "Nat" }, codomain: { kind: "ident", name: "y" } };
  assertEquals(exprEqual(a, b), true);
});

// ─── EqCheck handler ───────────────────────────────────────────────

Deno.test("meta-agents: EqCheck on equal terms produces TmVar(refl)", () => {
  const graph: Node[] = [];
  const eqAgent = mkNode(META_EQ_CHECK, META_EQ_CHECK, 4);
  const termA = mkNode(TM_VAR, "x", 1);
  const termB = mkNode(TM_VAR, "x", 1);
  const resultEq = mkNode("root", "root", 1);
  const resultNeq = mkNode("root", "root", 1);
  graph.push(eqAgent, termA, termB, resultEq, resultNeq);

  // Wire: principal ↔ termA, second ↔ termB, on_eq ↔ resultEq, on_neq ↔ resultNeq
  link({ node: eqAgent, port: 0 }, { node: termA, port: 0 });
  link({ node: eqAgent, port: 1 }, { node: termB, port: 0 });
  link({ node: eqAgent, port: 2 }, { node: resultEq, port: 0 });
  link({ node: eqAgent, port: 3 }, { node: resultNeq, port: 0 });

  const handler = createEqCheckHandler();
  const agentPorts: AgentPortDefs = new Map();
  handler(eqAgent, termA, graph, agentPorts);

  // on_eq should have TmVar("refl")
  const eqNode = resultEq.ports[0].node;
  assertEquals(eqNode.type, TM_VAR);
  assertEquals(eqNode.label, "refl");

  // on_neq should have eraser
  const neqNode = resultNeq.ports[0].node;
  assertEquals(neqNode.type, "era");
});

Deno.test("meta-agents: EqCheck on unequal terms branches to on_neq", () => {
  const graph: Node[] = [];
  const eqAgent = mkNode(META_EQ_CHECK, META_EQ_CHECK, 4);
  const termA = mkNode(TM_VAR, "x", 1);
  const termB = mkNode(TM_VAR, "y", 1);
  const resultEq = mkNode("root", "root", 1);
  const resultNeq = mkNode("root", "root", 1);
  graph.push(eqAgent, termA, termB, resultEq, resultNeq);

  link({ node: eqAgent, port: 0 }, { node: termA, port: 0 });
  link({ node: eqAgent, port: 1 }, { node: termB, port: 0 });
  link({ node: eqAgent, port: 2 }, { node: resultEq, port: 0 });
  link({ node: eqAgent, port: 3 }, { node: resultNeq, port: 0 });

  const handler = createEqCheckHandler();
  const agentPorts: AgentPortDefs = new Map();
  handler(eqAgent, termA, graph, agentPorts);

  // on_neq should have TmVar("x") (original goal)
  const neqNode = resultNeq.ports[0].node;
  assertEquals(neqNode.type, TM_VAR);
  assertEquals(neqNode.label, "x");

  // on_eq should have eraser
  const eqNode = resultEq.ports[0].node;
  assertEquals(eqNode.type, "era");
});

// ─── registerMetaAgents includes EqCheck ───────────────────────────

Deno.test("meta-agents: registerMetaAgents registers EqCheck rules", () => {
  const agents = new Map<string, import("@deltanets/lang").AgentDef>();
  const rules: import("@deltanets/lang").RuleDef[] = [];
  registerMetaAgents(agents, rules);
  assertEquals(agents.has(META_EQ_CHECK), true);
  const eqRules = rules.filter((r) => r.agentA === META_EQ_CHECK || r.agentB === META_EQ_CHECK);
  // Should have EqCheck × each of the 5 Tm* types
  assertEquals(eqRules.length >= 5, true, `expected ≥5 EqCheck rules, got ${eqRules.length}`);
});

Deno.test("meta-agents: registerMetaAgents registers CtxSearch agent", () => {
  const agents = new Map<string, import("@deltanets/lang").AgentDef>();
  const rules: import("@deltanets/lang").RuleDef[] = [];
  registerMetaAgents(agents, rules);
  assertEquals(agents.has(META_CTX_SEARCH), true);
  // CtxSearch rules are per-invocation only, not in registerMetaAgents
  const ctxRules = rules.filter((r) => r.agentA === META_CTX_SEARCH || r.agentB === META_CTX_SEARCH);
  assertEquals(ctxRules.length, 0);
});

// ─── open "Meta" integration ───────────────────────────────────────

Deno.test("meta-agents: open Meta registers CtxSearch and EqCheck agents", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has(META_CTX_SEARCH), true);
  assertEquals(sys.agents.has(META_EQ_CHECK), true);
});

Deno.test("meta-agents: EqCheck port structure via open Meta", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  const eq = sys.agents.get(META_EQ_CHECK)!;
  assertEquals(eq.ports.length, 4);
  assertEquals(eq.ports[0].name, "principal");
  assertEquals(eq.ports[1].name, "second");
  assertEquals(eq.ports[2].name, "on_eq");
  assertEquals(eq.ports[3].name, "on_neq");
});

Deno.test("meta-agents: CtxSearch port structure via open Meta", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  open "Quote"
  open "Meta"
}
`);
  const sys = result.systems.get("T")!;
  const cs = sys.agents.get(META_CTX_SEARCH)!;
  assertEquals(cs.ports.length, 2);
  assertEquals(cs.ports[0].name, "principal");
  assertEquals(cs.ports[1].name, "result");
});
