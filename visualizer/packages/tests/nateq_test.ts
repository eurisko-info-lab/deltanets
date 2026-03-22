// End-to-end tests for the NatEq (Nat + Eq) interaction net system.
// Verifies that proofs about natural numbers reduce correctly:
// cong_succ, nested congruences, and arithmetic proofs.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "@deltanets/core";
import { getRedexes } from "@deltanets/core";

// ─── Helpers ───────────────────────────────────────────────────────

const NATEQ_SOURCE = `
include "prelude"

system "Nat" extend "Prelude" {
  agent Zero(principal)
  agent Succ(principal, pred)
  agent add(principal, result, accum)

  rule add <> Zero -> {
    relink left.result left.accum
  }
  rule add <> Succ -> {
    let s = Succ
    let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }
}

system "Eq" extend "Nat" {
  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent cong(principal, result, func)
  agent trans(principal, result, second)

  rule subst <> refl -> { relink left.result left.value }
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule cong <> refl -> { let r = refl  relink left.result r.principal  erase left.func }
  rule trans <> refl -> { relink left.result left.second }
}

system "NatEq" extend "Eq" {
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> {
    let r = refl
    relink left.result r.principal
  }
}
`;

function compileNatEq(graphSource: string) {
  const source = NATEQ_SOURCE + "\n" + graphSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

function collectRules(core: ReturnType<typeof compileCore>): InteractionRule[] {
  const rules: InteractionRule[] = [];
  for (const sys of core.systems.values()) {
    for (const r of sys.rules) {
      rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
    }
  }
  return rules;
}

function collectAgentPorts(
  core: ReturnType<typeof compileCore>,
): AgentPortDefs {
  const defs: AgentPortDefs = new Map();
  for (const sys of core.systems.values()) {
    for (const [name, agent] of sys.agents) {
      if (!defs.has(name)) defs.set(name, agent.portIndex);
    }
  }
  return defs;
}

function reduceAll(
  graph: Graph,
  rules: InteractionRule[],
  agentPorts: AgentPortDefs,
  maxSteps = 100,
): number {
  let steps = 0;
  for (let i = 0; i < maxSteps; i++) {
    const redexes = getRedexes(graph, "full", false, rules, agentPorts);
    if (redexes.length === 0) break;
    redexes[0].reduce();
    steps++;
  }
  return steps;
}

function readRootType(graph: Graph): string {
  const root = graph.find((n) => n.type === "root");
  if (!root) throw new Error("no root node");
  return root.ports[0].node.type;
}

function countNodes(graph: Graph): number {
  return graph.filter((n) => n.type !== "root").length;
}

// ─── Tests ─────────────────────────────────────────────────────────

Deno.test("nateq: system compiles with all agents and rules", () => {
  const result = compileCore(NATEQ_SOURCE);
  assertEquals(result.errors.length, 0);
  const nateq = result.systems.get("NatEq")!;
  // NatEq inherits Nat + Eq agents + adds cong_succ
  assertEquals(nateq.agents.has("cong_succ"), true);
  // rules are flattened from inheritance: 2 Nat + 4 Eq + 1 NatEq = 7
  assertEquals(nateq.rules.length, 7);
});

Deno.test("nateq: cong_succ(refl) → refl", () => {
  const core = compileNatEq(`
    graph test {
      let r   = root
      let cs  = cong_succ
      let rf  = refl
      wire r.principal  -- cs.result
      wire cs.principal -- rf.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(graph.graph), "refl");
});

Deno.test("nateq: cong_succ(cong_succ(refl)) → refl in 2 steps", () => {
  const core = compileNatEq(`
    graph test {
      let r    = root
      let cs1  = cong_succ
      let cs2  = cong_succ
      let rf   = refl
      wire r.principal   -- cs1.result
      wire cs1.principal -- cs2.result
      wire cs2.principal -- rf.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(graph.graph), "refl");
});

Deno.test("nateq: sym(cong_succ(refl)) → refl in 2 steps", () => {
  const core = compileNatEq(`
    graph test {
      let r   = root
      let s   = sym
      let cs  = cong_succ
      let rf  = refl
      wire r.principal  -- s.result
      wire s.principal  -- cs.result
      wire cs.principal -- rf.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  // Step 1: cong_succ >< refl → new refl at sym's principal
  // Step 2: sym >< refl → new refl at root
  assertEquals(steps, 2);
  assertEquals(readRootType(graph.graph), "refl");
});

Deno.test("nateq: trans(cong_succ(refl), cong_succ(refl)) → refl", () => {
  const core = compileNatEq(`
    graph test {
      let r    = root
      let t    = trans
      let cs1  = cong_succ
      let cs2  = cong_succ
      let rf1  = refl
      let rf2  = refl
      wire r.principal   -- t.result
      wire t.principal   -- cs1.result
      wire cs1.principal -- rf1.principal
      wire t.second      -- cs2.result
      wire cs2.principal -- rf2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  // The two cong_succ >< refl fire, then trans >< refl fires
  assertEquals(readRootType(graph.graph), "refl");
});

Deno.test("nateq: subst carries value through add(Zero,Zero) → Zero", () => {
  const core = compileNatEq(`
    graph test {
      let r   = root
      let sub = subst
      let rf  = refl
      let a   = add
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- sub.result
      wire sub.principal -- rf.principal
      wire sub.value     -- a.result
      wire a.principal   -- z1.principal
      wire a.accum       -- z2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  // subst >< refl → result ← value (the add chain)
  // add >< Zero → result ← accum (Zero)
  assertEquals(readRootType(graph.graph), "Zero");
  assertEquals(countNodes(graph.graph), 1); // just Zero
});

Deno.test("nateq: Nat add still works (1+1 = Succ(Succ(Zero)))", () => {
  const core = compileNatEq(`
    graph test {
      let r   = root
      let a   = add
      let s1  = Succ
      let z1  = Zero
      let s2  = Succ
      let z2  = Zero
      wire r.principal -- a.result
      wire a.principal -- s1.principal
      wire s1.pred    -- z1.principal
      wire a.accum    -- s2.principal
      wire s2.pred    -- z2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(graph.graph), "Succ");
  assertEquals(countNodes(graph.graph), 3); // Succ -> Succ -> Zero
});
