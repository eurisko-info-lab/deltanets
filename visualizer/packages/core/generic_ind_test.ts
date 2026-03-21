// End-to-end tests for the Generic Nat Eliminator system.
// Verifies that nat_ind and nat_ind_param correctly abstract
// the plus_zero_right and plus_succ_right proof patterns.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "./types.ts";
import { getRedexes } from "./systems/deltanets/redexes.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const GENERIC_IND_SOURCE = `
include "prelude"

system "Nat" extend "Prelude" {
  agent Zero(principal)
  agent Succ(principal, pred)
  agent add(principal, result, accum)

  rule add <> Zero -> { relink left.result left.accum }
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

system "GenericInd" extend "NatEq" {
  agent nat_ind(principal, result, base)
  rule nat_ind <> Zero -> { relink left.result left.base }
  rule nat_ind <> Succ -> {
    let ni = nat_ind
    let cs = cong_succ
    relink left.result cs.result
    wire cs.principal -- ni.result
    relink right.pred ni.principal
    relink left.base ni.base
  }

  agent nat_ind_param(principal, result, base, param)
  rule nat_ind_param <> Zero -> { relink left.result left.base  erase left.param }
  rule nat_ind_param <> Succ -> {
    let ni = nat_ind_param
    let cs = cong_succ
    relink left.result cs.result
    wire cs.principal -- ni.result
    relink right.pred ni.principal
    relink left.base ni.base
    relink left.param ni.param
  }
}
`;

function compileGenInd(graphSource: string) {
  const source = GENERIC_IND_SOURCE + "\n" + graphSource;
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
  maxSteps = 200,
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

Deno.test("generic-ind: system compiles with all agents and rules", () => {
  const result = compileCore(GENERIC_IND_SOURCE);
  assertEquals(result.errors.length, 0);
  const gi = result.systems.get("GenericInd")!;
  // Nat(2) + Eq(4) + NatEq(1) + GenericInd(4) = 11 rules
  assertEquals(gi.rules.length, 11);
  assertEquals(gi.agents.has("nat_ind"), true);
  assertEquals(gi.agents.has("nat_ind_param"), true);
  assertEquals(gi.agents.has("cong_succ"), true);
});

// ─── nat_ind tests (generic plus_zero_right) ───────────────────────

Deno.test("generic-ind: nat_ind(0, refl) → refl in 1 step", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind
      let z  = Zero
      let rf = refl
      wire r.principal  -- ni.result
      wire ni.principal -- z.principal
      wire ni.base      -- rf.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("generic-ind: nat_ind(1, refl) → refl in 3 steps", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind
      let s  = Succ
      let z  = Zero
      let rf = refl
      wire r.principal  -- ni.result
      wire ni.principal -- s.principal
      wire s.pred       -- z.principal
      wire ni.base      -- rf.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 3);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("generic-ind: nat_ind(2, refl) → refl in 5 steps", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind
      let s1 = Succ
      let s2 = Succ
      let z  = Zero
      let rf = refl
      wire r.principal  -- ni.result
      wire ni.principal -- s1.principal
      wire s1.pred      -- s2.principal
      wire s2.pred      -- z.principal
      wire ni.base      -- rf.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 5);   // 2n+1 = 5
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("generic-ind: nat_ind(3, refl) → refl in 7 steps", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind
      let s1 = Succ
      let s2 = Succ
      let s3 = Succ
      let z  = Zero
      let rf = refl
      wire r.principal  -- ni.result
      wire ni.principal -- s1.principal
      wire s1.pred      -- s2.principal
      wire s2.pred      -- s3.principal
      wire s3.pred      -- z.principal
      wire ni.base      -- rf.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 7);   // 2n+1 = 7
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

// ─── nat_ind_param tests (generic plus_succ_right) ─────────────────

Deno.test("generic-ind: nat_ind_param(0, refl, 0) → refl in 2 steps", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind_param
      let z1 = Zero
      let rf = refl
      let z2 = Zero
      wire r.principal  -- ni.result
      wire ni.principal -- z1.principal
      wire ni.base      -- rf.principal
      wire ni.param     -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);   // base + erase
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("generic-ind: nat_ind_param(1, refl, 0) → refl in 4 steps", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind_param
      let s  = Succ
      let z1 = Zero
      let rf = refl
      let z2 = Zero
      wire r.principal  -- ni.result
      wire ni.principal -- s.principal
      wire s.pred       -- z1.principal
      wire ni.base      -- rf.principal
      wire ni.param     -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 4);   // 2n + m + 2 = 4
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("generic-ind: nat_ind_param(2, refl, 1) → refl in 7 steps", () => {
  const core = compileGenInd(`
    graph test {
      let r  = root
      let ni = nat_ind_param
      let s1 = Succ
      let s2 = Succ
      let z1 = Zero
      let rf = refl
      let sm = Succ
      let z2 = Zero
      wire r.principal  -- ni.result
      wire ni.principal -- s1.principal
      wire s1.pred      -- s2.principal
      wire s2.pred      -- z1.principal
      wire ni.base      -- rf.principal
      wire ni.param     -- sm.principal
      wire sm.pred      -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 7);   // 2*2 + 1 + 2 = 7
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});
