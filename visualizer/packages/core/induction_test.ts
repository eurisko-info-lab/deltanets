// End-to-end tests for the Induction system (plus_zero_right).
// Verifies that proof-by-induction over Nat reduces correctly,
// producing refl for every concrete input.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "./types.ts";
import { getRedexes } from "./systems/deltanets/redexes.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const INDUCTION_SOURCE = `
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

system "Induction" extend "NatEq" {
  agent plus_zero_right(principal, result)

  rule plus_zero_right <> Zero -> {
    let r = refl
    relink left.result r.principal
  }
  rule plus_zero_right <> Succ -> {
    let pzr = plus_zero_right
    let cs  = cong_succ
    relink left.result cs.result
    wire cs.principal -- pzr.result
    relink right.pred pzr.principal
  }
}
`;

function compileInduction(graphSource: string) {
  const source = INDUCTION_SOURCE + "\n" + graphSource;
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

Deno.test("induction: system compiles with all agents and rules", () => {
  const result = compileCore(INDUCTION_SOURCE);
  assertEquals(result.errors.length, 0);
  const ind = result.systems.get("Induction")!;
  // Induction inherits everything: 2 Nat + 4 Eq + 1 NatEq + 2 Induction = 9 rules
  assertEquals(ind.rules.length, 9);
  assertEquals(ind.agents.has("plus_zero_right"), true);
  assertEquals(ind.agents.has("cong_succ"), true);
  assertEquals(ind.agents.has("refl"), true);
  assertEquals(ind.agents.has("add"), true);
});

Deno.test("induction: plus_zero_right(Zero) → refl in 1 step", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- z.principal
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

Deno.test("induction: plus_zero_right(1) → refl in 3 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s   = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s.principal
      wire s.pred        -- z.principal
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

Deno.test("induction: plus_zero_right(2) → refl in 5 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 5);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_zero_right(3) → refl in 7 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let s3  = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- s3.principal
      wire s3.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 7);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: step count follows 2n+1 formula (n=5)", () => {
  // Build Succ(Succ(Succ(Succ(Succ(Zero))))) = 5
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let s3  = Succ
      let s4  = Succ
      let s5  = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- s3.principal
      wire s3.pred       -- s4.principal
      wire s4.pred       -- s5.principal
      wire s5.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 11); // 2*5 + 1
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: verify-two-plus-zero via subst+add", () => {
  // subst(refl, add(Succ(Succ(Zero)), Zero)) should reduce to Succ(Succ(Zero))
  const core = compileInduction(`
    graph test {
      let r   = root
      let sub = subst
      let rf  = refl
      let a   = add
      let s1  = Succ
      let s2  = Succ
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- sub.result
      wire sub.principal -- rf.principal
      wire sub.value     -- a.result
      wire a.principal   -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z1.principal
      wire a.accum       -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  // add(Succ(Succ(Zero)), Zero) → Succ(Succ(Zero))
  // subst(refl, Succ(Succ(Zero))) → Succ(Succ(Zero))
  assertEquals(readRootType(g.graph), "Succ");
  // Succ(Succ(Zero)) = 3 nodes
  assertEquals(countNodes(g.graph), 3);
});

Deno.test("induction: NatEq regression — cong_succ(refl) still works", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let cs  = cong_succ
      let rf  = refl
      wire r.principal  -- cs.result
      wire cs.principal -- rf.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
});
