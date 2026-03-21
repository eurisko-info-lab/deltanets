// End-to-end tests for the `prove` tactic sugar.
// Verifies that prove-generated agents produce identical results
// to their hand-written counterparts.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "./types.ts";
import { getRedexes } from "./systems/deltanets/redexes.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const TACTIC_SOURCE = `
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

system "TacticProofs" extend "NatEq" {
  prove plus_zero_right(n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }

  prove plus_succ_right(n, m) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_succ_right(k, m))
  }
}
`;

function compileTactic(graphSource: string) {
  const source = TACTIC_SOURCE + "\n" + graphSource;
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

Deno.test("tactic: system compiles with prove-generated agents", () => {
  const result = compileCore(TACTIC_SOURCE);
  assertEquals(result.errors.length, 0);
  const tp = result.systems.get("TacticProofs")!;
  assertEquals(tp.agents.has("plus_zero_right"), true);
  assertEquals(tp.agents.has("plus_succ_right"), true);
  // Nat(2) + Eq(4) + NatEq(1) + pzr(2) + psr(2) = 11 rules
  assertEquals(tp.rules.length, 11);
});

Deno.test("tactic: plus_zero_right agent has correct ports", () => {
  const result = compileCore(TACTIC_SOURCE);
  const pzr = result.systems.get("TacticProofs")!.agents.get(
    "plus_zero_right",
  )!;
  assertEquals(pzr.ports.length, 2);
  assertEquals(pzr.ports[0].name, "principal");
  assertEquals(pzr.ports[1].name, "result");
});

Deno.test("tactic: plus_succ_right agent has correct ports", () => {
  const result = compileCore(TACTIC_SOURCE);
  const psr = result.systems.get("TacticProofs")!.agents.get(
    "plus_succ_right",
  )!;
  assertEquals(psr.ports.length, 3);
  assertEquals(psr.ports[0].name, "principal");
  assertEquals(psr.ports[1].name, "result");
  assertEquals(psr.ports[2].name, "m");
});

// ─── plus_zero_right tests (identical to manual version) ───────────

Deno.test("tactic: pzr(0) → refl in 1 step", () => {
  const core = compileTactic(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let z   = Zero
      wire r.principal  -- pzr.result
      wire pzr.principal -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("tactic: pzr(1) → refl in 3 steps", () => {
  const core = compileTactic(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s   = Succ
      let z   = Zero
      wire r.principal  -- pzr.result
      wire pzr.principal -- s.principal
      wire s.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 3);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("tactic: pzr(2) → refl in 5 steps", () => {
  const core = compileTactic(`
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
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 5);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("tactic: pzr(3) → refl in 7 steps", () => {
  const core = compileTactic(`
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
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 7);
  assertEquals(readRootType(g.graph), "refl");
});

// ─── plus_succ_right tests (identical to manual version) ───────────

Deno.test("tactic: psr(0, 0) → refl in 2 steps", () => {
  const core = compileTactic(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- z1.principal
      wire psr.m         -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("tactic: psr(1, 0) → refl in 4 steps", () => {
  const core = compileTactic(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let s   = Succ
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- s.principal
      wire s.pred        -- z1.principal
      wire psr.m         -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 4);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("tactic: psr(2, 1) → refl in 7 steps", () => {
  const core = compileTactic(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let s1  = Succ
      let s2  = Succ
      let z   = Zero
      let sm  = Succ
      let zm  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z.principal
      wire psr.m         -- sm.principal
      wire sm.pred       -- zm.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 7);
  assertEquals(readRootType(g.graph), "refl");
});
