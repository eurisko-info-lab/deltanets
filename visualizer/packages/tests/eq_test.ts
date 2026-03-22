// End-to-end tests for the Eq (propositional equality) interaction net system.
// Compiles eq.inet source, builds explicit graphs, and runs reductions
// to verify that equality proof combinators reduce correctly.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule, Node } from "@deltanets/core";
import { getRedexes } from "@deltanets/core";

// ─── Helpers ───────────────────────────────────────────────────────

const EQ_SOURCE = `
include "prelude"

system "Eq" extend "Prelude" {
  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent cong(principal, result, func)
  agent trans(principal, result, second)

  rule subst <> refl -> {
    relink left.result left.value
  }

  rule sym <> refl -> {
    let r = refl
    relink left.result r.principal
  }

  rule cong <> refl -> {
    let r = refl
    relink left.result r.principal
    erase left.func
  }

  rule trans <> refl -> {
    relink left.result left.second
  }
}
`;

function compileEq(graphSource: string) {
  const source = EQ_SOURCE + "\n" + graphSource;
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

/** Reduce all redexes until no more remain, return step count. */
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

/** Read what's connected to the root node. */
function readRootType(graph: Graph): string {
  const root = graph.find((n) => n.type === "root");
  if (!root) throw new Error("no root node");
  return root.ports[0].node.type;
}

/** Count remaining non-root nodes. */
function countNodes(graph: Graph): number {
  return graph.filter((n) => n.type !== "root").length;
}

// ─── Tests ─────────────────────────────────────────────────────────

Deno.test("eq: system compiles with agents and rules", () => {
  const result = compileCore(EQ_SOURCE);
  assertEquals(result.errors.length, 0);
  const eq = result.systems.get("Eq")!;
  assertEquals(eq.agents.has("refl"), true);
  assertEquals(eq.agents.has("subst"), true);
  assertEquals(eq.agents.has("sym"), true);
  assertEquals(eq.agents.has("cong"), true);
  assertEquals(eq.agents.has("trans"), true);
  assertEquals(eq.rules.length, 4);
});

Deno.test("eq: subst(refl, value) → value", () => {
  const core = compileEq(`
    graph test {
      let r  = root
      let s  = subst
      let rf = refl
      let v  = refl "value"
      wire r.principal -- s.result
      wire s.principal -- rf.principal
      wire s.value    -- v.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(graph.graph), "refl");
  // After subst >< refl, only root + the value refl remain
  assertEquals(countNodes(graph.graph), 1);
});

Deno.test("eq: sym(refl) → refl", () => {
  const core = compileEq(`
    graph test {
      let r  = root
      let s  = sym
      let rf = refl
      wire r.principal -- s.result
      wire s.principal -- rf.principal
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

Deno.test("eq: cong(refl) → refl, func erased", () => {
  const core = compileEq(`
    graph test {
      let r  = root
      let c  = cong
      let rf = refl
      let f  = refl "f"
      wire r.principal -- c.result
      wire c.principal -- rf.principal
      wire c.func     -- f.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  // Step 1: cong >< refl → result ← new refl, erase inserts eraser on func
  // Step 2: era >< refl("f") annihilates
  assertEquals(steps, 2);
  assertEquals(readRootType(graph.graph), "refl");
});

Deno.test("eq: trans(refl, refl) → refl", () => {
  const core = compileEq(`
    graph test {
      let r  = root
      let t  = trans
      let r1 = refl
      let r2 = refl
      wire r.principal -- t.result
      wire t.principal -- r1.principal
      wire t.second   -- r2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  // trans >< refl (step 1) links result to second (refl),
  // so root connects directly to r2 — done in 1 step
  assertEquals(steps, 1);
  assertEquals(readRootType(graph.graph), "refl");
});

Deno.test("eq: sym(sym(refl)) → refl in 2 steps", () => {
  const core = compileEq(`
    graph test {
      let r   = root
      let s1  = sym
      let s2  = sym
      let rf  = refl
      wire r.principal  -- s1.result
      wire s1.principal -- s2.result
      wire s2.principal -- rf.principal
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

Deno.test("eq: trans(refl, sym(refl)) → refl in 2 steps", () => {
  const core = compileEq(`
    graph test {
      let r   = root
      let t   = trans
      let r1  = refl
      let s   = sym
      let r2  = refl
      wire r.principal  -- t.result
      wire t.principal  -- r1.principal
      wire t.second    -- s.result
      wire s.principal  -- r2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(graph.graph, rules, ports);
  // Step 1: trans >< refl → result ← second (which is sym)
  // Now root → sym → refl
  // Step 2: sym >< refl → result ← new refl
  // Final: root → refl
  assertEquals(steps, 2);
  assertEquals(readRootType(graph.graph), "refl");
});
