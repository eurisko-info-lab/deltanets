// End-to-end tests for the Eq (propositional equality) interaction net system.
// Compiles eq.inet source, builds explicit graphs, and runs reductions
// to verify that equality proof combinators reduce correctly.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { EQ_AGENTS, collectRules, collectAgentPorts, reduceAll, readRootType, countNodes } from "./helpers.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const EQ_SOURCE = `
include "prelude"

system "Eq" extend "Prelude" {
${EQ_AGENTS}
}
`;

function compileEq(graphSource: string) {
  const source = EQ_SOURCE + "\n" + graphSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
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
