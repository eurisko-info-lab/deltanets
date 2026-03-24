// End-to-end tests for the NatEq (Nat + Eq) interaction net system.
// Verifies that proofs about natural numbers reduce correctly:
// cong_succ, nested congruences, and arithmetic proofs.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "@deltanets/core";
import { NATEQ_SYSTEM, collectRules, collectAgentPorts, reduceAll, readRootType } from "./helpers.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const NATEQ_SOURCE = NATEQ_SYSTEM;

function compileNatEq(graphSource: string) {
  const source = NATEQ_SOURCE + "\n" + graphSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
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
  // 29 Prelude + 2 Nat + 4 Eq + 1 NatEq = 36
  assertEquals(nateq.rules.length, 36);
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
