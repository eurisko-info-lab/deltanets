// End-to-end tests for the Nat interaction net system.
// Compiles nat.inet source, builds explicit graphs, and runs reductions
// to verify that the custom rule engine produces correct arithmetic results.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "@deltanets/core";
import { getRedexes } from "@deltanets/core";
import { NAT_SYSTEM, collectRules, collectAgentPorts, readNat } from "./helpers.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const NAT_SOURCE = NAT_SYSTEM;

function compileNat(graphSource: string) {
  const source = NAT_SOURCE + "\n" + graphSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

/** Reduce all redexes until no more remain, return the final graph. */
function reduceAll(
  graph: Graph,
  rules: InteractionRule[],
  agentPorts: AgentPortDefs,
  maxSteps = 100,
): Graph {
  for (let i = 0; i < maxSteps; i++) {
    const redexes = getRedexes(graph, "full", false, rules, agentPorts);
    if (redexes.length === 0) break;
    redexes[0].reduce();
  }
  return graph;
}

// ─── Tests ─────────────────────────────────────────────────────────

Deno.test("nat: system compiles with agents and rules", () => {
  const result = compileCore(NAT_SOURCE);
  assertEquals(result.errors.length, 0);
  const nat = result.systems.get("Nat")!;
  assertEquals(nat.agents.has("Zero"), true);
  assertEquals(nat.agents.has("Succ"), true);
  assertEquals(nat.agents.has("add"), true);
  assertEquals(nat.rules.length, 31); // 29 Prelude (Quote+Meta) + 2 Nat
});

Deno.test("nat: 0 + 0 = 0", () => {
  const core = compileNat(`
    graph test {
      let r  = root
      let a  = add
      let z1 = Zero
      let z2 = Zero
      wire r.principal -- a.result
      wire a.principal -- z1.principal
      wire a.accum    -- z2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(graph.graph, rules, ports);
  assertEquals(readNat(graph.graph), 0);
});

Deno.test("nat: 1 + 0 = 1", () => {
  const core = compileNat(`
    graph test {
      let r  = root
      let a  = add
      let s1 = Succ
      let z1 = Zero
      let z2 = Zero
      wire r.principal -- a.result
      wire a.principal -- s1.principal
      wire s1.pred    -- z1.principal
      wire a.accum    -- z2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(graph.graph, rules, ports);
  assertEquals(readNat(graph.graph), 1);
});

Deno.test("nat: 1 + 1 = 2", () => {
  const core = compileNat(`
    graph test {
      let r  = root
      let a  = add
      let s1 = Succ
      let z1 = Zero
      let s2 = Succ
      let z2 = Zero
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
  reduceAll(graph.graph, rules, ports);
  assertEquals(readNat(graph.graph), 2);
});

Deno.test("nat: 2 + 1 = 3", () => {
  const core = compileNat(`
    graph test {
      let r  = root
      let a  = add
      let s1 = Succ
      let s2 = Succ
      let z1 = Zero
      let s3 = Succ
      let z2 = Zero
      wire r.principal -- a.result
      wire a.principal -- s1.principal
      wire s1.pred    -- s2.principal
      wire s2.pred    -- z1.principal
      wire a.accum    -- s3.principal
      wire s3.pred    -- z2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(graph.graph, rules, ports);
  assertEquals(readNat(graph.graph), 3);
});

Deno.test("nat: 2 + 2 = 4", () => {
  const core = compileNat(`
    graph test {
      let r  = root
      let a  = add
      let s1 = Succ
      let s2 = Succ
      let z1 = Zero
      let s3 = Succ
      let s4 = Succ
      let z2 = Zero
      wire r.principal -- a.result
      wire a.principal -- s1.principal
      wire s1.pred    -- s2.principal
      wire s2.pred    -- z1.principal
      wire a.accum    -- s3.principal
      wire s3.pred    -- s4.principal
      wire s4.pred    -- z2.principal
    }
  `);
  const graph = core.graphs.get("test")!;
  if (graph.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(graph.graph, rules, ports);
  assertEquals(readNat(graph.graph), 4);
});
