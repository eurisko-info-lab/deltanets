// End-to-end tests for the Nat interaction net system.
// Compiles nat.inet source, builds explicit graphs, and runs reductions
// to verify that the custom rule engine produces correct arithmetic results.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule, Node } from "./types.ts";
import { getRedexes } from "./systems/deltanets/redexes.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const NAT_SOURCE = `
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
`;

function compileNat(graphSource: string) {
  const source = NAT_SOURCE + "\n" + graphSource;
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

/** Read a Nat value from the graph by following a root → Succ chain. */
function readNat(graph: Graph): number {
  const root = graph.find((n) => n.type === "root");
  if (!root) throw new Error("no root node");
  let current: Node = root.ports[0].node;
  let count = 0;
  while (current.type === "Succ") {
    count++;
    current = current.ports[1].node; // pred port
  }
  if (current.type !== "Zero") {
    throw new Error(`expected Zero at end of chain, got ${current.type}`);
  }
  return count;
}

// ─── Tests ─────────────────────────────────────────────────────────

Deno.test("nat: system compiles with agents and rules", () => {
  const result = compileCore(NAT_SOURCE);
  assertEquals(result.errors.length, 0);
  const nat = result.systems.get("Nat")!;
  assertEquals(nat.agents.has("Zero"), true);
  assertEquals(nat.agents.has("Succ"), true);
  assertEquals(nat.agents.has("add"), true);
  assertEquals(nat.rules.length, 2);
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
