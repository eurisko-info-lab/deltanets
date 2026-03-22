// Shared test helpers and INet system fixtures.
// Reduces boilerplate across all test files.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "@deltanets/core";
import { getRedexes } from "@deltanets/core";

// ─── Common INet source fragments ─────────────────────────────────

export const NAT_SYSTEM = `
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
`;

export const EQ_AGENTS = `
  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent cong(principal, result, func)
  agent trans(principal, result, second)

  rule subst <> refl -> { relink left.result left.value }
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule cong <> refl -> { let r = refl  relink left.result r.principal  erase left.func }
  rule trans <> refl -> { relink left.result left.second }
`;

export const EQ_SYSTEM = NAT_SYSTEM + `
system "Eq" extend "Nat" {
${EQ_AGENTS}
}
`;

export const NATEQ_SYSTEM = EQ_SYSTEM + `
system "NatEq" extend "Eq" {
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> {
    let r = refl
    relink left.result r.principal
  }
}
`;

// ─── Shared helper functions ───────────────────────────────────────

export function compileAndAssert(source: string) {
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

export function collectRules(core: ReturnType<typeof compileCore>): InteractionRule[] {
  const rules: InteractionRule[] = [];
  for (const sys of core.systems.values()) {
    for (const r of sys.rules) {
      rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
    }
  }
  return rules;
}

export function collectAgentPorts(
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

export function reduceAll(
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

export function readRootType(graph: Graph): string {
  const root = graph.find((n) => n.type === "root");
  if (!root) throw new Error("no root node");
  return root.ports[0].node.type;
}

export function countNodes(graph: Graph): number {
  return graph.filter((n) => n.type !== "root").length;
}

export function readNat(graph: Graph): number {
  const root = graph.find((n) => n.type === "root");
  if (!root) throw new Error("no root node");
  let current = root.ports[0].node;
  let count = 0;
  while (current.type === "Succ") {
    count++;
    current = current.ports[1].node; // pred port
  }
  if (current.type !== "Zero") {
    throw new Error(`unexpected node type: ${current.type}`);
  }
  return count;
}
