// End-to-end tests for the BoolProofs system.
// Verifies that proof-by-case-analysis over Bool reduces correctly,
// producing refl for every concrete input.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "@deltanets/core";
import { getRedexes } from "@deltanets/core";

// ─── Helpers ───────────────────────────────────────────────────────

const BOOL_SOURCE = `
include "prelude"

system "Bool" extend "Prelude" {
  agent True(principal)
  agent False(principal)
  agent not(principal, result)
  agent and(principal, result, b)
  agent or(principal, result, b)

  rule not <> True -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True  relink left.result t.principal }
  rule and <> True -> { relink left.result left.b }
  rule and <> False -> { let f = False  relink left.result f.principal  erase left.b }
  rule or <> True -> { let t = True  relink left.result t.principal  erase left.b }
  rule or <> False -> { relink left.result left.b }
}

system "Eq" extend "Bool" {
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

system "BoolProofs" extend "Eq" {
  agent dup_bool(principal, copy1, copy2)
  rule dup_bool <> True -> { let t1 = True  let t2 = True  relink left.copy1 t1.principal  relink left.copy2 t2.principal }
  rule dup_bool <> False -> { let f1 = False  let f2 = False  relink left.copy1 f1.principal  relink left.copy2 f2.principal }

  agent not_not(principal, result)
  rule not_not <> True -> { let r = refl  relink left.result r.principal }
  rule not_not <> False -> { let r = refl  relink left.result r.principal }

  agent and_comm(principal, result, b)
  agent and_comm_t(principal, result)
  agent and_comm_f(principal, result)
  rule and_comm <> True -> { let h = and_comm_t  relink left.result h.result  relink left.b h.principal }
  rule and_comm <> False -> { let h = and_comm_f  relink left.result h.result  relink left.b h.principal }
  rule and_comm_t <> True -> { let r = refl  relink left.result r.principal }
  rule and_comm_t <> False -> { let r = refl  relink left.result r.principal }
  rule and_comm_f <> True -> { let r = refl  relink left.result r.principal }
  rule and_comm_f <> False -> { let r = refl  relink left.result r.principal }

  agent demorgan(principal, result, b)
  rule demorgan <> True -> { let r = refl  relink left.result r.principal  erase left.b }
  rule demorgan <> False -> { let r = refl  relink left.result r.principal  erase left.b }
}
`;

function compileBool(graphSource: string) {
  const source = BOOL_SOURCE + "\n" + graphSource;
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

Deno.test("bool: system compiles with all agents and rules", () => {
  const result = compileCore(BOOL_SOURCE);
  assertEquals(result.errors.length, 0);
  const bp = result.systems.get("BoolProofs")!;
  // Bool(6) + Eq(4) + BoolProofs(12) = 22 rules
  assertEquals(bp.rules.length, 22);
  assertEquals(bp.agents.has("True"), true);
  assertEquals(bp.agents.has("False"), true);
  assertEquals(bp.agents.has("not"), true);
  assertEquals(bp.agents.has("and"), true);
  assertEquals(bp.agents.has("or"), true);
  assertEquals(bp.agents.has("refl"), true);
  assertEquals(bp.agents.has("dup_bool"), true);
  assertEquals(bp.agents.has("not_not"), true);
  assertEquals(bp.agents.has("and_comm"), true);
  assertEquals(bp.agents.has("and_comm_t"), true);
  assertEquals(bp.agents.has("and_comm_f"), true);
  assertEquals(bp.agents.has("demorgan"), true);
});

// ─── Computation tests ─────────────────────────────────────────────

Deno.test("bool: not(True) = False", () => {
  const core = compileBool(`
    graph test {
      let r = root
      let n = not
      let t = True
      wire r.principal -- n.result
      wire n.principal -- t.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "False");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: not(False) = True", () => {
  const core = compileBool(`
    graph test {
      let r = root
      let n = not
      let f = False
      wire r.principal -- n.result
      wire n.principal -- f.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "True");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: and(True, False) = False", () => {
  const core = compileBool(`
    graph test {
      let r = root
      let a = and
      let t = True
      let f = False
      wire r.principal -- a.result
      wire a.principal -- t.principal
      wire a.b         -- f.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "False");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: or(False, True) = True", () => {
  const core = compileBool(`
    graph test {
      let r = root
      let o = or
      let f = False
      let t = True
      wire r.principal -- o.result
      wire o.principal -- f.principal
      wire o.b         -- t.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "True");
  assertEquals(countNodes(g.graph), 1);
});

// ─── dup_bool tests ────────────────────────────────────────────────

Deno.test("bool: dup_bool(True) + and → True", () => {
  const core = compileBool(`
    graph test {
      let r = root
      let d = dup_bool
      let a = and
      let t = True
      wire r.principal -- a.result
      wire d.principal -- t.principal
      wire d.copy1     -- a.principal
      wire d.copy2     -- a.b
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);   // dup → True+True, and(True,True) → True
  assertEquals(readRootType(g.graph), "True");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: dup_bool(False) + or → False", () => {
  const core = compileBool(`
    graph test {
      let r = root
      let d = dup_bool
      let o = or
      let f = False
      wire r.principal -- o.result
      wire d.principal -- f.principal
      wire d.copy1     -- o.principal
      wire d.copy2     -- o.b
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);   // dup → False+False, or(False,False) → False
  assertEquals(readRootType(g.graph), "False");
  assertEquals(countNodes(g.graph), 1);
});

// ─── not_not proof tests ───────────────────────────────────────────

Deno.test("bool: not_not(True) → refl in 1 step", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let nn = not_not
      let t  = True
      wire r.principal  -- nn.result
      wire nn.principal -- t.principal
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

Deno.test("bool: not_not(False) → refl in 1 step", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let nn = not_not
      let f  = False
      wire r.principal  -- nn.result
      wire nn.principal -- f.principal
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

// ─── and_comm proof tests ──────────────────────────────────────────

Deno.test("bool: and_comm(True, True) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let ac = and_comm
      let t1 = True
      let t2 = True
      wire r.principal  -- ac.result
      wire ac.principal -- t1.principal
      wire ac.b         -- t2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: and_comm(True, False) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let ac = and_comm
      let t  = True
      let f  = False
      wire r.principal  -- ac.result
      wire ac.principal -- t.principal
      wire ac.b         -- f.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: and_comm(False, True) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let ac = and_comm
      let f  = False
      let t  = True
      wire r.principal  -- ac.result
      wire ac.principal -- f.principal
      wire ac.b         -- t.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: and_comm(False, False) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let ac = and_comm
      let f1 = False
      let f2 = False
      wire r.principal  -- ac.result
      wire ac.principal -- f1.principal
      wire ac.b         -- f2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

// ─── demorgan proof tests ──────────────────────────────────────────

Deno.test("bool: demorgan(True, True) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let dm = demorgan
      let t1 = True
      let t2 = True
      wire r.principal  -- dm.result
      wire dm.principal -- t1.principal
      wire dm.b         -- t2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: demorgan(True, False) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let dm = demorgan
      let t  = True
      let f  = False
      wire r.principal  -- dm.result
      wire dm.principal -- t.principal
      wire dm.b         -- f.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: demorgan(False, True) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let dm = demorgan
      let f  = False
      let t  = True
      wire r.principal  -- dm.result
      wire dm.principal -- f.principal
      wire dm.b         -- t.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: demorgan(False, False) → refl in 2 steps", () => {
  const core = compileBool(`
    graph test {
      let r  = root
      let dm = demorgan
      let f1 = False
      let f2 = False
      wire r.principal  -- dm.result
      wire dm.principal -- f1.principal
      wire dm.b         -- f2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

// ─── Verification tests ───────────────────────────────────────────

Deno.test("bool: verify not_not(True) via subst → True", () => {
  const core = compileBool(`
    graph test {
      let r   = root
      let sub = subst
      let nn  = not_not
      let t1  = True
      let n1  = not
      let n2  = not
      let t2  = True
      wire r.principal   -- sub.result
      wire sub.principal -- nn.result
      wire sub.value     -- n1.result
      wire nn.principal  -- t1.principal
      wire n1.principal  -- n2.result
      wire n2.principal  -- t2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 4);   // nn→refl, subst→pass, not(True)→False, not(False)→True
  assertEquals(readRootType(g.graph), "True");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("bool: verify and_comm(False, True) via subst → False", () => {
  const core = compileBool(`
    graph test {
      let r   = root
      let sub = subst
      let ac  = and_comm
      let f1  = False
      let t1  = True
      let a   = and
      let f2  = False
      let t2  = True
      wire r.principal   -- sub.result
      wire sub.principal -- ac.result
      wire sub.value     -- a.result
      wire ac.principal  -- f1.principal
      wire ac.b          -- t1.principal
      wire a.principal   -- f2.principal
      wire a.b           -- t2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 5);   // ac(2) + subst(1) + and→False+erase(1) + erase True(1)
  assertEquals(readRootType(g.graph), "False");
  assertEquals(countNodes(g.graph), 1);
});
