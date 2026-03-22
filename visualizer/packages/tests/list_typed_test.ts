// End-to-end tests for typed List prove blocks.
// Verifies that List proofs generated via `prove` syntax with dependent
// type checking compile, type-check, and reduce identically to hand-written versions.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "@deltanets/core";
import { getRedexes } from "@deltanets/core";

// ─── Helpers ───────────────────────────────────────────────────────

const BASE_SYSTEM = `
include "prelude"

system "Nat" extend "Prelude" {
  agent Zero(principal)
  agent Succ(principal, pred)
  agent add(principal, result, accum)

  rule add <> Zero -> { relink left.result left.accum }
  rule add <> Succ -> {
    let s = Succ  let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }
}

system "List" extend "Nat" {
  agent Nil(principal)
  agent Cons(principal, head, tail)
  agent length(principal, result)
  agent append(principal, result, ys)

  rule length <> Nil -> { let z = Zero  relink left.result z.principal }
  rule length <> Cons -> {
    let s = Succ  let l = length
    relink left.result s.principal
    wire s.pred -- l.result
    relink right.tail l.principal
    erase right.head
  }
  rule append <> Nil -> { relink left.result left.ys }
  rule append <> Cons -> {
    let c = Cons  let a = append
    relink left.result c.principal
    relink right.head c.head
    wire c.tail -- a.result
    relink right.tail a.principal
    relink left.ys a.ys
  }
}

system "Eq" extend "List" {
  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent trans(principal, result, second)

  rule subst <> refl -> { relink left.result left.value }
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule trans <> refl -> { relink left.result left.second }
}
`;

function compile(extraSource: string) {
  const source = BASE_SYSTEM + "\n" + extraSource;
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

// ─── Typed List Prove System ───────────────────────────────────────

const TYPED_LIST = `
system "TypedList" extend "Eq" {
  agent cong_cons(principal, result, head)
  rule cong_cons <> refl -> {
    let r = refl
    relink left.result r.principal
    erase left.head
  }

  prove append_nil_right(xs : List) -> Eq(append(xs, Nil), xs) {
    | Nil -> refl
    | Cons(h, t) -> cong_cons(append_nil_right(t), h)
  }
}
`;

// ─── Compilation Tests ─────────────────────────────────────────────

Deno.test("list-typed: append_nil_right compiles with correct ports", () => {
  const result = compile(TYPED_LIST);
  const sys = result.systems.get("TypedList")!;
  assertEquals(sys.agents.has("append_nil_right"), true);
  const anr = sys.agents.get("append_nil_right")!;
  assertEquals(anr.ports.map((p: { name: string }) => p.name), ["principal", "result"]);
});

Deno.test("list-typed: cong_cons agent present", () => {
  const result = compile(TYPED_LIST);
  const sys = result.systems.get("TypedList")!;
  assertEquals(sys.agents.has("cong_cons"), true);
});

// ─── Reduction Tests ───────────────────────────────────────────────
// Must match hand-written step counts: Nil→1, [0]→4, [0,0]→7, [0,0,0]→10

Deno.test("list-typed: append_nil_right(Nil) → refl in 1 step", () => {
  const core = compile(TYPED_LIST + `
    graph test {
      let r   = root  let anr = append_nil_right  let n = Nil
      wire r.principal -- anr.result
      wire anr.principal -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("list-typed: append_nil_right([0]) → refl in 4 steps", () => {
  const core = compile(TYPED_LIST + `
    graph test {
      let r   = root  let anr = append_nil_right
      let c   = Cons  let z = Zero  let n = Nil
      wire r.principal -- anr.result
      wire anr.principal -- c.principal
      wire c.head -- z.principal
      wire c.tail -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 4);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("list-typed: append_nil_right([0,0]) → refl in 7 steps", () => {
  const core = compile(TYPED_LIST + `
    graph test {
      let r   = root  let anr = append_nil_right
      let c1  = Cons  let z1 = Zero
      let c2  = Cons  let z2 = Zero  let n = Nil
      wire r.principal -- anr.result
      wire anr.principal -- c1.principal
      wire c1.head -- z1.principal
      wire c1.tail -- c2.principal
      wire c2.head -- z2.principal
      wire c2.tail -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 7);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("list-typed: append_nil_right([0,0,0]) → refl in 10 steps", () => {
  const core = compile(TYPED_LIST + `
    graph test {
      let r   = root  let anr = append_nil_right
      let c1  = Cons  let z1 = Zero
      let c2  = Cons  let z2 = Zero
      let c3  = Cons  let z3 = Zero  let n = Nil
      wire r.principal -- anr.result
      wire anr.principal -- c1.principal
      wire c1.head -- z1.principal
      wire c1.tail -- c2.principal
      wire c2.head -- z2.principal
      wire c2.tail -- c3.principal
      wire c3.head -- z3.principal
      wire c3.tail -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 10);
  assertEquals(readRootType(g.graph), "refl");
});

// ─── Type Error Detection ──────────────────────────────────────────

Deno.test("list-typed: wrong append proposition is caught", () => {
  const source = BASE_SYSTEM + `
    system "Wrong" extend "Eq" {
      agent cong_cons(principal, result, head)
      rule cong_cons <> refl -> {
        let r = refl  relink left.result r.principal  erase left.head
      }
      prove bad_anr(xs : List) -> Eq(append(xs, Nil), Nil) {
        | Nil -> refl
        | Cons(h, t) -> cong_cons(bad_anr(t), h)
      }
    }
  `;
  const result = compileCore(source);
  // Cons case: Eq(append(Cons(h,t), Nil), Nil) → Eq(Cons(h, append(t,Nil)), Nil)
  // recursive call bad_anr(t) : Eq(append(t,Nil), Nil), cong_cons wraps to
  // Eq(Cons(h, append(t,Nil)), Cons(h, Nil)) ≠ Eq(Cons(h, append(t,Nil)), Nil)
  assertEquals(result.errors.length > 0, true, "expected type errors for wrong List proposition");
});

Deno.test("list-typed: missing cong_cons in inductive case is caught", () => {
  const source = BASE_SYSTEM + `
    system "Wrong2" extend "Eq" {
      agent cong_cons(principal, result, head)
      rule cong_cons <> refl -> {
        let r = refl  relink left.result r.principal  erase left.head
      }
      prove bad_anr2(xs : List) -> Eq(append(xs, Nil), xs) {
        | Nil -> refl
        | Cons(h, t) -> bad_anr2(t)
      }
    }
  `;
  const result = compileCore(source);
  // Cons case: requires Eq(Cons(h, append(t,Nil)), Cons(h,t))
  // but bad_anr2(t) : Eq(append(t,Nil), t) — doesn't wrap in Cons
  assertEquals(result.errors.length > 0, true, "expected type errors for missing cong_cons");
});
