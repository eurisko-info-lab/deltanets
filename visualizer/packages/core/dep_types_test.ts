// End-to-end tests for dependent type checking in `prove` blocks.
// Verifies that typed prove blocks compile, type-check, and reduce identically
// to their untyped counterparts, and that type errors are caught.

import { assertEquals, assertThrows } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import type { AgentPortDefs, Graph, InteractionRule } from "./types.ts";
import { getRedexes } from "./systems/deltanets/redexes.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const BASE_SYSTEM = `
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

// ─── Compilation Tests ─────────────────────────────────────────────

Deno.test("deptype: typed plus_zero_right compiles and type-checks", () => {
  const result = compile(`
    system "Typed" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  const sys = result.systems.get("Typed")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

Deno.test("deptype: typed plus_succ_right compiles and type-checks", () => {
  const result = compile(`
    system "Typed" extend "NatEq" {
      prove plus_succ_right(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_succ_right(k, m))
      }
    }
  `);
  const sys = result.systems.get("Typed")!;
  assertEquals(sys.agents.has("plus_succ_right"), true);
});

Deno.test("deptype: untyped prove still works (no annotation)", () => {
  const result = compile(`
    system "Untyped" extend "NatEq" {
      prove plus_zero_right(n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  const sys = result.systems.get("Untyped")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

Deno.test("deptype: partial annotation (type on params only, no return) works", () => {
  const result = compile(`
    system "PartialAnnotation" extend "NatEq" {
      prove plus_zero_right(n : Nat) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  const sys = result.systems.get("PartialAnnotation")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

// ─── Type Error Detection ──────────────────────────────────────────

Deno.test("deptype: wrong proposition is caught — impossible equality", () => {
  const source = BASE_SYSTEM + `
    system "Wrong" extend "NatEq" {
      prove bad_pzr(n : Nat) -> Eq(add(n, Zero), Succ(n)) {
        | Zero -> refl
        | Succ(k) -> cong_succ(bad_pzr(k))
      }
    }
  `;
  const result = compileCore(source);
  // Eq(add(Zero, Zero), Succ(Zero)) = Eq(Zero, Succ(Zero)) — sides differ, refl fails
  assertEquals(result.errors.length > 0, true, "expected type errors for impossible equality");
});

Deno.test("deptype: wrong proof term is caught — missing cong_succ", () => {
  const source = BASE_SYSTEM + `
    system "Wrong2" extend "NatEq" {
      prove bad_pzr2(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> bad_pzr2(k)
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "expected type errors for missing cong_succ");
});

// ─── Reduction Tests (typed proofs behave identically) ─────────────

Deno.test("deptype: typed pzr(0) → refl in 1 step", () => {
  const core = compile(`
    system "Typed" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
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
});

Deno.test("deptype: typed pzr(2) → refl in 5 steps", () => {
  const core = compile(`
    system "Typed" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let z   = Zero
      wire r.principal  -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred      -- s2.principal
      wire s2.pred      -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 5);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: typed psr(1, 0) → refl in 4 steps", () => {
  const core = compile(`
    system "Typed" extend "NatEq" {
      prove plus_succ_right(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_succ_right(k, m))
      }
    }
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

// ─── Verification tests ────────────────────────────────────────────

Deno.test("deptype: subst(pzr(2), add(2,0)) → Succ(Succ(Zero))", () => {
  const core = compile(`
    system "Typed" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
    graph test {
      let r   = root
      let sub = subst
      let pzr = plus_zero_right
      let add1 = add
      let s1  = Succ
      let s2  = Succ
      let z1  = Zero
      let s3  = Succ
      let s4  = Succ
      let z2  = Zero
      let z3  = Zero
      wire r.principal    -- sub.result
      wire sub.principal  -- pzr.result
      wire sub.value      -- add1.result
      wire pzr.principal  -- s1.principal
      wire s1.pred        -- s2.principal
      wire s2.pred        -- z1.principal
      wire add1.principal -- s3.principal
      wire s3.pred        -- s4.principal
      wire s4.pred        -- z2.principal
      wire add1.accum     -- z3.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  // Should reduce to Succ(Succ(Zero)) — root connected to Succ
  assertEquals(readRootType(g.graph), "Succ");
});

// ─── plus_comm Tests ───────────────────────────────────────────────

const COMM_SYSTEM = `
system "Comm" extend "NatEq" {
  agent dup_nat(principal, copy1, copy2)
  rule dup_nat <> Zero -> {
    let z1 = Zero  let z2 = Zero
    relink left.copy1 z1.principal
    relink left.copy2 z2.principal
  }
  rule dup_nat <> Succ -> {
    let s1 = Succ  let s2 = Succ  let d = dup_nat
    relink left.copy1 s1.principal
    relink left.copy2 s2.principal
    wire s1.pred -- d.copy1
    wire s2.pred -- d.copy2
    relink right.pred d.principal
  }
  prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
  prove plus_succ_right(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_succ_right(k, m))
  }
  prove plus_comm(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
    | Zero -> sym(plus_zero_right(m))
    | Succ(k) -> trans(cong_succ(plus_comm(k, m)), sym(plus_succ_right(m, k)))
  }
}
`;

Deno.test("deptype: plus_comm compiles with auto-duplication and cross-lemma types", () => {
  const result = compile(COMM_SYSTEM);
  const sys = result.systems.get("Comm")!;
  assertEquals(sys.agents.has("plus_comm"), true);
  // plus_comm should have ports: principal, result, m
  const pc = sys.agents.get("plus_comm")!;
  assertEquals(pc.ports.map((p: { name: string }) => p.name), ["principal", "result", "m"]);
});

Deno.test("deptype: plus_comm(0, 0) → refl in 3 steps", () => {
  const core = compile(COMM_SYSTEM + `
    graph test {
      let r = root  let pc = plus_comm  let z1 = Zero  let z2 = Zero
      wire r.principal -- pc.result
      wire pc.principal -- z1.principal
      wire pc.m -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 3);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: plus_comm(1, 0) → refl in 11 steps", () => {
  const core = compile(COMM_SYSTEM + `
    graph test {
      let r = root  let pc = plus_comm
      let s = Succ  let z1 = Zero  let z2 = Zero
      wire r.principal -- pc.result
      wire pc.principal -- s.principal
      wire s.pred -- z1.principal
      wire pc.m -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 11);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: plus_comm(1, 1) → refl in 16 steps", () => {
  const core = compile(COMM_SYSTEM + `
    graph test {
      let r = root  let pc = plus_comm
      let s1 = Succ  let z1 = Zero  let s2 = Succ  let z2 = Zero
      wire r.principal -- pc.result
      wire pc.principal -- s1.principal
      wire s1.pred -- z1.principal
      wire pc.m -- s2.principal
      wire s2.pred -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 16);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: plus_comm(2, 1) → refl in 29 steps", () => {
  const core = compile(COMM_SYSTEM + `
    graph test {
      let r = root  let pc = plus_comm
      let s1 = Succ  let s2 = Succ  let z1 = Zero
      let s3 = Succ  let z2 = Zero
      wire r.principal -- pc.result
      wire pc.principal -- s1.principal
      wire s1.pred -- s2.principal
      wire s2.pred -- z1.principal
      wire pc.m -- s3.principal
      wire s3.pred -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 29);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: wrong plus_comm proof is caught", () => {
  const source = BASE_SYSTEM + `
    system "Wrong" extend "NatEq" {
      agent dup_nat(principal, copy1, copy2)
      rule dup_nat <> Zero -> {
        let z1 = Zero  let z2 = Zero
        relink left.copy1 z1.principal
        relink left.copy2 z2.principal
      }
      rule dup_nat <> Succ -> {
        let s1 = Succ  let s2 = Succ  let d = dup_nat
        relink left.copy1 s1.principal
        relink left.copy2 s2.principal
        wire s1.pred -- d.copy1
        wire s2.pred -- d.copy2
        relink right.pred d.principal
      }
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
      prove bad_comm(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
        | Zero -> refl
        | Succ(k) -> cong_succ(bad_comm(k, m))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "expected type errors for wrong plus_comm");
});

// ─── plus_assoc Tests ──────────────────────────────────────────────

const ASSOC_SYSTEM = COMM_SYSTEM.trimEnd().replace(/\}$/, "") + `
  prove plus_assoc(a : Nat, b : Nat, c : Nat) -> Eq(add(add(a, b), c), add(a, add(b, c))) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_assoc(k, b, c))
  }
}
`;

Deno.test("deptype: plus_assoc compiles with correct ports", () => {
  const result = compile(ASSOC_SYSTEM);
  const sys = result.systems.get("Comm")!;
  assertEquals(sys.agents.has("plus_assoc"), true);
  const pa = sys.agents.get("plus_assoc")!;
  assertEquals(pa.ports.map((p: { name: string }) => p.name), ["principal", "result", "b", "c"]);
});

Deno.test("deptype: plus_assoc(0, 0, 0) → refl in 3 steps", () => {
  const core = compile(ASSOC_SYSTEM + `
    graph test {
      let r = root  let pa = plus_assoc
      let z1 = Zero  let z2 = Zero  let z3 = Zero
      wire r.principal -- pa.result
      wire pa.principal -- z1.principal
      wire pa.b -- z2.principal
      wire pa.c -- z3.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 3);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: plus_assoc(1, 0, 0) → refl in 5 steps", () => {
  const core = compile(ASSOC_SYSTEM + `
    graph test {
      let r = root  let pa = plus_assoc
      let s = Succ  let z1 = Zero  let z2 = Zero  let z3 = Zero
      wire r.principal -- pa.result
      wire pa.principal -- s.principal
      wire s.pred -- z1.principal
      wire pa.b -- z2.principal
      wire pa.c -- z3.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 5);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: plus_assoc(2, 1, 1) → refl in 9 steps", () => {
  const core = compile(ASSOC_SYSTEM + `
    graph test {
      let r = root  let pa = plus_assoc
      let s1 = Succ  let s2 = Succ  let z1 = Zero
      let s3 = Succ  let z2 = Zero
      let s4 = Succ  let z3 = Zero
      wire r.principal -- pa.result
      wire pa.principal -- s1.principal
      wire s1.pred -- s2.principal
      wire s2.pred -- z1.principal
      wire pa.b -- s3.principal
      wire s3.pred -- z2.principal
      wire pa.c -- s4.principal
      wire s4.pred -- z3.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 9);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("deptype: wrong plus_assoc proof is caught", () => {
  const source = BASE_SYSTEM + `
    system "NatEq2" extend "NatEq" {
      prove bad_assoc(a : Nat, b : Nat, c : Nat) -> Eq(add(add(a, b), c), add(b, add(a, c))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(bad_assoc(k, b, c))
      }
    }
  `;
  const result = compileCore(source);
  // Zero case: Eq(add(b, c), add(b, add(Zero, c))) → Eq(add(b, c), add(b, c)) → refl OK
  // Succ case: left = Succ(add(add(k,b),c)), right = add(b, Succ(add(k,c)))
  //   cong_succ would give Succ(_) on both sides, but right isn't Succ(...)
  assertEquals(result.errors.length > 0, true, "expected type errors for wrong plus_assoc");
});

// ─── Generalized cong Tests ───────────────────────────────────────

Deno.test("deptype: generalized cong works for new constructors", () => {
  // Define a Wrap constructor and cong_wrap — the type checker handles it
  // via the generalized cong_ prefix rule without any special casing
  const result = compile(`
    system "WrapEq" extend "NatEq" {
      agent Wrap(principal, inner)

      agent cong_wrap(principal, result)
      rule cong_wrap <> refl -> {
        let r = refl
        relink left.result r.principal
      }

      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }

      # Uses generalized cong: cong_wrap isn't hardcoded in the type checker,
      # but the cong_ prefix detection handles it automatically.
      # Each case uses cross-lemma call to plus_zero_right.
      prove wrap_pzr(n : Nat) -> Eq(Wrap(add(n, Zero)), Wrap(n)) {
        | Zero -> refl
        | Succ(k) -> cong_wrap(cong_succ(plus_zero_right(k)))
      }
    }
  `);
  const sys = result.systems.get("WrapEq")!;
  assertEquals(sys.agents.has("wrap_pzr"), true);
});
