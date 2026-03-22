// End-to-end tests for dependent type checking in `prove` blocks.
// Verifies that typed prove blocks compile, type-check, and reduce identically
// to their untyped counterparts, and that type errors are caught.

import { assertEquals, assertThrows } from "$std/assert/mod.ts";
import { compileCore, exportProofJSON, exportProofText, exportProofTerm, universeLevel, typeUniverse, type ProofTree } from "@deltanets/lang";
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

// ═══════════════════════════════════════════════════════════════════
// Proof tree generation tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("proof tree: plus_zero_right has correct structure", () => {
  const result = compile(`
    system "PT" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  const tree = result.proofTrees.get("plus_zero_right");
  assertEquals(tree != null, true, "proof tree should exist");
  assertEquals(tree!.name, "plus_zero_right");
  assertEquals(tree!.proposition, "Eq(add(n, Zero), n)");
  assertEquals(tree!.cases.length, 2);

  // Case Zero: refl
  const zero = tree!.cases[0];
  assertEquals(zero.pattern, "Zero");
  assertEquals(zero.bindings.length, 0);
  assertEquals(zero.tree.rule, "refl");
  assertEquals(zero.tree.children.length, 0);

  // Case Succ(k): cong_succ(plus_zero_right(k))
  const succ = tree!.cases[1];
  assertEquals(succ.pattern, "Succ");
  assertEquals(succ.bindings, ["k"]);
  assertEquals(succ.tree.rule, "cong_succ");
  assertEquals(succ.tree.children.length, 1);
  assertEquals(succ.tree.children[0].rule, "IH");
  assertEquals(succ.tree.children[0].children.length, 0);
});

Deno.test("proof tree: trans produces two children", () => {
  const result = compile(`
    system "TransTree" extend "NatEq" {
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

      prove plus_succ_right(a : Nat, b : Nat) -> Eq(add(a, Succ(b)), Succ(add(a, b))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_succ_right(k, b))
      }

      prove plus_comm(a : Nat, b : Nat) -> Eq(add(a, b), add(b, a)) {
        | Zero -> sym(plus_zero_right(b))
        | Succ(k) -> trans(cong_succ(plus_comm(k, b)), sym(plus_succ_right(b, k)))
      }
    }
  `);
  const tree = result.proofTrees.get("plus_comm");
  assertEquals(tree != null, true);

  // Case Succ(k): trans(cong_succ(plus_comm(k, b)), sym(plus_succ_right(b, k)))
  const succ = tree!.cases[1];
  assertEquals(succ.tree.rule, "trans");
  assertEquals(succ.tree.children.length, 2);

  // First child: cong_succ(plus_comm(k, b))
  const left = succ.tree.children[0];
  assertEquals(left.rule, "cong_succ");
  assertEquals(left.children.length, 1);
  assertEquals(left.children[0].rule, "IH");

  // Second child: sym(plus_succ_right(b, k))
  const right = succ.tree.children[1];
  assertEquals(right.rule, "sym");
  assertEquals(right.children.length, 1);
  assertEquals(right.children[0].rule, "plus_succ_right");  // cross-lemma
});

Deno.test("proof tree: untyped prove yields no tree", () => {
  const result = compile(`
    system "Untyped" extend "NatEq" {
      prove plus_zero_right(n : Nat) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  assertEquals(result.proofTrees.has("plus_zero_right"), false);
});

// ═══════════════════════════════════════════════════════════════════
// Interactive proof mode (? holes) tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("hole: ? compiles without error and produces goal in tree", () => {
  const result = compile(`
    system "Hole1" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  const tree = result.proofTrees.get("pzr");
  assertEquals(tree != null, true);
  assertEquals(tree!.hasHoles, true);

  // Zero case should be normal
  assertEquals(tree!.cases[0].tree.rule, "refl");
  assertEquals(tree!.cases[0].tree.isGoal, undefined);

  // Succ case should be a goal node with the required type
  const succ = tree!.cases[1].tree;
  assertEquals(succ.isGoal, true);
  assertEquals(succ.rule, "goal");
  assertEquals(succ.term, "?");
  // Goal type: Eq(add(n, Zero), n) with n=Succ(k) normalizes to Eq(Succ(add(k, Zero)), Succ(k))
  assertEquals(succ.conclusion, "Eq(Succ(add(k, Zero)), Succ(k))");
});

Deno.test("hole: ? inside cong_succ gets correct inner goal", () => {
  const result = compile(`
    system "Hole2" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(?)
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  assertEquals(tree.hasHoles, true);

  const succ = tree.cases[1].tree;
  assertEquals(succ.rule, "cong_succ");
  // The inner hole: cong_succ wraps Eq(Succ(a),Succ(b)), so inner goal is Eq(a,b)
  const hole = succ.children[0];
  assertEquals(hole.isGoal, true);
  assertEquals(hole.conclusion, "Eq(add(k, Zero), k)");
});

Deno.test("hole: ? in trans gets goal from other arg", () => {
  const result = compile(`
    system "Hole3" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }

      prove psr(a : Nat, b : Nat) -> Eq(add(a, Succ(b)), Succ(add(a, b))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(psr(k, b))
      }

      prove pc(a : Nat, b : Nat) -> Eq(add(a, b), add(b, a)) {
        | Zero -> sym(pzr(b))
        | Succ(k) -> trans(?, sym(psr(b, k)))
      }
    }
  `);
  const tree = result.proofTrees.get("pc")!;
  assertEquals(tree.hasHoles, true);

  const succ = tree.cases[1].tree;
  assertEquals(succ.rule, "trans");
  // First arg is ?, second is sym(psr(b,k)) : Eq(Succ(add(b,k)), add(b,Succ(k)))
  // trans(?, q) : Eq(a, c) needs ? : Eq(a, b) where q : Eq(b, c)
  // Goal: Eq(Succ(add(k,b)), add(b,Succ(k))) with q=sym(psr(b,k))
  // q : Eq(Succ(add(b,k)), add(b,Succ(k)))  wait no — sym flips it
  // psr(b,k) : Eq(add(b,Succ(k)), Succ(add(b,k)))
  // sym(psr(b,k)) : Eq(Succ(add(b,k)), add(b,Succ(k)))
  // trans(?, sym(psr(b,k))) needs overall Eq(Succ(add(k,b)), add(b,Succ(k)))
  //   ? : Eq(Succ(add(k,b)), Succ(add(b,k)))
  const hole = succ.children[0];
  assertEquals(hole.isGoal, true);
  assertEquals(hole.conclusion, "Eq(Succ(add(k, b)), Succ(add(b, k)))");
});

Deno.test("hole: all-? prove generates no agent/rules", () => {
  const result = compile(`
    system "HoleNoRules" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `);
  // No agent should be generated for a prove with holes
  const sys = result.systems.get("HoleNoRules")!;
  assertEquals(sys.agents.has("pzr"), false);
  // But proof tree should still be generated
  assertEquals(result.proofTrees.has("pzr"), true);
  assertEquals(result.proofTrees.get("pzr")!.hasHoles, true);

  // Check goal types
  assertEquals(result.proofTrees.get("pzr")!.cases[0].tree.conclusion, "Eq(Zero, Zero)");
  assertEquals(result.proofTrees.get("pzr")!.cases[1].tree.conclusion, "Eq(Succ(add(k, Zero)), Succ(k))");
});

// ─── Proof Search / Auto-fill Tests ─────────────────────────────────

Deno.test("search: ? in Zero case of pzr suggests refl", () => {
  const result = compile(`
    system "Search1" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  // Zero case goal: Eq(Zero, Zero) — refl should be suggested
  const zeroNode = tree.cases[0].tree;
  assertEquals(zeroNode.isGoal, true);
  assertEquals(Array.isArray(zeroNode.suggestions), true);
  assertEquals(zeroNode.suggestions!.includes("refl"), true, `expected refl in suggestions, got: ${zeroNode.suggestions}`);
});

Deno.test("search: ? in Succ case of pzr suggests cong_succ(pzr(k))", () => {
  const result = compile(`
    system "Search2" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  // Succ case goal: Eq(Succ(add(k, Zero)), Succ(k))
  // Should suggest cong_succ(pzr(k))
  const succNode = tree.cases[1].tree;
  assertEquals(succNode.isGoal, true);
  assertEquals(Array.isArray(succNode.suggestions), true);
  assertEquals(
    succNode.suggestions!.includes("cong_succ(pzr(k))"),
    true,
    `expected cong_succ(pzr(k)) in suggestions, got: ${succNode.suggestions}`,
  );
});

Deno.test("search: ? in Zero case of plus_comm suggests sym(pzr(m))", () => {
  const result = compile(`
    system "Search3" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
      prove pc(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `);
  const tree = result.proofTrees.get("pc")!;
  // Zero case goal: Eq(m, add(m, Zero)) — should suggest sym(pzr(m))
  const zeroNode = tree.cases[0].tree;
  assertEquals(zeroNode.isGoal, true);
  assertEquals(
    zeroNode.suggestions!.includes("sym(pzr(m))"),
    true,
    `expected sym(pzr(m)) in suggestions, got: ${zeroNode.suggestions}`,
  );
});

// ═══════════════════════════════════════════════════════════════════
// Sigma types (dependent pairs) tests
// ═══════════════════════════════════════════════════════════════════

const SIGMA_SYSTEM = `
system "SigmaBase" extend "NatEq" {
  agent pair(principal, fst_val, snd_val)
  agent fst(principal, result)
  agent snd(principal, result)

  rule fst <> pair -> {
    relink left.result right.fst_val
    erase right.snd_val
  }
  rule snd <> pair -> {
    relink left.result right.snd_val
    erase right.fst_val
  }
}
`;

Deno.test("sigma: pair(Zero, refl) type-checks for Sigma(Nat, k, Eq(k, Zero))", () => {
  const result = compile(SIGMA_SYSTEM + `
    system "Sigma1" extend "SigmaBase" {
      prove sigma_test(n : Nat) -> Sigma(Nat, k, Eq(k, n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), refl)
      }
    }
  `);
  const sys = result.systems.get("Sigma1")!;
  assertEquals(sys.agents.has("sigma_test"), true);
  // pair should exist as well
  assertEquals(sys.agents.has("pair"), true);
});

Deno.test("sigma: pair with wrong witness is caught", () => {
  const source = BASE_SYSTEM + SIGMA_SYSTEM + `
    system "SigmaBad" extend "SigmaBase" {
      prove bad_sigma(n : Nat) -> Sigma(Nat, k, Eq(k, n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(m, refl)
      }
    }
  `;
  const result = compileCore(source);
  // Succ case: required Sigma(Nat, k, Eq(k, Succ(m))), witness=m → Eq(m, Succ(m))
  // refl needs equal sides: m ≠ Succ(m) → type error
  assertEquals(result.errors.length > 0, true, "expected type error for wrong witness");
});

Deno.test("sigma: proof tree for pair shows ∃-intro rule", () => {
  const result = compile(SIGMA_SYSTEM + `
    system "SigmaTree" extend "SigmaBase" {
      prove sigma_test(n : Nat) -> Sigma(Nat, k, Eq(k, n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), refl)
      }
    }
  `);
  const tree = result.proofTrees.get("sigma_test")!;
  assertEquals(tree.hasHoles, false);

  // Zero case: pair(Zero, refl) → ∃-intro with refl child
  const zero = tree.cases[0].tree;
  assertEquals(zero.rule, "∃-intro");
  assertEquals(zero.children.length, 1);
  assertEquals(zero.children[0].rule, "refl");
});

Deno.test("sigma: ? hole in pair gets correct inner goal", () => {
  const result = compile(SIGMA_SYSTEM + `
    system "SigmaHole" extend "SigmaBase" {
      prove sigma_test(n : Nat) -> Sigma(Nat, k, Eq(k, n)) {
        | Zero -> pair(Zero, ?)
        | Succ(m) -> pair(Succ(m), ?)
      }
    }
  `);
  const tree = result.proofTrees.get("sigma_test")!;
  assertEquals(tree.hasHoles, true);

  // Zero case: pair(Zero, ?) with expected Sigma(Nat, k, Eq(k, Zero))
  // Inner goal: Eq(Zero, Zero) (after subst k=Zero)
  const zeroHole = tree.cases[0].tree.children[0];
  assertEquals(zeroHole.isGoal, true);
  assertEquals(zeroHole.conclusion, "Eq(Zero, Zero)");

  // Succ case: pair(Succ(m), ?) → inner goal Eq(Succ(m), Succ(m))
  const succHole = tree.cases[1].tree.children[0];
  assertEquals(succHole.isGoal, true);
  assertEquals(succHole.conclusion, "Eq(Succ(m), Succ(m))");
});

// ═══════════════════════════════════════════════════════════════════
// Universe levels tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("universe: Type₀ equality provable with refl", () => {
  const result = compile(`
    system "Univ1" extend "NatEq" {
      prove type_refl(n : Nat) -> Eq(Type0, Type0) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  const tree = result.proofTrees.get("type_refl")!;
  assertEquals(tree.proposition, "Eq(Type\u2080, Type\u2080)");
  assertEquals(tree.hasHoles, false);
});

Deno.test("universe: Type alias — Type normalizes to Type₀", () => {
  const result = compile(`
    system "UnivAlias" extend "NatEq" {
      prove type_alias(n : Nat) -> Eq(Type, Type0) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  const tree = result.proofTrees.get("type_alias")!;
  assertEquals(tree.hasHoles, false);
  // Both normalize to Type(0), so refl succeeds
  assertEquals(tree.cases[0].tree.rule, "refl");
});

Deno.test("universe: Type₀ ≠ Type₁ — refl rejected", () => {
  const source = BASE_SYSTEM + `
    system "UnivBad" extend "NatEq" {
      prove type_bad(n : Nat) -> Eq(Type0, Type1) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "expected error for Type\u2080 \u2260 Type\u2081");
});

Deno.test("universe: subscript display in proof tree", () => {
  const result = compile(`
    system "UnivDisplay" extend "NatEq" {
      prove u_refl(n : Nat) -> Eq(Type1, Type1) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  const tree = result.proofTrees.get("u_refl")!;
  assertEquals(tree.proposition, "Eq(Type\u2081, Type\u2081)");
});

Deno.test("universe: universeLevel computation", () => {
  // Type / Type0 → level 0
  assertEquals(universeLevel({ kind: "ident", name: "Type" }), 0);
  assertEquals(universeLevel({ kind: "ident", name: "Type0" }), 0);
  // Type1 → level 1
  assertEquals(universeLevel({ kind: "ident", name: "Type1" }), 1);
  // Type2 → level 2
  assertEquals(universeLevel({ kind: "ident", name: "Type2" }), 2);
  // Nat → not a universe
  assertEquals(universeLevel({ kind: "ident", name: "Nat" }), -1);
});

Deno.test("universe: typeUniverse computation", () => {
  // Nat lives in Type₀
  assertEquals(typeUniverse({ kind: "ident", name: "Nat" }), 0);
  // Type₀ lives in Type₁
  assertEquals(typeUniverse({ kind: "ident", name: "Type0" }), 1);
  // Type₁ lives in Type₂
  assertEquals(typeUniverse({ kind: "ident", name: "Type1" }), 2);
  // Eq(a, b) lives in Type₀
  assertEquals(typeUniverse({ kind: "call", name: "Eq", args: [
    { kind: "ident", name: "a" }, { kind: "ident", name: "b" }
  ] }), 0);
  // W(A, B) lives in Type(max(level(A), level(B)))
  assertEquals(typeUniverse({ kind: "call", name: "W", args: [
    { kind: "ident", name: "Nat" }, { kind: "ident", name: "Bool" }
  ] }), 0);
  assertEquals(typeUniverse({ kind: "call", name: "W", args: [
    { kind: "ident", name: "Type0" }, { kind: "ident", name: "Nat" }
  ] }), 1);
});

// ═══════════════════════════════════════════════════════════════════
// W-types (well-founded trees) tests
// ═══════════════════════════════════════════════════════════════════

const W_SYSTEM = `
system "WBase" extend "NatEq" {
  agent Sup(principal, label, children)
  agent wrec(principal, result, step)

  agent cong_sup(principal, result, label_proof)
  rule cong_sup <> refl -> {
    let r = refl
    relink left.result r.principal
    erase left.label_proof
  }

  rule wrec <> Sup -> {
    # wrec(Sup(a, f), step) → step(a, f)
    relink left.result left.step
    erase right.label
    erase right.children
  }
}
`;

Deno.test("w-type: Sup equality provable with refl", () => {
  const result = compile(W_SYSTEM + `
    system "W1" extend "WBase" {
      prove sup_refl(n : Nat) -> Eq(Sup(n, Zero), Sup(n, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  const tree = result.proofTrees.get("sup_refl")!;
  assertEquals(tree.hasHoles, false);
});

Deno.test("w-type: cong_sup infers correct type", () => {
  const result = compile(W_SYSTEM + `
    system "W2" extend "WBase" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }

      prove sup_cong(n : Nat) -> Eq(Sup(Zero, add(n, Zero)), Sup(Zero, n)) {
        | Zero -> refl
        | Succ(k) -> cong_sup(plus_zero_right(Succ(k)), Zero)
      }
    }
  `);
  const tree = result.proofTrees.get("sup_cong")!;
  assertEquals(tree.hasHoles, false);
});

Deno.test("w-type: wrec(Sup(a, f), step) normalizes to step(a, f)", () => {
  const result = compile(W_SYSTEM + `
    system "W3" extend "WBase" {
      prove wrec_beta(n : Nat) -> Eq(wrec(Sup(n, Zero), id), id(n, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  const tree = result.proofTrees.get("wrec_beta")!;
  assertEquals(tree.hasHoles, false);
});

Deno.test("w-type: wrec normalization mismatch caught", () => {
  const source = BASE_SYSTEM + W_SYSTEM + `
    system "WBad" extend "WBase" {
      prove wrec_bad(n : Nat) -> Eq(wrec(Sup(n, Zero), id), id(Zero, n)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "expected error for wrec mismatch");
});

Deno.test("sigma: snd in proof position is not yet supported", () => {
  const source = BASE_SYSTEM + SIGMA_SYSTEM + `
    system "SigmaAdd" extend "SigmaBase" {
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
      prove sigma_add(n : Nat) -> Sigma(Nat, k, Eq(add(k, Zero), n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), cong_succ(snd(sigma_add(m))))
      }
    }
  `;
  const result = compileCore(source);
  // snd(sigma_add(m)) is an unknown proof combinator — type error expected
  assertEquals(result.errors.length > 0, true, "expected type error for snd in proof position");
});

Deno.test("sigma: fst/snd reduction in INet", () => {
  const core = compile(SIGMA_SYSTEM + `
    system "SigmaReduce" extend "SigmaBase" {
      prove sigma_id(n : Nat) -> Sigma(Nat, k, Eq(k, n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), refl)
      }
    }
    graph test {
      let r = root
      let f = fst
      let s = sigma_id
      let z = Zero
      wire r.principal -- f.result
      wire f.principal -- s.result
      wire s.principal -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  // fst(sigma_id(Zero)) → fst(pair(Zero, refl)) → Zero
  assertEquals(readRootType(g.graph), "Zero");
});

// ═══════════════════════════════════════════════════════════════════
// Transport / J elimination (subst) tests
// ═══════════════════════════════════════════════════════════════════

const SUBST_SYSTEM = `
system "SubstTest" extend "NatEq" {
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

  prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(pzr(k))
  }

  prove psr(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
    | Zero -> refl
    | Succ(k) -> cong_succ(psr(k, m))
  }

  prove succ_one(n : Nat) -> Eq(add(n, Succ(Zero)), Succ(n)) {
    | Zero -> refl
    | Succ(k) -> cong_succ(subst(pzr(k), psr(k, Zero)))
  }
}
`;

Deno.test("subst: subst(pzr(k), psr(k, Zero)) rewrites type correctly", () => {
  const result = compile(SUBST_SYSTEM);
  const sys = result.systems.get("SubstTest")!;
  assertEquals(sys.agents.has("succ_one"), true);
});

Deno.test("subst: proof tree shows subst rule with two children", () => {
  const result = compile(SUBST_SYSTEM);
  const tree = result.proofTrees.get("succ_one")!;
  const succ = tree.cases[1].tree; // Succ case
  assertEquals(succ.rule, "cong_succ");
  assertEquals(succ.children.length, 1);
  // Inner: subst(pzr(k), psr(k, Zero))
  const substNode = succ.children[0];
  assertEquals(substNode.rule, "subst");
  assertEquals(substNode.children.length, 2);
  assertEquals(substNode.children[0].rule, "pzr");       // cross-lemma
  assertEquals(substNode.children[1].rule, "psr");       // cross-lemma
});

Deno.test("subst: wrong subst argument is caught", () => {
  const source = BASE_SYSTEM + `
    system "SubstBad" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
      # subst(pzr(n), refl) doesn't help — refl type has no add(n,Zero) to replace
      prove bad(n : Nat) -> Eq(add(n, Succ(Zero)), Succ(n)) {
        | Zero -> refl
        | Succ(k) -> subst(pzr(k), refl)
      }
    }
  `;
  const result = compileCore(source);
  // subst(pzr(k), refl): a=add(k,Zero), b=k, T=Eq(_refl_a, _refl_a)
  // T[add(k,Zero):=k] = Eq(_refl_a, _refl_a) — no match
  // Expected: Eq(Succ(add(k, Succ(Zero))), Succ(Succ(k))) — mismatch
  assertEquals(result.errors.length > 0, true, "expected type error for bad subst");
});

Deno.test("subst: succ_one(1) reduces to refl", () => {
  const core = compile(SUBST_SYSTEM + `
    graph test {
      let r = root
      let so = succ_one
      let s = Succ
      let z = Zero
      wire r.principal -- so.result
      wire so.principal -- s.principal
      wire s.pred -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(readRootType(g.graph), "refl");
});

// ═══════════════════════════════════════════════════════════════════
// Proof term export tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("export: JSON round-trips ProofTree", () => {
  const result = compile(`
    system "Ex" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  const json = exportProofJSON(tree);
  const parsed = JSON.parse(json);
  assertEquals(parsed.name, "pzr");
  assertEquals(parsed.proposition, "Eq(add(n, Zero), n)");
  assertEquals(parsed.hasHoles, false);
  assertEquals(parsed.cases.length, 2);
  assertEquals(parsed.cases[0].pattern, "Zero");
  assertEquals(parsed.cases[1].pattern, "Succ");
  assertEquals(parsed.cases[1].tree.rule, "cong_succ");
});

Deno.test("export: text format produces readable certificate", () => {
  const result = compile(`
    system "Ex" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  const text = exportProofText(tree);
  // Should contain key elements
  assertEquals(text.includes("theorem pzr"), true);
  assertEquals(text.includes("[VERIFIED]"), true);
  assertEquals(text.includes("case Zero:"), true);
  assertEquals(text.includes("case Succ(k):"), true);
  assertEquals(text.includes("refl"), true);
  assertEquals(text.includes("cong_succ"), true);
});

Deno.test("export: text format marks incomplete proofs", () => {
  const result = compile(`
    system "Ex" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  const text = exportProofText(tree);
  assertEquals(text.includes("[INCOMPLETE]"), true);
  assertEquals(text.includes("? goal"), true);
});

Deno.test("export: term format produces Agda-like notation", () => {
  const result = compile(`
    system "Ex" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  const term = exportProofTerm(tree);
  const lines = term.split("\n");
  assertEquals(lines[0], "pzr : Eq(add(n, Zero), n)");
  assertEquals(lines[1], "pzr Zero = refl");
  assertEquals(lines[2], "pzr (Succ k) = cong_succ(pzr(k))");
});

Deno.test("export: JSON includes suggestions for holes", () => {
  const result = compile(`
    system "Ex" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `);
  const tree = result.proofTrees.get("pzr")!;
  const json = exportProofJSON(tree);
  const parsed = JSON.parse(json);
  assertEquals(parsed.hasHoles, true);
  // Zero case should have suggestions
  assertEquals(Array.isArray(parsed.cases[0].tree.suggestions), true);
  assertEquals(parsed.cases[0].tree.suggestions.includes("refl"), true);
});

// ═══════════════════════════════════════════════════════════════════
// Tactic combinators tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("tactic: exact(refl) is transparent wrapper", () => {
  const result = compile(`
    system "Tactic1" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> exact(refl)
        | Succ(k) -> exact(cong_succ(pzr(k)))
      }
    }
  `);
  const sys = result.systems.get("Tactic1")!;
  assertEquals(sys.agents.has("pzr"), true);
  const tree = result.proofTrees.get("pzr")!;
  assertEquals(tree.hasHoles, false);
  assertEquals(tree.cases[0].tree.rule, "exact");
});

Deno.test("tactic: apply(f, args) desugars to f(args)", () => {
  const result = compile(`
    system "Tactic2" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> apply(cong_succ, pzr(k))
      }
    }
  `);
  const sys = result.systems.get("Tactic2")!;
  assertEquals(sys.agents.has("pzr"), true);
  const tree = result.proofTrees.get("pzr")!;
  assertEquals(tree.hasHoles, false);
});

Deno.test("tactic: rewrite validates goal contextually", () => {
  const result = compile(`
    system "Tactic3" extend "NatEq" {
      prove rw_pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> rewrite(rw_pzr(k))
      }
    }
  `);
  const tree = result.proofTrees.get("rw_pzr")!;
  assertEquals(tree.hasHoles, false);
  assertEquals(tree.cases[1].tree.rule, "rewrite");
});

Deno.test("tactic: rewrite with wrong proof is caught", () => {
  const source = BASE_SYSTEM + `
    system "TacticBad" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
      prove bad_rewrite(n : Nat) -> Eq(Succ(n), Zero) {
        | Zero -> rewrite(pzr(Zero))
        | Succ(k) -> rewrite(pzr(k))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "expected error for invalid rewrite");
});

Deno.test("tactic: rewrite proof tree shows rule", () => {
  const result = compile(`
    system "TacticTree" extend "NatEq" {
      prove rw2(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> rewrite(rw2(k))
      }
    }
  `);
  const tree = result.proofTrees.get("rw2")!;
  const succ = tree.cases[1].tree;
  assertEquals(succ.rule, "rewrite");
  assertEquals(succ.children.length, 1);
});

// ═══════════════════════════════════════════════════════════════════
// Include-aware proof context tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("include-aware: extend inherits proved context from base", () => {
  // System A proves pzr, then system B extends A and uses pzr as a cross-lemma
  const result = compile(`
    system "IncBase" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
    system "IncExt" extend "IncBase" {
      prove double_pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  // double_pzr should type-check because pzr is in scope from IncBase
  const tree = result.proofTrees.get("double_pzr")!;
  assertEquals(tree.hasHoles, false);
});

Deno.test("include-aware: compose merges proved context from components", () => {
  const result = compile(`
    system "CompA" extend "NatEq" {
      prove lemma_a(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(lemma_a(k))
      }
    }
    system "CompB" extend "NatEq" {
      prove lemma_b(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(lemma_b(k))
      }
    }
    system "Merged" = compose "CompA" + "CompB" {
      prove uses_both(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(lemma_a(k))
      }
    }
  `);
  // uses_both should work because lemma_a is available from CompA
  const tree = result.proofTrees.get("uses_both")!;
  assertEquals(tree.hasHoles, false);
});

// ─── Additional negative tests ─────────────────────────────────────

Deno.test("deptype: refl on different constructors is caught", () => {
  // Eq(Zero, Succ(Zero)) — refl should fail since sides differ
  const source = BASE_SYSTEM + `
    system "Bad" extend "NatEq" {
      prove bad_eq() -> Eq(Zero, Succ(Zero)) {
        refl
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "refl on Zero ≠ Succ(Zero) should error");
});

Deno.test("deptype: single-case prove compiles when no other cases reveal more constructors", () => {
  // Only match Zero, missing Succ case — accepted because no other prove block
  // in this system declares Succ as a Nat constructor
  const source = BASE_SYSTEM + `
    system "Incomplete" extend "NatEq" {
      prove bad_pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, "accepted — exhaustiveness only checks known constructors");
});

Deno.test("deptype: using undefined lemma is caught", () => {
  const source = BASE_SYSTEM + `
    system "NoLemma" extend "NatEq" {
      prove bad(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(nonexistent_lemma(k))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "undefined lemma should error");
});

Deno.test("deptype: applying proof term to wrong type is caught", () => {
  // cong_succ expects Eq(a,b) but gets Nat
  const source = BASE_SYSTEM + `
    system "WrongApp" extend "NatEq" {
      prove bad_app(n : Nat) -> Eq(Succ(n), Succ(n)) {
        | Zero -> refl
        | Succ(k) -> cong_succ(k)
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "cong_succ applied to Nat should error");
});

Deno.test("deptype: universe level mismatch in prove return type", () => {
  // Try to prove Type₁ = Type₀ with refl — should be caught
  const source = BASE_SYSTEM + `
    system "UniMismatch" extend "NatEq" {
      prove bad_uni() -> Eq(Type₁, Type₀) {
        refl
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "Type₁ ≠ Type₀ refl should error");
});

// ─── Exhaustiveness Checking ───────────────────────────────────────

Deno.test("deptype: exhaustiveness — missing Succ case is caught", () => {
  const source = BASE_SYSTEM + `
    system "MissingCase" extend "NatEq" {
      prove only_zero(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
      }

      prove full_proof(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(full_proof(k))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "missing Succ case should error");
  assertEquals(result.errors[0].includes("non-exhaustive"), true, "error should mention non-exhaustive");
  assertEquals(result.errors[0].includes("Succ"), true, "error should mention missing Succ");
});

Deno.test("deptype: exhaustiveness — complete pattern match is fine", () => {
  const result = compile(`
    system "Complete" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  const sys = result.systems.get("Complete")!;
  assertEquals(sys.agents.has("pzr"), true);
});

Deno.test("deptype: exhaustiveness — untyped prove skips check", () => {
  // Without type annotation on first param, no exhaustiveness check
  const result = compile(`
    system "UntypedPartial" extend "NatEq" {
      prove partial_proof(n) {
        | Zero -> refl
      }
    }
  `);
  const sys = result.systems.get("UntypedPartial")!;
  assertEquals(sys.agents.has("partial_proof"), true);
});

// ─── Sigma Elimination (fst/snd in proof position) ─────────────────

Deno.test("deptype: snd extracts proof from pair", () => {
  // snd(pair(Zero, refl)) : Eq(Zero, Zero) — use snd to extract the proof
  const result = compile(`
    system "SndTest" extend "NatEq" {
      prove snd_test(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> snd(pair(Zero, refl))
        | Succ(k) -> cong_succ(snd_test(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0);
});

Deno.test("deptype: fst on non-Sigma type errors", () => {
  const source = BASE_SYSTEM + `
    system "FstBad" extend "NatEq" {
      prove fst_bad(n : Nat) -> Eq(n, n) {
        | Zero -> fst(refl)
        | Succ(k) -> cong_succ(fst_bad(k))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "fst on Eq should error");
});

Deno.test("deptype: snd on non-Sigma type errors", () => {
  const source = BASE_SYSTEM + `
    system "SndBad" extend "NatEq" {
      prove snd_bad(n : Nat) -> Eq(n, n) {
        | Zero -> snd(refl)
        | Succ(k) -> cong_succ(snd_bad(k))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "snd on Eq should error");
});

// ─── Induction Tactic ──────────────────────────────────────────────

Deno.test("deptype: induction(n) expands to case arms with holes", () => {
  // A sibling prove block establishes Zero/Succ as constructors of Nat.
  // induction(n) should then expand into | Zero -> ? | Succ(pred) -> ?
  const result = compile(`
    system "InductHole" extend "NatEq" {
      prove refl_proof(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(refl_proof(k))
      }
      prove ind_test(n : Nat) -> Eq(add(n, Zero), n) {
        induction(n)
      }
    }
  `);
  const sys = result.systems.get("InductHole")!;
  // Agent NOT generated because all cases are holes
  assertEquals(sys.agents.has("ind_test"), false);
  // But refl_proof should be generated
  assertEquals(sys.agents.has("refl_proof"), true);
});

Deno.test("deptype: induction on unknown variable errors", () => {
  const source = BASE_SYSTEM + `
    system "InductBadVar" extend "NatEq" {
      prove bad_ind(n : Nat) -> Eq(n, n) {
        induction(m)
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "induction on unknown var should error");
});

Deno.test("deptype: induction on untyped variable errors", () => {
  const source = BASE_SYSTEM + `
    system "InductNoType" extend "NatEq" {
      prove bad_ind(n) -> Eq(n, n) {
        induction(n)
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "induction on untyped var should error");
});
