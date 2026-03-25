// ═══════════════════════════════════════════════════════════════════════════
// Showcase: A comprehensive demonstration of the Rocq-like dependent type
// theory prover built on interaction nets.
//
// This single file exercises the breadth of the system in 15 cohesive tests:
//   1.  Data types, agents, compute rules
//   2.  Inductive proofs (prove blocks)
//   3.  Lean-style theorem/lemma syntax
//   4.  @[simp] / @[auto] attributes + tactic automation
//   5.  omega solver (linear arithmetic)
//   6.  decide tactic (ground computation)
//   7.  Ring tactic (polynomial normalization)
//   8.  Sections with variable auto-abstraction
//   9.  Scoped notations
//  10.  Type classes and instances
//  11.  Coinductive types (codata) with productivity
//  12.  Mutual inductive types
//  13.  Programs with termination obligations
//  14.  Deep pattern matching
//  15.  Module composition (compose)
// ═══════════════════════════════════════════════════════════════════════════

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert, collectRules, collectAgentPorts, reduceAll, readNat } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// ─── 1. Data types, agents, compute rules ──────────────────────────
// Demonstrates: data declarations with constructors, agent definitions,
// interaction rules, and compute rules for the type checker's normalizer.

Deno.test("showcase 01: data types with agents and compute rules", () => {
  const result = compileAndAssert(BASE + `
system "Arith" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  data Bool { | True | False }
  data List(A) { | Nil | Cons(head : A, tail : List(A)) }

  # Multiplication via repeated addition
  agent mul(principal, result, accum)
  rule mul <> Zero -> {
    erase left.accum
    let z = Zero
    relink left.result z.principal
  }
  rule mul <> Succ -> {
    let a = add
    let m = mul
    relink left.result a.result
    relink left.accum a.accum
    wire a.principal -- m.result
    relink right.pred m.principal
    relink left.accum m.accum
  }
  compute mul(Zero, y) = Zero
  compute mul(Succ(k), y) = add(y, mul(k, y))

  # Boolean negation
  agent not(principal, result)
  rule not <> True  -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True   relink left.result t.principal }
  compute not(True) = False
  compute not(False) = True
}
`);
  const sys = result.systems.get("Arith")!;
  assertEquals(sys.agents.has("mul"), true);
  assertEquals(sys.agents.has("not"), true);
  assertEquals(sys.agents.has("Zero"), true);
  assertEquals(sys.agents.has("Cons"), true);
});

// ─── 2. Inductive proofs (prove blocks) ────────────────────────────
// Demonstrates: structural induction, recursive calls, congruence lemmas,
// and the conv tactic for goals that reduce by computation alone.

Deno.test("showcase 02: inductive proofs by structural recursion", () => {
  const result = compileAndAssert(BASE + `
system "Proofs" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # add(Zero, n) = n holds by computation alone
  prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> conv
    | Succ(k) -> conv
  }

  # add(n, Zero) = n requires induction
  prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(add_zero_right(k))
  }

  # add(n, Succ(m)) = Succ(add(n, m))
  prove add_succ_right(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
    | Zero -> refl
    | Succ(k) -> cong_succ(add_succ_right(k, m))
  }
}
`);
  const sys = result.systems.get("Proofs")!;
  assertEquals(sys.provedCtx.has("add_zero_left"), true);
  assertEquals(sys.provedCtx.has("add_zero_right"), true);
  assertEquals(sys.provedCtx.has("add_succ_right"), true);
});

// ─── 3. Lean-style theorem/lemma syntax ────────────────────────────
// Demonstrates: theorem keyword, := by, =>, shared type bindings (n m : Nat),
// direct proof terms (:= refl), and induction ... with syntax.

Deno.test("showcase 03: Lean-style theorem and lemma declarations", () => {
  const result = compileAndAssert(BASE + `
system "LeanStyle" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Direct proof term — no case analysis needed
  theorem refl_id (n : Nat) : Eq(n, n) := refl

  # Lean-style case arms with =>
  theorem plus_zero (n : Nat) : Eq(add(n, Zero), n) := by
    | Zero => refl
    | Succ(k) => cong_succ(plus_zero(k))

  # Shared type bindings: (n m : Nat) means both have type Nat
  theorem plus_succ (n m : Nat) : Eq(add(n, Succ(m)), Succ(add(n, m))) := by
    | Zero => refl
    | Succ(k) => cong_succ(plus_succ(k, m))

  # lemma is an alias for theorem
  lemma plus_zero_left (n : Nat) : Eq(add(Zero, n), n) := refl

  # induction ... with syntax
  theorem plus_zero_v2 (n : Nat) : Eq(add(n, Zero), n) := by
    induction n with
    | Zero => refl
    | Succ(k) => cong_succ(plus_zero_v2(k))
}
`);
  const sys = result.systems.get("LeanStyle")!;
  assertEquals(sys.provedCtx.has("refl_id"), true);
  assertEquals(sys.provedCtx.has("plus_zero"), true);
  assertEquals(sys.provedCtx.has("plus_succ"), true);
  assertEquals(sys.provedCtx.has("plus_zero_left"), true);
  assertEquals(sys.provedCtx.has("plus_zero_v2"), true);
});

// ─── 4. @[simp] / @[auto] attributes + tactic automation ──────────
// Demonstrates: attribute-annotated lemmas that register into hint databases,
// then simp, auto, and eauto tactics that use those hints automatically.

Deno.test("showcase 04: simp/auto attributes and tactic automation", () => {
  const result = compileAndAssert(BASE + `
system "Automation" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Register as simp lemma — simp tactic can now apply this automatically
  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }

  # Register as auto lemma
  @[auto] prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_left(m))
  }

  # simp solves add(n, Zero) = n by finding add_zero_right in the hint DB
  prove simplified(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(simplified(k))
  }

  # auto solves add(Zero, n) = n by finding add_zero_left in the hint DB
  prove automated(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> auto
    | Succ(k) -> cong_succ(automated(k))
  }

  # eauto with backtracking search
  prove eautomated(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> eauto
    | Succ(k) -> cong_succ(eautomated(k))
  }

  # Nested simplification — simp applies add_zero_right twice
  prove double_simp(n : Nat) -> Eq(add(add(n, Zero), Zero), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(double_simp(k))
  }
}
`);
  const sys = result.systems.get("Automation")!;
  assertEquals(sys.provedCtx.has("simplified"), true);
  assertEquals(sys.provedCtx.has("automated"), true);
  assertEquals(sys.provedCtx.has("eautomated"), true);
  assertEquals(sys.provedCtx.has("double_simp"), true);
});

// ─── 5. omega solver (linear arithmetic) ──────────────────────────
// Demonstrates: the omega tactic that decides equalities over Nat
// by normalizing linear arithmetic expressions.

Deno.test("showcase 05: omega solver for linear arithmetic", () => {
  const result = compileAndAssert(BASE + `
system "Omega" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Ground fact: 1 + 1 = 2
  prove one_plus_one(n : Nat) -> Eq(add(Succ(Zero), Succ(Zero)), Succ(Succ(Zero))) {
    | Zero -> omega
    | Succ(k) -> omega
  }

  # add(Zero, n) = n — omega handles the base case and step
  prove omega_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> omega
    | Succ(k) -> omega
  }

  # add(Succ(Zero), n) = Succ(n) — omega normalizes +1
  prove omega_add_one(n : Nat) -> Eq(add(Succ(Zero), n), Succ(n)) {
    | Zero -> omega
    | Succ(k) -> omega
  }

  # Succ(n) = Succ(n) — trivial but omega handles it
  prove omega_succ_id(n : Nat) -> Eq(Succ(n), Succ(n)) {
    | Zero -> omega
    | Succ(k) -> omega
  }
}
`);
  const sys = result.systems.get("Omega")!;
  assertEquals(sys.provedCtx.has("one_plus_one"), true);
  assertEquals(sys.provedCtx.has("omega_zero_left"), true);
  assertEquals(sys.provedCtx.has("omega_add_one"), true);
  assertEquals(sys.provedCtx.has("omega_succ_id"), true);
});

// ─── 6. decide tactic (ground computation) ─────────────────────────
// Demonstrates: the decide tactic that fully normalizes ground terms
// and checks definitional equality.

Deno.test("showcase 06: decide tactic for ground computation", () => {
  const result = compileAndAssert(BASE + `
system "Decide" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Ground: 0 + 0 = 0
  prove zero_plus_zero(n : Nat) -> Eq(add(Zero, Zero), Zero) {
    | Zero -> decide
    | Succ(k) -> decide
  }

  # Ground: 2 + 1 = 3
  prove two_plus_one(n : Nat) -> Eq(add(Succ(Succ(Zero)), Succ(Zero)), Succ(Succ(Succ(Zero)))) {
    | Zero -> decide
    | Succ(k) -> decide
  }
}
`);
  const sys = result.systems.get("Decide")!;
  assertEquals(sys.provedCtx.has("zero_plus_zero"), true);
  assertEquals(sys.provedCtx.has("two_plus_one"), true);
});

// ─── 7. Ring tactic (polynomial normalization) ─────────────────────
// Demonstrates: ring declarations that register algebraic structure,
// and the ring tactic that normalizes both sides into canonical polynomial
// form (sum of sorted monomials) to prove identities.

Deno.test("showcase 07: ring tactic for algebraic identities", () => {
  const result = compileAndAssert(BASE + `
system "Ring" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  agent mul(principal, result, accum)
  compute mul(Zero, y) = Zero
  compute mul(Succ(k), y) = add(y, mul(k, y))

  # Register Nat as a commutative ring
  ring Nat { zero = Zero, add = add, mul = mul }

  # a = a — trivial polynomial identity
  prove ring_refl(a : Nat) -> Eq(a, a) {
    | Zero -> ring
    | Succ(k) -> ring
  }

  # Commutativity: add(a, Zero) = add(Zero, a)
  prove ring_add_comm_zero(a : Nat) -> Eq(add(a, Zero), add(Zero, a)) {
    | Zero -> ring
    | Succ(k) -> ring
  }

  # Associativity: add(add(0, b), c) = add(0, add(b, c))
  prove ring_add_assoc(b : Nat, c : Nat) -> Eq(add(add(Zero, b), c), add(Zero, add(b, c))) {
    | Zero -> ring
    | Succ(k) -> ring
  }
}
`);
  const sys = result.systems.get("Ring")!;
  assertEquals(sys.provedCtx.has("ring_refl"), true);
  assertEquals(sys.provedCtx.has("ring_add_comm_zero"), true);
  assertEquals(sys.provedCtx.has("ring_add_assoc"), true);
});

// ─── 8. Sections with variable auto-abstraction ───────────────────
// Demonstrates: section blocks that declare variables (A : Type) which
// are automatically lifted into implicit parameters of inner declarations.

Deno.test("showcase 08: sections with variable auto-abstraction", () => {
  const result = compileAndAssert(BASE + `
system "Sections" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Section introduces a shared variable; inner proves get it as implicit param
  section Arithmetic {
    variable(n : Nat)

    prove add_zero(n : Nat) -> Eq(add(n, Zero), n) {
      | Zero -> refl
      | Succ(k) -> cong_succ(add_zero(k))
    }

    prove refl_n(n : Nat) -> Eq(n, n) {
      | Zero -> refl
      | Succ(k) -> cong_succ(refl_n(k))
    }
  }

  # Nested sections accumulate variables
  section Outer {
    variable(a : Nat)
    section Inner {
      variable(b : Nat)

      prove inner_refl(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(inner_refl(k))
      }
    }
  }

  # Data types inside sections get the variable as type parameter
  section Parametric {
    variable(A : Type)

    data Wrapper {
      | Wrap(value : A)
    }
  }
}
`);
  const sys = result.systems.get("Sections")!;
  assertEquals(sys.provedCtx.has("add_zero"), true);
  assertEquals(sys.provedCtx.has("refl_n"), true);
  assertEquals(sys.provedCtx.has("inner_refl"), true);
  assertEquals(sys.agents.has("Wrap"), true);
});

// ─── 9. Scoped notations ──────────────────────────────────────────
// Demonstrates: notation declarations (binary infix + mixfix), precedence
// and associativity, and scopes that keep notations local.

Deno.test("showcase 09: scoped notations with precedence", () => {
  const result = compileAndAssert(BASE + `
system "Notations" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  agent mul(principal, result, accum)
  compute mul(Zero, y) = Zero
  compute mul(Succ(k), y) = add(mul(k, y), y)

  # Scope-local notations: + and * are only active inside nat_scope
  scope "nat_scope" {
    notation "+" = add (prec 50, left)
    notation "*" = mul (prec 60, left)

    # Uses infix notation n + Zero desugared to add(n, Zero)
    prove scoped_plus_zero(n : Nat) -> Eq(n + Zero, add(n, Zero)) {
      | Zero -> refl
      | Succ(k) -> refl
    }
  }

  # Outside scope, notation is not active — must use add(...) directly
  prove outside_scope(n : Nat) -> Eq(add(n, Zero), add(n, Zero)) {
    | Zero -> refl
    | Succ(k) -> refl
  }

  # Global notation (not in a scope)
  notation "+" = add (prec 50, left)

  prove global_notation(n : Nat) -> Eq(n + Zero, n + Zero) {
    | Zero -> refl
    | Succ(k) -> refl
  }
}
`);
  const sys = result.systems.get("Notations")!;
  assertEquals(sys.provedCtx.has("scoped_plus_zero"), true);
  assertEquals(sys.provedCtx.has("outside_scope"), true);
  assertEquals(sys.provedCtx.has("global_notation"), true);
});

// ─── 10. Type classes and instances ────────────────────────────────
// Demonstrates: class declarations with methods, instance declarations
// that provide implementations, and compute rules generated from instances.

Deno.test("showcase 10: type classes and instances", () => {
  const result = compileAndAssert(BASE + `
system "Typeclasses" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  data Bool { | True | False }

  # A type class with a single method
  class Show(A) { show : A }

  # An agent implementing the method
  agent showNat(principal, result)
  compute showNat(n) = n

  # Instance: Nat has a Show implementation
  instance Show(Nat) { show = showNat }

  # A class with multiple methods
  class Monoid(A) { empty : A, append : A }

  agent natEmpty(principal)
  agent natAppend(principal, result, second)

  instance Monoid(Nat) { empty = natEmpty, append = natAppend }
}
`);
  const sys = result.systems.get("Typeclasses")!;
  assertEquals(sys.classes !== undefined && sys.classes!.has("Show"), true);
  assertEquals(sys.classes !== undefined && sys.classes!.has("Monoid"), true);
});

// ─── 11. Coinductive types (codata) with productivity ──────────────
// Demonstrates: codata declarations that generate guard agents and
// observation agents, plus prove blocks that construct infinite streams.

Deno.test("showcase 11: coinductive streams with observations", () => {
  const result = compileAndAssert(BASE + `
system "Codata" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Stream(A) is coinductive: observed via head and tail
  codata Stream(A) { head : A, tail : Stream(A) }

  # repeat(n) produces the infinite stream n, n, n, ...
  prove repeat(n : Nat) -> Stream(Nat) {
    | Zero -> guard_stream(Zero, repeat(Zero))
    | Succ(k) -> guard_stream(Succ(k), repeat(Succ(k)))
  }

  # Observation: head of guard_stream reduces by computation
  prove head_repeat(n : Nat) -> Eq(head(guard_stream(n, guard_stream(n, repeat(n)))), n) {
    | Zero -> conv
    | Succ(k) -> conv
  }
}
`);
  const sys = result.systems.get("Codata")!;
  assertEquals(sys.agents.has("guard_stream"), true);
  assertEquals(sys.agents.has("head"), true);
  assertEquals(sys.agents.has("tail"), true);
  assertEquals(sys.provedCtx.has("repeat"), true);
  assertEquals(sys.provedCtx.has("head_repeat"), true);
});

// ─── 12. Mutual inductive types ───────────────────────────────────
// Demonstrates: mutual blocks defining types that reference each other,
// and mutual prove blocks with cross-calls that are structurally decreasing.

Deno.test("showcase 12: mutual inductive types (Even/Odd)", () => {
  const result = compileAndAssert(BASE + `
system "Mutual" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }

  # Even and Odd reference each other
  mutual {
    data Even {
      | EZero
      | ESucc(pred : Odd)
    }
    data Odd {
      | OSucc(pred : Even)
    }
  }

  # Mutual proofs with structurally decreasing cross-calls
  mutual {
    prove even_trivial(n : Even) -> Eq(Zero, Zero) {
      | EZero -> refl
      | ESucc(p) -> odd_trivial(p)
    }
    prove odd_trivial(n : Odd) -> Eq(Zero, Zero) {
      | OSucc(p) -> even_trivial(p)
    }
  }
}
`);
  const sys = result.systems.get("Mutual")!;
  assertEquals(sys.agents.has("EZero"), true);
  assertEquals(sys.agents.has("ESucc"), true);
  assertEquals(sys.agents.has("OSucc"), true);
  assertEquals(sys.provedCtx.has("even_trivial"), true);
  assertEquals(sys.provedCtx.has("odd_trivial"), true);
});

// ─── 13. Programs with termination ────────────────────────────────
// Demonstrates: program declarations (dependent pattern matching with
// proof obligations), measure-based termination, and coexistence with prove.

Deno.test("showcase 13: programs with termination and obligations", () => {
  const result = compileAndAssert(BASE + `
system "Programs" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Simple program — structural recursion (default wf)
  program double(n : Nat) -> Nat {
    | Zero -> Zero
    | Succ(k) -> Succ(Succ(double(k)))
  }

  # Program with explicit measure annotation
  program halve(n : Nat) -> Nat {
    measure(n)
    | Zero -> Zero
    | Succ(k) -> halve(k)
  }

  # Program with proof obligations
  program sub(n : Nat, m : Nat) -> Nat {
    wf(Lt)
    | Zero -> Zero
    | Succ(k) -> sub(k, m)

    obligation sub_dec(k : Nat) -> Eq(k, k) {
      | Zero -> refl
      | Succ(k2) -> refl
    }
  }

  # Programs coexist with proofs in the same system
  prove double_zero(n : Nat) -> Eq(n, n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(double_zero(k))
  }
}
`);
  const sys = result.systems.get("Programs")!;
  assertEquals(sys.provedCtx.has("double"), true);
  assertEquals(sys.provedCtx.has("halve"), true);
  assertEquals(sys.provedCtx.has("sub"), true);
  assertEquals(sys.provedCtx.has("sub_dec"), true);
  assertEquals(sys.provedCtx.has("double_zero"), true);
});

// ─── 14. Deep pattern matching ─────────────────────────────────────
// Demonstrates: nested constructor patterns like Succ(Succ(k)) that
// pattern-match two levels deep in a single case arm.

Deno.test("showcase 14: deep (nested) pattern matching", () => {
  const result = compileAndAssert(BASE + `
system "Deep" extend "NatEq" {
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Two-deep nesting: Succ(Succ(k)) matches two constructors
  prove deep2(n : Nat) -> Eq(n, n) {
    | Zero -> refl
    | Succ(Succ(k)) -> ?
    | Succ(Zero) -> refl
  }

  # Three-deep nesting: Succ(Succ(Succ(k))) matches three constructors
  prove deep3(n : Nat) -> Eq(n, n) {
    | Zero -> refl
    | Succ(Zero) -> refl
    | Succ(Succ(Zero)) -> refl
    | Succ(Succ(Succ(k))) -> ?
  }
}
`);
  const sys = result.systems.get("Deep")!;
  assertEquals(sys.provedCtx.has("deep2"), true);
  assertEquals(sys.provedCtx.has("deep3"), true);
});

// ─── 15. Module composition ────────────────────────────────────────
// Demonstrates: compose merging two independent systems, and how the
// resulting system has agents from both sides available.

Deno.test("showcase 15: module composition", () => {
  const result = compileAndAssert(`
include "prelude"

system "NatMod" extend "Prelude" {
  data Nat { | Zero | Succ(pred : Nat) }
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
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}

system "BoolMod" extend "Prelude" {
  data Bool { | True | False }
  agent not(principal, result)
  rule not <> True  -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True   relink left.result t.principal }
  compute not(True) = False
  compute not(False) = True
}

# Compose merges NatMod and BoolMod into a single system
system "Combined" = compose "NatMod" + "BoolMod" {}
`);
  const combined = result.systems.get("Combined")!;
  assertEquals(combined.agents.has("Zero"), true);
  assertEquals(combined.agents.has("Succ"), true);
  assertEquals(combined.agents.has("add"), true);
  assertEquals(combined.agents.has("True"), true);
  assertEquals(combined.agents.has("False"), true);
  assertEquals(combined.agents.has("not"), true);
});

// ═══════════════════════════════════════════════════════════════════════════
// Grand Finale: A single system that combines many features together.
// ═══════════════════════════════════════════════════════════════════════════

Deno.test("showcase finale: combined features in a rich system", () => {
  const result = compileAndAssert(BASE + `
system "Showcase" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  data Bool { | True | False }

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  agent mul(principal, result, accum)
  compute mul(Zero, y) = Zero
  compute mul(Succ(k), y) = add(y, mul(k, y))

  agent not(principal, result)
  rule not <> True  -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True   relink left.result t.principal }
  compute not(True) = False
  compute not(False) = True

  # ── Notation ──
  notation "+" = add (prec 50, left)
  notation "*" = mul (prec 60, left)

  # ── Ring tactic ──
  ring Nat { zero = Zero, add = add, mul = mul }

  # ── Type class ──
  class Eq2(A) { eq2 : A }

  # ── Simp lemma ──
  @[simp] prove plus_zero_right(n : Nat) -> Eq(n + Zero, n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }

  # ── Lean-style theorem using notation ──
  theorem plus_succ_right (n m : Nat) : Eq(n + Succ(m), Succ(n + m)) := by
    | Zero => refl
    | Succ(k) => cong_succ(plus_succ_right(k, m))

  # ── Section with automation ──
  section Lemmas {
    variable(x : Nat)

    prove refl_x(n : Nat) -> Eq(n, n) {
      | Zero -> refl
      | Succ(k) -> cong_succ(refl_x(k))
    }

    # simp uses plus_zero_right from the hint DB
    prove simp_test(n : Nat) -> Eq(n + Zero, n) {
      | Zero -> simp
      | Succ(k) -> cong_succ(simp_test(k))
    }
  }

  # ── omega on a constant fact ──
  prove ground_omega(n : Nat) -> Eq(add(Succ(Zero), Succ(Zero)), Succ(Succ(Zero))) {
    | Zero -> omega
    | Succ(k) -> omega
  }

  # ── Ring solving a pure algebraic identity ──
  prove ring_comm_zero(a : Nat) -> Eq(a + Zero, Zero + a) {
    | Zero -> ring
    | Succ(k) -> ring
  }

  # ── Program with termination ──
  program halve(n : Nat) -> Nat {
    measure(n)
    | Zero -> Zero
    | Succ(k) -> halve(k)
  }
}
`);
  const sys = result.systems.get("Showcase")!;
  assertEquals(sys.provedCtx.has("plus_zero_right"), true);
  assertEquals(sys.provedCtx.has("plus_succ_right"), true);
  assertEquals(sys.provedCtx.has("refl_x"), true);
  assertEquals(sys.provedCtx.has("simp_test"), true);
  assertEquals(sys.provedCtx.has("ground_omega"), true);
  assertEquals(sys.provedCtx.has("ring_comm_zero"), true);
  assertEquals(sys.provedCtx.has("halve"), true);
  assertEquals(sys.classes !== undefined && sys.classes!.has("Eq2"), true);
});
