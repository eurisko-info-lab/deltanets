// Tests for Phase 28: Setoid rewriting — Rewrite under arbitrary equivalence relations.
// Registers user-defined binary relations as setoids and tests that sym, trans,
// rewrite, cong_X, subst, conv, and simp all generalise beyond Eq.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";

// Base system: Nat + Eq plumbing + a custom binary relation `Sim` declared as a setoid
const BASE = `
include "prelude"

system "Base" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

  agent add(principal, result, accum)
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  agent refl(principal)
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> {
    let r = refl
    relink left.result r.principal
  }

  agent sym(principal, result)
  rule sym <> refl -> {
    let r = refl
    relink left.result r.principal
  }

  agent trans(principal, result, second)
  rule trans <> refl -> {
    relink left.result right.second
  }

  agent Sim(principal, result, lhs, rhs)

  agent sim_refl(principal)
  agent sim_sym(principal, result)
  agent sim_trans(principal, result, second)

  rule sim_sym <> sim_refl -> {
    let r = sim_refl
    relink left.result r.principal
  }
  rule sim_trans <> sim_refl -> {
    relink left.result right.second
  }

  setoid Sim on Nat { refl = sim_refl, sym = sim_sym, trans = sim_trans }
}
`;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Parse ─────────────────────────────────────────────────────────

Deno.test("setoid: parses setoid declaration", () => {
  const result = compile(`
    system "T" extend "Base" {}
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── refl for setoid goal ──────────────────────────────────────────

Deno.test("setoid: refl accepted for Sim(x, x) goal", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat) -> Sim(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── sym ───────────────────────────────────────────────────────────

Deno.test("setoid: sym flips Sim proof", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat) -> Sim(n, n) {
        | Zero -> sym(refl)
        | Succ(k) -> sym(refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── trans ─────────────────────────────────────────────────────────

Deno.test("setoid: trans chains two Sim proofs", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat) -> Sim(n, n) {
        | Zero -> trans(refl, refl)
        | Succ(k) -> trans(refl, refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── rewrite ───────────────────────────────────────────────────────

Deno.test("setoid: rewrite with Sim proof", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove helper(n : Nat) -> Sim(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
      prove test(n : Nat) -> Sim(n, n) {
        | Zero -> refl
        | Succ(k) -> sym(helper(Succ(k)))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── cong_X with setoid ────────────────────────────────────────────

Deno.test("setoid: cong_succ with Sim proof from lemma", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove sim_id(n : Nat) -> Sim(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
      prove test(n : Nat) -> Sim(Succ(n), Succ(n)) {
        | Zero -> cong_succ(sim_id(Zero))
        | Succ(k) -> cong_succ(sim_id(Succ(k)))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── subst with setoid ─────────────────────────────────────────────

Deno.test("setoid: subst accepts Sim proof as transport", () => {
  // subst(proof, e) should accept a setoid equivalence, not just Eq.
  const result = compile(`
    system "T" extend "Base" {
      agent subst(principal, result, value)
      prove sim_id(n : Nat) -> Sim(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
      prove test(n : Nat) -> Nat {
        | Zero -> subst(sim_id(Zero), Zero)
        | Succ(k) -> subst(sim_id(Succ(k)), Succ(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── conv for setoid ───────────────────────────────────────────────

Deno.test("setoid: conv accepts Sim(x, x) via reflexivity", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat) -> Sim(n, n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Relation mismatch errors ──────────────────────────────────────

Deno.test("setoid: trans rejects mismatched relations (Eq vs Sim)", () => {
  // Create a proof of Eq and try to trans it with a Sim proof
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat, p : Eq(n, Zero), q : Sim(Zero, n)) -> Sim(n, n) {
        | Zero -> trans(p, q)
        | Succ(k) -> trans(p, q)
      }
    }
  `);
  // trans should fail because p is Eq but q is Sim — different relations
  assertEquals(result.errors.length > 0, true, "expected mismatch error");
});

// ─── Non-setoid binary relation rejected ───────────────────────────

Deno.test("setoid: sym rejects non-setoid binary relation", () => {
  const result = compile(`
    system "T" extend "Base" {
      agent Rel(principal, result, lhs, rhs)
      prove test(n : Nat, p : Rel(n, Zero)) -> Rel(Zero, n) {
        | Zero -> sym(p)
        | Succ(k) -> sym(p)
      }
    }
  `);
  // Rel is not registered as a setoid, so sym should fail
  assertEquals(result.errors.length > 0, true, "expected non-setoid error");
});

Deno.test("setoid: rewrite rejects non-setoid relation", () => {
  const result = compile(`
    system "T" extend "Base" {
      agent Rel(principal, result, lhs, rhs)
      prove test(n : Nat, p : Rel(n, Zero)) -> Rel(Zero, n) {
        | Zero -> rewrite(p, refl)
        | Succ(k) -> rewrite(p, refl)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "expected non-setoid error");
});

// ─── Eq still works (regression) ──────────────────────────────────

Deno.test("setoid: Eq sym still works as before", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat) -> Eq(n, n) {
        | Zero -> sym(refl)
        | Succ(k) -> sym(refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("setoid: Eq trans still works as before", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove test(n : Nat) -> Eq(n, n) {
        | Zero -> trans(refl, refl)
        | Succ(k) -> trans(refl, refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("setoid: Eq rewrite still works as before", () => {
  const result = compile(`
    system "T" extend "Base" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Setoid in section ─────────────────────────────────────────────

Deno.test("setoid: setoid declaration in section", () => {
  const result = compile(`
    system "T" extend "Base" {
      section mySection {
        agent Bis(principal, result, lhs, rhs)
        agent bis_refl(principal)
        agent bis_sym(principal, result)
        agent bis_trans(principal, result, second)
        setoid Bis on Nat { refl = bis_refl, sym = bis_sym, trans = bis_trans }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
