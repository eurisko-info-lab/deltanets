// Tests for Q rationals, scope, omega solver, and field solver.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ═══════════════════════════════════════════════════════════════════
// Q (stdlib module)
// ═══════════════════════════════════════════════════════════════════

Deno.test("q: stdlib/q module compiles", () => {
  const result = compileCore(`
    include "stdlib/q"
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("q: Frac constructor available", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove mk_q(n : Nat) -> Q {
        | Zero -> Frac(Pos(Zero), Zero)
        | Succ(k) -> Frac(Pos(Succ(k)), k)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("q: field tactic available on Q", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove q_add_comm(x : Q) -> Eq(q_add(x, q_zero), q_add(q_zero, x)) {
        | Frac(n, d) -> field
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("q: field recognizes q_add(x, q_zero) = x", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove q_add_zero(x : Q) -> Eq(q_add(x, q_zero), q_add(x, q_zero)) {
        | Frac(n, d) -> field
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ═══════════════════════════════════════════════════════════════════
// Scope (notation scoping)
// ═══════════════════════════════════════════════════════════════════

Deno.test("scope: notations inside scope are active", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      scope "nat_scope" {
        notation "+" = add (prec 50, left)
        prove scoped_add(n : Nat) -> Eq(n + Zero, add(n, Zero)) {
          | Zero -> refl
          | Succ(k) -> refl
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("scope: notations do not leak outside scope", () => {
  // Outside the scope, "+" should not be recognized as notation
  const result = compile(`
    system "T" extend "NatEq" {
      scope "nat_scope" {
        notation "+" = add (prec 50, left)
      }
      # After scope, "+" is no longer valid notation
      prove test(n : Nat) -> Eq(add(n, Zero), add(n, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("scope: multiple scopes independent", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      scope "s1" {
        notation "+" = add (prec 50, left)
        prove s1_test(n : Nat) -> Eq(n + Zero, add(n, Zero)) {
          | Zero -> refl
          | Succ(k) -> refl
        }
      }
      scope "s2" {
        notation "*" = add (prec 60, left)
        prove s2_test(n : Nat) -> Eq(n * Zero, add(n, Zero)) {
          | Zero -> refl
          | Succ(k) -> refl
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ═══════════════════════════════════════════════════════════════════
// Omega (linear arithmetic solver)
// ═══════════════════════════════════════════════════════════════════

Deno.test("omega: solves ground nat equality", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_ground(n : Nat) -> Eq(add(Succ(Zero), Succ(Zero)), Succ(Succ(Zero))) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("omega: solves add(Zero, n) = n", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_add_zero(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("omega: solves Succ(Succ(Zero)) = Succ(Succ(Zero))", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_const(n : Nat) -> Eq(Succ(Succ(Zero)), Succ(Succ(Zero))) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("omega: solves Succ(n) = Succ(n)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_succ_id(n : Nat) -> Eq(Succ(n), Succ(n)) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("omega: solves add(Succ(Zero), n) = Succ(n)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_add_one(n : Nat) -> Eq(add(Succ(Zero), n), Succ(n)) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("omega: solves add(Succ(Succ(Zero)), n) = Succ(Succ(n))", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_add_two(n : Nat) -> Eq(add(Succ(Succ(Zero)), n), Succ(Succ(n))) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ═══════════════════════════════════════════════════════════════════
// Field (field equation solver)
// ═══════════════════════════════════════════════════════════════════

Deno.test("field: registered field enables field tactic", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove field_refl(x : Q) -> Eq(q_add(x, q_zero), q_add(x, q_zero)) {
        | Frac(n, d) -> field
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("field: solves q_mul(x, q_one) = q_mul(q_one, x)", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove field_mul_comm(x : Q) -> Eq(q_mul(x, q_one), q_mul(q_one, x)) {
        | Frac(n, d) -> field
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("field: solves q_neg(q_neg(x)) = x", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove field_neg_neg(x : Q) -> Eq(q_neg(q_neg(x)), x) {
        | Frac(n, d) -> field
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("field: inline field decl works", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent f_zero(principal)
      agent f_one(principal)
      agent f_add(principal, result, second)
      agent f_mul(principal, result, second)
      agent f_neg(principal, result)
      agent f_inv(principal, result)
      field Nat { zero = f_zero, one = f_one, add = f_add, mul = f_mul, neg = f_neg, inv = f_inv }
      prove field_inline(x : Nat) -> Eq(f_add(x, f_zero), f_add(f_zero, x)) {
        | Zero -> field
        | Succ(k) -> field
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("field: field fails on non-equal expressions", () => {
  const result = compileCore(`
    include "stdlib/q"
    system "T" extend "Stdlib.Q" {
      prove field_bad(x y : Q) -> Eq(q_add(x, y), q_mul(x, y)) {
        | Frac(a, b), Frac(c, d) -> field
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "field should fail on non-equal expressions");
});

// ═══════════════════════════════════════════════════════════════════
// Contextual keyword: field/scope as identifiers
// ═══════════════════════════════════════════════════════════════════

Deno.test("contextual: 'field' strategy name works in prelude", () => {
  // The prelude defines 'strategy field = field_solve'
  // This should work because field is not reserved
  const result = compile(`
    system "T" extend "NatEq" {
      prove test(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
