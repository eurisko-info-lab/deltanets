// Tests for Phase 32: Definitional equality — conversion judgment.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore, convertible, checkConvertible } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// ─── convertible() function tests ──────────────────────────────────

Deno.test("convertible: identical exprs are convertible", () => {
  const a = { kind: "ident" as const, name: "x" };
  assertEquals(convertible(a, a), true);
});

Deno.test("convertible: structurally equal exprs are convertible", () => {
  const a = { kind: "ident" as const, name: "x" };
  const b = { kind: "ident" as const, name: "x" };
  assertEquals(convertible(a, b), true);
});

Deno.test("convertible: different idents are not convertible", () => {
  const a = { kind: "ident" as const, name: "x" };
  const b = { kind: "ident" as const, name: "y" };
  assertEquals(convertible(a, b), false);
});

Deno.test("convertible: call expressions match structurally", () => {
  const a = { kind: "call" as const, name: "Succ", args: [{ kind: "ident" as const, name: "Zero" }] };
  const b = { kind: "call" as const, name: "Succ", args: [{ kind: "ident" as const, name: "Zero" }] };
  assertEquals(convertible(a, b), true);
});

// ─── checkConvertible() detailed result ────────────────────────────

Deno.test("checkConvertible: returns convertible:true for equal exprs", () => {
  const a = { kind: "ident" as const, name: "Zero" };
  const result = checkConvertible(a, a);
  assertEquals(result.convertible, true);
});

Deno.test("checkConvertible: returns detailed info for non-convertible exprs", () => {
  const a = { kind: "ident" as const, name: "x" };
  const b = { kind: "ident" as const, name: "y" };
  const result = checkConvertible(a, b);
  assertEquals(result.convertible, false);
  if (!result.convertible) {
    assertEquals(result.syntacticallyEqual, false);
    assertEquals(typeof result.lhsNorm, "string");
    assertEquals(typeof result.rhsNorm, "string");
  }
});

// ─── conv tactic still works with normalization ────────────────────

Deno.test("conv: proves goal when sides normalize to same term", () => {
  compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(m) -> cong_succ(add_zero_left(m))
      }
    }
  `);
});

Deno.test("conv: fails when sides are not definitionally equal", () => {
  const result = compileCore(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove bad(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> conv
        | Succ(m) -> conv
      }
    }
  `);
  // The Succ case should fail: add(Succ(m), Zero) normalizes to Succ(add(m, Zero)),
  // not Succ(m)
  const convErrors = result.errors.filter((e) => e.includes("conv failed"));
  assertEquals(convErrors.length, 1, `expected 1 conv failure, got: ${result.errors}`);
});

Deno.test("conv: error message includes normalized forms", () => {
  const result = compileCore(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove bad(n : Nat) -> Eq(add(n, Zero), n) {
        | Succ(m) -> conv
      }
    }
  `);
  const convErrors = result.errors.filter((e) => e.includes("conv failed"));
  assertEquals(convErrors.length >= 1, true, `expected conv failure, got: ${result.errors}`);
  // Error should mention normalized forms
  const err = convErrors[0];
  assertEquals(err.includes("lhs normalizes to") || err.includes("rhs normalizes to"), true,
    `error should include normalized forms: ${err}`);
});

// ─── refl still works (Rocq semantics: refl proves a=b when a≡b) ──

Deno.test("refl: works for definitionally equal terms (base case)", () => {
  compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_left(m))
      }
    }
  `);
});

Deno.test("refl: works for syntactically identical terms", () => {
  compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove trivial(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(m) -> refl
      }
    }
  `);
});
