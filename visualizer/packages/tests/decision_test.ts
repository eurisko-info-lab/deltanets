// Tests for decision procedures: decide, omega, and auto tactics.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── decide: ground-term equality ──────────────────────────────────

Deno.test("tactic: decide proves ground equality (add(Zero, Zero) = Zero)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove ground_eq(n : Nat) -> Eq(add(Zero, Zero), Zero) {
        | Zero -> decide
        | Succ(k) -> decide
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: decide proves ground computed equality (add(Succ(Zero), Succ(Zero)) = Succ(Succ(Zero)))", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove ground_add(n : Nat) -> Eq(add(Succ(Zero), Succ(Zero)), Succ(Succ(Zero))) {
        | Zero -> decide
        | Succ(k) -> decide
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: decide fails on non-ground terms", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad_decide(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> decide
        | Succ(k) -> decide
      }
    }
  `);
  // Zero case: add(Zero, Zero) → Zero, ground → should succeed
  // Succ(k) case: add(Succ(k), Zero) has free variable k → decide should fail
  assertEquals(result.errors.length > 0, true, "decide should fail on non-ground Succ case");
});

Deno.test("tactic: decide generates agent", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove dec_agent(n : Nat) -> Eq(add(Zero, Zero), Zero) {
        | Zero -> decide
        | Succ(k) -> decide
      }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("dec_agent"), true);
});

// ─── omega: linear arithmetic ──────────────────────────────────────

Deno.test("tactic: omega proves add(Zero, n) = n", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_conv(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: omega proves plus_zero_right via IH rewrite", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove omega_pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: omega generates agent", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove omega_agent(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> omega
        | Succ(k) -> omega
      }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("omega_agent"), true);
});

// ─── auto: depth-bounded proof search ──────────────────────────────

Deno.test("tactic: auto resolves via conv (add(Zero, n) = n)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove auto_conv(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> auto
        | Succ(k) -> auto
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: auto resolves via assumption (n = n)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove auto_refl(n : Nat) -> Eq(n, n) {
        | Zero -> auto
        | Succ(k) -> auto
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: auto resolves IH rewrite (add(n, Zero) = n)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove auto_pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> auto
        | Succ(k) -> auto
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: auto generates agent", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove auto_agent(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> auto
        | Succ(k) -> auto
      }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("auto_agent"), true);
});
