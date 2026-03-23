// Tests for let-bindings in prove blocks.
// Verifies parsing, type-checking, and desugaring of let expressions.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic let binding ─────────────────────────────────────────────

Deno.test("let: basic let binding in prove body", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove let_refl(n : Nat) -> Eq(n, n) {
        | Zero -> let p = refl in p
        | Succ(k) -> let ih = let_refl(k) in cong_succ(ih)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Nested let bindings ───────────────────────────────────────────

Deno.test("let: nested let bindings", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove nested_let(n : Nat) -> Eq(n, n) {
        | Zero -> let a = refl in let b = a in b
        | Succ(k) -> let ih = nested_let(k) in let r = cong_succ(ih) in r
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Let with IH in inductive proof ────────────────────────────────

Deno.test("let: let with IH in add_zero proof", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove add_zero(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> let ih = add_zero(k) in cong_succ(ih)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Let used as argument ──────────────────────────────────────────

Deno.test("let: let binding used inside call argument", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove let_in_arg(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(let ih = let_in_arg(k) in ih)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
