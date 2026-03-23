// Tests for termination checking — structural recursion guard on prove blocks.
// Verifies that non-decreasing recursive calls are rejected while valid
// structural recursion (including nested matches) is accepted.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Valid recursion ───────────────────────────────────────────────

Deno.test("termination: simple structural recursion accepted", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("termination: multi-param recursion with binding accepted", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove psr(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(psr(k, m))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("termination: nested match with inner binding accepted", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove foo(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
        | Zero -> match(m) {
          | Zero -> refl
          | Succ(j) -> cong_succ(foo(Zero, j))
        }
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Invalid recursion ─────────────────────────────────────────────

Deno.test("termination: same-argument recursion rejected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> bad(Succ(k))
      }
    }
  `);
  assertEquals(result.errors.some((e) => e.includes("not structurally decreasing")), true,
    `expected termination error, got: ${result.errors}`);
});

Deno.test("termination: no-arg-is-binding rejected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad2(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> bad2(Succ(Zero))
      }
    }
  `);
  assertEquals(result.errors.some((e) => e.includes("not structurally decreasing")), true,
    `expected termination error, got: ${result.errors}`);
});
