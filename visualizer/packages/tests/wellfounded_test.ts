// Tests for well-founded recursion: `measure(expr)` and `wf(name)` annotations
// on prove blocks. Verifies that measure-based termination checking accepts
// decreasing measures and rejects non-decreasing ones, and that wf trusts the user.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── measure: accepted ─────────────────────────────────────────────

Deno.test("measure: simple structural recursion with measure(n) accepted", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        measure(n)
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("measure: multi-param with measure on first param accepted", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove psr(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
        measure(n)
        | Zero -> refl
        | Succ(k) -> cong_succ(psr(k, m))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("measure: nested match with inner binding accepted", () => {
  // measure(n): in Succ case, recursive call uses j from nested match(k),
  // j < Succ(k) via binding fallback (j is a binding, Succ(k) is Succ-wrapped)
  const result = compile(`
    system "T" extend "NatEq" {
      prove deep(n : Nat) -> Eq(add(n, Zero), n) {
        measure(n)
        | Zero -> refl
        | Succ(k) -> match(k) {
          | Zero -> ?
          | Succ(j) -> cong_succ(cong_succ(deep(j)))
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── measure: rejected ─────────────────────────────────────────────

Deno.test("measure: same-argument recursion rejected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad(n : Nat) -> Eq(n, n) {
        measure(n)
        | Zero -> refl
        | Succ(k) -> bad(Succ(k))
      }
    }
  `);
  assertEquals(result.errors.some((e) => e.includes("not smaller")), true,
    `expected measure error, got: ${result.errors}`);
});

Deno.test("measure: constant argument recursion rejected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad2(n : Nat) -> Eq(n, n) {
        measure(n)
        | Zero -> refl
        | Succ(k) -> bad2(Succ(Zero))
      }
    }
  `);
  assertEquals(result.errors.some((e) => e.includes("not smaller")), true,
    `expected measure error, got: ${result.errors}`);
});

// ─── wf: trusted ──────────────────────────────────────────────────

Deno.test("wf: non-decreasing recursion accepted (trusted)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove trusted(n : Nat) -> Eq(n, n) {
        wf(lt)
        | Zero -> refl
        | Succ(k) -> trusted(Succ(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("wf: arbitrary recursion accepted (trusted)", () => {
  // wf: Succ(k) is not a case binding, but wf trusts the user
  const result = compile(`
    system "T" extend "NatEq" {
      prove tricky(n : Nat) -> Eq(n, n) {
        wf(myrel)
        | Zero -> refl
        | Succ(k) -> tricky(Succ(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── measure with compute rules ────────────────────────────────────

Deno.test("measure: compute-rule measure with x < Succ(x) accepted", () => {
  // measure(add(n, Zero)): add(Succ(k), Zero) normalizes to Succ(add(k, Zero)),
  // and the recursive call's measure add(k, Zero) < Succ(add(k, Zero)) via x < Succ(x)
  const result = compile(`
    system "T" extend "NatEq" {
      prove combo(n : Nat) -> Eq(add(n, Zero), n) {
        measure(add(n, Zero))
        | Zero -> refl
        | Succ(k) -> cong_succ(combo(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── holes with measure/wf ─────────────────────────────────────────

Deno.test("measure: holes skip measure check", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove partial(n : Nat) -> Eq(add(n, Zero), n) {
        measure(n)
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("wf: holes with wf accepted", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove partial2(n : Nat) -> Eq(n, n) {
        wf(R)
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
