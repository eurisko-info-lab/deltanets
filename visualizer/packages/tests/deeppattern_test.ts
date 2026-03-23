// Tests for Phase 24: Nested pattern matching — deep patterns, with-clauses,
// and overlapping/redundancy detection.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Deep patterns: accepted ───────────────────────────────────────

Deno.test("deep patterns: Succ(Succ(k)) desugars to nested match", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove dbl(n : Nat) -> Eq(add(n, n), add(n, n)) {
        | Zero -> refl
        | Succ(Succ(k)) -> ?
        | Succ(Zero) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("deep patterns: triple nesting Succ(Succ(Succ(k)))", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove trip(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(Zero) -> refl
        | Succ(Succ(Zero)) -> refl
        | Succ(Succ(Succ(k))) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("deep patterns: mixed flat and deep in same prove", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove mixed(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(mixed(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("deep patterns: with measure annotation", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove dm(n : Nat) -> Eq(add(n, Zero), n) {
        measure(n)
        | Zero -> refl
        | Succ(Succ(k)) -> ?
        | Succ(Zero) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Deep patterns in match expressions ────────────────────────────

Deno.test("deep patterns: nested pattern inside match expression", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove dm2(n : Nat, m : Nat) -> Eq(add(n, m), add(n, m)) {
        | Zero -> refl
        | Succ(k) -> match(m) {
          | Zero -> refl
          | Succ(Succ(j)) -> ?
          | Succ(Zero) -> refl
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── With-clauses ──────────────────────────────────────────────────

Deno.test("with-clause: basic with expression", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove wtest(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> with(k) {
          | Zero -> refl
          | Succ(j) -> refl
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("with-clause: desugars to let + match", () => {
  // Just check it parses and type-checks without crashing
  const result = compile(`
    system "T" extend "NatEq" {
      prove wtest2(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> with(k) {
          | Zero -> refl
          | Succ(j) -> refl
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Overlap detection ─────────────────────────────────────────────

Deno.test("overlap: duplicate case arm in prove rejected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
        | Zero -> refl
      }
    }
  `);
  assertEquals(result.errors.some((e) => e.includes("redundant")), true,
    `expected overlap error, got: ${result.errors}`);
});

Deno.test("overlap: duplicate case arm in match rejected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad2(n : Nat, m : Nat) -> Eq(n, n) {
        | Zero -> match(m) {
          | Zero -> refl
          | Succ(k) -> refl
          | Zero -> refl
        }
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.some((e) => e.includes("redundant")), true,
    `expected overlap error, got: ${result.errors}`);
});

Deno.test("overlap: no false positive on distinct constructors", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove ok(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(ok(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Edge cases ────────────────────────────────────────────────────

Deno.test("deep patterns: zero-arg constructor in nested position", () => {
  // Succ(Zero) — Zero is a constructor with no args, should be treated as ctor pattern
  const result = compile(`
    system "T" extend "NatEq" {
      prove edge(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(Zero) -> refl
        | Succ(Succ(k)) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("deep patterns: holes in deep pattern bodies", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove holed(n : Nat) -> Eq(n, n) {
        | Zero -> ?
        | Succ(Succ(k)) -> ?
        | Succ(Zero) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
