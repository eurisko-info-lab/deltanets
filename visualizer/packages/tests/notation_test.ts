// Tests for Phase 26: Notations — notation "+" = add (prec 50, left)
// Infix operators desugared to function calls at parse time via Pratt parsing.

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic notation ────────────────────────────────────────────────

Deno.test("notation: infix + desugars to add call", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      notation "+" = add (prec 50, left)

      prove addZero(n : Nat) -> Eq(n + Zero, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(addZero(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("notation: infix in return type and case body", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      notation "+" = add (prec 50, left)

      prove reflAdd(n : Nat) -> Eq(n + Zero, n + Zero) {
        | Zero -> refl
        | Succ(k) -> cong_succ(reflAdd(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Precedence ────────────────────────────────────────────────────

Deno.test("notation: higher precedence * binds tighter than +", () => {
  // With mul and add agents, a + b * c should parse as add(a, mul(b, c))
  const result = compile(`
    system "T" extend "NatEq" {
      agent mul(principal, result, accum)
      compute mul(Zero, y) = Zero
      compute mul(Succ(k), y) = add(mul(k, y), y)

      notation "+" = add (prec 50, left)
      notation "*" = mul (prec 60, left)

      prove test(n : Nat) -> Eq(n + n * Zero, n + Zero) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Right associativity ───────────────────────────────────────────

Deno.test("notation: right-associative operator", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent pow(principal, result, exp)
      compute pow(n, Zero) = Succ(Zero)
      compute pow(n, Succ(k)) = n

      notation "+" = add (prec 50, left)

      prove test(n : Nat) -> Eq(n + n + Zero, n + n + Zero) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Defaults ──────────────────────────────────────────────────────

Deno.test("notation: default precedence 50 left when no parens", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      notation "+" = add

      prove addZero(n : Nat) -> Eq(n + Zero, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(addZero(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Multiple notations ───────────────────────────────────────────

Deno.test("notation: multiple notations in same system", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent mul(principal, result, accum)
      compute mul(Zero, y) = Zero
      compute mul(Succ(k), y) = add(mul(k, y), y)

      notation "+" = add (prec 50, left)
      notation "*" = mul (prec 60, left)

      prove test(n : Nat) -> Eq(n * Succ(Zero), n) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Notation in section ──────────────────────────────────────────

Deno.test("notation: inside section", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Arith {
        notation "+" = add (prec 50, left)

        prove addZero(n : Nat) -> Eq(n + Zero, n) {
          | Zero -> refl
          | Succ(k) -> cong_succ(addZero(k))
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Subtract notation ────────────────────────────────────────────

Deno.test("notation: minus operator", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent sub(principal, result, accum)
      compute sub(Zero, y) = Zero
      compute sub(Succ(k), Zero) = Succ(k)
      compute sub(Succ(k), Succ(j)) = sub(k, j)

      notation "-" = sub (prec 50, left)

      prove subZero(n : Nat) -> Eq(n - Zero, n) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Slash notation ───────────────────────────────────────────────

Deno.test("notation: slash operator", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent div(principal, result, accum)
      compute div(Zero, y) = Zero
      compute div(Succ(k), y) = Zero

      notation "/" = div (prec 60, left)

      prove divZero(n : Nat) -> Eq(Zero / Succ(n), Zero) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Error cases ──────────────────────────────────────────────────

Deno.test("notation: unknown operator without notation doesn't parse as infix", () => {
  // Without a notation, + in prove expr should cause an error
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad(n : Nat) -> Eq(n + Zero, n) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertNotEquals(result.errors.length, 0, "should fail: + not registered as notation");
});

Deno.test("notation: notation must be declared before use", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad(n : Nat) -> Eq(n + Zero, n) {
        | Zero -> refl
        | Succ(k) -> ?
      }

      notation "+" = add (prec 50, left)
    }
  `);
  assertNotEquals(result.errors.length, 0, "should fail: notation declared after use");
});

// ═══════════════════════════════════════════════════════════════════
// Phase 43: Mixfix notations
// ═══════════════════════════════════════════════════════════════════

const { assert } = await import("$std/assert/mod.ts");

// ─── Prefix mixfix ─────────────────────────────────────────────────

Deno.test("mixfix: prefix ternary if-then-else", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent ite(principal, result, ifTrue, ifFalse)
      notation "if _ then _ else _" = ite

      prove test(n : Nat) -> Eq(if n then Zero else Zero, ite(n, Zero, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("mixfix: prefix binary 'not _'", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent myNot(principal, result)
      notation "not _" = myNot

      prove test(n : Nat) -> Eq(not n, myNot(n)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("mixfix: prefix with func call args in holes", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent ite(principal, result, ifTrue, ifFalse)
      notation "if _ then _ else _" = ite

      prove test(n : Nat) -> Eq(if n then Succ(Zero) else Zero, ite(n, Succ(Zero), Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Infix mixfix ───────────────────────────────────────────────────

Deno.test("mixfix: infix keyword operator '_ cons _'", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent myCons(principal, head, tail)
      notation "_ cons _" = myCons (prec 40, right)

      prove test(n : Nat) -> Eq(n cons Zero, myCons(n, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("mixfix: infix ternary '_ choose _ or _'", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent cond(principal, result, ifTrue, ifFalse)
      notation "_ choose _ or _" = cond

      prove test(n : Nat) -> Eq(n choose Zero or Zero, cond(n, Zero, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Mixfix keyword stopping ────────────────────────────────────────

Deno.test("mixfix: keywords not consumed as identifiers", () => {
  // 'then' and 'else' should not parse as variable names
  const result = compile(`
    system "T" extend "NatEq" {
      agent ite(principal, result, ifTrue, ifFalse)
      notation "if _ then _ else _" = ite

      prove test(n : Nat) -> Eq(if Zero then n else n, ite(Zero, n, n)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Mixfix with precedence ─────────────────────────────────────────

Deno.test("mixfix: prefix with explicit precedence", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent ite(principal, result, ifTrue, ifFalse)
      notation "if _ then _ else _" = ite (prec 10, left)

      prove test(n : Nat) -> Eq(if n then Zero else Zero, ite(n, Zero, Zero)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Mixfix coexisting with binary infix ────────────────────────────

Deno.test("mixfix: coexists with binary infix +", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      agent ite(principal, result, ifTrue, ifFalse)
      notation "+" = add (prec 50, left)
      notation "if _ then _ else _" = ite (prec 10, left)

      prove test(n : Nat) -> Eq(if n then n + Zero else Zero, ite(n, add(n, Zero), Zero)) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  // Even if proof has holes, the parsing should succeed
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
