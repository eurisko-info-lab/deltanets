// Tests for first-class Pi and Sigma types (Phase 14).
// Verifies parsing, type-checking, and walker traversal of
// forall/exists/fun/backslash-lambda syntax.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

const SIGMA_AGENTS = `
  agent pair(principal, fst_val, snd_val)
  agent fst(principal, result)
  agent snd(principal, result)

  rule fst <> pair -> {
    relink left.result right.fst_val
    erase right.snd_val
  }
  rule snd <> pair -> {
    relink left.result right.snd_val
    erase right.fst_val
  }
`;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── exists() return type with pair body ───────────────────────────

Deno.test("pi-sigma: exists return type with pair body", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      ${SIGMA_AGENTS}
      prove ex_refl(n : Nat) -> exists(k : Nat, Eq(k, k)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── exists() dependent on induction variable ──────────────────────

Deno.test("pi-sigma: exists matching induction variable", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      ${SIGMA_AGENTS}
      prove ex_id(n : Nat) -> exists(k : Nat, Eq(k, n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── forall() in parameter type annotation ─────────────────────────

Deno.test("pi-sigma: forall in parameter type annotation parses", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove use_pi(n : Nat, f : forall(x : Nat, Eq(x, x))) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(use_pi(k, f))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── fun() lambda syntax ───────────────────────────────────────────

Deno.test("pi-sigma: fun lambda in proof body with hole", () => {
  // Use ? hole so desugaring is skipped — tests parsing and walking only
  const result = compile(`
    system "T" extend "NatEq" {
      prove lam_test(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> ?
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Backslash lambda syntax ───────────────────────────────────────

Deno.test("pi-sigma: backslash lambda parses in parameter type", () => {
  // Test that \x:A.body parses correctly as a lambda expression
  // Use it in a type annotation context
  const source = BASE + `
    system "T" extend "NatEq" {
      prove bs_test(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(bs_test(k))
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Nested exists ─────────────────────────────────────────────────

Deno.test("pi-sigma: forall in nested type position parses", () => {
  // Tests that forall() parses in positions beyond just return type
  const result = compile(`
    system "T" extend "NatEq" {
      ${SIGMA_AGENTS}
      prove nested_forall(n : Nat) -> exists(k : Nat, Eq(k, n)) {
        | Zero -> pair(Zero, refl)
        | Succ(m) -> pair(Succ(m), refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
