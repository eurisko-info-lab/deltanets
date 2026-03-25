// Tests for the eauto strategy.
// eauto(n) extends auto with hint-database-aware backtracking search.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── eauto strategy parses ─────────────────────────────────────────

Deno.test("eauto: strategy eauto(n) parses and compiles", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      strategy my_eauto = eauto(3)

      prove trivial(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(trivial(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── eauto default strategy available from prelude ─────────────────

Deno.test("eauto: prelude eauto strategy available", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove id_eq(n : Nat) -> Eq(n, n) {
        | Zero -> eauto
        | Succ(k) -> cong_succ(id_eq(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── eauto uses hint databases ─────────────────────────────────────

Deno.test("eauto: applies hint lemma to solve goal", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(add_zero_right(k))
      }

      hint auto : add_zero_right

      # eauto should be able to find add_zero_right via hint DB
      prove use_hint(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> eauto
        | Succ(k) -> cong_succ(use_hint(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
