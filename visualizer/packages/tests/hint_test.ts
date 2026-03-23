// Tests for Phase 31: Hint databases — user-extensible hint sets for auto and simp.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// ─── Basic hint declaration ─────────────────────────────────────────

Deno.test("hint: basic hint declaration registers in SystemDef", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      agent A(x)
      agent B(x)
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      hint auto : add_zero_right
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.hints !== undefined, true, "should have hints");
  assertEquals(sys.hints!.has("auto"), true, "should have auto DB");
  assertEquals(sys.hints!.get("auto")!.has("add_zero_right"), true, "should contain lemma");
});

Deno.test("hint: multiple hints in same DB", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_left(m))
      }
      hint auto : add_zero_right
      hint auto : add_zero_left
    }
  `);
  const sys = result.systems.get("T")!;
  const autoDb = sys.hints!.get("auto")!;
  assertEquals(autoDb.size, 2);
  assertEquals(autoDb.has("add_zero_right"), true);
  assertEquals(autoDb.has("add_zero_left"), true);
});

Deno.test("hint: separate hint databases", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_left(m))
      }
      hint auto : add_zero_right
      hint simp : add_zero_left
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.hints!.get("auto")!.has("add_zero_right"), true);
  assertEquals(sys.hints!.get("simp")!.has("add_zero_left"), true);
  assertEquals(sys.hints!.get("auto")!.has("add_zero_left"), false);
});

// ─── Hint inheritance ───────────────────────────────────────────────

Deno.test("hint: extend inherits hints from base", () => {
  const result = compileAndAssert(BASE + `
    system "A" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      hint auto : add_zero_right
    }
    system "B" extend "A" {
      prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_left(m))
      }
      hint auto : add_zero_left
    }
  `);
  const sysB = result.systems.get("B")!;
  const autoDb = sysB.hints!.get("auto")!;
  assertEquals(autoDb.has("add_zero_right"), true, "should inherit from base");
  assertEquals(autoDb.has("add_zero_left"), true, "should have own hint");
});

Deno.test("hint: compose merges hints from components", () => {
  const result = compileAndAssert(BASE + `
    system "A" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      hint auto : add_zero_right
    }
    system "B" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_left(m))
      }
      hint simp : add_zero_left
    }
    system "C" = compose "A" + "B" {
    }
  `);
  const sysC = result.systems.get("C")!;
  assertEquals(sysC.hints!.get("auto")!.has("add_zero_right"), true);
  assertEquals(sysC.hints!.get("simp")!.has("add_zero_left"), true);
});

// ─── No hints means no hints field ─────────────────────────────────

Deno.test("hint: system without hints has undefined hints", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      agent A(x)
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.hints, undefined);
});

// ─── Hint-prioritized auto resolution ───────────────────────────────

Deno.test("hint: auto tactic uses hint-DB lemmas", () => {
  // This test verifies that the auto tactic can find proofs using hint-DB lemmas.
  // The `auto` tactic should resolve the goal using lemmas registered in the auto DB.
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      hint auto : add_zero_right

      prove test_auto(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> auto
        | Succ(m) -> cong_succ(test_auto(m))
      }
    }
  `);
  assertEquals(result.errors.length, 0, "auto should resolve using hint DB lemma");
});

Deno.test("hint: simp tactic uses hint-DB lemmas", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(x), y) = Succ(add(x, y))
      prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(m) -> cong_succ(add_zero_right(m))
      }
      hint simp : add_zero_right

      prove test_simp(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> simp
        | Succ(m) -> cong_succ(test_simp(m))
      }
    }
  `);
  assertEquals(result.errors.length, 0, "simp should resolve using hint DB lemma");
});
