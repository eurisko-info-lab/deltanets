// Tests for Phase 35: Rewriting with lemma databases.
// @[simp] attribute syntax, multi-step simp rewriting.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// ─── @[simp] attribute syntax ──────────────────────────────────────

Deno.test("phase35: @[simp] attribute auto-registers hint", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.hints !== undefined, true, "should have hints");
  assertEquals(sys.hints!.get("simp")!.has("add_zero_right"), true);
});

Deno.test("phase35: @[auto] attribute auto-registers auto hint", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[auto] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.hints!.get("auto")!.has("add_zero_right"), true);
});

Deno.test("phase35: @[simp, auto] registers in both databases", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[simp, auto] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.hints!.get("simp")!.has("add_zero_right"), true);
  assertEquals(sys.hints!.get("auto")!.has("add_zero_right"), true);
});

// ─── @[simp] used by simp tactic ──────────────────────────────────

Deno.test("phase35: simp uses @[simp]-annotated lemmas", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
  prove test(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(test(k))
  }
}
`);
});

Deno.test("phase35: auto uses @[auto]-annotated lemmas", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[auto] prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_left(m))
  }
  prove test(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> auto
    | Succ(k) -> cong_succ(test(k))
  }
}
`);
});

// ─── @[simp] inherited through extend ──────────────────────────────

Deno.test("phase35: @[simp] hints inherited through extend", () => {
  const result = compileAndAssert(BASE + `
system "Base" extend "NatEq" {
  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
}
system "Child" extend "Base" {
  prove test(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(test(k))
  }
}
`);
  const child = result.systems.get("Child")!;
  assertEquals(child.hints!.get("simp")!.has("add_zero_right"), true, "should inherit @[simp]");
});

// ─── Multi-step rewriting ──────────────────────────────────────────

Deno.test("phase35: multi-step simp with two lemmas", () => {
  // Goal: Eq(add(add(n, Zero), Zero), n)
  // Step 1: add_zero_right rewrites add(add(n, Zero), Zero) → add(n, Zero)
  // Step 2: add_zero_right rewrites add(n, Zero) → n
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
  prove test(n : Nat) -> Eq(add(add(n, Zero), Zero), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(test(k))
  }
}
`);
});

Deno.test("phase35: multi-step simp with distinct lemmas", () => {
  // Two different lemmas working together:
  // add_zero_right: add(n, Zero) → n
  // add_zero_left: add(Zero, n) → n (trivial by compute, but registered)
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
  @[simp] prove add_zero_left(n : Nat) -> Eq(add(Zero, n), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_left(m))
  }
  prove test(n : Nat) -> Eq(add(Zero, add(n, Zero)), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(test(k))
  }
}
`);
});

// ─── Backward compatibility ────────────────────────────────────────

Deno.test("phase35: explicit hint simp: still works", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
  hint simp : add_zero_right
  prove test(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> simp
    | Succ(k) -> cong_succ(test(k))
  }
}
`);
});

Deno.test("phase35: proofs without @[simp] still work", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(m) -> cong_succ(add_zero_right(m))
  }
}
`);
});

// ─── Compat: existing tests pass with attributes present ───────────

Deno.test("phase35: @[simp] on plus_succ_right", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  @[simp] prove plus_succ_right(n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_succ_right(k, m))
  }
}
`);
});
