// Tests for Phase 34: Tactic combinator language (try, first, repeat, then/seq).

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

// ─── Base system with proofs for combinator tests ──────────────────

const COMBO_BASE = NATEQ_SYSTEM + `
system "ComboBase" extend "NatEq" {
  prove plus_zero_right(n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
}
`;

// ─── first() combinator ────────────────────────────────────────────

Deno.test("first: first(simp) resolves simple goal", () => {
  const source = COMBO_BASE + `
system "FirstSimp" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> first(simp)
    | Succ(k) -> first(simp)
  }
}
`;
  compileAndAssert(source);
});

Deno.test("first: first(simp, auto) falls back to auto", () => {
  const source = COMBO_BASE + `
system "FirstFallback" extend "ComboBase" {
  prove plus_zero(n) {
    | Zero -> first(simp, auto)
    | Succ(k) -> cong_succ(plus_zero(k))
  }
}
`;
  compileAndAssert(source);
});

Deno.test("first: first(assumption) resolves from context", () => {
  const source = COMBO_BASE + `
system "FirstAssumption" extend "ComboBase" {
  prove trivial_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> first(assumption, simp)
    | Succ(k) -> first(assumption, simp)
  }
}
`;
  compileAndAssert(source);
});

Deno.test("first: all alternatives fail produces error", () => {
  const source = COMBO_BASE + `
system "FirstFail" extend "ComboBase" {
  prove bad(n : Nat) -> Eq(Succ(Zero), Zero) {
    | Zero -> first(omega)
    | Succ(k) -> first(omega)
  }
}
`;
  const result = compileCore(source);
  assertNotEquals(result.errors.length, 0, "should have errors");
});

// ─── try() combinator ──────────────────────────────────────────────

Deno.test("try: try(simp) succeeds when simp works", () => {
  const source = COMBO_BASE + `
system "TrySuccess" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> try(simp)
    | Succ(k) -> try(simp)
  }
}
`;
  compileAndAssert(source);
});

Deno.test("try: try(omega) produces hole instead of hard error", () => {
  const source = COMBO_BASE + `
system "TryFail" extend "ComboBase" {
  prove plus_zero(n) {
    | Zero -> try(omega)
    | Succ(k) -> cong_succ(plus_zero(k))
  }
}
`;
  const result = compileCore(source);
  // try should NOT produce a hard "omega failed" error
  const hasTacticError = result.errors.some((e: string) =>
    e.includes("omega failed") || e.includes("try failed")
  );
  assertEquals(hasTacticError, false, "try should not produce tactic failure errors");
});

// ─── then() / seq() combinator ─────────────────────────────────────

Deno.test("then: then(simp, auto) resolves sequentially", () => {
  const source = COMBO_BASE + `
system "ThenSimp" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> then(simp, auto)
    | Succ(k) -> then(simp, auto)
  }
}
`;
  compileAndAssert(source);
});

Deno.test("seq: seq(simp, auto) is alias for then", () => {
  const source = COMBO_BASE + `
system "SeqAlias" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> seq(simp, auto)
    | Succ(k) -> seq(simp, auto)
  }
}
`;
  compileAndAssert(source);
});

// ─── repeat() combinator ───────────────────────────────────────────

Deno.test("repeat: repeat(simp) resolves trivial goal", () => {
  const source = COMBO_BASE + `
system "RepeatSimp" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> repeat(simp)
    | Succ(k) -> repeat(simp)
  }
}
`;
  compileAndAssert(source);
});

// ─── Nested combinators ────────────────────────────────────────────

Deno.test("nested: first(try(omega), simp) works", () => {
  const source = COMBO_BASE + `
system "Nested" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> first(try(omega), simp)
    | Succ(k) -> first(try(omega), simp)
  }
}
`;
  compileAndAssert(source);
});

Deno.test("nested: then(try(simp), auto) fallback chain", () => {
  const source = COMBO_BASE + `
system "NestedThen" extend "ComboBase" {
  prove plus_zero(n) {
    | Zero -> then(try(simp), auto)
    | Succ(k) -> cong_succ(plus_zero(k))
  }
}
`;
  compileAndAssert(source);
});

// ─── Combinators with explicit proof terms ─────────────────────────

Deno.test("first: first with explicit fallback term", () => {
  const source = COMBO_BASE + `
system "FirstExplicit" extend "ComboBase" {
  prove plus_zero(n) {
    | Zero -> first(simp, refl)
    | Succ(k) -> cong_succ(plus_zero(k))
  }
}
`;
  compileAndAssert(source);
});

// ─── Backward compatibility ────────────────────────────────────────

Deno.test("phase34 compat: existing proofs without combinators", () => {
  const source = COMBO_BASE + `
system "BackCompat" extend "ComboBase" {
  prove plus_succ_right(n, m) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_succ_right(k, m))
  }
}
`;
  compileAndAssert(source);
});

Deno.test("phase34 compat: simp without combinator wrapper", () => {
  const source = COMBO_BASE + `
system "PlainSimp" extend "ComboBase" {
  prove zero_eq(n : Nat) -> Eq(Zero, Zero) {
    | Zero -> simp
    | Succ(k) -> simp
  }
}
`;
  compileAndAssert(source);
});
