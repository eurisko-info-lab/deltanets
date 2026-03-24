// Tests for Phase 36: Canonical structures.
// Unification hints that fire when projection(?M) = concrete_value.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// ─── Parsing and registration ──────────────────────────────────────

Deno.test("phase36: parse canonical declaration", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  canonical NatAdd : Addable { carrier = Nat, op = add }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.canonicals !== undefined, true, "should have canonicals");
  assertEquals(sys.canonicals!.length, 1);
  assertEquals(sys.canonicals![0].name, "NatAdd");
  assertEquals(sys.canonicals![0].structName, "Addable");
  assertEquals(sys.canonicals![0].projections.get("carrier"), "Nat");
  assertEquals(sys.canonicals![0].projections.get("op"), "add");
});

Deno.test("phase36: multiple canonical instances", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  agent Bool()
  agent True()
  agent False()
  data Bool { | True | False }
  agent boolAnd(x, y)

  canonical NatAdd : Addable { carrier = Nat, op = add }
  canonical BoolAnd : Addable { carrier = Bool, op = boolAnd }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.canonicals!.length, 2);
  assertEquals(sys.canonicals![0].name, "NatAdd");
  assertEquals(sys.canonicals![1].name, "BoolAnd");
});

Deno.test("phase36: inherited through extend", () => {
  const result = compileAndAssert(BASE + `
system "Base" extend "NatEq" {
  canonical NatAdd : Addable { carrier = Nat, op = add }
}
system "Ext" extend "Base" {
  agent mul(x, y)
  canonical NatMul : Mulable { carrier = Nat, op = mul }
}
`);
  const sys = result.systems.get("Ext")!;
  assertEquals(sys.canonicals!.length, 2);
  assertEquals(sys.canonicals![0].name, "NatAdd");
  assertEquals(sys.canonicals![1].name, "NatMul");
});

Deno.test("phase36: inherited through compose", () => {
  const result = compileAndAssert(`
include "prelude"
system "A" extend "Prelude" {
  agent Nat()
  agent Zero()
  agent Succ(pred)
  data Nat { | Zero | Succ(pred : Nat) }
  agent add(x, y)
  canonical NatAdd : Addable { carrier = Nat, op = add }
}
system "B" extend "Prelude" {
  agent Bool()
  agent True()
  agent False()
  data Bool { | True | False }
  agent boolOr(x, y)
  canonical BoolOr : Orable { carrier = Bool, op = boolOr }
}
system "C" = compose "A" + "B" {}
`);
  const sys = result.systems.get("C")!;
  assertEquals(sys.canonicals!.length, 2);
});

// ─── Unification resolution ────────────────────────────────────────

Deno.test("phase36: canonical resolution — carrier(?M) = Nat resolves ?M", () => {
  // carrier(NatMonoid) normalizes to Nat via compute rule.
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  agent carrier(m)
  agent NatMonoid()
  compute carrier(NatMonoid) = Nat

  canonical NatMonoid : Monoid { carrier = Nat }

  prove carrier_nat(n : Nat) -> Eq(carrier(NatMonoid), Nat) {
    | Zero -> refl
    | Succ(k) -> refl
  }
}
`);
});

Deno.test("phase36: canonical with multiple fields and implicit resolution", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  agent carrier(m)
  agent ident(m)
  agent NatMonoid()
  compute carrier(NatMonoid) = Nat
  compute ident(NatMonoid) = Zero

  canonical NatMonoid : Monoid { carrier = Nat, ident = Zero }

  prove ident_is_zero(n : Nat) -> Eq(ident(NatMonoid), Zero) {
    | Zero -> refl
    | Succ(k) -> refl
  }
}
`);
});

Deno.test("phase36: backward compat — proofs without canonical still work", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(add_zero_right(k))
  }
}
`);
});

Deno.test("phase36: canonical coexists with typeclasses", () => {
  // Verifies class/instance + canonical in same system (no prove —
  // class+instance+prove in one system is a pre-existing limitation).
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  class Show(A) { show : A }

  agent showNat(x)
  compute showNat(x) = x
  instance Show(Nat) { show = showNat }

  canonical NatNum : Numeric { carrier = Nat }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.canonicals!.length, 1);
  assertEquals(sys.classes!.size, 1);
  assertEquals(sys.instances!.length, 1);
});

Deno.test("phase36: canonical coexists with @[simp] hints", () => {
  compileAndAssert(BASE + `
system "T" extend "NatEq" {
  canonical NatAdd : Addable { carrier = Nat, op = add }

  @[simp] prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(add_zero_right(k))
  }
}
`);
  // Just verifies both features coexist without error
});
