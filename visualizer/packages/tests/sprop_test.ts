// Tests for Phase 46: SProp — Strict Propositions (definitional proof irrelevance).

import { assertEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  isPropSort,
  isSPropSort,
  sortOf,
  typeSubsumes,
  universeLevel,
  typeUniverse,
  convertibleInSort,
} from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

// ─── Helper expression constructors ────────────────────────────────

function ident(name: string) {
  return { kind: "ident" as const, name };
}

function call(name: string, ...args: { kind: string; name?: string }[]) {
  return { kind: "call" as const, name, args: args as any[] };
}

// ─── universeLevel: SProp ──────────────────────────────────────────

Deno.test("universeLevel: SProp returns -3", () => {
  assertEquals(universeLevel(ident("SProp")), -3);
});

// ─── isSPropSort tests ─────────────────────────────────────────────

Deno.test("isSPropSort: SProp is SProp", () => {
  assertEquals(isSPropSort(ident("SProp")), true);
});

Deno.test("isSPropSort: Prop is not SProp", () => {
  assertEquals(isSPropSort(ident("Prop")), false);
});

Deno.test("isSPropSort: Type(0) is not SProp", () => {
  assertEquals(isSPropSort(call("Type", ident("0"))), false);
});

Deno.test("isSPropSort: arbitrary ident is not SProp", () => {
  assertEquals(isSPropSort(ident("Nat")), false);
});

Deno.test("isPropSort: SProp is not Prop", () => {
  assertEquals(isPropSort(ident("SProp")), false);
});

// ─── typeUniverse: SProp ───────────────────────────────────────────

Deno.test("typeUniverse: SProp inhabits Type₀", () => {
  assertEquals(typeUniverse(ident("SProp")), 0);
});

// ─── typeSubsumes: SProp hierarchy ─────────────────────────────────

Deno.test("typeSubsumes: SProp ≤ SProp", () => {
  assertEquals(typeSubsumes(ident("SProp"), ident("SProp")), true);
});

Deno.test("typeSubsumes: SProp ≤ Prop", () => {
  assertEquals(typeSubsumes(ident("SProp"), ident("Prop")), true);
});

Deno.test("typeSubsumes: SProp ≤ Type(0)", () => {
  assertEquals(typeSubsumes(ident("SProp"), call("Type", ident("0"))), true);
});

Deno.test("typeSubsumes: SProp ≤ Type(1)", () => {
  assertEquals(typeSubsumes(ident("SProp"), call("Type", ident("1"))), true);
});

Deno.test("typeSubsumes: Prop NOT ≤ SProp", () => {
  assertEquals(typeSubsumes(ident("Prop"), ident("SProp")), false);
});

Deno.test("typeSubsumes: Type(0) NOT ≤ SProp", () => {
  assertEquals(typeSubsumes(call("Type", ident("0")), ident("SProp")), false);
});

// ─── sortOf: SProp ─────────────────────────────────────────────────

Deno.test("sortOf: SProp literal returns SProp", () => {
  assertEquals(sortOf(ident("SProp")), "SProp");
});

Deno.test("sortOf: user-declared SProp data type returns SProp", () => {
  const ds = new Map<string, "Prop" | "Set" | "SProp">([["StrictTrue", "SProp"]]);
  assertEquals(sortOf(ident("StrictTrue"), ds), "SProp");
  assertEquals(sortOf(call("StrictTrue", ident("x")), ds), "SProp");
});

Deno.test("sortOf: Pi with SProp codomain is impredicative (returns SProp)", () => {
  const ds = new Map<string, "Prop" | "Set" | "SProp">([["SPrf", "SProp"]]);
  const piExpr = {
    kind: "pi" as const,
    param: "x",
    domain: call("Type", ident("0")),
    codomain: ident("SPrf"),
  };
  assertEquals(sortOf(piExpr, ds), "SProp");
});

Deno.test("sortOf: Pi with Prop codomain still returns Prop", () => {
  const piExpr = {
    kind: "pi" as const,
    param: "x",
    domain: call("Type", ident("0")),
    codomain: ident("Prop"),
  };
  assertEquals(sortOf(piExpr), "Prop");
});

// ─── convertibleInSort ─────────────────────────────────────────────

Deno.test("convertibleInSort: SProp makes all terms equal", () => {
  assertEquals(convertibleInSort(ident("a"), ident("b"), "SProp"), true);
  assertEquals(convertibleInSort(call("f", ident("x")), ident("y"), "SProp"), true);
});

Deno.test("convertibleInSort: Prop falls back to normal conversion", () => {
  assertEquals(convertibleInSort(ident("a"), ident("a"), "Prop"), true);
  assertEquals(convertibleInSort(ident("a"), ident("b"), "Prop"), false);
});

Deno.test("convertibleInSort: no sort falls back to normal conversion", () => {
  assertEquals(convertibleInSort(ident("x"), ident("x")), true);
  assertEquals(convertibleInSort(ident("x"), ident("y")), false);
});

Deno.test("convertibleInSort: numeric sort falls back to normal conversion", () => {
  assertEquals(convertibleInSort(ident("a"), ident("a"), 0), true);
  assertEquals(convertibleInSort(ident("a"), ident("b"), 0), false);
});

// ─── Sort annotation parsing: SProp ────────────────────────────────

const SPROP_DECL_SOURCE = NATEQ_SYSTEM + `
system "SPropTest" extend "NatEq" {
  data StrictTrue : SProp {
    | STrue()
  }
}
`;

Deno.test("sort annotation: data X : SProp parses without error", () => {
  const result = compileCore(SPROP_DECL_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});

Deno.test("sort annotation: dataSorts contains SProp entry", () => {
  const result = compileCore(SPROP_DECL_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  const sys = result.systems.get("SPropTest");
  assertEquals(sys?.dataSorts?.get("StrictTrue"), "SProp");
});

// ─── SProp proof irrelevance in prove blocks ───────────────────────

const SPROP_IRRELEVANCE_SOURCE = NATEQ_SYSTEM + `
system "SPropIrrel" extend "NatEq" {
  data StrictUnit : SProp {
    | STT()
  }

  compute sunit(Zero) = STT
  compute sunit(Succ(k)) = STT

  prove strict_irrel(n) -> StrictUnit {
    | Zero -> STT
    | Succ(k) -> STT
  }
}
`;

Deno.test("SProp proof irrelevance: prove block with SProp return type typechecks", () => {
  const result = compileCore(SPROP_IRRELEVANCE_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});

// ─── SProp coexists with Prop ──────────────────────────────────────

const MIXED_SORTS_SOURCE = NATEQ_SYSTEM + `
system "MixedSorts" extend "NatEq" {
  data StrictTrue : SProp {
    | STrue()
  }

  data WeakTrue : Prop {
    | WTrue()
  }

  data Color : Set {
    | Red()
    | Green()
  }
}
`;

Deno.test("mixed sorts: SProp, Prop, and Set coexist", () => {
  const result = compileCore(MIXED_SORTS_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  const sys = result.systems.get("MixedSorts");
  assertEquals(sys?.dataSorts?.get("StrictTrue"), "SProp");
  assertEquals(sys?.dataSorts?.get("WeakTrue"), "Prop");
  assertEquals(sys?.dataSorts?.get("Color"), "Set");
});

// ─── Backward compatibility ────────────────────────────────────────

Deno.test("SProp: existing NatEq system still compiles", () => {
  const result = compileCore(NATEQ_SYSTEM);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});

Deno.test("SProp: existing proofs still typecheck", () => {
  const source = NATEQ_SYSTEM + `
system "SPropCompat" extend "NatEq" {
  prove plus_zero_right(n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
}
`;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});
