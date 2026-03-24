// Tests for Phase 33: Prop / Set / Type sorting.

import { assertEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  isPropSort,
  sortOf,
  typeSubsumes,
  universeLevel,
  typeUniverse,
} from "@deltanets/lang";
import type { Sort } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

// ─── Helper expression constructors ────────────────────────────────

function ident(name: string) {
  return { kind: "ident" as const, name };
}

function call(name: string, ...args: { kind: string; name?: string }[]) {
  return { kind: "call" as const, name, args: args as any[] };
}

// ─── universeLevel tests ───────────────────────────────────────────

Deno.test("universeLevel: Prop returns -2", () => {
  assertEquals(universeLevel(ident("Prop")), -2);
});

Deno.test("universeLevel: Type(0) returns 0", () => {
  assertEquals(universeLevel(call("Type", ident("0"))), 0);
});

Deno.test("universeLevel: Type(1) returns 1", () => {
  assertEquals(universeLevel(call("Type", ident("1"))), 1);
});

// ─── isPropSort tests ──────────────────────────────────────────────

Deno.test("isPropSort: Prop is Prop", () => {
  assertEquals(isPropSort(ident("Prop")), true);
});

Deno.test("isPropSort: Type(0) is not Prop", () => {
  assertEquals(isPropSort(call("Type", ident("0"))), false);
});

Deno.test("isPropSort: arbitrary ident is not Prop", () => {
  assertEquals(isPropSort(ident("Nat")), false);
});

// ─── typeUniverse tests ────────────────────────────────────────────

Deno.test("typeUniverse: Prop inhabits Type₀", () => {
  assertEquals(typeUniverse(ident("Prop")), 0);
});

Deno.test("typeUniverse: Type(0) inhabits Type(1)", () => {
  assertEquals(typeUniverse(call("Type", ident("0"))), 1);
});

// ─── typeSubsumes tests ────────────────────────────────────────────

Deno.test("typeSubsumes: Prop ≤ Prop", () => {
  assertEquals(typeSubsumes(ident("Prop"), ident("Prop")), true);
});

Deno.test("typeSubsumes: Prop ≤ Type(0)", () => {
  assertEquals(typeSubsumes(ident("Prop"), call("Type", ident("0"))), true);
});

Deno.test("typeSubsumes: Prop ≤ Type(1)", () => {
  assertEquals(typeSubsumes(ident("Prop"), call("Type", ident("1"))), true);
});

Deno.test("typeSubsumes: Type(0) NOT ≤ Prop", () => {
  assertEquals(typeSubsumes(call("Type", ident("0")), ident("Prop")), false);
});

Deno.test("typeSubsumes: Type(0) ≤ Type(1)", () => {
  assertEquals(typeSubsumes(call("Type", ident("0")), call("Type", ident("1"))), true);
});

Deno.test("typeSubsumes: Type(1) NOT ≤ Type(0)", () => {
  assertEquals(typeSubsumes(call("Type", ident("1")), call("Type", ident("0"))), false);
});

// ─── sortOf tests ──────────────────────────────────────────────────

Deno.test("sortOf: Eq is always Prop", () => {
  assertEquals(sortOf(call("Eq", ident("Nat"), ident("a"), ident("b"))), "Prop");
});

Deno.test("sortOf: Prop literal returns Prop", () => {
  assertEquals(sortOf(ident("Prop")), "Prop");
});

Deno.test("sortOf: user-declared Prop data type returns Prop", () => {
  const ds = new Map<string, "Prop" | "Set">([["MyProp", "Prop"]]);
  assertEquals(sortOf(ident("MyProp"), ds), "Prop");
  assertEquals(sortOf(call("MyProp", ident("x")), ds), "Prop");
});

Deno.test("sortOf: user-declared Set data type returns 0", () => {
  const ds = new Map<string, "Prop" | "Set">([["MySet", "Set"]]);
  assertEquals(sortOf(ident("MySet"), ds), 0);
});

Deno.test("sortOf: Pi with Prop codomain is impredicative", () => {
  const propCodomain = {
    kind: "pi" as const,
    param: "x",
    domain: call("Type", ident("0")),
    codomain: ident("Prop"),
  };
  assertEquals(sortOf(propCodomain), "Prop");
});

Deno.test("sortOf: Pi with non-Prop codomain is not Prop", () => {
  const typeCodomain = {
    kind: "pi" as const,
    param: "x",
    domain: call("Type", ident("0")),
    codomain: ident("Nat"),
  };
  assertEquals(sortOf(typeCodomain) !== "Prop", true);
});

// ─── Sort annotation parsing via compileCore ───────────────────────

const PROP_DECL_SOURCE = NATEQ_SYSTEM + `
system "SortTest" extend "NatEq" {
  data Trivial : Prop {
    | MkTrivial()
  }
}
`;

Deno.test("sort annotation: data X : Prop parses without error", () => {
  const result = compileCore(PROP_DECL_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});

Deno.test("sort annotation: dataSorts contains Prop entry", () => {
  const result = compileCore(PROP_DECL_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  const sys = result.systems.get("SortTest");
  assertEquals(sys?.dataSorts?.get("Trivial"), "Prop");
});

const SET_DECL_SOURCE = NATEQ_SYSTEM + `
system "SetTest" extend "NatEq" {
  data Color : Set {
    | Red()
    | Green()
    | Blue()
  }
}
`;

Deno.test("sort annotation: data X : Set parses and stores in dataSorts", () => {
  const result = compileCore(SET_DECL_SOURCE);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  const sys = result.systems.get("SetTest");
  assertEquals(sys?.dataSorts?.get("Color"), "Set");
});

// ─── Backward compatibility ────────────────────────────────────────

Deno.test("sort: existing NatEq system compiles without errors", () => {
  const result = compileCore(NATEQ_SYSTEM);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});

Deno.test("sort: existing proofs still typecheck after sort changes", () => {
  const source = NATEQ_SYSTEM + `
system "SortCompat" extend "NatEq" {
  prove plus_zero_right(n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
}
`;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
});
