// Tests for code extraction (Phase 45).
// Verifies TypeScript/JS generation from compiled systems,
// Prop erasure, and correct handling of data types and compute rules.

import { assertEquals, assertStringIncludes } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { extractSystem, renderTypeScript, renderJavaScript } from "../lang/core/extract.ts";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileAndAssert(BASE + "\n" + extra);
}

function extractFirst(extra: string) {
  const result = compile(extra);
  // Get the last system (the one the test defined)
  const systems = [...result.systems.values()];
  return extractSystem(systems[systems.length - 1]);
}

// ─── Type extraction ───────────────────────────────────────────────

Deno.test("extract: Nat type with two constructors", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const nat = ext.types.find((t) => t.name === "Nat");
  assertEquals(nat !== undefined, true, "Nat type should be extracted");
  assertEquals(nat!.constructors.length, 2);
  assertEquals(nat!.constructors[0].name, "Zero");
  assertEquals(nat!.constructors[0].fields.length, 0);
  assertEquals(nat!.constructors[1].name, "Succ");
  assertEquals(nat!.constructors[1].fields.length, 1);
  assertEquals(nat!.constructors[1].fields[0].name, "pred");
});

Deno.test("extract: Bool type", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Bool { | True | False }
      compute not(True) = False
      compute not(False) = True
    }
  `);
  const bool = ext.types.find((t) => t.name === "Bool");
  assertEquals(bool !== undefined, true);
  assertEquals(bool!.constructors.length, 2);
  assertEquals(bool!.constructors[0].name, "True");
  assertEquals(bool!.constructors[1].name, "False");
});

Deno.test("extract: parameterized List type", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data List(A) { | Nil | Cons(head : A, tail : List(A)) }
      compute append(Nil, ys) = ys
      compute append(Cons(x, xs), ys) = Cons(x, append(xs, ys))
    }
  `);
  const list = ext.types.find((t) => t.name === "List");
  assertEquals(list !== undefined, true);
  assertEquals(list!.params, ["A"]);
  assertEquals(list!.constructors.length, 2);
  assertEquals(list!.constructors[1].name, "Cons");
  assertEquals(list!.constructors[1].fields.length, 2);
});

// ─── Function extraction ───────────────────────────────────────────

Deno.test("extract: add function with two clauses", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const add = ext.functions.find((f) => f.name === "add");
  assertEquals(add !== undefined, true, "add function should be extracted");
  assertEquals(add!.arity, 2);
  // May have inherited + redefined clauses
  assertEquals(add!.clauses.length >= 2, true, `expected ≥2 clauses, got ${add!.clauses.length}`);
});

Deno.test("extract: not function", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Bool { | True | False }
      compute not(True) = False
      compute not(False) = True
    }
  `);
  const notFn = ext.functions.find((f) => f.name === "not");
  assertEquals(notFn !== undefined, true);
  assertEquals(notFn!.arity, 1);
  assertEquals(notFn!.clauses.length, 2);
});

Deno.test("extract: append function", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data List(A) { | Nil | Cons(head : A, tail : List(A)) }
      compute append(Nil, ys) = ys
      compute append(Cons(x, xs), ys) = Cons(x, append(xs, ys))
    }
  `);
  const append = ext.functions.find((f) => f.name === "append");
  assertEquals(append !== undefined, true);
  assertEquals(append!.arity, 2);
});

// ─── Prop erasure ──────────────────────────────────────────────────

Deno.test("extract: proof agents are erased", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  // refl, sym, etc. should not appear as extracted functions
  const proofFuncs = ext.functions.filter((f) =>
    ["refl", "sym", "trans", "subst", "cong"].includes(f.name)
  );
  assertEquals(proofFuncs.length, 0, "proof agents should be erased");
});

Deno.test("extract: Eq type is erased", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      data Eq(A, a, b) : Prop { | Refl }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const eq = ext.types.find((t) => t.name === "Eq");
  assertEquals(eq, undefined, "Eq type should be erased (Prop)");
  assertEquals(ext.erased.includes("Eq"), true);
});

Deno.test("extract: Prop-declared data type is erased", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      data MyProp : Prop { | MkProp }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  assertEquals(ext.erased.includes("MyProp"), true, "Prop data type erased");
  assertEquals(ext.types.find(t => t.name === "MyProp"), undefined, "Prop type not in extracted types");
});

// ─── TypeScript rendering ──────────────────────────────────────────

Deno.test("render: TypeScript output contains type definitions", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const ts = renderTypeScript(ext);
  assertStringIncludes(ts, 'tag: "Zero"');
  assertStringIncludes(ts, 'tag: "Succ"');
  assertStringIncludes(ts, "export type Nat");
  assertStringIncludes(ts, "export function add");
});

Deno.test("render: TypeScript constructor functions", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const ts = renderTypeScript(ext);
  // Zero should be a const (no fields)
  assertStringIncludes(ts, 'export const Zero');
  // Succ should be a function (has fields)
  assertStringIncludes(ts, 'export function Succ');
});

Deno.test("render: TypeScript function with pattern matching", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const ts = renderTypeScript(ext);
  assertStringIncludes(ts, '.tag === "Zero"');
  assertStringIncludes(ts, '.tag === "Succ"');
});

Deno.test("render: field access uses field names not variable names", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const ts = renderTypeScript(ext);
  // Pattern `Succ(k)` should access field `pred`, not variable name `k`
  assertStringIncludes(ts, "x.pred", "should use field name 'pred' not variable name 'k'");
  assertEquals(ts.includes("x.k"), false, "should NOT use variable name as field accessor");
});

Deno.test("render: system name in header comment", () => {
  const ext = extractFirst(`
    system "MySystem" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const ts = renderTypeScript(ext);
  assertStringIncludes(ts, 'Extracted from system "MySystem"');
});

Deno.test("render: erased items listed in header", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const ts = renderTypeScript(ext);
  assertStringIncludes(ts, "Prop-erased:");
});

// ─── JavaScript rendering ──────────────────────────────────────────

Deno.test("render: JavaScript output has no type annotations", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
    }
  `);
  const js = renderJavaScript(ext);
  // Should not contain TypeScript type annotations
  assertEquals(js.includes(": any"), false, "JS output should not have type annotations");
  // Should still have function definitions
  assertStringIncludes(js, "function add");
});

// ─── Stdlib extraction (integration) ───────────────────────────────

Deno.test("extract: stdlib Nat system round-trips", () => {
  const result = compileCore(`
    include "stdlib"
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const stdlib = result.systems.get("Stdlib");
  if (!stdlib) return; // stdlib might not be present as a named system
  const ext = extractSystem(stdlib);
  const nat = ext.types.find((t) => t.name === "Nat");
  assertEquals(nat !== undefined, true, "Nat extracted from stdlib");
  const add = ext.functions.find((f) => f.name === "add");
  assertEquals(add !== undefined, true, "add extracted from stdlib");
});

Deno.test("extract: full TypeScript output is valid syntax", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Nat { | Zero | Succ(pred : Nat) }
      data Bool { | True | False }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))
      compute not(True) = False
      compute not(False) = True
    }
  `);
  const ts = renderTypeScript(ext);
  // Basic structural checks
  const opens = (ts.match(/{/g) || []).length;
  const closes = (ts.match(/}/g) || []).length;
  assertEquals(opens, closes, "braces should be balanced");
});

// ─── Edge cases ────────────────────────────────────────────────────

Deno.test("extract: empty system yields empty extraction", () => {
  const ext = extractFirst(`
    system "Empty" extend "NatEq" { }
  `);
  // Should have inherited types/functions but no new ones beyond inherited
  assertEquals(ext.systemName, "Empty");
});

Deno.test("extract: Option type with type parameter", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Option(A) { | None | Some(value : A) }
    }
  `);
  const opt = ext.types.find((t) => t.name === "Option");
  assertEquals(opt !== undefined, true);
  assertEquals(opt!.params, ["A"]);
  assertEquals(opt!.constructors.length, 2);
});

Deno.test("extract: record type extracts", () => {
  const ext = extractFirst(`
    system "T" extend "NatEq" {
      data Sigma(A, B) { | Pair(fst : A, snd : B) }
    }
  `);
  const sigma = ext.types.find((t) => t.name === "Sigma");
  assertEquals(sigma !== undefined, true);
  assertEquals(sigma!.constructors[0].name, "Pair");
  assertEquals(sigma!.constructors[0].fields.length, 2);
});
