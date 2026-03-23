// Tests for Phase 30: Typeclasses — class/instance declarations with method dispatch.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NAT_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NAT_SYSTEM;

// ─── Basic class declaration ────────────────────────────────────────

Deno.test("typeclass: class declaration registers ClassDef", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      class Show(A) { show : A }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.classes !== undefined, true, "should have classes");
  assertEquals(sys.classes!.has("Show"), true, "should have Show class");
  const cls = sys.classes!.get("Show")!;
  assertEquals(cls.name, "Show");
  assertEquals(cls.params, ["A"]);
  assertEquals(cls.methods.length, 1);
  assertEquals(cls.methods[0].name, "show");
});

Deno.test("typeclass: class with multiple methods", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      class Monoid(A) { empty : A, append : A }
    }
  `);
  const sys = result.systems.get("T")!;
  const cls = sys.classes!.get("Monoid")!;
  assertEquals(cls.methods.length, 2);
  assertEquals(cls.methods[0].name, "empty");
  assertEquals(cls.methods[1].name, "append");
});

// ─── Instance declaration ────────────────────────────────────────────

Deno.test("typeclass: instance registers InstanceDef", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      agent showNat(principal, result)

      class Show(A) { show : A }
      instance Show(Nat) { show = showNat }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.instances !== undefined, true, "should have instances");
  assertEquals(sys.instances!.length, 1);
  const inst = sys.instances![0];
  assertEquals(inst.className, "Show");
  assertEquals(inst.args, ["Nat"]);
  assertEquals(inst.methods.get("show"), "showNat");
});

Deno.test("typeclass: instance generates compute rules", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      agent showNat(principal, result)

      class Show(A) { show : A }
      instance Show(Nat) { show = showNat }
    }
  `);
  const sys = result.systems.get("T")!;
  const cr = sys.computeRules.find((r) => r.head === "show" && r.patterns.length === 1 && r.patterns[0].kind === "ident" && r.patterns[0].name === "Nat");
  assertEquals(cr !== undefined, true, "should have compute rule for show(Nat)");
  assertEquals(cr!.body.kind, "ident");
  if (cr!.body.kind === "ident") {
    assertEquals(cr!.body.name, "showNat");
  }
});

// ─── Error cases ───────────────────────────────────────────────────

Deno.test("typeclass: instance for unknown class throws", () => {
  const result = compileCore(BASE + `
    system "T" extend "Nat" {
      instance Unknown(Nat) { foo = bar }
    }
  `);
  assertEquals(result.errors.length > 0, true, "expected error for unknown class");
  assertEquals(result.errors.some((e: string) => e.includes("unknown class")), true);
});

Deno.test("typeclass: instance with unknown method throws", () => {
  const result = compileCore(BASE + `
    system "T" extend "Nat" {
      class Show(A) { show : A }
      instance Show(Nat) { display = showNat }
    }
  `);
  assertEquals(result.errors.length > 0, true, "expected error for unknown method");
  assertEquals(result.errors.some((e: string) => e.includes("unknown method")), true);
});

Deno.test("typeclass: instance missing method throws", () => {
  const result = compileCore(BASE + `
    system "T" extend "Nat" {
      class Monoid(A) { empty : A, append : A }
      instance Monoid(Nat) { empty = Zero }
    }
  `);
  assertEquals(result.errors.length > 0, true, "expected error for missing method");
  assertEquals(result.errors.some((e: string) => e.includes("missing method")), true);
});

// ─── Inheritance through extend ──────────────────────────────────

Deno.test("typeclass: class inherited through extend", () => {
  const result = compileAndAssert(BASE + `
    system "Base" extend "Nat" {
      class Show(A) { show : A }
    }
    system "Ext" extend "Base" {
      agent showNat(principal, result)
      instance Show(Nat) { show = showNat }
    }
  `);
  const sys = result.systems.get("Ext")!;
  assertEquals(sys.classes!.has("Show"), true, "extended system has class");
  assertEquals(sys.instances!.length, 1, "extended system has instance");
});

// ─── Inheritance through compose ─────────────────────────────────

Deno.test("typeclass: class/instance merged through compose", () => {
  const result = compileAndAssert(BASE + `
    system "A" extend "Nat" {
      class Show(A) { show : A }
    }
    system "B" extend "Nat" {
      agent showNat(principal, result)
    }
    system "C" = compose "A" + "B" {
      instance Show(Nat) { show = showNat }
    }
  `);
  const sys = result.systems.get("C")!;
  assertEquals(sys.classes!.has("Show"), true, "composed system has class");
  assertEquals(sys.instances!.length, 1, "composed system has instance");
});

// ─── Class with no params ────────────────────────────────────────

Deno.test("typeclass: class with no params", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      class Unit { value : Nat }
    }
  `);
  const sys = result.systems.get("T")!;
  const cls = sys.classes!.get("Unit")!;
  assertEquals(cls.params, []);
  assertEquals(cls.methods.length, 1);
});
