// Tests for module system: open (selective import) and export (visibility control).

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { compileAndAssert, NAT_SYSTEM, collectRules, collectAgentPorts, reduceAll, readNat } from "./helpers.ts";

// ─── open: import agents from another system ───────────────────────

Deno.test("module: open imports all agents from another system", () => {
  const result = compileAndAssert(`
    include "prelude"

    system "Nat" {
      agent Zero(principal)
      agent Succ(principal, pred)
    }

    system "Arith" {
      open "Nat"
      agent add(principal, result, accum)
      rule add <> Zero -> { relink left.result left.accum }
      rule add <> Succ -> {
        let s = Succ
        let a = add
        relink left.result s.principal
        wire s.pred -- a.result
        relink left.accum a.accum
        relink right.pred a.principal
      }
    }
  `);
  const sys = result.systems.get("Arith")!;
  assertEquals(sys.agents.has("Zero"), true, "should have Zero from open");
  assertEquals(sys.agents.has("Succ"), true, "should have Succ from open");
  assertEquals(sys.agents.has("add"), true, "should have own add agent");
});

Deno.test("module: open use selects specific agents", () => {
  const result = compileAndAssert(`
    include "prelude"

    system "Nat" {
      agent Zero(principal)
      agent Succ(principal, pred)
      agent Double(principal, result)
    }

    system "Minimal" {
      open "Nat" use Zero, Succ
      agent myFunc(principal, result)
    }
  `);
  const sys = result.systems.get("Minimal")!;
  assertEquals(sys.agents.has("Zero"), true, "should have Zero");
  assertEquals(sys.agents.has("Succ"), true, "should have Succ");
  assertEquals(sys.agents.has("Double"), false, "should NOT have Double");
  assertEquals(sys.agents.has("myFunc"), true, "should have own agent");
});

Deno.test("module: open imports rules between visible agents", () => {
  const result = compileAndAssert(`
    include "prelude"

    system "Nat" {
      agent Zero(principal)
      agent Succ(principal, pred)
      agent add(principal, result, accum)
      rule add <> Zero -> { relink left.result left.accum }
    }

    system "User" {
      open "Nat"
    }
  `);
  const sys = result.systems.get("User")!;
  assertEquals(sys.rules.length >= 1, true, "should have imported rule");
  assertEquals(sys.rules.some(r => r.agentA === "add" && r.agentB === "Zero"), true);
});

// ─── export: visibility control ────────────────────────────────────

Deno.test("module: export restricts visible agents for open", () => {
  const result = compileAndAssert(`
    include "prelude"

    system "Internal" {
      agent Public(principal)
      agent Private(principal, value)
      export Public
    }

    system "Consumer" {
      open "Internal"
    }
  `);
  const sys = result.systems.get("Consumer")!;
  assertEquals(sys.agents.has("Public"), true, "should have exported Public");
  assertEquals(sys.agents.has("Private"), false, "should NOT have non-exported Private");
});

Deno.test("module: export with open use respects both filters", () => {
  const result = compileAndAssert(`
    include "prelude"

    system "Lib" {
      agent A(principal)
      agent B(principal)
      agent C(principal)
      export A, B
    }

    system "App" {
      open "Lib" use A
    }
  `);
  const sys = result.systems.get("App")!;
  assertEquals(sys.agents.has("A"), true, "should have A (exported + selected)");
  assertEquals(sys.agents.has("B"), false, "should NOT have B (exported but not selected)");
  assertEquals(sys.agents.has("C"), false, "should NOT have C (not exported)");
});

// ─── open with data types ──────────────────────────────────────────

Deno.test("module: open imports data type constructors", () => {
  const result = compileAndAssert(NAT_SYSTEM + `
    system "Lists" {
      open "Nat"
      data List(A) {
        | Nil
        | Cons(head : A, tail : List(A))
      }
    }
  `);
  const sys = result.systems.get("Lists")!;
  assertEquals(sys.agents.has("Zero"), true, "should have Nat agents");
  assertEquals(sys.agents.has("Succ"), true, "should have Nat agents");
  assertEquals(sys.agents.has("Nil"), true, "should have List constructors");
  assertEquals(sys.agents.has("Cons"), true, "should have List constructors");
});

Deno.test("module: open with extend inherits and opens", () => {
  const result = compileAndAssert(`
    include "prelude"

    system "Base" {
      agent Zero(principal)
      agent Succ(principal, pred)
    }

    system "Extra" {
      agent Double(principal, result)
    }

    system "Combined" extend "Base" {
      open "Extra"
    }
  `);
  const sys = result.systems.get("Combined")!;
  assertEquals(sys.agents.has("Zero"), true, "from extend");
  assertEquals(sys.agents.has("Succ"), true, "from extend");
  assertEquals(sys.agents.has("Double"), true, "from open");
});

// ═══════════════════════════════════════════════════════════════════
// Phase 42: Module type declarations, sealing, functors, aliases
// ═══════════════════════════════════════════════════════════════════

const { assert } = await import("$std/assert/mod.ts");

// ─── module type declarations ──────────────────────────────────────

Deno.test("module type: basic declaration", () => {
  const r = compileAndAssert(`
    module type "Monoid" {
      agent e(principal)
      agent op(principal, result, second)
    }
  `);
  assert(r.moduleTypes.has("Monoid"), "missing Monoid module type");
  const mt = r.moduleTypes.get("Monoid")!;
  assertEquals(mt.specs.length, 2);
  assertEquals(mt.specs[0].name, "e");
  assertEquals(mt.specs[0].arity, 1);
  assertEquals(mt.specs[1].name, "op");
  assertEquals(mt.specs[1].arity, 3);
});

Deno.test("module type: empty signature", () => {
  const r = compileAndAssert(`
    module type "Empty" { }
  `);
  assert(r.moduleTypes.has("Empty"));
  assertEquals(r.moduleTypes.get("Empty")!.specs.length, 0);
});

// ─── system sealing ────────────────────────────────────────────────

Deno.test("seal: system satisfies signature", () => {
  const r = compileAndAssert(`
    module type "HasBool" {
      agent myTrue(principal)
      agent myFalse(principal)
      agent myNot(principal, result)
    }
    system "BoolImpl" : "HasBool" {
      agent myTrue(principal)
      agent myFalse(principal)
      agent myNot(principal, result)
      rule myNot <> myTrue -> { let f = myFalse  relink left.result f.principal }
      rule myNot <> myFalse -> { let t = myTrue  relink left.result t.principal }
    }
  `);
  const sys = r.systems.get("BoolImpl")!;
  assert(sys.exports, "sealed system should have exports set");
  assert(sys.exports!.has("myTrue"));
  assert(sys.exports!.has("myFalse"));
  assert(sys.exports!.has("myNot"));
});

Deno.test("seal: missing agent produces error", () => {
  const r = compileCore(`
    module type "NeedTwo" {
      agent foo(principal)
      agent bar(principal, result)
    }
    system "OnlyFoo" : "NeedTwo" {
      agent foo(principal)
    }
  `);
  assert(r.errors.length > 0, "should have errors");
  assert(r.errors.some(e => e.includes("bar")), `expected error about 'bar': ${r.errors}`);
});

Deno.test("seal: wrong arity produces error", () => {
  const r = compileCore(`
    module type "Sig" {
      agent op(principal, result, second)
    }
    system "WrongArity" : "Sig" {
      agent op(principal, result)
    }
  `);
  assert(r.errors.length > 0, "should have errors");
  assert(r.errors.some(e => e.includes("ports")), `expected arity error: ${r.errors}`);
});

Deno.test("seal: extend with seal", () => {
  const r = compileAndAssert(`
    include "prelude"
    module type "HasAdd" {
      agent Zero(principal)
      agent Succ(principal, pred)
      agent add(principal, result, accum)
    }
    system "NatBase" extend "Prelude" {
      data Nat { | Zero | Succ(pred : Nat) }
      agent add(principal, result, accum)
      rule add <> Zero -> { relink left.result left.accum }
      rule add <> Succ -> {
        let s = Succ
        let a = add
        relink left.result s.principal
        wire s.pred -- a.result
        relink left.accum a.accum
        relink right.pred a.principal
      }
    }
    system "NatSealed" : "HasAdd" extend "NatBase" { }
  `);
  const sys = r.systems.get("NatSealed")!;
  assert(sys.exports, "sealed system should have exports");
  assertEquals(sys.exports!.size, 3);
});

// ─── alias declarations ────────────────────────────────────────────

Deno.test("alias: basic agent alias", () => {
  const r = compileAndAssert(`
    module type "HasE" {
      agent e(principal)
    }
    system "WithAlias" : "HasE" {
      agent Zero(principal)
      alias e = Zero
    }
  `);
  const sys = r.systems.get("WithAlias")!;
  assert(sys.agents.has("e"), "alias should create agent");
  assert(sys.agents.has("Zero"), "original should exist");
});

Deno.test("alias: unknown target errors", () => {
  const r = compileCore(`
    system "BadAlias" {
      alias e = NonExistent
    }
  `);
  assert(r.errors.length > 0, "should have errors");
});

Deno.test("alias: copies rules from target", () => {
  const r = compileAndAssert(`
    system "AliasRules" {
      agent A(principal)
      agent B(principal, result)
      rule B <> A -> { let a = A  relink left.result a.principal }
      alias C = A
    }
  `);
  const sys = r.systems.get("AliasRules")!;
  assert(sys.agents.has("C"), "alias C should exist");
  // Original rule: B <> A
  // Alias should produce: B <> C
  assert(sys.rules.some(r => r.agentA === "B" && r.agentB === "C"),
    `expected B <> C rule, got: ${sys.rules.map(r => `${r.agentA} <> ${r.agentB}`).join(", ")}`);
});

// ─── functor declarations ──────────────────────────────────────────

Deno.test("functor: basic declaration", () => {
  const r = compileAndAssert(`
    module type "Carrier" {
      agent e(principal)
      agent op(principal, result, second)
    }
    module "Double" (M : "Carrier") {
      agent double(principal, result)
    }
  `);
  assert(r.functors.has("Double"), "functor should be stored");
  const f = r.functors.get("Double")!;
  assertEquals(f.params.length, 1);
  assertEquals(f.params[0].name, "M");
  assertEquals(f.params[0].sig, "Carrier");
});

Deno.test("functor: with extend base", () => {
  const r = compileAndAssert(`
    include "prelude"
    module type "Sig" {
      agent e(principal)
    }
    module "F" (M : "Sig") extend "Prelude" {
      agent wrap(principal, result)
    }
  `);
  const f = r.functors.get("F")!;
  assertEquals(f.base, "Prelude");
});

// ─── functor application ───────────────────────────────────────────

Deno.test("functor app: basic instantiation", () => {
  const r = compileAndAssert(`
    module type "HasE" {
      agent e(principal)
    }
    system "Impl" {
      agent e(principal)
    }
    module "F" (M : "HasE") {
      agent wrap(principal, result)
    }
    module "Result" := "F"("Impl")
  `);
  assert(r.systems.has("Result"), "functor app should create system");
  const sys = r.systems.get("Result")!;
  assert(sys.agents.has("e"), "should have sig agent from arg");
  assert(sys.agents.has("wrap"), "should have agent from functor body");
});

Deno.test("functor app: inherits rules from argument", () => {
  const r = compileAndAssert(`
    module type "BoolSig" {
      agent myTrue(principal)
      agent myFalse(principal)
      agent myNot(principal, result)
    }
    system "BoolImpl" {
      agent myTrue(principal)
      agent myFalse(principal)
      agent myNot(principal, result)
      rule myNot <> myTrue -> { let f = myFalse  relink left.result f.principal }
      rule myNot <> myFalse -> { let t = myTrue  relink left.result t.principal }
    }
    module "Negate" (B : "BoolSig") {
      agent doubleNeg(principal, result)
      rule doubleNeg <> myTrue -> {
        let n1 = myNot
        let n2 = myNot
        wire n1.result -- n2.principal
        relink left.result n2.result
        let t = myTrue
        relink t.principal n1.principal
      }
    }
    module "BoolNeg" := "Negate"("BoolImpl")
  `);
  const sys = r.systems.get("BoolNeg")!;
  assert(sys.agents.has("doubleNeg"), "should have functor body agent");
  assert(sys.agents.has("myNot"), "should have arg agent");
  assert(sys.rules.length >= 3, `expected >=3 rules, got ${sys.rules.length}`);
});

Deno.test("functor app: with extend base", () => {
  const r = compileAndAssert(`
    include "prelude"
    module type "EqSig" {
      agent refl(principal)
    }
    system "EqImpl" {
      agent refl(principal)
    }
    module "F" (E : "EqSig") extend "Prelude" {
      agent myAgent(principal, result)
    }
    module "Result" := "F"("EqImpl")
  `);
  const sys = r.systems.get("Result")!;
  assert(sys.agents.has("refl"), "should have sig agent");
  assert(sys.agents.has("myAgent"), "should have functor agent");
  assert(sys.agents.has("root"), "should have Prelude agents");
});

Deno.test("functor app: arg missing sig agent errors", () => {
  const r = compileCore(`
    module type "NeedFoo" {
      agent foo(principal)
    }
    system "NoFoo" {
      agent bar(principal)
    }
    module "F" (M : "NeedFoo") {
      agent wrap(principal)
    }
    module "Bad" := "F"("NoFoo")
  `);
  assert(r.errors.length > 0, "should have errors");
  assert(r.errors.some(e => e.includes("foo")), `expected error about 'foo': ${r.errors}`);
});

Deno.test("functor app: unknown functor errors", () => {
  const r = compileCore(`
    module "Bad" := "NonExistent"("Arg")
  `);
  assert(r.errors.length > 0, "should have errors");
  assert(r.errors.some(e => e.includes("NonExistent")), `expected functor error: ${r.errors}`);
});

Deno.test("functor app: wrong argument count errors", () => {
  const r = compileCore(`
    module type "Sig" {
      agent e(principal)
    }
    module "F" (M : "Sig") {
      agent wrap(principal)
    }
    module "Bad" := "F"("A", "B")
  `);
  assert(r.errors.length > 0, "should have errors");
});

Deno.test("functor app: multiple parameters", () => {
  const r = compileAndAssert(`
    module type "Sig1" {
      agent a1(principal)
    }
    module type "Sig2" {
      agent a2(principal, result)
    }
    system "Impl1" {
      agent a1(principal)
    }
    system "Impl2" {
      agent a2(principal, result)
    }
    module "Multi" (X : "Sig1", Y : "Sig2") {
      agent combined(principal, result)
    }
    module "Result" := "Multi"("Impl1", "Impl2")
  `);
  const sys = r.systems.get("Result")!;
  assert(sys.agents.has("a1"), "should have a1 from first arg");
  assert(sys.agents.has("a2"), "should have a2 from second arg");
  assert(sys.agents.has("combined"), "should have functor body agent");
});

Deno.test("functor app: data types from argument", () => {
  const r = compileAndAssert(`
    include "prelude"
    module type "NatSig" {
      agent Zero(principal)
      agent Succ(principal, pred)
      agent add(principal, result, accum)
    }
    system "NatImpl" extend "Prelude" {
      data Nat { | Zero | Succ(pred : Nat) }
      agent add(principal, result, accum)
      rule add <> Zero -> { relink left.result left.accum }
      rule add <> Succ -> {
        let s = Succ
        let a = add
        relink left.result s.principal
        wire s.pred -- a.result
        relink left.accum a.accum
        relink right.pred a.principal
      }
    }
    module "NatOps" (N : "NatSig") extend "Prelude" {
      agent isZero(principal, result)
      rule isZero <> Zero -> {
        let t = Zero
        relink left.result t.principal
      }
      rule isZero <> Succ -> {
        erase right.pred
        let s = Succ
        let z = Zero
        relink left.result s.principal
        relink z.principal s.pred
      }
    }
    module "MyNatOps" := "NatOps"("NatImpl")
  `);
  const sys = r.systems.get("MyNatOps")!;
  assert(sys.agents.has("isZero"), "should have functor agent");
  assert(sys.agents.has("Zero"), "should have Zero from arg");
  assert(sys.agents.has("Succ"), "should have Succ from arg");
  assert(sys.agents.has("add"), "should have add from arg");
});
