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
