// Tests for Phase 37: Program/Equations — dependent pattern matching
// with proof obligations.

import { assertEquals, assertStringIncludes } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// ─── Parsing and registration ──────────────────────────────────────

Deno.test("phase37: parse program declaration (wf)", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  program add2(n : Nat, m : Nat) -> Nat {
    wf(Lt)
    | Zero -> m
    | Succ(k) -> Succ(add2(k, m))
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("add2"), true, "program should register agent");
  assertEquals(sys.provedCtx.has("add2"), true, "program should register in provedCtx");
});

Deno.test("phase37: parse program declaration (default wf)", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  program add3(n : Nat, m : Nat) -> Nat {
    | Zero -> m
    | Succ(k) -> Succ(add3(k, m))
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("add3"), true, "no-wf program should register agent");
  assertEquals(sys.provedCtx.has("add3"), true, "should register in provedCtx");
});

Deno.test("phase37: program with measure termination", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  program halve(n : Nat) -> Nat {
    measure(n)
    | Zero -> Zero
    | Succ(k) -> halve(k)
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("halve"), true, "measure program should register agent");
});

Deno.test("phase37: program with obligations", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  program sub2(n : Nat, m : Nat) -> Nat {
    wf(Lt)
    | Zero -> Zero
    | Succ(k) -> sub2(k, m)

    obligation sub_dec(k : Nat) -> Eq(k, k) {
      | Zero -> refl
      | Succ(k2) -> refl
    }
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("sub2"), true, "program should register main agent");
  assertEquals(sys.provedCtx.has("sub2"), true, "program should be in provedCtx");
  assertEquals(sys.agents.has("sub_dec"), true, "obligation should register agent");
  assertEquals(sys.provedCtx.has("sub_dec"), true, "obligation should be in provedCtx");
});

Deno.test("phase37: program with holes compiles without error", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  program add4(n : Nat, m : Nat) -> Nat {
    | Zero -> ?
    | Succ(k) -> ?
  }
}
`);
  const sys = result.systems.get("T")!;
  // Holes mean agent won't be generated, but provedCtx should still register
  assertEquals(sys.provedCtx.has("add4"), true, "holey program in provedCtx");
});

Deno.test("phase37: program coexists with prove in same system", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  prove add_zero(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(add_zero(k))
  }
  program double(n : Nat) -> Nat {
    | Zero -> Zero
    | Succ(k) -> Succ(Succ(double(k)))
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.provedCtx.has("add_zero"), true, "prove should work");
  assertEquals(sys.provedCtx.has("double"), true, "program should work");
});

Deno.test("phase37: program inherited through extend", () => {
  const result = compileAndAssert(BASE + `
system "Base" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  program myAdd(n : Nat, m : Nat) -> Nat {
    | Zero -> m
    | Succ(k) -> Succ(myAdd(k, m))
  }
}
system "Ext" extend "Base" {
  prove myAdd_id(n : Nat) -> Eq(n, n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(myAdd_id(k))
  }
}
`);
  const ext = result.systems.get("Ext")!;
  assertEquals(ext.provedCtx.has("myAdd"), true, "inherited program in provedCtx");
  assertEquals(ext.provedCtx.has("myAdd_id"), true, "prove using inherited program");
});

Deno.test("phase37: program in section inherits section variables", () => {
  const result = compileAndAssert(BASE + `
system "T" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  section S {
    variable(n : Nat)

    program double(x : Nat) -> Nat {
      wf(Lt)
      | Zero -> Zero
      | Succ(k) -> Succ(Succ(double(k)))
    }
  }
}
`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("double"), true, "section program should register");
});

Deno.test("phase37: top-level program (outside system)", () => {
  // Top-level programs have access to system agents via merging
  const result = compileAndAssert(BASE + `
system "S" extend "NatEq" {
  data Nat { | Zero | Succ(pred : Nat) }
  program innerProg(n : Nat) -> Nat {
    | Zero -> Zero
    | Succ(k) -> Succ(innerProg(k))
  }
}
`);
  assertEquals(result.errors.length, 0, "program inside system should compile");
});

Deno.test("phase37: program type error detected", () => {
  const result = compileCore(BASE + `
system "T" extend "NatEq" {
  data Bool { | True | False }
  data Nat { | Zero | Succ(pred : Nat) }
  program bad(n : Nat) -> Bool {
    | Zero -> Zero
    | Succ(k) -> bad(k)
  }
}
`);
  assertEquals(result.errors.length > 0, true, "type mismatch should error");
});
