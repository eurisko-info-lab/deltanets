// Tests for auto-generated eliminators (TypeName_rec) from data declarations.

import { assertEquals } from "$std/assert/mod.ts";
import { compileAndAssert } from "./helpers.ts";

// ─── Nat_rec eliminator ────────────────────────────────────────────

const NAT_SOURCE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }
}
`;

Deno.test("eliminator: Nat_rec rules auto-generated", () => {
  const core = compileAndAssert(NAT_SOURCE);
  const nat = core.systems.get("Nat")!;
  const recRules = nat.computeRules.filter((r) => r.funcName === "Nat_rec");
  assertEquals(recRules.length, 2, "two Nat_rec rules: base + step");
});

Deno.test("eliminator: Nat_rec Zero rule — base case returns first method arg", () => {
  const core = compileAndAssert(NAT_SOURCE);
  const nat = core.systems.get("Nat")!;
  const recRules = nat.computeRules.filter((r) => r.funcName === "Nat_rec");
  // Find the Zero rule (scrutinee-first: args[0] is the ctor)
  const zeroRule = recRules.find((r) => {
    const first = r.args[0];
    return first.kind === "ctor" && first.name === "Zero";
  })!;
  assertEquals(zeroRule !== undefined, true, "Zero rule exists");
  // scrutinee + two method args = 3 total
  assertEquals(zeroRule.args.length, 3);
  // Result should be the Zero-method arg (ident)
  assertEquals(zeroRule.result.kind, "ident");
});

Deno.test("eliminator: Nat_rec Succ rule — step case recurses", () => {
  const core = compileAndAssert(NAT_SOURCE);
  const nat = core.systems.get("Nat")!;
  const recRules = nat.computeRules.filter((r) => r.funcName === "Nat_rec");
  const succRule = recRules.find((r) => {
    const first = r.args[0];
    return first.kind === "ctor" && first.name === "Succ";
  })!;
  assertEquals(succRule !== undefined, true, "Succ rule exists");
  assertEquals(succRule.args.length, 3);
  // Result should be a call to the step method _m1
  assertEquals(succRule.result.kind, "call");
  if (succRule.result.kind === "call") {
    // Arguments should include the field var and a recursive Nat_rec call
    const hasRecCall = succRule.result.args.some(
      (a) => a.kind === "call" && a.name === "Nat_rec"
    );
    assertEquals(hasRecCall, true, "step method receives recursive call");
  }
});

// ─── Bool_rec eliminator ───────────────────────────────────────────

const BOOL_SOURCE = `
include "prelude"

system "Bool" extend "Prelude" {
  data Bool {
    | True
    | False
  }
}
`;

Deno.test("eliminator: Bool_rec rules for nullary constructors", () => {
  const core = compileAndAssert(BOOL_SOURCE);
  const sys = core.systems.get("Bool")!;
  const recRules = sys.computeRules.filter((r) => r.funcName === "Bool_rec");
  assertEquals(recRules.length, 2, "two Bool_rec rules");
  // Both constructors are nullary, so result is just the method ident
  for (const rule of recRules) {
    assertEquals(rule.result.kind, "ident", "nullary ctor → method ident");
    assertEquals(rule.args.length, 3, "2 methods + scrutinee");
  }
});

// ─── Nat_rec normalization in prove ────────────────────────────────

const NAT_REC_PROVE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

  agent refl(principal)
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}

system "RecProofs" extend "Nat" {
  prove rec_identity(n : Nat) -> Eq(Nat_rec(n, Zero, Succ), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(rec_identity(k))
  }
}
`;

Deno.test("eliminator: Nat_rec normalizes in prove block", () => {
  // Nat_rec(Zero, Zero, Succ) = Zero  → Eq(Zero, Zero) → refl
  // Nat_rec(Succ(k), Zero, Succ) = Succ(k, Nat_rec(k, Zero, Succ))
  //   → cong_succ applied to recursive call
  const core = compileAndAssert(NAT_REC_PROVE);
  const sys = core.systems.get("RecProofs")!;
  assertEquals(sys.agents.has("rec_identity"), true);
});
