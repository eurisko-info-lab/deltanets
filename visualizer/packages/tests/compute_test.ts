// Tests for `compute` declarations — user-declared normalization rules
// that replace hardcoded NORM_RULES and enable extensible dependent typing.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { compileAndAssert } from "./helpers.ts";

// ─── Parsing tests ─────────────────────────────────────────────────

const COMPUTE_NAT = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

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

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}
`;

Deno.test("compute: parses without errors", () => {
  const core = compileAndAssert(COMPUTE_NAT);
  const nat = core.systems.get("Nat")!;
  // 2 explicit add rules + 2 auto-generated Nat_rec rules
  assertEquals(nat.computeRules.length, 4);
});

Deno.test("compute: rule funcName is correct", () => {
  const core = compileAndAssert(COMPUTE_NAT);
  const nat = core.systems.get("Nat")!;
  assertEquals(nat.computeRules[0].funcName, "add");
  assertEquals(nat.computeRules[1].funcName, "add");
});

Deno.test("compute: base case pattern — Zero resolves to ctor", () => {
  const core = compileAndAssert(COMPUTE_NAT);
  const nat = core.systems.get("Nat")!;
  const baseRule = nat.computeRules[0];
  // First arg: Zero (nullary constructor, resolved from var)
  assertEquals(baseRule.args[0].kind, "ctor");
  assertEquals(baseRule.args[0].name, "Zero");
  // Second arg: y (variable)
  assertEquals(baseRule.args[1].kind, "var");
  assertEquals(baseRule.args[1].name, "y");
});

Deno.test("compute: step case pattern — Succ(k) is a ctor pattern", () => {
  const core = compileAndAssert(COMPUTE_NAT);
  const nat = core.systems.get("Nat")!;
  const stepRule = nat.computeRules[1];
  assertEquals(stepRule.args[0].kind, "ctor");
  assertEquals(stepRule.args[0].name, "Succ");
  if (stepRule.args[0].kind === "ctor") {
    assertEquals(stepRule.args[0].args, ["k"]);
  }
  assertEquals(stepRule.args[1].kind, "var");
  assertEquals(stepRule.args[1].name, "y");
});

// ─── Constructor typing from data declarations ────────────────────

Deno.test("compute: constructorTyping populated from data decl", () => {
  const core = compileAndAssert(COMPUTE_NAT);
  const nat = core.systems.get("Nat")!;
  assertEquals(nat.constructorTyping.has("Zero"), true);
  assertEquals(nat.constructorTyping.has("Succ"), true);
  assertEquals(nat.constructorTyping.get("Zero")!.typeName, "Nat");
  assertEquals(nat.constructorTyping.get("Succ")!.typeName, "Nat");
  assertEquals(nat.constructorTyping.get("Zero")!.fields.length, 0);
  assertEquals(nat.constructorTyping.get("Succ")!.fields.length, 1);
  assertEquals(nat.constructorTyping.get("Succ")!.fields[0].name, "pred");
});

// ─── Compute inheritance via extend ────────────────────────────────

const EXTEND_SOURCE = COMPUTE_NAT + `
system "Eq" extend "Nat" {
  agent refl(principal)
  agent sym(principal, result)
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
}
`;

Deno.test("compute: extend inherits compute rules from base", () => {
  const core = compileAndAssert(EXTEND_SOURCE);
  const eq = core.systems.get("Eq")!;
  // 2 add + 2 Nat_rec inherited from Nat
  assertEquals(eq.computeRules.length, 4, "Eq inherits 4 compute rules from Nat");
  assertEquals(eq.computeRules[0].funcName, "add");
  assertEquals(eq.computeRules[1].funcName, "add");
});

Deno.test("compute: extend inherits constructorTyping from base", () => {
  const core = compileAndAssert(EXTEND_SOURCE);
  const eq = core.systems.get("Eq")!;
  assertEquals(eq.constructorTyping.has("Zero"), true);
  assertEquals(eq.constructorTyping.has("Succ"), true);
});

// ─── Compute inheritance via compose ───────────────────────────────

const COMPOSE_SOURCE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

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

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}

system "Bool" extend "Prelude" {
  data Bool {
    | True
    | False
  }

  agent not(principal, result)
  rule not <> True -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True  relink left.result t.principal }

  compute not(True) = False
  compute not(False) = True
}

system "Combined" = compose "Nat" + "Bool" {}
`;

Deno.test("compute: compose merges compute rules from components", () => {
  const core = compileAndAssert(COMPOSE_SOURCE);
  const combined = core.systems.get("Combined")!;
  // 2 add + 2 Nat_rec + 2 not + 2 Bool_rec
  assertEquals(combined.computeRules.length, 8);
  const funcNames = new Set(combined.computeRules.map((r) => r.funcName));
  assertEquals(funcNames.has("add"), true);
  assertEquals(funcNames.has("not"), true);
});

Deno.test("compute: compose merges constructorTyping from components", () => {
  const core = compileAndAssert(COMPOSE_SOURCE);
  const combined = core.systems.get("Combined")!;
  assertEquals(combined.constructorTyping.has("Zero"), true);
  assertEquals(combined.constructorTyping.has("Succ"), true);
  assertEquals(combined.constructorTyping.has("True"), true);
  assertEquals(combined.constructorTyping.has("False"), true);
});

// ─── Normalization in prove blocks ─────────────────────────────────

const TYPED_PROVE = COMPUTE_NAT + `
system "Eq" extend "Nat" {
  agent refl(principal)
  agent sym(principal, result)
  agent trans(principal, result, second)
  agent cong_succ(principal, result)
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule trans <> refl -> { relink left.result left.second }
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }
}

system "Proofs" extend "Eq" {
  prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
}
`;

Deno.test("compute: normalization enables type-checking plus_zero_right", () => {
  const core = compileAndAssert(TYPED_PROVE);
  const sys = core.systems.get("Proofs")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

Deno.test("compute: proof tree generated for typed prove", () => {
  const core = compileAndAssert(TYPED_PROVE);
  const tree = core.proofTrees.get("plus_zero_right");
  assertEquals(tree !== undefined, true, "proof tree should exist");
});

// ─── Normalization with Bool compute rules ─────────────────────────

const BOOL_PROVE = `
include "prelude"

system "Bool" extend "Prelude" {
  data Bool {
    | True
    | False
  }

  agent not(principal, result)
  rule not <> True -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True  relink left.result t.principal }

  compute not(True) = False
  compute not(False) = True

  agent and(principal, result, second)
  rule and <> True -> { relink left.result left.second }
  rule and <> False -> { let f = False  relink left.result f.principal  erase left.second }

  compute and(True, y) = y
  compute and(False, y) = False

  agent refl(principal)
  rule refl <> refl -> {}
}

system "BoolProofs" extend "Bool" {
  prove not_not(b : Bool) -> Eq(not(not(b)), b) {
    | True -> refl
    | False -> refl
  }
}
`;

Deno.test("compute: Bool normalization enables not_not proof", () => {
  const core = compileAndAssert(BOOL_PROVE);
  const sys = core.systems.get("BoolProofs")!;
  assertEquals(sys.agents.has("not_not"), true);
});

// ─── Missing compute rules cause type errors ──────────────────────

const NO_COMPUTE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

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

system "Eq" extend "Nat" {
  agent refl(principal)
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }
}

system "Bad" extend "Eq" {
  prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
}
`;

Deno.test("compute: missing compute rules → type error on typed prove", () => {
  const result = compileCore(NO_COMPUTE);
  // Without compute rules, add(Zero, Zero) won't normalize to Zero,
  // so the Zero case should fail type checking
  assertEquals(result.errors.length > 0, true, "should have type errors without compute rules");
});

// ─── Compute with explicit agents (no data sugar) ──────────────────

const EXPLICIT_AGENTS = `
include "prelude"

system "Nat" extend "Prelude" {
  agent Zero(principal)
  agent Succ(principal, pred)
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

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}
`;

Deno.test("compute: works with explicit agent decls (no data sugar)", () => {
  const core = compileAndAssert(EXPLICIT_AGENTS);
  const nat = core.systems.get("Nat")!;
  assertEquals(nat.computeRules.length, 2);
  // Zero should resolve to ctor because it's a known agent
  assertEquals(nat.computeRules[0].args[0].kind, "ctor");
  assertEquals(nat.computeRules[0].args[0].name, "Zero");
});

// ─── Multiple compute functions in one system ──────────────────────

const MULTI_COMPUTE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

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

  agent mul(principal, result, accum)
  rule mul <> Zero -> { let z = Zero  relink left.result z.principal  erase left.accum }
  rule mul <> Succ -> {
    let a = add
    let m = mul
    relink left.result a.result
    relink left.accum a.accum
    wire a.principal -- m.result
    relink right.pred m.principal
  }

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
  compute mul(Zero, y) = Zero
  compute mul(Succ(k), y) = add(mul(k, y), y)
}
`;

Deno.test("compute: multiple functions in one system", () => {
  const core = compileAndAssert(MULTI_COMPUTE);
  const nat = core.systems.get("Nat")!;
  // 2 add + 2 mul + 2 Nat_rec
  assertEquals(nat.computeRules.length, 6);
  const funcNames = nat.computeRules.map((r) => r.funcName);
  assertEquals(funcNames.filter((n) => n === "add").length, 2);
  assertEquals(funcNames.filter((n) => n === "mul").length, 2);
  assertEquals(funcNames.filter((n) => n === "Nat_rec").length, 2);
});

// ─── Compute extend adds new rules to inherited ones ───────────────

const EXTEND_NEW_COMPUTE = COMPUTE_NAT + `
system "NatExt" extend "Nat" {
  agent mul(principal, result, accum)
  rule mul <> Zero -> { let z = Zero  relink left.result z.principal  erase left.accum }
  rule mul <> Succ -> {
    let a = add
    let m = mul
    relink left.result a.result
    relink left.accum a.accum
    wire a.principal -- m.result
    relink right.pred m.principal
  }

  compute mul(Zero, y) = Zero
  compute mul(Succ(k), y) = add(mul(k, y), y)
}
`;

Deno.test("compute: extending system adds new compute rules to inherited", () => {
  const core = compileAndAssert(EXTEND_NEW_COMPUTE);
  const ext = core.systems.get("NatExt")!;
  // 2 add + 2 Nat_rec inherited from Nat + 2 new mul
  assertEquals(ext.computeRules.length, 6);
  const funcNames = new Set(ext.computeRules.map((r) => r.funcName));
  assertEquals(funcNames.has("add"), true);
  assertEquals(funcNames.has("mul"), true);
  assertEquals(funcNames.has("Nat_rec"), true);
});

// ─── Constructor typing for multi-field data ───────────────────────

const LIST_DATA = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }
}

system "List" extend "Nat" {
  data List {
    | Nil
    | Cons(head : Nat, tail : List)
  }
}
`;

Deno.test("compute: constructor typing for multi-field data (List)", () => {
  const core = compileAndAssert(LIST_DATA);
  const list = core.systems.get("List")!;
  assertEquals(list.constructorTyping.has("Nil"), true);
  assertEquals(list.constructorTyping.has("Cons"), true);
  assertEquals(list.constructorTyping.get("Nil")!.typeName, "List");
  assertEquals(list.constructorTyping.get("Cons")!.typeName, "List");
  assertEquals(list.constructorTyping.get("Cons")!.fields.length, 2);
  assertEquals(list.constructorTyping.get("Cons")!.fields[0].name, "head");
  assertEquals(list.constructorTyping.get("Cons")!.fields[1].name, "tail");
});

Deno.test("compute: extend inherits constructorTyping across chains", () => {
  const core = compileAndAssert(LIST_DATA);
  const list = core.systems.get("List")!;
  // List extends Nat, so should also have Nat's constructors
  assertEquals(list.constructorTyping.has("Zero"), true);
  assertEquals(list.constructorTyping.has("Succ"), true);
});
