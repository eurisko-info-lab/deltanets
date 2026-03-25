// Phase 41: Standard Library tests
// Verifies include "stdlib" and individual module includes compile correctly,
// all expected agents/rules exist, and theorems are proved.

import { assertEquals, assert } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";

// ─── Combined stdlib ──────────────────────────────────────────────

Deno.test("stdlib: include stdlib compiles with zero errors", () => {
  const r = compileCore(`include "stdlib"`);
  assertEquals(r.errors.length, 0, `errors: ${r.errors}`);
  assert(r.systems.has("Stdlib"), "missing Stdlib system");
});

Deno.test("stdlib: all individual modules compile", () => {
  for (const mod of ["nat", "bool", "eq", "option", "list", "sigma", "z", "stream"]) {
    const r = compileCore(`include "stdlib/${mod}"`);
    assertEquals(r.errors.length, 0, `stdlib/${mod} errors: ${r.errors}`);
  }
});

Deno.test("stdlib: combined system has all data constructors", () => {
  const r = compileCore(`include "stdlib"`);
  const s = r.systems.get("Stdlib")!;
  const agents = [...s.agents.keys()];
  for (const name of ["Zero", "Succ", "True", "False", "Nil", "Cons", "None", "Some", "Pair"]) {
    assert(agents.includes(name), `missing constructor agent: ${name}`);
  }
});

Deno.test("stdlib: combined system has all function agents", () => {
  const r = compileCore(`include "stdlib"`);
  const s = r.systems.get("Stdlib")!;
  const agents = [...s.agents.keys()];
  for (const name of ["add", "not", "and", "or", "append", "length"]) {
    assert(agents.includes(name), `missing function agent: ${name}`);
  }
});

Deno.test("stdlib: combined system has proof agents", () => {
  const r = compileCore(`include "stdlib"`);
  const s = r.systems.get("Stdlib")!;
  const agents = [...s.agents.keys()];
  for (const name of ["refl", "subst", "sym", "cong", "trans", "cong_succ", "cong_cons"]) {
    assert(agents.includes(name), `missing proof agent: ${name}`);
  }
});

Deno.test("stdlib: all 7 theorems are proved", () => {
  const r = compileCore(`include "stdlib"`);
  const s = r.systems.get("Stdlib")!;
  const proved = [...(s.provedCtx?.keys() ?? [])];
  for (const name of [
    "plus_zero_right", "plus_succ_right", "plus_zero_left",
    "not_not", "and_true_right", "or_false_right",
    "append_nil_right",
  ]) {
    assert(proved.includes(name), `theorem not proved: ${name}`);
  }
});

Deno.test("stdlib: theorem agents are generated", () => {
  const r = compileCore(`include "stdlib"`);
  const s = r.systems.get("Stdlib")!;
  const agents = [...s.agents.keys()];
  for (const name of [
    "plus_zero_right", "plus_succ_right", "plus_zero_left",
    "not_not", "and_true_right", "or_false_right",
    "append_nil_right",
  ]) {
    assert(agents.includes(name), `missing theorem agent: ${name}`);
  }
});

// ─── Individual module systems ────────────────────────────────────

Deno.test("stdlib/nat: has Nat constructors and add", () => {
  const r = compileCore(`include "stdlib/nat"`);
  const s = r.systems.get("Stdlib.Nat")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("Zero"), "missing Zero");
  assert(agents.includes("Succ"), "missing Succ");
  assert(agents.includes("add"), "missing add");
});

Deno.test("stdlib/bool: has Bool constructors and operators", () => {
  const r = compileCore(`include "stdlib/bool"`);
  const s = r.systems.get("Stdlib.Bool")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("True"), "missing True");
  assert(agents.includes("False"), "missing False");
  for (const name of ["not", "and", "or"]) {
    assert(agents.includes(name), `missing ${name}`);
  }
});

Deno.test("stdlib/eq: has equality proof agents", () => {
  const r = compileCore(`include "stdlib/eq"`);
  const s = r.systems.get("Stdlib.Eq")!;
  const agents = [...s.agents.keys()];
  for (const name of ["refl", "subst", "sym", "cong", "trans"]) {
    assert(agents.includes(name), `missing ${name}`);
  }
});

Deno.test("stdlib/option: has Option constructors", () => {
  const r = compileCore(`include "stdlib/option"`);
  const s = r.systems.get("Stdlib.Option")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("None"), "missing None");
  assert(agents.includes("Some"), "missing Some");
});

Deno.test("stdlib/list: has List constructors and append/length", () => {
  const r = compileCore(`include "stdlib/list"`);
  const s = r.systems.get("Stdlib.List")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("Nil"), "missing Nil");
  assert(agents.includes("Cons"), "missing Cons");
  assert(agents.includes("append"), "missing append");
  assert(agents.includes("length"), "missing length");
});

Deno.test("stdlib/sigma: has Sigma/Pair constructor", () => {
  const r = compileCore(`include "stdlib/sigma"`);
  const s = r.systems.get("Stdlib.Sigma")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("Pair"), "missing Pair");
});

// ─── Extend stdlib with user theorems ─────────────────────────────

Deno.test("stdlib: extend Stdlib with user theorem", () => {
  const r = compileCore(`
include "stdlib"
system "MyLib" extend "Stdlib" {
  theorem plus_comm_zero (n : Nat) : Eq(add(Zero, n), add(n, Zero)) := by
    | Zero => refl
    | Succ(k) => cong_succ(plus_comm_zero(k))
}
`);
  assertEquals(r.errors.length, 0, `errors: ${r.errors}`);
  const s = r.systems.get("MyLib")!;
  assert([...(s.provedCtx?.keys() ?? [])].includes("plus_comm_zero"), "missing user theorem");
});

Deno.test("stdlib: extend Stdlib reuses proved lemmas", () => {
  const r = compileCore(`
include "stdlib"
system "UserLib" extend "Stdlib" {
  theorem double_zero_right (n : Nat) : Eq(add(add(n, Zero), Zero), n) := by
    | Zero => refl
    | Succ(k) => cong_succ(double_zero_right(k))
}
`);
  assertEquals(r.errors.length, 0, `errors: ${r.errors}`);
  assert(r.systems.has("UserLib"), "missing UserLib system");
});

Deno.test("stdlib: rule count is reasonable", () => {
  const r = compileCore(`include "stdlib"`);
  const s = r.systems.get("Stdlib")!;
  // 70 rules at time of writing; allow some growth
  assert(s.rules.length >= 50, `too few rules: ${s.rules.length}`);
  assert(s.rules.length <= 120, `too many rules: ${s.rules.length}`);
});

// ─── Z (integers) module ──────────────────────────────────────────

Deno.test("stdlib/z: compiles without errors", () => {
  const r = compileCore(`include "stdlib/z"`);
  assertEquals(r.errors.length, 0, `stdlib/z errors: ${r.errors}`);
});

Deno.test("stdlib/z: has Z constructors", () => {
  const r = compileCore(`include "stdlib/z"`);
  const s = r.systems.get("Stdlib.Z")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("Pos"), "missing Pos");
  assert(agents.includes("NegSucc"), "missing NegSucc");
});

Deno.test("stdlib/z: has neg_z and succ_z agents", () => {
  const r = compileCore(`include "stdlib/z"`);
  const s = r.systems.get("Stdlib.Z")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("neg_z"), "missing neg_z");
  assert(agents.includes("succ_z"), "missing succ_z");
});

Deno.test("stdlib/z: neg_z compute rules available", () => {
  const r = compileCore(`include "stdlib/z"`);
  const s = r.systems.get("Stdlib.Z")!;
  assert(s.computeRules !== undefined, "should have compute rules");
  assert(s.computeRules!.length > 0, "should have some compute rules");
});

// ─── Stream (coinductive) module ──────────────────────────────────

Deno.test("stdlib/stream: compiles without errors", () => {
  const r = compileCore(`include "stdlib/stream"`);
  assertEquals(r.errors.length, 0, `stdlib/stream errors: ${r.errors}`);
});

Deno.test("stdlib/stream: has Stream codata agents", () => {
  const r = compileCore(`include "stdlib/stream"`);
  const s = r.systems.get("Stdlib.Stream")!;
  const agents = [...s.agents.keys()];
  assert(agents.includes("guard_stream"), "missing guard_stream");
  assert(agents.includes("head"), "missing head");
  assert(agents.includes("tail"), "missing tail");
});

Deno.test("stdlib/stream: repeat theorem proved", () => {
  const r = compileCore(`include "stdlib/stream"`);
  const s = r.systems.get("Stdlib.Stream")!;
  const proved = [...(s.provedCtx?.keys() ?? [])];
  assert(proved.includes("repeat"), "repeat not proved");
  assert(proved.includes("head_repeat"), "head_repeat not proved");
});
