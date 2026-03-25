// Phase 49: Bytecode VM Normalization Tests

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  enableVM, disableVM, isVMEnabled,
  vmNormalize, vmConvertible, vmCheckConvertible,
  getVMStats, resetVMStats, clearVMCache,
  compileExpr, exprHash, withVMContext, precompile,
  normalize,
} from "@deltanets/lang";
import { exprEqual, exprToString, withNormTable } from "../lang/core/normalize.ts";
import type { ComputeRule } from "../lang/core/normalize.ts";

// ─── Helpers ───────────────────────────────────────────────────────

function id(name: string): any { return { kind: "ident", name }; }
function call(name: string, ...args: any[]): any { return { kind: "call", name, args }; }
function hole(): any { return { kind: "hole" }; }
function metavar(n: number): any { return { kind: "metavar", id: n }; }
function pi(param: string, domain: any, codomain: any): any {
  return { kind: "pi", param, domain, codomain };
}
function sigma(param: string, domain: any, codomain: any): any {
  return { kind: "sigma", param, domain, codomain };
}
function lambda(param: string, paramType: any, body: any): any {
  return { kind: "lambda", param, paramType, body };
}
function letExpr(name: string, value: any, body: any): any {
  return { kind: "let", name, value, body };
}

// ─── Compilation tests ─────────────────────────────────────────────

Deno.test("compile: ident produces bytecode", () => {
  const code = compileExpr(id("x"));
  assertEquals(code.length, 1);
});

Deno.test("compile: call with args", () => {
  const code = compileExpr(call("add", id("x"), id("y")));
  assertEquals(code.length, 3); // x, y, CALL
});

Deno.test("compile: nested call", () => {
  const code = compileExpr(call("add", call("Succ", id("k")), id("y")));
  assertEquals(code.length, 4); // k, CALL(Succ), y, CALL(add)
});

Deno.test("compile: pi/sigma/lambda produce bytecode", () => {
  const e = pi("x", id("Nat"), call("add", id("x"), id("Zero")));
  const code = compileExpr(e);
  assertEquals(code.length, 5); // Nat, x, Zero, CALL(add), PI
});

Deno.test("compile: let produces bytecode", () => {
  const e = letExpr("x", id("Zero"), call("Succ", id("x")));
  const code = compileExpr(e);
  assertEquals(code.length, 4); // Zero, x, CALL(Succ), LET
});

Deno.test("compile: hole and metavar", () => {
  const c1 = compileExpr(hole());
  assertEquals(c1.length, 1);
  const c2 = compileExpr(metavar(5));
  assertEquals(c2.length, 1);
});

// ─── Hashing tests ─────────────────────────────────────────────────

Deno.test("hash: equal expressions have equal hashes", () => {
  const a = call("add", id("x"), id("y"));
  const b = call("add", id("x"), id("y"));
  assertEquals(exprHash(a), exprHash(b));
});

Deno.test("hash: different expressions have different hashes", () => {
  const a = call("add", id("x"), id("y"));
  const b = call("add", id("y"), id("x"));
  assertNotEquals(exprHash(a), exprHash(b));
});

Deno.test("hash: ident vs call are different", () => {
  assertNotEquals(exprHash(id("Zero")), exprHash(call("Zero")));
});

Deno.test("hash: pi vs sigma differentiated", () => {
  const a = pi("x", id("Nat"), id("x"));
  const b = sigma("x", id("Nat"), id("x"));
  assertNotEquals(exprHash(a), exprHash(b));
});

Deno.test("hash: metavar ids matter", () => {
  assertNotEquals(exprHash(metavar(1)), exprHash(metavar(2)));
});

// ─── VM normalization (basic, no rules) ────────────────────────────

Deno.test("vm: normalize ident passthrough", () => {
  const result = vmNormalize(id("x"));
  assertEquals(result.kind, "ident");
  assertEquals((result as any).name, "x");
});

Deno.test("vm: normalize Type → Type(0)", () => {
  const result = vmNormalize(id("Type"));
  assertEquals(exprToString(result), "Type₀");
});

Deno.test("vm: normalize Set → Type(0)", () => {
  const result = vmNormalize(id("Set"));
  assertEquals(exprToString(result), "Type₀");
});

Deno.test("vm: normalize Type3 → Type(3)", () => {
  const result = vmNormalize(id("Type3"));
  assertEquals(exprToString(result), "Type₃");
});

Deno.test("vm: normalize Prop stays Prop", () => {
  const result = vmNormalize(id("Prop"));
  assertEquals(exprToString(result), "Prop");
});

Deno.test("vm: normalize hole passthrough", () => {
  assertEquals(vmNormalize(hole()).kind, "hole");
});

Deno.test("vm: normalize metavar passthrough", () => {
  assertEquals(vmNormalize(metavar(7)).kind, "metavar");
});

Deno.test("vm: normalize let inlines binding", () => {
  // let x = Zero in Succ(x) → Succ(Zero)
  const e = letExpr("x", id("Zero"), call("Succ", id("x")));
  const result = vmNormalize(e);
  assertEquals(exprToString(result), "Succ(Zero)");
});

Deno.test("vm: normalize pi normalizes subexprs", () => {
  // pi(x : Type, x) → pi(x : Type₀, x)
  const e = pi("x", id("Type"), id("x"));
  const result = vmNormalize(e);
  assertEquals(result.kind, "pi");
  assertEquals(exprToString((result as any).domain), "Type₀");
});

Deno.test("vm: normalize lambda normalizes paramType", () => {
  const e = lambda("x", id("Type"), id("x"));
  const result = vmNormalize(e);
  assertEquals(result.kind, "lambda");
  assertEquals(exprToString((result as any).paramType), "Type₀");
});

Deno.test("vm: normalize sigma normalizes subexprs", () => {
  const e = sigma("x", id("Set"), id("x"));
  const result = vmNormalize(e);
  assertEquals(result.kind, "sigma");
  assertEquals(exprToString((result as any).domain), "Type₀");
});

// ─── VM with compute rules ─────────────────────────────────────────

function addRules(): ComputeRule[] {
  return [
    {
      funcName: "add",
      args: [{ kind: "ctor", name: "Zero", args: [] }, { kind: "var", name: "y" }],
      result: id("y"),
    },
    {
      funcName: "add",
      args: [{ kind: "ctor", name: "Succ", args: ["k"] }, { kind: "var", name: "y" }],
      result: call("Succ", call("add", id("k"), id("y"))),
    },
  ];
}

Deno.test("vm: table-driven base case reduction", () => {
  // add(Zero, y) → y
  withVMContext(addRules(), () => {
    const result = vmNormalize(call("add", id("Zero"), id("y")));
    assertEquals(exprToString(result), "y");
  });
});

Deno.test("vm: table-driven step case reduction", () => {
  // add(Succ(k), y) → Succ(add(k, y))
  withVMContext(addRules(), () => {
    const result = vmNormalize(call("add", call("Succ", id("k")), id("y")));
    assertEquals(exprToString(result), "Succ(add(k, y))");
  });
});

Deno.test("vm: multi-step reduction", () => {
  // add(Succ(Zero), Zero) → Succ(add(Zero, Zero)) → Succ(Zero)
  withVMContext(addRules(), () => {
    const result = vmNormalize(call("add", call("Succ", id("Zero")), id("Zero")));
    assertEquals(exprToString(result), "Succ(Zero)");
  });
});

Deno.test("vm: nested reduction", () => {
  // add(Succ(Succ(Zero)), Zero)
  // → Succ(add(Succ(Zero), Zero)) → Succ(Succ(add(Zero, Zero))) → Succ(Succ(Zero))
  withVMContext(addRules(), () => {
    const result = vmNormalize(call("add", call("Succ", call("Succ", id("Zero"))), id("Zero")));
    assertEquals(exprToString(result), "Succ(Succ(Zero))");
  });
});

Deno.test("vm: fst/snd builtins", () => {
  // fst(pair(a, b)) → a
  const result = vmNormalize(call("fst", call("pair", id("a"), id("b"))));
  assertEquals(exprToString(result), "a");
});

Deno.test("vm: snd builtin", () => {
  const result = vmNormalize(call("snd", call("pair", id("a"), id("b"))));
  assertEquals(exprToString(result), "b");
});

// ─── Caching tests ─────────────────────────────────────────────────

Deno.test("vm: cache hit on repeated normalize", () => {
  resetVMStats();
  clearVMCache();
  const e = call("add", id("x"), id("y"));
  vmNormalize(e);
  vmNormalize(e);
  const stats = getVMStats();
  assertEquals(stats.hits, 1);
  assertEquals(stats.misses, 1);
});

Deno.test("vm: cache cleared on context change", () => {
  clearVMCache();
  resetVMStats();
  vmNormalize(id("x"));
  assertEquals(getVMStats().cacheSize, 1);
  withVMContext(addRules(), () => {
    assertEquals(getVMStats().cacheSize, 0); // fresh context = fresh cache
  });
});

// ─── Convertibility tests ──────────────────────────────────────────

Deno.test("vm: vmConvertible true for equal after norm", () => {
  withVMContext(addRules(), () => {
    // add(Zero, x) vs x
    assertEquals(vmConvertible(call("add", id("Zero"), id("x")), id("x")), true);
  });
});

Deno.test("vm: vmConvertible false for different terms", () => {
  assertEquals(vmConvertible(id("x"), id("y")), false);
});

Deno.test("vm: vmCheckConvertible returns diagnostics", () => {
  const result = vmCheckConvertible(id("x"), id("y"));
  assertEquals(result.convertible, false);
  if (!result.convertible) {
    assertEquals(result.lhsNorm, "x");
    assertEquals(result.rhsNorm, "y");
  }
});

// ─── Precompile tests ──────────────────────────────────────────────

Deno.test("vm: precompile batch normalization", () => {
  clearVMCache();
  withVMContext(addRules(), () => {
    const exprs = [
      call("add", id("Zero"), id("a")),
      call("add", id("Zero"), id("b")),
    ];
    const batch = precompile(exprs);
    assertEquals(exprToString(batch.normalize(0)), "a");
    assertEquals(exprToString(batch.normalize(1)), "b");
  });
});

// ─── Enable/disable integration ────────────────────────────────────

Deno.test("vm: enable/disable toggles", () => {
  const was = isVMEnabled();
  enableVM();
  assertEquals(isVMEnabled(), true);
  disableVM();
  assertEquals(isVMEnabled(), false);
  // restore
  if (was) enableVM();
});

Deno.test("vm: normalize() delegates to VM when enabled", () => {
  // Enable VM, then call normalize() from normalize.ts — should use VM
  enableVM();
  try {
    withNormTable(addRules(), () => {
      const result = normalize(call("add", id("Zero"), id("x")));
      assertEquals(exprToString(result), "x");
    });
  } finally {
    disableVM();
  }
});

Deno.test("vm: normalize() works normally when VM disabled", () => {
  disableVM();
  withNormTable(addRules(), () => {
    const result = normalize(call("add", id("Zero"), id("x")));
    assertEquals(exprToString(result), "x");
  });
});

// ─── VM parity with tree-walking normalize ─────────────────────────

Deno.test("vm: parity with normalize for universe types", () => {
  for (const name of ["Type", "Set", "Type0", "Type1", "Type3", "Prop"]) {
    const treeResult = normalize(id(name));
    const vmResult = vmNormalize(id(name));
    assertEquals(
      exprToString(vmResult),
      exprToString(treeResult),
      `parity failed for ${name}`,
    );
  }
});

Deno.test("vm: parity with normalize for let-inlining", () => {
  const e = letExpr("a", call("Succ", id("Zero")), call("add", id("a"), id("y")));
  withNormTable(addRules(), () => {
    const treeResult = normalize(e);
    withVMContext(addRules(), () => {
      const vmResult = vmNormalize(e);
      assertEquals(exprToString(vmResult), exprToString(treeResult));
    });
  });
});

Deno.test("vm: parity with normalize for nested reductions", () => {
  const e = call("add", call("Succ", call("Succ", call("Succ", id("Zero")))), id("Zero"));
  withNormTable(addRules(), () => {
    const treeResult = normalize(e);
    withVMContext(addRules(), () => {
      const vmResult = vmNormalize(e);
      assertEquals(exprToString(vmResult), exprToString(treeResult));
    });
  });
});

// ─── Full-system integration: compile + VM normalize ───────────────

Deno.test("vm: full system compile parity", () => {
  const src = `
include "prelude"
system "VmTest" extend "Prelude" {
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
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  agent refl(principal)
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }

  prove add_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
  | Zero -> refl
  | Succ(k) -> cong_succ(add_zero_right(k))
  }
}
  `;
  const result = compileCore(src);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
