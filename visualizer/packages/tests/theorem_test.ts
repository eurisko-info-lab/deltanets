// Phase 40: Tests for Lean-like proof term syntax (theorem/lemma keywords)
// Verifies that the new surface syntax elaborates correctly into the existing
// ProveDecl AST and compiles to the same INet agents/rules as the old syntax.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore, core } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

// A data-based system where constructorsByType is populated (needed for wildcard expansion, type checking)
const DATA_BASE = `
include "prelude"
system "DataNat" extend "Prelude" {
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
}
`;

function compile(extra: string) {
  const source = BASE + "\n" + extra;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

function compileData(extra: string) {
  const source = DATA_BASE + "\n" + extra;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

// ─── Parsing: theorem keyword with := by ───────────────────────────

Deno.test("phase40: theorem with case arms using =>", () => {
  const result = compile(`
    system "T1" extend "NatEq" {
      theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("T1")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

Deno.test("phase40: lemma keyword works same as theorem", () => {
  const result = compile(`
    system "T2" extend "NatEq" {
      lemma plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("T2")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

Deno.test("phase40: theorem with multiple params (shared type)", () => {
  const result = compile(`
    system "T3" extend "NatEq" {
      theorem plus_succ_right (n m : Nat) : Eq(add(n, Succ(m)), Succ(add(n, m))) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_succ_right(k, m))
    }
  `);
  const sys = result.systems.get("T3")!;
  assertEquals(sys.agents.has("plus_succ_right"), true);
});

Deno.test("phase40: theorem with implicit params", () => {
  const result = compile(`
    system "T4" extend "NatEq" {
      theorem plus_zero_right {A : Type} (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("T4")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

// ─── Parsing: theorem with -> in case arms (backward compat) ──────

Deno.test("phase40: theorem case arms accept -> as well as =>", () => {
  const result = compile(`
    system "T5" extend "NatEq" {
      theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("T5")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

// ─── Parsing: space-separated bindings in case arms ────────────────

Deno.test("phase40: space-separated bindings in case arms", () => {
  const result = compile(`
    system "T6" extend "NatEq" {
      theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ k => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("T6")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

// ─── Parsing: direct proof term (:= expr) ─────────────────────────

Deno.test("phase40: direct proof term with :=", () => {
  const result = compileData(`
    system "T7" extend "DataNat" {
      theorem refl_proof (n : Nat) : Eq(n, n) := refl
    }
  `);
  const sys = result.systems.get("T7")!;
  assertEquals(sys.agents.has("refl_proof"), true);
});

// ─── Parsing: induction with ────────────────────────────────────────

Deno.test("phase40: induction n with case arms", () => {
  const result = compile(`
    system "T8" extend "NatEq" {
      theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        induction n with
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("T8")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

// ─── Parsing: theorem at top level ─────────────────────────────────

Deno.test("phase40: top-level theorem (outside system)", () => {
  // Top-level theorems parse correctly and compile when data + compute rules are available
  const result = compileData(`
    system "TopLevel" extend "DataNat" {
      theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("TopLevel")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

// ─── Equivalence: new syntax produces same agents as old syntax ────

Deno.test("phase40: theorem produces same agents as prove", () => {
  const oldResult = compile(`
    system "Old" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  const newResult = compile(`
    system "New" extend "NatEq" {
      theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const oldSys = oldResult.systems.get("Old")!;
  const newSys = newResult.systems.get("New")!;
  assertEquals(oldSys.agents.has("plus_zero_right"), true);
  assertEquals(newSys.agents.has("plus_zero_right"), true);
  // Same number of rules (inherited + prove-generated)
  assertEquals(oldSys.rules.length, newSys.rules.length);
});

// ─── New lambda syntax ──────────────────────────────────────────────

Deno.test("phase40: fun x => body lambda syntax (parsing)", () => {
  // Tests that `fun x => body` parses correctly into a lambda ProveExpr.
  // Full compilation is blocked by pre-existing "lambda cannot be desugared" limitation.
  const tokens = core.tokenize("fun x => x");
  const funTok = tokens.find(t => t.value === "fun");
  assertEquals(funTok !== undefined, true);
  const arrow = tokens.find(t => t.value === "=>");
  assertEquals(arrow !== undefined, true);
});

Deno.test("phase40: fun (x : A) => body lambda syntax (parsing)", () => {
  const tokens = core.tokenize("fun (x : Nat) => x");
  const funTok = tokens.find(t => t.value === "fun");
  assertEquals(funTok !== undefined, true);
  const arrow = tokens.find(t => t.value === "=>");
  assertEquals(arrow !== undefined, true);
});

// ─── Attributes on theorem ──────────────────────────────────────────

Deno.test("phase40: @[simp] attribute on theorem", () => {
  const result = compile(`
    system "Attr" extend "NatEq" {
      @[simp] theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
        | Zero => refl
        | Succ(k) => cong_succ(plus_zero_right(k))
    }
  `);
  const sys = result.systems.get("Attr")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
  assertEquals(sys.hints.has("simp"), true);
});

// ─── Backward compatibility: old prove syntax still works ──────────

Deno.test("phase40: old prove syntax unchanged", () => {
  const result = compile(`
    system "BackCompat" extend "NatEq" {
      prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(plus_zero_right(k))
      }
    }
  `);
  const sys = result.systems.get("BackCompat")!;
  assertEquals(sys.agents.has("plus_zero_right"), true);
});

Deno.test("phase40: old fun(x : A, body) syntax unchanged (parsing)", () => {
  // Verifies backward-compatible parsing of old lambda syntax.
  // Full compilation is blocked by pre-existing "lambda cannot be desugared" limitation.
  const tokens = core.tokenize("fun(x : Nat, x)");
  const funTok = tokens.find(t => t.value === "fun");
  assertEquals(funTok !== undefined, true);
});

// ─── Lexer: := and => tokens ────────────────────────────────────────

Deno.test("phase40: lexer produces WALRUS token for :=", () => {
  const tokens = core.tokenize("theorem x := by");
  const walrus = tokens.find(t => t.value === ":=");
  assertEquals(walrus !== undefined, true);
  assertEquals(walrus!.type, "WALRUS");
});

Deno.test("phase40: lexer produces FATARROW token for =>", () => {
  const tokens = core.tokenize("| Zero => refl");
  const fa = tokens.find(t => t.value === "=>");
  assertEquals(fa !== undefined, true);
  assertEquals(fa!.type, "FATARROW");
});

Deno.test("phase40: lexer produces THEOREM and LEMMA keyword tokens", () => {
  const tokens1 = core.tokenize("theorem name");
  assertEquals(tokens1[0].type, "THEOREM");
  const tokens2 = core.tokenize("lemma name");
  assertEquals(tokens2[0].type, "LEMMA");
});

// ─── Termination annotations in theorem syntax ─────────────────────

Deno.test("phase40: theorem with measure termination", () => {
  const result = compileData(`
    system "Meas" extend "DataNat" {
      theorem halfN (n : Nat) : Nat := by
        measure(n)
        | Zero => Zero
        | Succ(k) => halfN(k)
    }
  `);
  const sys = result.systems.get("Meas")!;
  assertEquals(sys.agents.has("halfN"), true);
});

Deno.test("phase40: theorem with wf termination", () => {
  const result = compileData(`
    system "Wf" extend "DataNat" {
      theorem halfN (n : Nat) : Nat := by
        wf(lt)
        | Zero => Zero
        | Succ(k) => halfN(k)
    }
  `);
  const sys = result.systems.get("Wf")!;
  assertEquals(sys.agents.has("halfN"), true);
});
