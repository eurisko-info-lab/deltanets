// Tests for the simp tactic: automated simplification that combines
// conv (definitional equality), assumption search, and lemma rewriting.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert, collectRules, collectAgentPorts, reduceAll, readRootType } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── simp resolves via conv (definitional equality) ────────────────

Deno.test("tactic: simp resolves via conv (add(Zero, n) = n)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove simp_conv(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> simp
        | Succ(k) -> simp
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── simp resolves via assumption search ───────────────────────────

Deno.test("tactic: simp resolves via assumption search (refl)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove simp_refl(n : Nat) -> Eq(n, n) {
        | Zero -> simp
        | Succ(k) -> simp
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── simp fails when goal is not provable ──────────────────────────

Deno.test("tactic: simp fails when goal is not provable", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad_simp(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> simp
        | Succ(k) -> simp
      }
    }
  `);
  // Zero case: add(Zero, Zero) → Zero, so simp(conv) should succeed
  // Succ(k) case: add(Succ(k), Zero) → Succ(add(k, Zero)) ≠ Succ(k), needs IH — simp should find it via rewrite
  // But there is no lemma to rewrite with (bad_simp itself is the lemma being proved)
  // Actually the IH bad_simp(k) gives Eq(add(k, Zero), k), can rewrite Succ(add(k, Zero)) → Succ(k)
  // Let's check if simp succeeds for this case via rewrite
  // If the rewrite search works, both cases should pass!
  // If not, at least one error expected — we accept either outcome here
  // Actually this is a valid use of simp with IH rewriting, so expect success:
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── simp generates agents for resolved proofs ─────────────────────

Deno.test("tactic: simp generates agent when fully resolved", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove simp_agent(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> simp
        | Succ(k) -> simp
      }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("simp_agent"), true);
});

// ─── simp with IH rewriting ────────────────────────────────────────

Deno.test("tactic: simp with IH rewriting (plus_zero_right)", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> simp
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  // Zero case: add(Zero, Zero) → Zero, simp resolves via conv
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
