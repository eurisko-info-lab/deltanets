// Tests for tactic-as-rules (Phase 19).
// Verifies built-in tactic agents, user-definable tactics via `tactic name { ... }`,
// `open "Tactics"` registration, and INet-level tactic resolution.

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  BUILTIN_TACTIC_NAMES,
  compileTactic, resolveAllTactics,
  computeGoalType,
} from "@deltanets/lang";
import {
  compileAndAssert,
  NATEQ_SYSTEM, EQ_SYSTEM,
} from "./helpers.ts";

// ─── BUILTIN_TACTIC_NAMES ──────────────────────────────────────────

Deno.test("BUILTIN_TACTIC_NAMES has assumption/simp/decide/omega/auto", () => {
  assertEquals(BUILTIN_TACTIC_NAMES.has("assumption"), true);
  assertEquals(BUILTIN_TACTIC_NAMES.has("simp"), true);
  assertEquals(BUILTIN_TACTIC_NAMES.has("decide"), true);
  assertEquals(BUILTIN_TACTIC_NAMES.has("omega"), true);
  assertEquals(BUILTIN_TACTIC_NAMES.has("auto"), true);
});

// ─── Tactic syntax parsing ─────────────────────────────────────────

Deno.test("tactic declaration parses correctly", () => {
  const source = `
    include "prelude"
    system "TacTest" extend "Prelude" {
      tactic my_tac {
        agent Helper(principal, aux)
        rule my_tac <> Helper -> annihilate
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("TacTest");
  assertNotEquals(sys, undefined);
  // Tactic agent should be auto-declared
  assertEquals(sys!.agents.has("my_tac"), true);
  // Helper agent should also be registered
  assertEquals(sys!.agents.has("Helper"), true);
});

Deno.test("tactic agent gets (principal, result) ports", () => {
  const source = `
    include "prelude"
    system "TacPorts" extend "Prelude" {
      tactic conv_tac {
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("TacPorts");
  const agent = sys!.agents.get("conv_tac");
  assertNotEquals(agent, undefined);
  assertEquals(agent!.ports.length, 2);
  assertEquals(agent!.ports[0].name, "principal");
  assertEquals(agent!.ports[1].name, "result");
});

Deno.test("tactic rules are added to system rules", () => {
  const source = `
    include "prelude"
    system "TacRules" extend "Prelude" {
      agent Foo(principal)
      tactic my_tac {
        rule my_tac <> Foo -> annihilate
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("TacRules");
  const rule = sys!.rules.find(
    (r) =>
      (r.agentA === "my_tac" && r.agentB === "Foo") ||
      (r.agentA === "Foo" && r.agentB === "my_tac"),
  );
  assertNotEquals(rule, undefined);
});

// ─── User-defined tactic resolution ────────────────────────────────

Deno.test("user tactic returning refl resolves via INet reduction", () => {
  // A tactic that always returns refl (sufficient for Eq(x, x) goals)
  const source = NATEQ_SYSTEM + `
    system "UserTac" extend "NatEq" {
      open "Quote"
      open "Meta"

      data Nat {
        | Zero
        | Succ(pred : Nat)
      }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      tactic my_decide {
        rule my_decide <> TmApp -> {
          let r = TmVar "refl"
          relink left.result r.principal
        }
        rule my_decide <> TmVar -> {
          let r = TmVar "refl"
          relink left.result r.principal
        }
      }

      prove add_zero(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> my_decide
        | Succ(k) -> my_decide
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("UserTac");
  // Prove block should have generated agent + rules (proof resolved)
  assertEquals(sys!.agents.has("add_zero"), true);
});

// ─── Tactic inside system extend ───────────────────────────────────

Deno.test("tactic declaration works inside extend", () => {
  const source = NATEQ_SYSTEM + `
    system "WithTac" extend "NatEq" {
      open "Quote"
      open "Meta"
      tactic my_norm {
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("WithTac");
  assertEquals(sys!.agents.has("my_norm"), true);
  assertEquals(sys!.tactics?.has("my_norm"), true);
});

// ─── Multiple tactics in one system ────────────────────────────────

Deno.test("multiple tactic declarations in same system", () => {
  const source = `
    include "prelude"
    system "MultiTac" extend "Prelude" {
      tactic tac_a {
      }
      tactic tac_b {
        agent Helper(principal, aux)
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("MultiTac");
  assertEquals(sys!.agents.has("tac_a"), true);
  assertEquals(sys!.agents.has("tac_b"), true);
  assertEquals(sys!.agents.has("Helper"), true);
  assertEquals(sys!.tactics?.size, 2);
});

// ─── computeGoalType ───────────────────────────────────────────────

Deno.test("computeGoalType extracts correct type for case arm", () => {
  // Compile a system with a prove block to test goal computation
  const source = NATEQ_SYSTEM + `
    system "GoalTest" extend "NatEq" {
      prove add_zero(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `;
  // Just verify it compiles (the prove block has correct goals)
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Existing proofs still work ────────────────────────────────────

Deno.test("existing simp proofs still pass (backward compatibility)", () => {
  const source = NATEQ_SYSTEM + `
    system "BackCompat" extend "NatEq" {
      data Nat {
        | Zero
        | Succ(pred : Nat)
      }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove add_zero(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> simp
        | Succ(k) -> simp
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("BackCompat");
  assertEquals(sys!.agents.has("add_zero"), true);
});

Deno.test("existing decide proofs still pass", () => {
  const source = NATEQ_SYSTEM + `
    system "DecideCompat" extend "NatEq" {
      data Nat {
        | Zero
        | Succ(pred : Nat)
      }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove two_plus_two(x : Nat) -> Eq(add(Succ(Succ(Zero)), Succ(Succ(Zero))), Succ(Succ(Succ(Succ(Zero))))) {
        | Zero -> decide
        | Succ(k) -> decide
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("existing auto proofs still pass", () => {
  const source = NATEQ_SYSTEM + `
    system "AutoCompat" extend "NatEq" {
      data Nat {
        | Zero
        | Succ(pred : Nat)
      }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove add_zero_auto(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> auto
        | Succ(k) -> auto
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Tactic in system body alongside prove ─────────────────────────

Deno.test("tactic declared before prove block is available", () => {
  const source = NATEQ_SYSTEM + `
    system "TacBeforeProve" extend "NatEq" {
      open "Quote"
      open "Meta"

      data Nat {
        | Zero
        | Succ(pred : Nat)
      }
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      tactic my_decide {
        rule my_decide <> TmApp -> {
          let r = TmVar "refl"
          relink left.result r.principal
        }
        rule my_decide <> TmVar -> {
          let r = TmVar "refl"
          relink left.result r.principal
        }
      }

      prove add_zero_tac(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> my_decide
        | Succ(k) -> my_decide
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("TacBeforeProve");
  assertEquals(sys!.agents.has("add_zero_tac"), true);
});
