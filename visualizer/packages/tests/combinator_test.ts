// Tests for tactic combinators: calc (chained transitivity) and conv (conversion).

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, compileAndAssert, collectRules, collectAgentPorts, reduceAll, readRootType, countNodes } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── calc — chained transitivity ───────────────────────────────────

Deno.test("tactic: calc with two steps type-checks", () => {
  // We prove Eq(add(Zero, n), add(Zero, n)) — trivially refl at each step,
  // but demonstrating calc(refl, refl) = trans(refl, refl) type-checks.
  const result = compile(`
    system "T" extend "NatEq" {
      prove calc_test(n : Nat) -> Eq(add(Zero, n), add(Zero, n)) {
        | Zero -> calc(refl, refl)
        | Succ(k) -> calc(refl, refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: calc desugars to trans for agent generation", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove round_trip(n : Nat) -> Eq(add(Zero, n), add(Zero, n)) {
        | Zero -> calc(refl, refl)
        | Succ(k) -> calc(refl, refl)
      }
    }
  `);
  const sys = result.systems.get("T")!;
  // calc is desugared to trans, so agent should be generated
  assertEquals(sys.agents.has("round_trip"), true);
});

// ─── conv — definitional equality ──────────────────────────────────

Deno.test("tactic: conv succeeds when sides normalize to same term", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove conv_test(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("tactic: conv desugars to refl for agent generation", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove conv_agent(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("conv_agent"), true);
});

Deno.test("tactic: conv fails when sides differ", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove bad_conv(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  // Zero case: add(Zero, Zero) normalizes to Zero, Eq(Zero, Zero) — should pass
  // Succ(k) case: add(Succ(k), Zero) normalizes to Succ(add(k, Zero)), not Succ(k) — should fail
  assertEquals(result.errors.some((e) => e.includes("conv failed")), true,
    `expected conv failure, got: ${result.errors}`);
});

Deno.test("tactic: conv produces refl agent that reduces", () => {
  const core = compileAndAssert(BASE + `
    system "T" extend "NatEq" {
      prove id_zero(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }

    graph test {
      let r  = root
      let id = id_zero
      let z  = Zero
      wire r.principal -- id.result
      wire id.principal -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps >= 1, true, "should reduce");
  assertEquals(readRootType(g.graph), "refl");
});
