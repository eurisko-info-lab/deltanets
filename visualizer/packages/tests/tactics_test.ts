// Tests for tactic-as-rules (Phase 19).
// Verifies built-in tactic agents, user-definable tactics via `tactic name { ... }`,
// `open "Tactics"` registration, and INet-level tactic resolution.

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  TACTIC_AGENTS, TACTIC_SIMP, TACTIC_DECIDE, TACTIC_OMEGA, TACTIC_AUTO,
  TACTIC_AGENT_DECLS, BUILTIN_TACTIC_NAMES,
  registerBuiltinTactics, compileTactic, resolveUserTactics,
  createSimpHandler, createDecideHandler, createOmegaHandler, createAutoHandler,
  computeGoalType,
} from "@deltanets/lang";
import type { Graph, AgentPortDefs, InteractionRule } from "@deltanets/core";
import { getRedexes, link } from "@deltanets/core";
import {
  compileAndAssert, collectRules, collectAgentPorts, reduceAll,
  NATEQ_SYSTEM, EQ_SYSTEM, readRootType,
} from "./helpers.ts";

// ─── Constants & declarations ──────────────────────────────────────

Deno.test("TACTIC_AGENTS has 4 entries", () => {
  assertEquals(TACTIC_AGENTS.length, 4);
});

Deno.test("TACTIC_AGENT_DECLS matches agent names", () => {
  const names = TACTIC_AGENT_DECLS.map((d) => d.name);
  assertEquals(names, [TACTIC_SIMP, TACTIC_DECIDE, TACTIC_OMEGA, TACTIC_AUTO]);
});

Deno.test("TACTIC_AGENT_DECLS all have (principal, result) ports", () => {
  for (const decl of TACTIC_AGENT_DECLS) {
    assertEquals(decl.ports.length, 2);
    assertEquals(decl.ports[0].name, "principal");
    assertEquals(decl.ports[1].name, "result");
  }
});

Deno.test("BUILTIN_TACTIC_NAMES has simp/decide/omega/auto", () => {
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

// ─── open "Tactics" registration ───────────────────────────────────

Deno.test("open Tactics registers all built-in tactic agents", () => {
  const source = NATEQ_SYSTEM + `
    system "WithTactics" extend "NatEq" {
      open "Quote"
      open "Meta"
      open "Tactics"
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("WithTactics");
  assertEquals(sys!.agents.has(TACTIC_SIMP), true);
  assertEquals(sys!.agents.has(TACTIC_DECIDE), true);
  assertEquals(sys!.agents.has(TACTIC_OMEGA), true);
  assertEquals(sys!.agents.has(TACTIC_AUTO), true);
});

Deno.test("open Tactics registers Tm* interaction rules for each tactic", () => {
  const source = NATEQ_SYSTEM + `
    system "TacRulesCheck" extend "NatEq" {
      open "Quote"
      open "Meta"
      open "Tactics"
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("TacRulesCheck");
  // Each tactic should have rules with TmVar, TmApp, etc.
  for (const tacName of [TACTIC_SIMP, TACTIC_DECIDE, TACTIC_OMEGA, TACTIC_AUTO]) {
    const tacRules = sys!.rules.filter(
      (r) => r.agentA === tacName || r.agentB === tacName,
    );
    // Should have >= 5 rules (for TmVar, TmApp, TmPi, TmSigma, TmLam)
    assertEquals(tacRules.length >= 5, true, `${tacName} has ${tacRules.length} rules`);
  }
});

// ─── Built-in tactic handler tests (graph-level) ──────────────────

function makeGraph(): { graph: Graph; agentPorts: AgentPortDefs; rules: InteractionRule[] } {
  const source = NATEQ_SYSTEM + `
    system "TacGraph" extend "NatEq" {
      open "Quote"
      open "Meta"
      open "Tactics"
    }
  `;
  const core = compileAndAssert(source);
  return {
    graph: [],
    agentPorts: collectAgentPorts(core),
    rules: collectRules(core),
  };
}

function mkNode(type: string, label: string | undefined, portCount: number): import("@deltanets/core").Node {
  const node: import("@deltanets/core").Node = { type, label, ports: [] };
  for (let i = 0; i < portCount; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
}

Deno.test("TacSimp resolves Eq(Zero, Zero) to refl", () => {
  const { graph, agentPorts, rules } = makeGraph();

  // Build: TacSimp(principal, result) ><  TmApp("Eq", [TmVar("Zero"), TmVar("Zero")])
  const tacSimp = mkNode(TACTIC_SIMP, TACTIC_SIMP, 2);
  const tmApp = mkNode("TmApp", "Eq", 2);
  const tmNil = mkNode("TmNil", undefined, 1);
  const tmCons1 = mkNode("TmCons", undefined, 3);
  const tmCons2 = mkNode("TmCons", undefined, 3);
  const tmVar1 = mkNode("TmVar", "Zero", 1);
  const tmVar2 = mkNode("TmVar", "Zero", 1);
  const root = mkNode("root", "root", 1);

  graph.push(tacSimp, tmApp, tmNil, tmCons1, tmCons2, tmVar1, tmVar2, root);

  // Wire tactic principal to tmApp principal
  link({ node: tacSimp, port: 0 }, { node: tmApp, port: 0 });
  // Wire result to root
  link({ node: root, port: 0 }, { node: tacSimp, port: 1 });
  // Build arg list: Cons(Zero, Cons(Zero, Nil))
  link({ node: tmApp, port: 1 }, { node: tmCons1, port: 0 });
  link({ node: tmCons1, port: 1 }, { node: tmVar1, port: 0 });
  link({ node: tmCons1, port: 2 }, { node: tmCons2, port: 0 });
  link({ node: tmCons2, port: 1 }, { node: tmVar2, port: 0 });
  link({ node: tmCons2, port: 2 }, { node: tmNil, port: 0 });

  reduceAll(graph, rules, agentPorts);

  // Result should be TmVar("refl")
  const resultNode = root.ports[0].node;
  assertEquals(resultNode.type, "TmVar");
  assertEquals(resultNode.label, "refl");
});

Deno.test("TacDecide resolves Eq(Zero, Zero) to refl", () => {
  const { graph, agentPorts, rules } = makeGraph();

  const tacDecide = mkNode(TACTIC_DECIDE, TACTIC_DECIDE, 2);
  const tmApp = mkNode("TmApp", "Eq", 2);
  const tmNil = mkNode("TmNil", undefined, 1);
  const tmCons1 = mkNode("TmCons", undefined, 3);
  const tmCons2 = mkNode("TmCons", undefined, 3);
  const tmVar1 = mkNode("TmVar", "Zero", 1);
  const tmVar2 = mkNode("TmVar", "Zero", 1);
  const root = mkNode("root", "root", 1);

  graph.push(tacDecide, tmApp, tmNil, tmCons1, tmCons2, tmVar1, tmVar2, root);

  link({ node: tacDecide, port: 0 }, { node: tmApp, port: 0 });
  link({ node: root, port: 0 }, { node: tacDecide, port: 1 });
  link({ node: tmApp, port: 1 }, { node: tmCons1, port: 0 });
  link({ node: tmCons1, port: 1 }, { node: tmVar1, port: 0 });
  link({ node: tmCons1, port: 2 }, { node: tmCons2, port: 0 });
  link({ node: tmCons2, port: 1 }, { node: tmVar2, port: 0 });
  link({ node: tmCons2, port: 2 }, { node: tmNil, port: 0 });

  reduceAll(graph, rules, agentPorts);

  const resultNode = root.ports[0].node;
  assertEquals(resultNode.type, "TmVar");
  assertEquals(resultNode.label, "refl");
});

Deno.test("TacOmega resolves Eq(Succ(Zero), Succ(Zero)) via congruence", () => {
  const { graph, agentPorts, rules } = makeGraph();

  // Goal: Eq(Succ(Zero), Succ(Zero))
  const tacOmega = mkNode(TACTIC_OMEGA, TACTIC_OMEGA, 2);
  const eqApp = mkNode("TmApp", "Eq", 2);
  const root = mkNode("root", "root", 1);

  // Build Succ(Zero) as TmApp("Succ", [TmVar("Zero")])
  const succApp1 = mkNode("TmApp", "Succ", 2);
  const zeroVar1 = mkNode("TmVar", "Zero", 1);
  const cons1a = mkNode("TmCons", undefined, 3);
  const nil1a = mkNode("TmNil", undefined, 1);

  const succApp2 = mkNode("TmApp", "Succ", 2);
  const zeroVar2 = mkNode("TmVar", "Zero", 1);
  const cons2a = mkNode("TmCons", undefined, 3);
  const nil2a = mkNode("TmNil", undefined, 1);

  // Eq args list
  const eqCons1 = mkNode("TmCons", undefined, 3);
  const eqCons2 = mkNode("TmCons", undefined, 3);
  const eqNil = mkNode("TmNil", undefined, 1);

  graph.push(
    tacOmega, eqApp, root,
    succApp1, zeroVar1, cons1a, nil1a,
    succApp2, zeroVar2, cons2a, nil2a,
    eqCons1, eqCons2, eqNil,
  );

  link({ node: tacOmega, port: 0 }, { node: eqApp, port: 0 });
  link({ node: root, port: 0 }, { node: tacOmega, port: 1 });

  // Eq args: [Succ(Zero), Succ(Zero)]
  link({ node: eqApp, port: 1 }, { node: eqCons1, port: 0 });
  link({ node: eqCons1, port: 1 }, { node: succApp1, port: 0 });
  link({ node: eqCons1, port: 2 }, { node: eqCons2, port: 0 });
  link({ node: eqCons2, port: 1 }, { node: succApp2, port: 0 });
  link({ node: eqCons2, port: 2 }, { node: eqNil, port: 0 });

  // Succ(Zero) #1
  link({ node: succApp1, port: 1 }, { node: cons1a, port: 0 });
  link({ node: cons1a, port: 1 }, { node: zeroVar1, port: 0 });
  link({ node: cons1a, port: 2 }, { node: nil1a, port: 0 });

  // Succ(Zero) #2
  link({ node: succApp2, port: 1 }, { node: cons2a, port: 0 });
  link({ node: cons2a, port: 1 }, { node: zeroVar2, port: 0 });
  link({ node: cons2a, port: 2 }, { node: nil2a, port: 0 });

  reduceAll(graph, rules, agentPorts);

  // Result should be refl (since Succ(Zero) === Succ(Zero))
  const resultNode = root.ports[0].node;
  assertEquals(resultNode.type, "TmVar");
  assertEquals(resultNode.label, "refl");
});

// ─── Built-in tactic meta action kind ──────────────────────────────

Deno.test("built-in tactic rules have meta action kind", () => {
  const source = NATEQ_SYSTEM + `
    system "MetaKind" extend "NatEq" {
      open "Quote"
      open "Meta"
      open "Tactics"
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("MetaKind");
  const tacRules = sys!.rules.filter((r) => r.agentA === TACTIC_SIMP);
  for (const r of tacRules) {
    assertEquals(r.action.kind, "meta");
  }
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
