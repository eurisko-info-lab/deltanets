// Tests for quotation & reflection (Phase 17).
// Verifies quoteExpr, unquoteStatements, buildGoalStatements,
// and integration with prove blocks via quote/unquote.

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import {
  compileCore,
  quoteExpr,
  unquoteStatements,
  buildGoalStatements,
  QUOTE_AGENTS,
  TM_VAR,
  TM_APP,
  TM_PI,
  TM_SIGMA,
  TM_LAM,
  TM_NIL,
  TM_CONS,
  Q_GOAL,
  CTX_NIL,
  CTX_CONS,
} from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";
import type { RuleStmt, ProveExpr } from "../lang/core/types.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// Helper constructors
const ident = (name: string): ProveExpr => ({ kind: "ident", name });
const call = (name: string, ...args: ProveExpr[]): ProveExpr => ({ kind: "call", name, args });
const pi = (param: string, domain: ProveExpr, codomain: ProveExpr): ProveExpr =>
  ({ kind: "pi", param, domain, codomain });
const sigma = (param: string, domain: ProveExpr, codomain: ProveExpr): ProveExpr =>
  ({ kind: "sigma", param, domain, codomain });
const lam = (param: string, paramType: ProveExpr, body: ProveExpr): ProveExpr =>
  ({ kind: "lambda", param, paramType, body });

// ─── quoteExpr: basic term encoding ────────────────────────────────

Deno.test("quote: ident produces TmVar", () => {
  const counter = { value: 0 };
  const { stmts, root } = quoteExpr(ident("Nat"), counter);
  // Should produce one TmVar agent
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  assertEquals(lets.length, 1);
  assertEquals(lets[0].agentType, TM_VAR);
  assertEquals(lets[0].label, "Nat");
  assertEquals(root.port, "principal");
});

Deno.test("quote: call produces TmApp + arg list", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr(call("add", ident("x"), ident("y")), counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const types = lets.map((l) => l.agentType);
  // Should have: TmApp, TmVar("x"), TmVar("y"), TmCons, TmCons, TmNil
  assertEquals(types.includes(TM_APP), true);
  assertEquals(types.filter((t) => t === TM_VAR).length, 2);
  assertEquals(types.filter((t) => t === TM_CONS).length, 2);
  assertEquals(types.filter((t) => t === TM_NIL).length, 1);
});

Deno.test("quote: pi produces TmPi", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr(pi("x", ident("Nat"), ident("Nat")), counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const types = lets.map((l) => l.agentType);
  assertEquals(types.includes(TM_PI), true);
  assertEquals(types.filter((t) => t === TM_VAR).length, 2); // domain + codomain
});

Deno.test("quote: sigma produces TmSigma", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr(sigma("x", ident("Nat"), ident("Nat")), counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const types = lets.map((l) => l.agentType);
  assertEquals(types.includes(TM_SIGMA), true);
});

Deno.test("quote: lambda produces TmLam", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr(lam("x", ident("Nat"), ident("x")), counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const types = lets.map((l) => l.agentType);
  assertEquals(types.includes(TM_LAM), true);
});

Deno.test("quote: hole produces TmVar with ? label", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr({ kind: "hole" }, counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  assertEquals(lets.length, 1);
  assertEquals(lets[0].agentType, TM_VAR);
  assertEquals(lets[0].label, "?");
});

Deno.test("quote: nested call tree", () => {
  // cong_succ(foo(k)) → TmApp("cong_succ", [TmApp("foo", [TmVar("k")])])
  const counter = { value: 0 };
  const { stmts } = quoteExpr(call("cong_succ", call("foo", ident("k"))), counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const tmApps = lets.filter((l) => l.agentType === TM_APP);
  assertEquals(tmApps.length, 2); // cong_succ and foo
  assertEquals(tmApps.map((a) => a.label).sort(), ["cong_succ", "foo"]);
});

// ─── unquoteStatements: roundtrip ──────────────────────────────────

Deno.test("unquote: roundtrip ident", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr(ident("Nat"), counter);
  const result = unquoteStatements(stmts);
  assertEquals(result, ident("Nat"));
});

Deno.test("unquote: roundtrip call", () => {
  const counter = { value: 0 };
  const { stmts } = quoteExpr(call("add", ident("x"), ident("y")), counter);
  const result = unquoteStatements(stmts);
  assertNotEquals(result, null);
  assertEquals(result!.kind, "call");
  if (result!.kind === "call") {
    assertEquals(result!.name, "add");
    assertEquals(result!.args.length, 2);
    assertEquals(result!.args[0], ident("x"));
    assertEquals(result!.args[1], ident("y"));
  }
});

Deno.test("unquote: roundtrip pi", () => {
  const counter = { value: 0 };
  const expr = pi("x", ident("Nat"), ident("Nat"));
  const { stmts } = quoteExpr(expr, counter);
  const result = unquoteStatements(stmts);
  assertNotEquals(result, null);
  assertEquals(result!.kind, "pi");
  if (result!.kind === "pi") {
    assertEquals(result!.domain, ident("Nat"));
    assertEquals(result!.codomain, ident("Nat"));
  }
});

Deno.test("unquote: roundtrip nested call", () => {
  const counter = { value: 0 };
  const expr = call("cong_succ", call("foo", ident("k")));
  const { stmts } = quoteExpr(expr, counter);
  const result = unquoteStatements(stmts);
  assertNotEquals(result, null);
  assertEquals(result!.kind, "call");
  if (result!.kind === "call") {
    assertEquals(result!.name, "cong_succ");
    assertEquals(result!.args.length, 1);
    assertEquals(result!.args[0].kind, "call");
  }
});

// ─── buildGoalStatements ───────────────────────────────────────────

Deno.test("goal: builds QGoal with proposition and context", () => {
  const counter = { value: 0 };
  const prop = call("Eq", ident("n"), ident("n"));
  const ctx = [
    { name: "n", type: ident("Nat") },
    { name: "p", type: call("Eq", ident("n"), ident("n")) },
  ];
  const { stmts, root } = buildGoalStatements(prop, ctx, counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const types = lets.map((l) => l.agentType);
  assertEquals(types.includes(Q_GOAL), true);
  assertEquals(types.includes(CTX_CONS), true);
  assertEquals(types.filter((t) => t === CTX_CONS).length, 2); // two context entries
  assertEquals(types.includes(CTX_NIL), true);
  assertEquals(root.port, "principal");
});

Deno.test("goal: empty context produces CtxNil", () => {
  const counter = { value: 0 };
  const { stmts } = buildGoalStatements(ident("Nat"), [], counter);
  const lets = stmts.filter((s): s is Extract<RuleStmt, { kind: "let" }> => s.kind === "let");
  const types = lets.map((l) => l.agentType);
  assertEquals(types.includes(Q_GOAL), true);
  assertEquals(types.includes(CTX_NIL), true);
  assertEquals(types.includes(CTX_CONS), false);
});

// ─── Integration: quote in prove blocks ────────────────────────────

Deno.test("quote: prove block with quote(refl) compiles", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      open "Quote"
      prove quoted_refl(n : Nat) -> Term {
        | Zero -> quote(refl)
        | Succ(k) -> quote(refl)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("quote: prove block with quote(cong_succ(refl)) compiles", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      open "Quote"
      prove quoted_cong(n : Nat) -> Term {
        | Zero -> quote(refl)
        | Succ(k) -> quote(cong_succ(refl))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("quote: prove block with quoted Pi type compiles", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      open "Quote"
      prove quoted_pi(n : Nat) -> Term {
        | Zero -> quote(forall(x : Nat, Eq(x, x)))
        | Succ(k) -> quote(forall(x : Nat, Eq(x, x)))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Integration: unquote(quote(e)) roundtrip ──────────────────────

Deno.test("quote: unquote(quote(refl)) type-checks as refl", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove roundtrip(n : Nat) -> Eq(n, n) {
        | Zero -> unquote(quote(refl))
        | Succ(k) -> cong_succ(roundtrip(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── QUOTE_AGENTS constant ────────────────────────────────────────

Deno.test("quote: QUOTE_AGENTS has all expected agent names", () => {
  const expected = [
    "TmVar", "TmApp", "TmPi", "TmSigma", "TmLam", "TmNil", "TmCons",
    "QGoal", "CtxNil", "CtxCons",
  ];
  for (const name of expected) {
    assertEquals(QUOTE_AGENTS.includes(name as typeof QUOTE_AGENTS[number]), true, `missing: ${name}`);
  }
});

// ─── open "Quote" registers agents ─────────────────────────────────

Deno.test("quote: open Quote registers quotation agents in system", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      open "Quote"
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T");
  assertNotEquals(sys, undefined);
  for (const name of QUOTE_AGENTS) {
    assertEquals(sys!.agents.has(name), true, `agent ${name} not registered`);
  }
});

// ─── Counter management ───────────────────────────────────────────

Deno.test("quote: counter increments correctly for complex expressions", () => {
  const counter = { value: 0 };
  quoteExpr(call("f", ident("a"), ident("b"), ident("c")), counter);
  // Should have allocated: TmApp, TmVar×3, TmCons×3, TmNil = 8
  assertEquals(counter.value, 8);
});
