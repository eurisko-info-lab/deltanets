// Phase 48: Interactive Proof Mode – session-based step-through tests

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore, core } from "@deltanets/lang";

// ─── Test source: data-based Nat + Eq system ──────────────────────

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

/** Parse source and extract the first ProveDecl with the given name. */
function extractProve(src: string, proveName: string): any {
  const tokens = core.tokenize(src);
  const ast = core.parse(tokens);
  for (const stmt of ast) {
    const body = (stmt as any).body;
    if (!Array.isArray(body)) continue;
    for (const inner of body) {
      if (inner.kind === "prove" && inner.name === proveName) return inner;
    }
  }
  throw new Error(`prove "${proveName}" not found in AST`);
}

/** Compile source, extract prove decl, and start a session. */
function startSession(systemSrc: string, proveName: string, systemName: string) {
  const src = DATA_BASE + "\n" + systemSrc;
  const result = compileCore(src);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  const sys = result.systems.get(systemName)!;
  const proveDecl = extractProve(src, proveName);
  const session = core.startProofSession(
    proveDecl,
    sys.provedCtx,
    sys.computeRules,
    sys.constructorTyping,
    sys.constructorsByType,
    sys.hints,
    sys.instances,
  );
  return { result, sys, proveDecl, session };
}

// ─── Session creation ──────────────────────────────────────────────

Deno.test("phase48: startProofSession creates session from prove with holes", () => {
  const { session } = startSession(`
    system "S1" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S1");
  assertEquals(typeof session.id, "string");
  assertEquals(session.complete, false);
  assertEquals(session.goals.length, 2);
  assertEquals(session.canUndo, false);
  assertEquals(session.canRedo, false);
  core.closeSession(session.id);
});

Deno.test("phase48: session goals report correct types for zero and succ", () => {
  const { session } = startSession(`
    system "S2" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S2");
  assertEquals(session.goals.length, 2);
  assertEquals(session.goals[0].caseIndex, 0);
  assertEquals(session.goals[1].caseIndex, 1);
  // Zero case: Eq(Zero, Zero)
  assertEquals(session.goals[0].goal, "Eq(Zero, Zero)");
  // Succ case: Eq(Succ(add(k, Zero)), Succ(k))
  assertEquals(session.goals[1].goal, "Eq(Succ(add(k, Zero)), Succ(k))");
  core.closeSession(session.id);
});

// ─── Apply proof term ──────────────────────────────────────────────

Deno.test("phase48: applyProofString fills a hole and rebuilds tree", () => {
  const { session } = startSession(`
    system "S3" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S3");
  const zeroGoal = session.goals.find(g => g.caseIndex === 0)!;
  const r = core.applyProofString(session.id, zeroGoal.id, "refl");
  assertEquals(r.success, true, `apply refl failed: ${r.error}`);
  assertEquals(core.getGoals(session.id).length, 1);
  core.closeSession(session.id);
});

// ─── Tactic application ────────────────────────────────────────────

Deno.test("phase48: applyTactic conv solves reflexive goal", () => {
  const { session } = startSession(`
    system "S4" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S4");
  const zeroGoal = session.goals.find(g => g.caseIndex === 0)!;
  const r = core.applySessionTactic(session.id, zeroGoal.id, "conv");
  assertEquals(r.success, true, `conv failed: ${r.error}`);
  core.closeSession(session.id);
});

Deno.test("phase48: applyTactic auto attempts proof search", () => {
  const { session } = startSession(`
    system "S4b" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S4b");
  const zeroGoal = session.goals.find(g => g.caseIndex === 0)!;
  const r = core.applySessionTactic(session.id, zeroGoal.id, "auto");
  assertEquals(r.success, true, `auto failed: ${r.error}`);
  core.closeSession(session.id);
});

// ─── Undo / redo ───────────────────────────────────────────────────

Deno.test("phase48: undo reverts a tactic step", () => {
  const { session } = startSession(`
    system "S5" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S5");
  const goalsBefore = core.getGoals(session.id).length;
  const zeroGoal = core.getGoals(session.id).find(g => g.caseIndex === 0)!;
  const r = core.applyProofString(session.id, zeroGoal.id, "refl");
  assertEquals(r.success, true);
  assertEquals(core.getGoals(session.id).length < goalsBefore, true);

  const undone = core.undoTactic(session.id);
  assertEquals(undone != null, true, "undo should succeed");
  assertEquals(undone!.canUndo, false);
  assertEquals(undone!.canRedo, true);
  assertEquals(core.getGoals(session.id).length, goalsBefore);

  const redone = core.redoTactic(session.id);
  assertEquals(redone != null, true, "redo should succeed");
  core.closeSession(session.id);
});

// ─── Session management ────────────────────────────────────────────

Deno.test("phase48: getSession returns null for unknown id", () => {
  assertEquals(core.getSession("nonexistent-session"), null);
});

Deno.test("phase48: closeSession removes session", () => {
  const { session } = startSession(`
    system "S6" extend "DataNat" {
      prove p(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "p", "S6");
  const id = session.id;
  assertEquals(core.getSession(id) != null, true);
  core.closeSession(id);
  assertEquals(core.getSession(id), null);
});

Deno.test("phase48: listSessions returns active sessions", () => {
  const { session } = startSession(`
    system "S7" extend "DataNat" {
      prove p1(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "p1", "S7");
  assertEquals(core.listSessions().includes(session.id), true);
  core.closeSession(session.id);
});

// ─── Export ────────────────────────────────────────────────────────

Deno.test("phase48: exportSessionText shows goals and status", () => {
  const { session } = startSession(`
    system "S8" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S8");
  const text = core.exportSessionText(session.id);
  assertEquals(text.includes("pzr"), true);
  assertEquals(text.includes("goal"), true);
  core.closeSession(session.id);
});

Deno.test("phase48: exportSessionText for unknown session", () => {
  assertEquals(core.exportSessionText("unknown-session"), "Session not found");
});

// ─── Error handling ────────────────────────────────────────────────

Deno.test("phase48: applyTactic on unknown session returns error", () => {
  const r = core.applySessionTactic("nonexistent", 1, "conv");
  assertEquals(r.success, false);
  assertEquals(r.error!.includes("Session not found"), true);
});

Deno.test("phase48: applyTactic on bad goal id returns error", () => {
  const { session } = startSession(`
    system "S9" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S9");
  const r = core.applySessionTactic(session.id, 9999, "conv");
  assertEquals(r.success, false);
  assertEquals(r.error!.includes("9999"), true);
  core.closeSession(session.id);
});

Deno.test("phase48: undo with no history returns null", () => {
  const { session } = startSession(`
    system "S10" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S10");
  assertEquals(core.undoTactic(session.id), null);
  core.closeSession(session.id);
});

// ─── Goal bindings ─────────────────────────────────────────────────

Deno.test("phase48: goals include case bindings from constructor", () => {
  const { session } = startSession(`
    system "S11" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S11");
  const succGoal = session.goals.find(g => g.caseIndex === 1)!;
  const kBinding = succGoal.bindings.find(b => b.name === "k");
  assertEquals(kBinding != null, true, "Succ case should have binding k");
  core.closeSession(session.id);
});

// ─── createSessionsForSystem ───────────────────────────────────────

Deno.test("phase48: createSessionsForSystem creates sessions for proves with holes", () => {
  const src = DATA_BASE + `
    system "S12" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `;
  const result = compileCore(src);
  assertEquals(result.errors.length, 0);
  const sys = result.systems.get("S12")!;
  const proveDecl = extractProve(src, "pzr");
  const sessions = core.createSessionsForSystem(
    [{ prove: proveDecl, hasHoles: true }],
    sys.provedCtx, sys.computeRules, sys.constructorTyping,
    sys.constructorsByType, sys.hints, sys.instances,
  );
  assertEquals(sessions.size, 1);
  assertEquals(sessions.has("pzr"), true);
  assertEquals(sessions.get("pzr")!.complete, false);
  core.closeSession(sessions.get("pzr")!.id);
});

// ─── Full proof workflow ───────────────────────────────────────────

Deno.test("phase48: complete proof via two manual steps", () => {
  const { session } = startSession(`
    system "S13" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S13");
  assertEquals(session.goals.length, 2);
  assertEquals(session.stepCount, 0);

  const zeroGoal = core.getGoals(session.id).find(g => g.caseIndex === 0)!;
  const r1 = core.applyProofString(session.id, zeroGoal.id, "refl");
  assertEquals(r1.success, true, `step 1 failed: ${r1.error}`);

  const succGoal = core.getGoals(session.id).find(g => g.caseIndex === 1)!;
  const r2 = core.applyProofString(session.id, succGoal.id, "cong_succ(pzr(k))");
  assertEquals(r2.success, true, `step 2 failed: ${r2.error}`);

  const final = core.getSession(session.id)!;
  assertEquals(final.complete, true, "proof should be complete");
  assertEquals(final.stepCount, 2);
  core.closeSession(session.id);
});

// ─── Proof term with applyProofTerm API ────────────────────────────

Deno.test("phase48: applyProofTerm with AST node", () => {
  const { session } = startSession(`
    system "S14" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `, "pzr", "S14");
  assertEquals(session.goals.length, 1);
  const reflExpr = { kind: "ident" as const, name: "refl" };
  const r = core.applyProofTerm(session.id, session.goals[0].id, reflExpr);
  assertEquals(r.success, true, `applyProofTerm failed: ${r.error}`);
  core.closeSession(session.id);
});

// ─── Goal suggestions ──────────────────────────────────────────────

Deno.test("phase48: goals include suggestions from proof search", () => {
  const { session } = startSession(`
    system "S15" extend "DataNat" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> ?
        | Succ(k) -> ?
      }
    }
  `, "pzr", "S15");
  const zeroGoal = session.goals.find(g => g.caseIndex === 0)!;
  assertEquals(
    zeroGoal.suggestions.includes("refl"),
    true,
    `expected refl in suggestions, got: ${zeroGoal.suggestions}`,
  );
  core.closeSession(session.id);
});
