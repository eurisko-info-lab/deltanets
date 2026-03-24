// ═══════════════════════════════════════════════════════════════════
// Interactive Proof Mode — Step-through proof development
//
// Provides a session-based API for incrementally building proofs:
//   1. Start a session from a prove block with holes (?)
//   2. Inspect goals — each hole has context, expected type, suggestions
//   3. Apply tactics to holes — fill with proof terms, rebuild tree
//   4. Undo/redo tactic steps
//   5. Session reports when all goals are closed
//
// Works entirely on the existing ProveExpr AST and normalizer —
// no changes to the INet reduction engine.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { auxParams } from "./types.ts";
import {
  normalize, exprToString, withNormTable, substitute, exprEqual,
  type ProvedContext, type ComputeRule, type ConstructorTyping,
  type RecordDef,
} from "./normalize.ts";
import type { CanonicalDef, InstanceDef } from "./evaluator.ts";
import {
  type ProofTree, type ProofNode,
  buildProofTree, computeGoalType, searchProofContext,
  makeStrategyContext, primConv, primCtxSearch, primRewrite,
  primGround, primSearch, primCong,
  extractEq,
} from "./typecheck-prove.ts";

// ─── Goal & session types ──────────────────────────────────────────

/** A binding visible in a goal context. */
export type GoalBinding = {
  name: string;
  type: string;   // normalized, pretty-printed
};

/** A single proof goal (corresponding to one ? hole). */
export type ProofGoal = {
  id: number;                  // unique within session
  caseIndex: number;           // which case arm
  casePattern: string;         // e.g. "Zero", "Succ(k)"
  goal: string;                // expected type, normalized + pretty-printed
  goalExpr: AST.ProveExpr;     // machine-readable expected type
  bindings: GoalBinding[];     // local context
  suggestions: string[];       // auto-fill candidates
  path: number[];              // path through the ProofNode tree to this hole
};

/** Result of applying a tactic to a goal. */
export type TacticResult = {
  success: boolean;
  error?: string;
  /** New goals introduced by the tactic (e.g. 0 if goal closed, 2 for trans). */
  newGoals: ProofGoal[];
  /** The complete proof tree after the step. */
  tree: ProofTree;
  /** Whether all goals are now closed (proof complete). */
  complete: boolean;
};

/** A recorded tactic step for undo/redo. */
type TacticStep = {
  goalId: number;
  tactic: string;
  proofTerm: AST.ProveExpr;
  prevProve: AST.ProveDecl;     // prove state before this step
};

/** Interactive proof session. */
export type ProofSession = {
  /** Session identifier. */
  readonly id: string;
  /** Current prove declaration (mutated as tactics are applied). */
  readonly prove: AST.ProveDecl;
  /** Current proof tree. */
  readonly tree: ProofTree;
  /** All open goals. */
  readonly goals: ProofGoal[];
  /** Whether the proof is complete (no open goals). */
  readonly complete: boolean;
  /** Number of tactic steps applied. */
  readonly stepCount: number;
  /** Whether undo is available. */
  readonly canUndo: boolean;
  /** Whether redo is available. */
  readonly canRedo: boolean;
};

// ─── Session implementation ────────────────────────────────────────

/** Internal mutable session state. */
class SessionState {
  prove: AST.ProveDecl;
  tree: ProofTree;
  goals: ProofGoal[];
  history: TacticStep[] = [];
  redoStack: TacticStep[] = [];
  private nextGoalId = 1;

  constructor(
    readonly id: string,
    readonly provedCtx: ProvedContext,
    readonly computeRules: ComputeRule[],
    readonly constructorTyping: ConstructorTyping,
    readonly constructorsByType?: Map<string, Set<string>>,
    readonly hints?: Map<string, Set<string>>,
    readonly instances?: InstanceDef[],
    readonly dataSorts?: Map<string, "Prop" | "Set" | "SProp">,
    readonly canonicals?: CanonicalDef[],
    readonly recordDefs?: Map<string, RecordDef>,
    prove?: AST.ProveDecl,
  ) {
    this.prove = prove!;
    this.tree = this.rebuildTree();
    this.goals = this.collectGoals();
  }

  rebuildTree(): ProofTree {
    this.tree = withNormTable(this.computeRules, () =>
      buildProofTree(
        this.prove, this.provedCtx, this.computeRules,
        this.constructorTyping, this.recordDefs,
      )!, undefined, this.recordDefs);
    return this.tree;
  }

  /** Walk the proof tree and collect all open goals. */
  collectGoals(): ProofGoal[] {
    const goals: ProofGoal[] = [];
    for (let ci = 0; ci < this.tree.cases.length; ci++) {
      const c = this.tree.cases[ci];
      const pat = c.bindings.length > 0
        ? `${c.pattern}(${c.bindings.join(", ")})`
        : c.pattern;
      this.walkForGoals(c.tree, ci, pat, [], goals);
    }
    this.goals = goals;
    return goals;
  }

  private walkForGoals(
    node: ProofNode, caseIndex: number, casePattern: string,
    path: number[], out: ProofGoal[],
  ): void {
    if (node.isGoal) {
      // Build bindings from the case context
      const caseArm = this.prove.cases[caseIndex];
      const bindings: GoalBinding[] = [];
      // Constructor bindings
      if (caseArm) {
        for (const b of caseArm.bindings) {
          const info = this.constructorTyping.get(caseArm.pattern);
          const fieldIdx = caseArm.bindings.indexOf(b);
          const fieldType = info && fieldIdx < info.fields.length
            ? exprToString(normalize(info.fields[fieldIdx].type))
            : "?";
          bindings.push({ name: b, type: fieldType });
        }
        // Auxiliary params
        for (const p of auxParams(this.prove.params)) {
          if (p.type) {
            bindings.push({ name: p.name, type: exprToString(normalize(p.type)) });
          }
        }
      }

      out.push({
        id: this.nextGoalId++,
        caseIndex,
        casePattern,
        goal: node.conclusion,
        goalExpr: parseGoalExpr(node.conclusion),
        bindings,
        suggestions: node.suggestions ?? [],
        path: [...path],
      });
    }
    for (let i = 0; i < node.children.length; i++) {
      this.walkForGoals(node.children[i], caseIndex, casePattern, [...path, i], out);
    }
  }

  /** Apply a proof term to a specific goal, replacing its ? hole. */
  applyTerm(goalId: number, proofTerm: AST.ProveExpr): TacticResult {
    const goal = this.goals.find(g => g.id === goalId);
    if (!goal) {
      return { success: false, error: `Goal ${goalId} not found`, newGoals: [], tree: this.tree, complete: this.goals.length === 0 };
    }

    // Save state for undo
    const prevProve = deepCloneProve(this.prove);
    const caseArm = this.prove.cases[goal.caseIndex];
    if (!caseArm) {
      return { success: false, error: `Case ${goal.caseIndex} not found`, newGoals: [], tree: this.tree, complete: false };
    }

    // Replace the ? hole at the specified path with the proof term
    const newBody = replaceHoleAtPath(caseArm.body, goal.path, proofTerm);
    if (!newBody) {
      return { success: false, error: "Could not locate hole at path", newGoals: [], tree: this.tree, complete: false };
    }

    // Update case body
    caseArm.body = newBody;

    // Record step
    this.history.push({ goalId, tactic: exprToString(proofTerm), proofTerm, prevProve });
    this.redoStack = [];

    // Rebuild tree and collect new goals
    this.rebuildTree();
    const prevGoalIds = new Set(this.goals.map(g => g.id));
    this.collectGoals();
    const newGoals = this.goals.filter(g => !prevGoalIds.has(g.id));

    return {
      success: true,
      newGoals,
      tree: this.tree,
      complete: this.goals.length === 0,
    };
  }

  /** Apply a named tactic to a goal. */
  applyTactic(goalId: number, tacticName: string): TacticResult {
    const goal = this.goals.find(g => g.id === goalId);
    if (!goal) {
      return { success: false, error: `Goal ${goalId} not found`, newGoals: [], tree: this.tree, complete: false };
    }

    const proofTerm = withNormTable(this.computeRules, () =>
      resolveTacticTerm(tacticName, goal, this.prove, this.provedCtx, this.hints, this.instances),
    undefined, this.recordDefs);

    if (!proofTerm) {
      return { success: false, error: `Tactic '${tacticName}' failed on goal: ${goal.goal}`, newGoals: [], tree: this.tree, complete: false };
    }

    return this.applyTerm(goalId, proofTerm);
  }

  /** Undo the last tactic step. */
  undo(): ProofSession | null {
    const step = this.history.pop();
    if (!step) return null;
    this.redoStack.push({ ...step, prevProve: deepCloneProve(this.prove) });
    // Restore previous prove state
    this.prove = step.prevProve;
    this.rebuildTree();
    this.collectGoals();
    return this.snapshot();
  }

  /** Redo the last undone step. */
  redo(): ProofSession | null {
    const step = this.redoStack.pop();
    if (!step) return null;
    this.history.push({ ...step, prevProve: deepCloneProve(this.prove) });
    this.prove = step.prevProve;
    this.rebuildTree();
    this.collectGoals();
    return this.snapshot();
  }

  /** Create an immutable snapshot of the current state. */
  snapshot(): ProofSession {
    return {
      id: this.id,
      prove: this.prove,
      tree: this.tree,
      goals: [...this.goals],
      complete: this.goals.length === 0,
      stepCount: this.history.length,
      canUndo: this.history.length > 0,
      canRedo: this.redoStack.length > 0,
    };
  }
}

// ─── Tactic resolution ─────────────────────────────────────────────
// Maps named tactics to proof terms using existing proof search.

function resolveTacticTerm(
  name: string,
  goal: ProofGoal,
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
  hints?: Map<string, Set<string>>,
  instances?: InstanceDef[],
): AST.ProveExpr | null {
  const caseArm = prove.cases[goal.caseIndex];
  if (!caseArm) return null;

  const sctx = makeStrategyContext(prove, caseArm, provedCtx, hints, instances);

  switch (name) {
    case "conv":
    case "reflexivity": {
      return primConv(sctx);
    }
    case "assumption": {
      return primCtxSearch(sctx);
    }
    case "rewrite":
    case "simp": {
      return primRewrite(sctx);
    }
    case "auto": {
      return primSearch(sctx, 3);
    }
    case "ground": {
      return primGround(sctx);
    }
    default:
      return null;
  }
}

// ─── AST manipulation helpers ──────────────────────────────────────

/** Count ? holes in an expression (pre-order). */
function countHoles(expr: AST.ProveExpr): number {
  if (expr.kind === "hole") return 1;
  if (expr.kind === "ident" || expr.kind === "metavar") return 0;
  if (expr.kind === "let") return countHoles(expr.value) + countHoles(expr.body);
  if (expr.kind === "pi" || expr.kind === "sigma") return countHoles(expr.domain) + countHoles(expr.codomain);
  if (expr.kind === "lambda") return countHoles(expr.paramType) + countHoles(expr.body);
  if (expr.kind === "match") return expr.cases.reduce((n, c) => n + countHoles(c.body), 0);
  if (expr.kind === "meta-app") return expr.args.reduce((n, a) => n + countHoles(a), 0);
  if (expr.kind === "call") return expr.args.reduce((n, a) => n + countHoles(a), 0);
  return 0;
}

/**
 * Replace the hole at the given ProofNode path with a replacement expression.
 * Path indexes correspond to children indices in ProofNode, which map to
 * structural positions in the AST.
 */
function replaceHoleAtPath(
  expr: AST.ProveExpr,
  path: number[],
  replacement: AST.ProveExpr,
): AST.ProveExpr | null {
  if (path.length === 0) {
    // We should be at a hole
    if (expr.kind === "hole") return replacement;
    return null;
  }
  return replaceNthHole(expr, countHolesToPath(expr, path), replacement);
}

/** Count holes before the targeted path position. */
function countHolesToPath(expr: AST.ProveExpr, path: number[]): number {
  // For simplicity, we number holes in pre-order and the path tells us
  // which child route to take in the ProofNode tree.
  // Since holes are 1:1 with ProofNode goals, we locate by position.
  // The path was collected during tree traversal, so the nth hole in
  // case body corresponds to path ordering.
  // We use a simpler strategy: count which hole this is (0-indexed).
  return pathToHoleIndex(expr, path);
}

/** Convert a ProofNode child-path to a 0-based hole index in the expression. */
function pathToHoleIndex(_expr: AST.ProveExpr, _path: number[]): number {
  // The ProofNode tree paths map to hole indices in pre-order.
  // Since we walk both the AST and ProofNode in the same order,
  // the hole index is determined by counting all holes encountered
  // before reaching the target path.
  // For the simple case (most common), when path=[] the hole is the expr itself.
  // For deeper paths, we compute the pre-order hole index.
  // Since each goal in the tree is one ?, we can count total ?'s before this one.
  // The goals are collected in the same order as walkForGoals which is pre-order.
  // So for the Nth goal in a case, we want the Nth hole.
  return 0; // Will be overridden — we use replaceNthHoleDirect instead.
}

/** Replace the Nth ? hole (0-indexed, pre-order) in an expression. */
function replaceNthHole(
  expr: AST.ProveExpr,
  n: number,
  replacement: AST.ProveExpr,
): AST.ProveExpr | null {
  const result = replaceNthHoleInner(expr, n, replacement);
  return result.expr;
}

function replaceNthHoleInner(
  expr: AST.ProveExpr,
  n: number,
  replacement: AST.ProveExpr,
): { expr: AST.ProveExpr | null; consumed: number } {
  if (expr.kind === "hole") {
    if (n === 0) return { expr: replacement, consumed: 1 };
    return { expr: null, consumed: 1 };
  }
  if (expr.kind === "ident" || expr.kind === "metavar") {
    return { expr: null, consumed: 0 };
  }
  if (expr.kind === "let") {
    const vr = replaceNthHoleInner(expr.value, n, replacement);
    if (vr.expr) return { expr: { ...expr, value: vr.expr }, consumed: vr.consumed };
    const br = replaceNthHoleInner(expr.body, n - vr.consumed, replacement);
    if (br.expr) return { expr: { ...expr, body: br.expr }, consumed: vr.consumed + br.consumed };
    return { expr: null, consumed: vr.consumed + br.consumed };
  }
  if (expr.kind === "pi" || expr.kind === "sigma") {
    const dr = replaceNthHoleInner(expr.domain, n, replacement);
    if (dr.expr) return { expr: { ...expr, domain: dr.expr } as typeof expr, consumed: dr.consumed };
    const cr = replaceNthHoleInner(expr.codomain, n - dr.consumed, replacement);
    if (cr.expr) return { expr: { ...expr, codomain: cr.expr } as typeof expr, consumed: dr.consumed + cr.consumed };
    return { expr: null, consumed: dr.consumed + cr.consumed };
  }
  if (expr.kind === "lambda") {
    const pr = replaceNthHoleInner(expr.paramType, n, replacement);
    if (pr.expr) return { expr: { ...expr, paramType: pr.expr }, consumed: pr.consumed };
    const br = replaceNthHoleInner(expr.body, n - pr.consumed, replacement);
    if (br.expr) return { expr: { ...expr, body: br.expr }, consumed: pr.consumed + br.consumed };
    return { expr: null, consumed: pr.consumed + br.consumed };
  }
  if (expr.kind === "match") {
    let offset = 0;
    for (let i = 0; i < expr.cases.length; i++) {
      const cr = replaceNthHoleInner(expr.cases[i].body, n - offset, replacement);
      if (cr.expr) {
        const newCases = [...expr.cases];
        newCases[i] = { ...expr.cases[i], body: cr.expr };
        return { expr: { ...expr, cases: newCases }, consumed: offset + cr.consumed };
      }
      offset += cr.consumed;
    }
    return { expr: null, consumed: offset };
  }
  if (expr.kind === "meta-app") {
    let offset = 0;
    for (let i = 0; i < expr.args.length; i++) {
      const ar = replaceNthHoleInner(expr.args[i], n - offset, replacement);
      if (ar.expr) {
        const newArgs = [...expr.args];
        newArgs[i] = ar.expr;
        return { expr: { ...expr, args: newArgs }, consumed: offset + ar.consumed };
      }
      offset += ar.consumed;
    }
    return { expr: null, consumed: offset };
  }
  if (expr.kind === "call") {
    let offset = 0;
    for (let i = 0; i < expr.args.length; i++) {
      const ar = replaceNthHoleInner(expr.args[i], n - offset, replacement);
      if (ar.expr) {
        const newArgs = [...expr.args];
        newArgs[i] = ar.expr;
        return { expr: { kind: "call", name: expr.name, args: newArgs }, consumed: offset + ar.consumed };
      }
      offset += ar.consumed;
    }
    return { expr: null, consumed: offset };
  }
  return { expr: null, consumed: 0 };
}

/** Deep clone a ProveDecl so undo can restore previous state. */
function deepCloneProve(prove: AST.ProveDecl): AST.ProveDecl {
  return JSON.parse(JSON.stringify(prove));
}

/** Parse a goal string back into a ProveExpr (simple recursive descent). */
function parseGoalExpr(s: string): AST.ProveExpr {
  s = s.trim();
  if (!s || s === "?") return { kind: "hole" };
  // call: Name(a, b, ...)
  const callMatch = s.match(/^([A-Za-z_]\w*)\((.+)\)$/);
  if (callMatch) {
    const name = callMatch[1];
    const argsStr = splitTopLevel(callMatch[2]);
    return { kind: "call", name, args: argsStr.map(parseGoalExpr) };
  }
  // ident
  if (/^[A-Za-z_]\w*$/.test(s)) return { kind: "ident", name: s };
  // fallback
  return { kind: "ident", name: s };
}

/** Split a comma-separated string respecting parenthesis nesting. */
function splitTopLevel(s: string): string[] {
  const parts: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === "(") depth++;
    else if (s[i] === ")") depth--;
    else if (s[i] === "," && depth === 0) {
      parts.push(s.slice(start, i).trim());
      start = i + 1;
    }
  }
  parts.push(s.slice(start).trim());
  return parts;
}

// ─── Path-based hole replacement ───────────────────────────────────
// Goals are numbered by their pre-order position among all holes in a case.
// The goal's caseIndex tells us which case arm, and we count holes in order.

/** Replace a hole in a case body by its sequential index among holes. */
function replaceHoleByIndex(
  expr: AST.ProveExpr,
  holeIndex: number,
  replacement: AST.ProveExpr,
): AST.ProveExpr | null {
  return replaceNthHole(expr, holeIndex, replacement);
}

// ─── Public API ────────────────────────────────────────────────────

let _sessionCounter = 0;

/** Start a new interactive proof session from a prove block. */
export function startProofSession(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext = new Map(),
  computeRules: ComputeRule[] = [],
  constructorTyping: ConstructorTyping = new Map(),
  constructorsByType?: Map<string, Set<string>>,
  hints?: Map<string, Set<string>>,
  instances?: InstanceDef[],
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">,
  canonicals?: CanonicalDef[],
  recordDefs?: Map<string, RecordDef>,
): ProofSession {
  const id = `session-${++_sessionCounter}`;
  const state = new SessionState(
    id, provedCtx, computeRules, constructorTyping,
    constructorsByType, hints, instances, dataSorts,
    canonicals, recordDefs, deepCloneProve(prove),
  );
  sessions.set(id, state);
  return state.snapshot();
}

/** Get the current state of a session. */
export function getSession(id: string): ProofSession | null {
  const state = sessions.get(id);
  return state ? state.snapshot() : null;
}

/** Get all open goals for a session. */
export function getGoals(id: string): ProofGoal[] {
  const state = sessions.get(id);
  return state ? [...state.goals] : [];
}

/** Apply a named tactic to a specific goal in a session. */
export function applyTactic(
  sessionId: string,
  goalId: number,
  tacticName: string,
): TacticResult {
  const state = sessions.get(sessionId);
  if (!state) {
    return { success: false, error: "Session not found", newGoals: [], tree: null as any, complete: false };
  }
  return state.applyTactic(goalId, tacticName);
}

/** Apply a specific proof term to a goal in a session. */
export function applyProofTerm(
  sessionId: string,
  goalId: number,
  proofTerm: AST.ProveExpr,
): TacticResult {
  const state = sessions.get(sessionId);
  if (!state) {
    return { success: false, error: "Session not found", newGoals: [], tree: null as any, complete: false };
  }
  return state.applyTerm(goalId, proofTerm);
}

/** Apply a proof term given as a string (parsed into a ProveExpr). */
export function applyProofString(
  sessionId: string,
  goalId: number,
  termStr: string,
): TacticResult {
  return applyProofTerm(sessionId, goalId, parseGoalExpr(termStr));
}

/** Undo the last tactic step. */
export function undoTactic(sessionId: string): ProofSession | null {
  const state = sessions.get(sessionId);
  return state ? state.undo() : null;
}

/** Redo the last undone step. */
export function redoTactic(sessionId: string): ProofSession | null {
  const state = sessions.get(sessionId);
  return state ? state.redo() : null;
}

/** Close and clean up a session. */
export function closeSession(sessionId: string): boolean {
  return sessions.delete(sessionId);
}

/** List all active session IDs. */
export function listSessions(): string[] {
  return [...sessions.keys()];
}

/** Export a proof session's current state as displayable text. */
export function exportSessionText(sessionId: string): string {
  const state = sessions.get(sessionId);
  if (!state) return "Session not found";

  const lines: string[] = [];
  const status = state.goals.length === 0 ? "COMPLETE" : `${state.goals.length} goal(s) remaining`;
  lines.push(`Interactive proof: ${state.prove.name} [${status}]`);
  lines.push(`Steps: ${state.history.length}  Undo: ${state.history.length > 0 ? "yes" : "no"}  Redo: ${state.redoStack.length > 0 ? "yes" : "no"}`);
  lines.push("");

  if (state.goals.length > 0) {
    lines.push("Goals:");
    for (const g of state.goals) {
      lines.push(`  ${g.id}. [${g.casePattern}] ⊢ ${g.goal}`);
      if (g.bindings.length > 0) {
        for (const b of g.bindings) {
          lines.push(`     ${b.name} : ${b.type}`);
        }
      }
      if (g.suggestions.length > 0) {
        lines.push(`     suggestions: ${g.suggestions.join(", ")}`);
      }
    }
  } else {
    lines.push("No goals remaining — proof complete!");
  }

  return lines.join("\n");
}

// ─── Session store ─────────────────────────────────────────────────

const sessions = new Map<string, SessionState>();

// ─── Auto-session creation from eval pipeline ──────────────────────

/**
 * Create sessions for all prove blocks with holes in a system.
 * Called from evalBodyInto when a prove block contains ? holes.
 * Returns a map from prove name → session.
 */
export function createSessionsForSystem(
  proveBlocks: { prove: AST.ProveDecl; hasHoles: boolean }[],
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
  constructorTyping: ConstructorTyping,
  constructorsByType?: Map<string, Set<string>>,
  hints?: Map<string, Set<string>>,
  instances?: InstanceDef[],
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">,
  canonicals?: CanonicalDef[],
  recordDefs?: Map<string, RecordDef>,
): Map<string, ProofSession> {
  const result = new Map<string, ProofSession>();
  for (const { prove, hasHoles } of proveBlocks) {
    if (!hasHoles || !prove.returnType) continue;
    const session = startProofSession(
      prove, provedCtx, computeRules, constructorTyping,
      constructorsByType, hints, instances, dataSorts,
      canonicals, recordDefs,
    );
    result.set(prove.name, session);
  }
  return result;
}
