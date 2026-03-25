// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Termination & Exhaustiveness Checking
// Structural recursion, productivity, measure termination, and
// pattern exhaustiveness/overlap checking.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { inductionParam } from "./types.ts";
import { exprEqual, exprToString, normalize, substitute, substituteAll, type ConstructorTyping } from "./normalize.ts";

// ─── Termination checking (structural recursion) ───────────────────

function collectRecursiveCalls(
  expr: AST.ProveExpr,
  funcName: string,
  activeBindings: Set<string>,
): { call: AST.ProveExpr; bindings: Set<string> }[] {
  const calls: { call: AST.ProveExpr; bindings: Set<string> }[] = [];
  function walk(e: AST.ProveExpr, bindings: Set<string>) {
    if (e.kind === "call") {
      if (e.name === funcName) calls.push({ call: e, bindings });
      for (const a of e.args) walk(a, bindings);
    }
    if (e.kind === "let") {
      walk(e.value, bindings);
      walk(e.body, bindings);
    }
    if (e.kind === "pi" || e.kind === "sigma") {
      walk(e.domain, bindings);
      walk(e.codomain, bindings);
    }
    if (e.kind === "lambda") {
      walk(e.paramType, bindings);
      walk(e.body, bindings);
    }
    if (e.kind === "match") {
      for (const c of e.cases) {
        const inner = new Set(bindings);
        for (const b of c.bindings) inner.add(b);
        walk(c.body, inner);
      }
    }
  }
  walk(expr, activeBindings);
  return calls;
}

export function checkTermination(
  prove: AST.ProveDecl,
): string[] {
  const errors: string[] = [];
  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue;
    const topBindings = new Set(caseArm.bindings);
    const recCalls = collectRecursiveCalls(caseArm.body, prove.name, topBindings);
    for (const { call, bindings } of recCalls) {
      if (call.kind !== "call" || call.args.length === 0) continue;
      const hasDecreasing = call.args.some(
        (a) => a.kind === "ident" && bindings.has(a.name),
      );
      if (!hasDecreasing) {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: recursive call ` +
          `${prove.name}(${call.args.map(exprToString).join(", ")}) ` +
          `is not structurally decreasing — at least one argument must be a case binding` +
          (bindings.size > 0 ? ` (${[...bindings].join(", ")})` : ``),
        );
      }
    }
  }
  return errors;
}

// ─── Guard condition for cofixpoints ───────────────────────────────
// Robust nested corecursive productivity checking.
//
// The guard condition ensures every corecursive call is "guarded" —
// it must appear under a constructor of the coinductive return type.
// This is the dual of the structural recursion check: recursion must
// consume data (arguments get smaller), corecursion must produce
// codata (results are wrapped in a constructor).
//
// Key rules:
//  1. Guard constructors (guard_xxx) set guarded=true for their args
//  2. Other constructors are transparent — propagate current guard status
//  3. Function/observation calls are opaque — block guard propagation
//  4. Structural forms (match, let, lambda) propagate guard status
//  5. Type forms (pi, sigma) never propagate guard status
//  6. Let-binding transparency: a recursive call in a let value is
//     productive if the bound variable is only used in guarded positions

/** Context for guard condition analysis. */
interface GuardCtx {
  funcName: string;
  guardName: string;
  allConstructors: Set<string>;
  observationAgents: Set<string>;
}

/** A detected guard violation with context for error reporting. */
interface GuardViolation {
  call: AST.ProveExpr;
  context: "bare" | "observation" | "function" | "type";
  wrapper?: string; // the blocking function/observation name
}

/** Productivity checking for codata-returning proves.
 *  Dual of termination: every recursive call must appear under a guard
 *  constructor application (guarded corecursion).
 *
 *  Enhanced guard condition supports:
 *  - Nested guards and constructors (transparent propagation)
 *  - Match/let/lambda inside guard args (structural propagation)
 *  - Observation-aware error messages
 *  - Let-binding transparency analysis */
export function checkProductivity(
  prove: AST.ProveDecl,
  codataTypeName: string,
  constructorTyping?: ConstructorTyping,
): string[] {
  const guardName = `guard_${codataTypeName.toLowerCase()}`;

  // Build sets of known constructors and observation agents
  const allConstructors = new Set<string>();
  const observationAgents = new Set<string>();
  if (constructorTyping) {
    for (const [ctorName, info] of constructorTyping) {
      allConstructors.add(ctorName);
      // Observation agents are generated from codata field names.
      // Identify them: if the constructor is a guard_xxx, its fields
      // become observation agents.
      if (ctorName.startsWith("guard_")) {
        for (const f of info.fields) observationAgents.add(f.name);
      }
    }
  } else {
    // Fallback: at least know our own guard
    allConstructors.add(guardName);
  }

  const ctx: GuardCtx = { funcName: prove.name, guardName, allConstructors, observationAgents };
  const errors: string[] = [];

  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue;
    const violations = analyzeGuardCondition(caseArm.body, ctx);
    for (const v of violations) {
      const callStr = v.call.kind === "call" ? v.call.args.map(exprToString).join(", ") : "";
      let msg = `prove ${prove.name}, case ${caseArm.pattern}: corecursive call ` +
        `${prove.name}(${callStr}) is not productive`;
      if (v.context === "observation" && v.wrapper) {
        msg += ` — appears under observation ${v.wrapper}(), not a guard constructor`;
      } else if (v.context === "function" && v.wrapper) {
        msg += ` — blocked by function call ${v.wrapper}()`;
      } else if (v.context === "type") {
        msg += ` — corecursive call in type position is not productive`;
      } else {
        msg += ` — must appear under ${guardName}(...)`;
      }
      errors.push(msg);
    }
  }
  return errors;
}

/** Analyze an expression for guard condition violations.
 *  Returns all corecursive calls that are NOT properly guarded. */
function analyzeGuardCondition(
  expr: AST.ProveExpr,
  ctx: GuardCtx,
): GuardViolation[] {
  // Phase 1: collect violations with basic walk
  const violations: GuardViolation[] = [];
  // Track let-bound variables that hold recursive calls, for let-transparency
  const letRecCalls = new Map<string, AST.ProveExpr>();

  function walk(e: AST.ProveExpr, guarded: boolean, inType: boolean): void {
    // Recursive call found — check if guarded
    if (e.kind === "call" && e.name === ctx.funcName) {
      if (!guarded) {
        violations.push({ call: e, context: inType ? "type" : "bare" });
      }
      // Don't recurse into args of the recursive call itself
      return;
    }

    if (e.kind === "call") {
      const isGuard = e.name === ctx.guardName;
      const isCtor = ctx.allConstructors.has(e.name);
      const isObs = ctx.observationAgents.has(e.name);

      if (isGuard) {
        // Guard constructor: args become guarded
        for (const a of e.args) walk(a, true, false);
      } else if (isCtor) {
        // Other constructors are transparent — propagate current guard context
        for (const a of e.args) walk(a, guarded, false);
      } else {
        // Functions/observations: block guard propagation
        // But record the blocking agent for better errors
        for (const a of e.args) {
          walkWithBlocker(a, e.name, isObs, inType);
        }
      }
      return;
    }

    if (e.kind === "let") {
      walk(e.value, guarded, false);
      // Track let-bound recursive calls for transparency analysis
      if (e.value.kind === "call" && e.value.name === ctx.funcName) {
        letRecCalls.set(e.name, e.value);
      }
      walk(e.body, guarded, false);
      return;
    }

    if (e.kind === "match") {
      // Match scrutinee: walk without guard (scrutinee is consumed, not produced)
      if (e.cases.length > 0 && e.cases[0].body) {
        // Walk each case body with inherited guard context
        for (const c of e.cases) walk(c.body, guarded, false);
      }
      return;
    }

    if (e.kind === "lambda") {
      walk(e.paramType, false, true); // type annotation — no guard propagation
      walk(e.body, guarded, false);   // body inherits guard context
      return;
    }

    if (e.kind === "pi" || e.kind === "sigma") {
      // Type-level forms: never propagate guard (recursive calls in types are errors)
      walk(e.domain, false, true);
      walk(e.codomain, false, true);
      return;
    }

    if (e.kind === "meta-app") {
      walk(e.fn, guarded, inType);
      for (const a of e.args) walk(a, guarded, inType);
      return;
    }
    // ident, hole, metavar — leaf nodes, nothing to walk
  }

  /** Walk inside a function/observation call that blocks guard propagation.
   *  Records context info for better error messages. */
  function walkWithBlocker(
    e: AST.ProveExpr,
    blockerName: string,
    isObs: boolean,
    inType: boolean,
  ): void {
    if (e.kind === "call" && e.name === ctx.funcName) {
      violations.push({
        call: e,
        context: isObs ? "observation" : "function",
        wrapper: blockerName,
      });
      return;
    }
    // Recurse with guarded=false since we're inside a blocking call
    walk(e, false, inType);
  }

  walk(expr, false, false);

  // Phase 2: Let-transparency — check if any "unguarded" let-bound
  // recursive calls are actually used exclusively in guarded positions.
  // Pattern: let x = f(args) in ... guard_xxx(..., x, ...) ...
  if (letRecCalls.size > 0 && violations.length > 0) {
    const rescuable = new Set<AST.ProveExpr>();
    for (const [varName, recCall] of letRecCalls) {
      // Check if this variable is only used in guarded positions
      if (isVarOnlyUsedGuarded(expr, varName, ctx)) {
        rescuable.add(recCall);
      }
    }
    if (rescuable.size > 0) {
      return violations.filter(v => !rescuable.has(v.call));
    }
  }

  return violations;
}

/** Check if a variable is used only in guarded positions in an expression.
 *  Used for let-transparency: `let x = rec_call in guard(x)` is productive. */
function isVarOnlyUsedGuarded(
  expr: AST.ProveExpr,
  varName: string,
  ctx: GuardCtx,
): boolean {
  let allGuarded = true;
  let anyUse = false;

  function walk(e: AST.ProveExpr, guarded: boolean): void {
    if (!allGuarded) return; // short-circuit

    if (e.kind === "ident" && e.name === varName) {
      anyUse = true;
      if (!guarded) allGuarded = false;
      return;
    }

    if (e.kind === "call") {
      const isGuard = e.name === ctx.guardName;
      const isCtor = ctx.allConstructors.has(e.name);
      if (isGuard) {
        for (const a of e.args) walk(a, true);
      } else if (isCtor) {
        for (const a of e.args) walk(a, guarded);
      } else {
        for (const a of e.args) walk(a, false);
      }
      return;
    }
    if (e.kind === "let") {
      walk(e.value, guarded);
      walk(e.body, guarded);
      return;
    }
    if (e.kind === "match") {
      for (const c of e.cases) walk(c.body, guarded);
      return;
    }
    if (e.kind === "lambda") {
      walk(e.paramType, false);
      walk(e.body, guarded);
      return;
    }
    if (e.kind === "pi" || e.kind === "sigma") {
      walk(e.domain, false);
      walk(e.codomain, false);
      return;
    }
    if (e.kind === "meta-app") {
      walk(e.fn, guarded);
      for (const a of e.args) walk(a, guarded);
    }
  }

  walk(expr, false);
  return anyUse && allGuarded;
}

// ─── Measure-based termination checking ────────────────────────────

export function checkMeasureTermination(
  prove: AST.ProveDecl,
  measureExpr: AST.ProveExpr,
): string[] {
  const errors: string[] = [];
  const paramNames = prove.params.filter((p) => !p.implicit).map((p) => p.name);

  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue;
    const topBindings = new Set(caseArm.bindings);
    const recCalls = collectRecursiveCalls(caseArm.body, prove.name, topBindings);

    const inductVar = paramNames[0];
    const patternExpr: AST.ProveExpr = caseArm.bindings.length > 0
      ? { kind: "call", name: caseArm.pattern, args: caseArm.bindings.map((b) => ({ kind: "ident" as const, name: b })) }
      : { kind: "ident", name: caseArm.pattern };
    const originalMeasure = normalize(substitute(measureExpr, inductVar, patternExpr));

    for (const { call, bindings } of recCalls) {
      if (call.kind !== "call" || call.args.length === 0) continue;

      const callBindings = new Map<string, AST.ProveExpr>();
      for (let i = 0; i < Math.min(call.args.length, paramNames.length); i++) {
        callBindings.set(paramNames[i], call.args[i]);
      }
      const newMeasure = normalize(substituteAll(measureExpr, callBindings));

      if (!measureStrictlySmaller(newMeasure, originalMeasure, bindings)) {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: recursive call ` +
          `${prove.name}(${call.args.map(exprToString).join(", ")}) ` +
          `— measure ${exprToString(newMeasure)} is not smaller than ${exprToString(originalMeasure)}`,
        );
      }
    }
  }
  return errors;
}

function measureStrictlySmaller(
  a: AST.ProveExpr,
  b: AST.ProveExpr,
  bindings: Set<string>,
): boolean {
  if (a.kind === "ident" && bindings.has(a.name) &&
      b.kind === "call" && b.name === "Succ") return true;
  if (a.kind === "ident" && a.name === "Zero" &&
      b.kind === "call" && b.name === "Succ") return true;
  if (a.kind === "call" && a.name === "Succ" && a.args.length === 1 &&
      b.kind === "call" && b.name === "Succ" && b.args.length === 1) {
    return measureStrictlySmaller(a.args[0], b.args[0], bindings);
  }
  if (b.kind === "call" && b.name === "Succ" && b.args.length === 1 &&
      exprEqual(a, b.args[0])) return true;
  return false;
}

// ─── Exhaustiveness checking ───────────────────────────────────────

export function checkExhaustiveness(
  prove: AST.ProveDecl,
  constructorsByType: Map<string, Set<string>>,
): string[] {
  const firstParam = inductionParam(prove.params);
  if (!firstParam?.type) return [];
  const typeName = firstParam.type.kind === "ident"
    ? firstParam.type.name
    : firstParam.type.kind === "call"
    ? firstParam.type.name
    : null;
  if (!typeName) return [];

  const knownConstructors = constructorsByType.get(typeName);
  if (!knownConstructors || knownConstructors.size === 0) return [];

  const casePatterns = new Set(prove.cases.map((c) => c.pattern));
  const missing = [...knownConstructors].filter((c) => !casePatterns.has(c));

  if (missing.length > 0) {
    return [
      `prove ${prove.name}: non-exhaustive pattern match on type ${typeName}\n` +
        `  missing: ${missing.join(", ")}`,
    ];
  }
  return [];
}

export function checkOverlap(prove: AST.ProveDecl): string[] {
  const errors: string[] = [];
  const refined = new Set<string>();
  for (const arm of prove.cases) {
    if (arm.bindings.some((b) => b.startsWith("_dp"))) refined.add(arm.pattern);
  }
  const seen = new Map<string, number>();
  for (let i = 0; i < prove.cases.length; i++) {
    const pat = prove.cases[i].pattern;
    if (refined.has(pat)) continue;
    const prev = seen.get(pat);
    if (prev !== undefined) {
      errors.push(
        `prove ${prove.name}: redundant case ${pat} (already covered by case ${prev + 1})`,
      );
    }
    seen.set(pat, i + 1);
  }
  return errors;
}
