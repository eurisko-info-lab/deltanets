// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Termination & Exhaustiveness Checking
// Structural recursion, productivity, measure termination, and
// pattern exhaustiveness/overlap checking.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { inductionParam } from "./types.ts";
import { exprEqual, exprToString, normalize, substitute, substituteAll } from "./normalize.ts";

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

/** Productivity checking for codata-returning proves.
 *  Dual of termination: every recursive call must appear under a guard
 *  constructor application (guarded corecursion). */
export function checkProductivity(
  prove: AST.ProveDecl,
  codataTypeName: string,
): string[] {
  const guardName = `guard_${codataTypeName.toLowerCase()}`;
  const errors: string[] = [];
  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue;
    const unguarded = collectUnguardedRecCalls(caseArm.body, prove.name, guardName);
    for (const call of unguarded) {
      errors.push(
        `prove ${prove.name}, case ${caseArm.pattern}: corecursive call ` +
        `${prove.name}(${call.kind === "call" ? call.args.map(exprToString).join(", ") : ""}) ` +
        `is not productive — must appear under ${guardName}(...)`,
      );
    }
  }
  return errors;
}

function collectUnguardedRecCalls(
  expr: AST.ProveExpr,
  funcName: string,
  guardName: string,
): AST.ProveExpr[] {
  const calls: AST.ProveExpr[] = [];
  function walk(e: AST.ProveExpr, guarded: boolean) {
    if (e.kind === "call" && e.name === funcName && !guarded) {
      calls.push(e);
    }
    if (e.kind === "call") {
      const isGuard = e.name === guardName;
      for (const a of e.args) walk(a, isGuard);
    }
    if (e.kind === "let") {
      walk(e.value, false);
      walk(e.body, false);
    }
    if (e.kind === "pi" || e.kind === "sigma") {
      walk(e.domain, false);
      walk(e.codomain, false);
    }
    if (e.kind === "lambda") {
      walk(e.paramType, false);
      walk(e.body, false);
    }
    if (e.kind === "match") {
      for (const c of e.cases) walk(c.body, false);
    }
  }
  walk(expr, false);
  return calls;
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
