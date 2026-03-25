// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Dependent Type Checker for prove blocks
//
// Verifies that each case arm in a typed `prove` block produces
// a proof term whose type matches the declared proposition.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { inductionParam, auxParams } from "./types.ts";
import {
  ident, app, substitute, substituteAll, exprEqual, exprToString,
  normalize, withNormTable, buildNormTable, convertible, checkConvertible,
  substituteExprPattern, getActiveCanonicals, substituteComputeResult,
  BUILTIN_NORM_RULES, type ProvedContext, type ComputeRule,
  type ConstructorTyping, type ConversionResult,
} from "./normalize.ts";
import {
  checkTermination, checkProductivity, checkMeasureTermination,
  checkExhaustiveness, checkOverlap,
} from "./termination.ts";

// Re-exports for backward compatibility
export type { ProvedContext, ComputeRule, ConstructorTyping, ConversionResult } from "./normalize.ts";
export { exprEqual, convertible, checkConvertible, normalize, withNormTable, exprToString } from "./normalize.ts";
export { convertibleInSort } from "./normalize.ts";

// ─── Proof tree types ──────────────────────────────────────────────

/** A node in a natural-deduction proof derivation tree. */
export type ProofNode = {
  rule: string;        // inference rule: "refl", "cong_succ", "sym", "trans", "recursive", lemma name
  term: string;        // the proof term at this node
  conclusion: string;  // the derived type (Eq(..., ...))
  children: ProofNode[];
  isGoal?: boolean;    // true when this node is an unfilled ? hole
  suggestions?: string[]; // auto-fill candidates that would satisfy the goal
};

/** Proof derivation tree for one prove block. */
export type ProofTree = {
  name: string;          // prove block name
  proposition: string;   // declared proposition
  cases: { pattern: string; bindings: string[]; tree: ProofNode }[];
  hasHoles: boolean;     // true if any case contains a ? hole
};

// ─── ProveExpr helpers ─────────────────────────────────────────────

/** Build the return type for a constructor, using index annotations when present.
 *  Non-indexed: Nat. Indexed: Vec(A, Zero) for VNil. */
function constructorReturnType(
  info: { typeName: string; params: string[]; indices: AST.DataIndex[]; returnIndices?: AST.ProveExpr[] },
): AST.ProveExpr {
  if (info.returnIndices && info.returnIndices.length > 0) {
    const paramArgs = info.params.map(ident);
    return app(info.typeName, ...paramArgs, ...info.returnIndices);
  }
  if (info.params.length > 0) {
    return app(info.typeName, ...info.params.map(ident));
  }
  return ident(info.typeName);
}

// ─── Unification engine ────────────────────────────────────────────

/** Mutable map from metavar id → solved ProveExpr. */
export type UnifCtx = Map<number, AST.ProveExpr>;

let _metaCounter = 0;
/** Create a fresh metavariable. */
export function freshMeta(): AST.ProveExpr {
  return { kind: "metavar", id: _metaCounter++ };
}

/** Walk an expression, replacing solved metavars with their solutions. */
export function zonk(expr: AST.ProveExpr, ctx: UnifCtx): AST.ProveExpr {
  if (expr.kind === "metavar") {
    const sol = ctx.get(expr.id);
    if (sol) return zonk(sol, ctx);
    return expr;
  }
  if (expr.kind === "meta-app") {
    const sol = ctx.get(expr.id);
    if (sol) {
      // Apply solution to arguments: if sol is a lambda, beta-reduce
      let result = zonk(sol, ctx);
      for (const arg of expr.args) {
        const zArg = zonk(arg, ctx);
        if (result.kind === "lambda") {
          result = zonk(substitute(result.body, result.param, zArg), ctx);
        } else if (result.kind === "ident") {
          // Solution is a name — reconstruct as a call
          result = { kind: "call", name: result.name, args: expr.args.map(a => zonk(a, ctx)) };
          break;
        } else if (result.kind === "call") {
          // Solution is already a call — append args
          result = { kind: "call", name: result.name, args: [...result.args, ...expr.args.map(a => zonk(a, ctx))] };
          break;
        } else {
          return { kind: "meta-app", id: expr.id, args: expr.args.map(a => zonk(a, ctx)) };
        }
      }
      return result;
    }
    return { kind: "meta-app", id: expr.id, args: expr.args.map(a => zonk(a, ctx)) };
  }
  if (expr.kind === "hole" || expr.kind === "ident") return expr;
  if (expr.kind === "call") {
    const args = expr.args.map((a) => zonk(a, ctx));
    return { kind: "call", name: expr.name, args };
  }
  if (expr.kind === "let") {
    return { kind: "let", name: expr.name, value: zonk(expr.value, ctx), body: zonk(expr.body, ctx) };
  }
  if (expr.kind === "pi") {
    return { kind: "pi", param: expr.param, domain: zonk(expr.domain, ctx), codomain: zonk(expr.codomain, ctx) };
  }
  if (expr.kind === "sigma") {
    return { kind: "sigma", param: expr.param, domain: zonk(expr.domain, ctx), codomain: zonk(expr.codomain, ctx) };
  }
  if (expr.kind === "lambda") {
    return { kind: "lambda", param: expr.param, paramType: zonk(expr.paramType, ctx), body: zonk(expr.body, ctx) };
  }
  if (expr.kind === "match") {
    return { kind: "match", scrutinee: expr.scrutinee, cases: expr.cases.map((c) => ({ ...c, body: zonk(c.body, ctx) })) };
  }
  return expr;
}

/** Returns true if metavar `id` occurs anywhere in `expr`. */
function occursIn(id: number, expr: AST.ProveExpr, ctx: UnifCtx): boolean {
  if (expr.kind === "metavar") {
    if (expr.id === id) return true;
    const sol = ctx.get(expr.id);
    return sol ? occursIn(id, sol, ctx) : false;
  }
  if (expr.kind === "meta-app") {
    if (expr.id === id) return true;
    const sol = ctx.get(expr.id);
    if (sol) return occursIn(id, sol, ctx) || expr.args.some(a => occursIn(id, a, ctx));
    return expr.args.some(a => occursIn(id, a, ctx));
  }
  if (expr.kind === "ident" || expr.kind === "hole") return false;
  if (expr.kind === "call") return expr.args.some((a) => occursIn(id, a, ctx));
  if (expr.kind === "let") return occursIn(id, expr.value, ctx) || occursIn(id, expr.body, ctx);
  if (expr.kind === "pi" || expr.kind === "sigma") return occursIn(id, expr.domain, ctx) || occursIn(id, expr.codomain, ctx);
  if (expr.kind === "lambda") return occursIn(id, expr.paramType, ctx) || occursIn(id, expr.body, ctx);
  if (expr.kind === "match") return expr.cases.some((c) => occursIn(id, c.body, ctx));
  return false;
}

/**
 * First-order unification. Tries to make `a` and `b` equal by assigning
 * metavariables in `ctx`. Returns true on success.
 *
 * Both sides are normalized before comparison. Metavars are resolved
 * eagerly (follow chains via ctx).
 */
export function unify(a: AST.ProveExpr, b: AST.ProveExpr, ctx: UnifCtx): boolean {
  a = zonk(normalize(a), ctx);
  b = zonk(normalize(b), ctx);

  // Identical metavars
  if (a.kind === "metavar" && b.kind === "metavar" && a.id === b.id) return true;

  // Flex-rigid / flex-flex: assign metavar
  if (a.kind === "metavar") {
    if (occursIn(a.id, b, ctx)) return false; // occurs check
    ctx.set(a.id, b);
    return true;
  }
  if (b.kind === "metavar") {
    if (occursIn(b.id, a, ctx)) return false;
    ctx.set(b.id, a);
    return true;
  }

  // ── Higher-order pattern unification ──
  // meta-app(id, [x1,...,xn]) vs term: solve ?id = λx1...λxn. term
  // when all xi are distinct bound variables (Miller's pattern fragment).
  if (a.kind === "meta-app" && b.kind === "meta-app" && a.id === b.id) {
    // Same metavar applied to same number of args → unify args
    if (a.args.length === b.args.length) {
      return a.args.every((arg, i) => unify(arg, b.args[i], ctx));
    }
    return false;
  }
  if (a.kind === "meta-app") {
    return solvePattern(a.id, a.args, b, ctx);
  }
  if (b.kind === "meta-app") {
    return solvePattern(b.id, b.args, a, ctx);
  }

  // Holes never unify
  if (a.kind === "hole" || b.kind === "hole") return false;

  // Idents
  if (a.kind === "ident" && b.kind === "ident") return a.name === b.name;

  // Calls
  if (a.kind === "call" && b.kind === "call") {
    if (a.name === b.name && a.args.length === b.args.length) {
      return a.args.every((arg, i) => unify(arg, b.args[i], ctx));
    }
    // Canonical structure resolution: proj(?M) vs concrete
    if (resolveCanonical(a, b, ctx)) return true;
    if (resolveCanonical(b, a, ctx)) return true;
    return false;
  }

  // Canonical structure: call(proj, [metavar]) vs ident
  if (a.kind === "call" && b.kind === "ident") {
    if (resolveCanonical(a, b, ctx)) return true;
  }
  if (b.kind === "call" && a.kind === "ident") {
    if (resolveCanonical(b, a, ctx)) return true;
  }

  // Pi
  if (a.kind === "pi" && b.kind === "pi") {
    if (!unify(a.domain, b.domain, ctx)) return false;
    return unify(substitute(a.codomain, a.param, ident(b.param)), b.codomain, ctx);
  }

  // Sigma
  if (a.kind === "sigma" && b.kind === "sigma") {
    if (!unify(a.domain, b.domain, ctx)) return false;
    return unify(substitute(a.codomain, a.param, ident(b.param)), b.codomain, ctx);
  }

  // Lambda
  if (a.kind === "lambda" && b.kind === "lambda") {
    if (!unify(a.paramType, b.paramType, ctx)) return false;
    return unify(substitute(a.body, a.param, ident(b.param)), b.body, ctx);
  }

  return false;
}

/**
 * Miller's pattern fragment solver.
 * Given ?M(x1,...,xn) = body, where all xi are distinct ident variables,
 * solve ?M = λx1...λxn. body (after occurs check).
 * If the args are not all distinct idents, fall back to first-order:
 * treat the meta-app as a plain metavar assignment when args is empty.
 */
function solvePattern(
  id: number,
  args: AST.ProveExpr[],
  body: AST.ProveExpr,
  ctx: UnifCtx,
): boolean {
  // Check pattern condition: all args must be distinct ident variables
  const names: string[] = [];
  for (const arg of args) {
    const za = zonk(arg, ctx);
    if (za.kind !== "ident") {
      // Not a pattern — can't solve
      return false;
    }
    if (names.includes(za.name)) {
      // Non-linear pattern — can't solve
      return false;
    }
    names.push(za.name);
  }

  // Occurs check
  if (occursIn(id, body, ctx)) return false;

  // Build solution: λx1. λx2. ... λxn. body
  // We use a dummy type (hole) for param types — they are not needed for unification.
  let solution: AST.ProveExpr = body;
  for (let i = names.length - 1; i >= 0; i--) {
    solution = { kind: "lambda", param: names[i], paramType: { kind: "hole" }, body: solution };
  }

  ctx.set(id, solution);
  return true;
}

/**
 * Canonical structure resolution.
 * When `projSide` is `call(proj, [..., metavar, ...])` and `valueSide` is a
 * concrete expression, search canonical structures for proj→value mapping.
 * If found, assign the metavar to the canonical instance and re-unify.
 */
function resolveCanonical(
  projSide: AST.ProveExpr,
  valueSide: AST.ProveExpr,
  ctx: UnifCtx,
): boolean {
  if (getActiveCanonicals().length === 0) return false;
  if (projSide.kind !== "call") return false;
  const projName = projSide.name;
  // Look for a metavar among the args
  const metaIdx = projSide.args.findIndex(
    (a) => zonk(a, ctx).kind === "metavar",
  );
  if (metaIdx < 0) return false;
  const meta = zonk(projSide.args[metaIdx], ctx);
  if (meta.kind !== "metavar") return false;

  // Get the concrete value string for matching
  const valueStr = valueSide.kind === "ident"
    ? valueSide.name
    : valueSide.kind === "call"
    ? valueSide.name
    : null;
  if (!valueStr) return false;

  // Search canonical structures for a match: proj → value
  for (const cs of getActiveCanonicals()) {
    const csValue = cs.projections.get(projName);
    if (csValue === valueStr) {
      // Found: assign the metavar to the canonical instance name
      if (occursIn(meta.id, ident(cs.name), ctx)) continue;
      ctx.set(meta.id, ident(cs.name));
      // Re-unify (substitution resolves the metavar now)
      const resolved = zonk(projSide, ctx);
      return unify(resolved, valueSide, ctx);
    }
  }
  return false;
}

/**
 * Resolve a call to a prove/lemma with implicit parameters.
 *
 * Strategy:
 * 1. Fresh metavars for each implicit param
 * 2. Map explicit params → provided args
 * 3. For each explicit param with a type annotation, unify the param type
 *    (with metavar bindings) against the type of the corresponding arg
 *    (looked up from caseBindings / constructorTyping)
 * 4. Zonk metavars out of the substituted return type
 */
function resolveImplicitCall(
  params: AST.ProveParam[],
  returnType: AST.ProveExpr,
  args: AST.ProveExpr[],
  ctx: ProveCtx,
): { type: AST.ProveExpr; unifCtx: UnifCtx } {
  const bindings = new Map<string, AST.ProveExpr>();
  const unifCtx: UnifCtx = new Map();

  // Phase 1: assign bindings — metavars for implicits, args for explicits
  let argIdx = 0;
  for (const p of params) {
    if (p.implicit) {
      bindings.set(p.name, freshMeta());
    } else if (argIdx < args.length) {
      bindings.set(p.name, args[argIdx++]);
    }
  }

  // Phase 2: unify explicit param types against actual arg types to solve metavars
  argIdx = 0;
  for (const p of params) {
    if (p.implicit) continue;
    if (argIdx >= args.length) break;
    const arg = args[argIdx++];
    if (p.type) {
      // Expected type of this param (with metavar bindings)
      const expectedType = substituteAll(p.type, bindings);
      // Infer actual type of the argument
      const argResult = inferType(arg, ctx);
      if (argResult.ok) {
        unify(expectedType, argResult.type, unifCtx);
      }
    }
  }

  // Phase 3: substitute all bindings into return type, then zonk
  const rawType = substituteAll(returnType, bindings);
  return { type: rawType, unifCtx };
}

// ─── Universe levels ───────────────────────────────────────────────
// Cumulative universe hierarchy: Type₀ : Type₁ : Type₂ : …

/** Parse universe level from a type expression.
 *  Returns the level (≥ 0) if the expression is a universe Type(n), or -1 otherwise.
 *  Prop returns -2, SProp returns -3 (they're sorts but not Type(n)). */
export function universeLevel(type: AST.ProveExpr): number {
  const n = normalize(type);
  if (n.kind === "ident" && n.name === "SProp") return -3;
  if (n.kind === "ident" && n.name === "Prop") return -2;
  if (n.kind === "call" && n.name === "Type" && n.args.length === 1 &&
      n.args[0].kind === "ident" && /^\d+$/.test(n.args[0].name)) {
    return parseInt(n.args[0].name);
  }
  return -1;
}

/** Is this expression the sort Prop? */
export function isPropSort(type: AST.ProveExpr): boolean {
  const n = normalize(type);
  return n.kind === "ident" && n.name === "Prop";
}

/** Is this expression the sort SProp (strict propositions)? */
export function isSPropSort(type: AST.ProveExpr): boolean {
  const n = normalize(type);
  return n.kind === "ident" && n.name === "SProp";
}

/** Compute which universe level a type expression inhabits.
 *  Type₀ → 1, Type₁ → 2, Prop → 0, SProp → 0, Nat → 0, Eq(a,b) → 0, Sigma → max of components. */
export function typeUniverse(type: AST.ProveExpr): number {
  const uLevel = universeLevel(type);
  if (uLevel === -2 || uLevel === -3) return 0; // Prop : Type₀, SProp : Type₀
  if (uLevel >= 0) return uLevel + 1;
  const n = normalize(type);
  if (n.kind === "ident") return 0;
  if (n.kind === "pi" || n.kind === "sigma") {
    return Math.max(typeUniverse(n.domain), typeUniverse(n.codomain));
  }
  if (n.kind === "lambda") {
    return Math.max(typeUniverse(n.paramType), typeUniverse(n.body));
  }
  if (n.kind === "call") {
    if (n.name === "Eq") return 0;
    if (n.name === "Sigma" && n.args.length >= 3) {
      return Math.max(typeUniverse(n.args[0]), typeUniverse(n.args[2]));
    }
    if (n.name === "W" && n.args.length >= 2) {
      return Math.max(typeUniverse(n.args[0]), typeUniverse(n.args[1]));
    }
  }
  return 0;
}

/** Cumulative subtype check: `sub` is a subtype of `sup`.
 *  SProp ≤ SProp, SProp ≤ Prop, SProp ≤ Type(n).
 *  Prop ≤ Prop, Prop ≤ Type(n).
 *  Type(n) is NOT ≤ Prop or SProp.
 *  Type(i) ≤ Type(j) when i ≤ j. */
export function typeSubsumes(
  sub: AST.ProveExpr,
  sup: AST.ProveExpr,
): boolean {
  const a = normalize(sub);
  const b = normalize(sup);
  const aIsSProp = isSPropSort(a);
  const bIsSProp = isSPropSort(b);
  const aIsProp = isPropSort(a);
  const bIsProp = isPropSort(b);
  // SProp ≤ SProp
  if (aIsSProp && bIsSProp) return true;
  // SProp ≤ Prop
  if (aIsSProp && bIsProp) return true;
  // SProp ≤ Type(n) for any n
  if (aIsSProp && universeLevel(b) >= 0) return true;
  // Nothing above SProp subsumes SProp (Type, Prop NOT ≤ SProp)
  if (bIsSProp) return false;
  // Prop ≤ Prop
  if (aIsProp && bIsProp) return true;
  // Prop ≤ Type(n) for any n
  if (aIsProp && universeLevel(b) >= 0) return true;
  // Type(n) is NOT ≤ Prop
  if (bIsProp) return false;
  // Universe cumulativity: Type(i) ≤ Type(j) when i ≤ j
  const aLevel = universeLevel(a);
  const bLevel = universeLevel(b);
  if (aLevel >= 0 && bLevel >= 0) return aLevel <= bLevel;
  return exprEqual(a, b);
}

/** Determine the sort of a type expression.
 *  Returns "Prop" if the type lives in Prop, "SProp" if in SProp, or the universe level (number) for Set/Type.
 *  dataSorts maps type names to their declared sort ("Prop", "Set", or "SProp"). */
export function sortOf(
  type: AST.ProveExpr,
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">,
): "Prop" | "SProp" | number {
  const n = normalize(type);
  // Eq is always in Prop
  if (n.kind === "call" && n.name === "Eq") return "Prop";
  // User-declared data sort
  if (n.kind === "ident" && dataSorts?.has(n.name)) {
    const s = dataSorts.get(n.name)!;
    return s === "Prop" ? "Prop" : s === "SProp" ? "SProp" : 0;
  }
  if (n.kind === "call" && dataSorts?.has(n.name)) {
    const s = dataSorts.get(n.name)!;
    return s === "Prop" ? "Prop" : s === "SProp" ? "SProp" : 0;
  }
  // Impredicativity: Pi with Prop/SProp codomain stays in that sort
  if (n.kind === "pi") {
    const codSort = sortOf(n.codomain, dataSorts);
    if (codSort === "Prop") return "Prop";
    if (codSort === "SProp") return "SProp";
  }
  // Sort literals
  if (isSPropSort(n)) return "SProp";
  if (isPropSort(n)) return "Prop";
  return typeUniverse(type);
}

// Extract the top-level type constructor name from a ProveExpr.
function topTypeName(e: AST.ProveExpr): string | undefined {
  if (e.kind === "ident") return e.name;
  if (e.kind === "call") return e.name;
  return undefined;
}

// ─── Type inference ────────────────────────────────────────────────
// Infers the Eq-type of a proof expression given the prove context.

type ProveCtx = {
  prove: AST.ProveDecl;
  caseBindings: Map<string, AST.ProveExpr>; // binding name → type var
  bindingTypes: Map<string, string>; // binding name → type name (for scrutinee resolution)
  provedCtx: ProvedContext; // previously proved propositions
  constructorTyping: ConstructorTyping; // constructor → type info from data decls
  constructorsByType?: Map<string, Set<string>>; // type name → constructor names
  setoids?: Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>; // relation → setoid def
  hints?: Map<string, Set<string>>; // hint databases: db name → lemma names
  instances?: import("./evaluator.ts").InstanceDef[]; // typeclass instances
  canonicals?: import("./evaluator.ts").CanonicalDef[]; // canonical structures
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">; // type name → declared sort
};

type TypeResult =
  | { ok: true; type: AST.ProveExpr } // the Eq(..., ...) type
  | { ok: false; error: string };

function inferType(
  expr: AST.ProveExpr,
  ctx: ProveCtx,
): TypeResult {
  // Hole → can't infer, needs goal from context
  if (expr.kind === "hole") {
    return { ok: false, error: "hole" };
  }

  // Metavar → internal unification variable, shouldn't appear in user proofs
  if (expr.kind === "metavar") {
    return { ok: false, error: `unsolved metavariable ?${expr.id}` };
  }

  // Let → infer type of body with binding in scope
  if (expr.kind === "let") {
    const valResult = inferType(expr.value, ctx);
    if (!valResult.ok) return valResult;
    const innerBindings = new Map(ctx.caseBindings);
    innerBindings.set(expr.name, valResult.type);
    const innerCtx: ProveCtx = { ...ctx, caseBindings: innerBindings };
    return inferType(expr.body, innerCtx);
  }

  // Pi type → its type is a universe. Impredicative: if codomain is Prop/SProp, result is Prop/SProp.
  if (expr.kind === "pi") {
    const codSort = sortOf(expr.codomain, ctx.dataSorts);
    if (codSort === "SProp") return { ok: true, type: ident("SProp") };
    if (codSort === "Prop") return { ok: true, type: ident("Prop") };
    const domULevel = typeUniverse(expr.domain);
    const codULevel = typeUniverse(expr.codomain);
    return { ok: true, type: app("Type", ident(String(Math.max(domULevel, codULevel)))) };
  }

  // Sigma type → its type is a universe (max of domain and codomain universes)
  if (expr.kind === "sigma") {
    const domULevel = typeUniverse(expr.domain);
    const codULevel = typeUniverse(expr.codomain);
    return { ok: true, type: app("Type", ident(String(Math.max(domULevel, codULevel)))) };
  }

  // Lambda → infer Pi type: fun(x : A, body) : forall(x : A, typeof body)
  if (expr.kind === "lambda") {
    const innerBindings = new Map(ctx.caseBindings);
    innerBindings.set(expr.param, expr.paramType);
    const innerCtx: ProveCtx = { ...ctx, caseBindings: innerBindings };
    const bodyResult = inferType(expr.body, innerCtx);
    if (!bodyResult.ok) return bodyResult;
    return { ok: true, type: { kind: "pi", param: expr.param, domain: expr.paramType, codomain: bodyResult.type } };
  }

  // Match → infer type by checking each case arm; return first arm's type.
  if (expr.kind === "match") {
    let resultType: AST.ProveExpr | null = null;
    for (const c of expr.cases) {
      const { bindings: newBindings, types: newTypes } = buildTypedBindings(c, ctx.constructorTyping);
      for (const [k, v] of ctx.caseBindings) {
        if (!newBindings.has(k)) newBindings.set(k, v);
      }
      const mergedTypes = new Map(ctx.bindingTypes);
      for (const [k, v] of newTypes) mergedTypes.set(k, v);
      const innerCtx: ProveCtx = { ...ctx, caseBindings: newBindings, bindingTypes: mergedTypes };
      const inner = inferType(c.body, innerCtx);
      if (!inner.ok) return inner;
      if (!resultType) resultType = inner.type;
    }
    return resultType ? { ok: true, type: resultType } : { ok: false, error: "match: no cases" };
  }

  // refl → Eq(a, a) where 'a' is determined from context
  if (expr.kind === "ident" && expr.name === "refl") {
    return { ok: true, type: app("Eq", ident("_refl_a"), ident("_refl_a")) };
  }

  if (expr.kind === "ident") {
    if (expr.name === "assumption") {
      return { ok: false, error: "assumption: no matching hypothesis found in context" };
    }
    // conv — proves goal by definitional equality (normalization)
    if (expr.name === "conv") {
      return { ok: true, type: ident("conv") };
    }
    // simp — automated simplification (resolved before type-checking)
    if (expr.name === "simp") {
      return { ok: false, error: "simp: could not resolve — no proof found" };
    }
    // decide — ground term computation (resolved before type-checking)
    if (expr.name === "decide") {
      return { ok: false, error: "decide: could not resolve — terms may not be ground" };
    }
    // omega — linear arithmetic (resolved before type-checking)
    if (expr.name === "omega") {
      return { ok: false, error: "omega: could not resolve — not a linear arithmetic goal" };
    }
    // auto — depth-bounded proof search (resolved before type-checking)
    if (expr.name === "auto") {
      return { ok: false, error: "auto: could not resolve — no proof found" };
    }
    // ring — commutative ring normalization (checked directly in typecheckProve)
    if (expr.name === "ring") {
      return { ok: true, type: ident("ring") };
    }
    // Nullary constructor: infer type from data declaration
    const ctorInfo = ctx.constructorTyping.get(expr.name);
    if (ctorInfo) {
      return { ok: true, type: constructorReturnType(ctorInfo) };
    }
    // Let-bound or case-bound variable: look up type from caseBindings
    if (ctx.caseBindings.has(expr.name)) {
      return { ok: true, type: ctx.caseBindings.get(expr.name)! };
    }
    return { ok: false, error: `unexpected identifier '${expr.name}' in proof position` };
  }

  // call expressions
  const { name, args } = expr;

  // quote(expr) → Term (quoted representation of the expression)
  if (name === "quote" && args.length === 1) {
    return { ok: true, type: ident("Term") };
  }

  // unquote(term) → extracts the proof term represented by a quoted Term
  // At compile time, unquote requires the argument to be a literal quote(...)
  if (name === "unquote" && args.length === 1) {
    const inner = args[0];
    if (inner.kind === "call" && inner.name === "quote" && inner.args.length === 1) {
      // unquote(quote(e)) = e — roundtrip
      return inferType(inner.args[0], ctx);
    }
    return { ok: false, error: "unquote: argument must be a quote(...) expression at compile time" };
  }

  // Generalized congruence: cong_X(proof, c1, ..., cn) where X is a constructor.
  // The proof applies to the LAST position; c1..cn are constants for earlier positions.
  //   cong_succ(p)       : R(Succ(a), Succ(b))       when p : R(a, b) (R = Eq or setoid)
  //   cong_cons(p, h)    : R(Cons(h, a), Cons(h, b)) when p : R(a, b)
  if (name.startsWith("cong_") && args.length >= 1) {
    const suffix = name.slice(5);
    const constructorName = suffix.charAt(0).toUpperCase() + suffix.slice(1);
    const inner = inferType(args[0], ctx);
    if (!inner.ok) return inner;
    const equiv = extractEquiv(inner.type);
    if (!equiv || !isEquivRelation(equiv.rel, ctx.setoids)) {
      return { ok: false, error: `${name} first argument must have Eq or setoid type, got ${exprToString(inner.type)}` };
    }
    const constants = args.slice(1);
    return {
      ok: true,
      type: app(equiv.rel, app(constructorName, ...constants, equiv.left), app(constructorName, ...constants, equiv.right)),
    };
  }

  // sym(p) : R(b, a) when p : R(a, b) — works for Eq or any registered setoid
  if (name === "sym" && args.length === 1) {
    const inner = inferType(args[0], ctx);
    if (!inner.ok) return inner;
    const equiv = extractEquiv(inner.type);
    if (!equiv || !isEquivRelation(equiv.rel, ctx.setoids)) {
      return { ok: false, error: `sym argument must have Eq or setoid type, got ${exprToString(inner.type)}` };
    }
    return { ok: true, type: app(equiv.rel, equiv.right, equiv.left) };
  }

  // trans(p, q) : R(a, c) when p : R(a, b), q : R(b, c) — works for Eq or any registered setoid
  if (name === "trans" && args.length === 2) {
    const t1 = inferType(args[0], ctx);
    if (!t1.ok) return t1;
    const t2 = inferType(args[1], ctx);
    if (!t2.ok) return t2;
    const eq1 = extractEquiv(t1.type);
    const eq2 = extractEquiv(t2.type);
    if (!eq1 || !eq2 || !isEquivRelation(eq1.rel, ctx.setoids) || !isEquivRelation(eq2.rel, ctx.setoids)) {
      return { ok: false, error: `trans arguments must have Eq or setoid types` };
    }
    if (eq1.rel !== eq2.rel) {
      return { ok: false, error: `trans: relation mismatch: '${eq1.rel}' vs '${eq2.rel}'` };
    }
    // Check middle types match (after normalization)
    if (!convertible(eq1.right, eq2.left)) {
      return {
        ok: false,
        error: `trans: middle types don't match: ${exprToString(normalize(eq1.right))} vs ${exprToString(normalize(eq2.left))}`,
      };
    }
    return { ok: true, type: app(eq1.rel, eq1.left, eq2.right) };
  }

  // pair(witness, proof) : Sigma(witness, proofType) — ∃-introduction
  if (name === "pair" && args.length === 2) {
    const proofResult = inferType(args[1], ctx);
    if (!proofResult.ok) return proofResult;
    return { ok: true, type: app("Sigma", args[0], proofResult.type) };
  }

  // fst(p) : A  when p : Sigma(A, x, P) or Sigma(witness, proofType) — ∃-elim (first)
  if (name === "fst" && args.length === 1) {
    const inner = inferType(args[0], ctx);
    if (!inner.ok) return inner;
    const n = normalize(inner.type);
    const sigma3 = extractSigma(n);
    if (sigma3) return { ok: true, type: sigma3.domain };
    // 2-arg Sigma from pair inference: Sigma(witness, proofType) → witness
    if (n.kind === "call" && n.name === "Sigma" && n.args.length === 2) {
      return { ok: true, type: n.args[0] };
    }
    return { ok: false, error: `fst argument must have Sigma type, got ${exprToString(inner.type)}` };
  }

  // snd(p) : P[x := fst(p)]  when p : Sigma(A, x, P) — ∃-elim (second)
  if (name === "snd" && args.length === 1) {
    const inner = inferType(args[0], ctx);
    if (!inner.ok) return inner;
    const n = normalize(inner.type);
    const sigma3 = extractSigma(n);
    if (sigma3) {
      return { ok: true, type: normalize(substitute(sigma3.predicate, sigma3.boundVar, app("fst", args[0]))) };
    }
    // 2-arg Sigma from pair inference: Sigma(witness, proofType) → proofType
    if (n.kind === "call" && n.name === "Sigma" && n.args.length === 2) {
      return { ok: true, type: n.args[1] };
    }
    return { ok: false, error: `snd argument must have Sigma type, got ${exprToString(inner.type)}` };
  }

  // subst(p, e) : T[a := b]  where p : R(a, b) and R is Eq or a setoid
  // Transport / J elimination: rewrites the type of e through equality/equivalence p.
  if (name === "subst" && args.length === 2) {
    const pResult = inferType(args[0], ctx);
    if (!pResult.ok) return pResult;
    const equiv = extractEquiv(normalize(pResult.type));
    if (!equiv || !isEquivRelation(equiv.rel, ctx.setoids)) {
      return { ok: false, error: `subst first argument must have Eq or setoid type, got ${exprToString(pResult.type)}` };
    }
    const eResult = inferType(args[1], ctx);
    if (!eResult.ok) return eResult;
    const a = normalize(equiv.left);
    const b = normalize(equiv.right);
    return { ok: true, type: normalize(substituteExprPattern(normalize(eResult.type), a, b)) };
  }

  // Recursive call to a prove-declared agent
  if (name === ctx.prove.name) {
    if (!ctx.prove.returnType) {
      return { ok: false, error: `recursive call to ${name} but no return type declared` };
    }
    const { type, unifCtx } = resolveImplicitCall(ctx.prove.params, ctx.prove.returnType, args, ctx);
    return { ok: true, type: normalize(zonk(type, unifCtx)) };
  }

  // ── Tactic combinators ──

  // exact(e) — transparent wrapper
  if (name === "exact" && args.length === 1) {
    return inferType(args[0], ctx);
  }

  // apply(f, a1, a2, ...) → infer f(a1, a2, ...)
  if (name === "apply" && args.length >= 1 && args[0].kind === "ident") {
    return inferType(app(args[0].name, ...args.slice(1)), ctx);
  }

  // rewrite(proof) — returns proof's type; typecheckProve validates contextually
  if (name === "rewrite" && args.length === 1) {
    return inferType(args[0], ctx);
  }

  // calc(step1, step2, ...) — chained transitivity: calc(p1, p2) = trans(p1, p2)
  if (name === "calc" && args.length >= 2) {
    let acc = args[0];
    for (let i = 1; i < args.length; i++) {
      acc = app("trans", acc, args[i]);
    }
    return inferType(acc, ctx);
  }

  // conv — proves goal by definitional equality (normalization)
  if (name === "conv" && args.length === 0) {
    return { ok: true, type: ident("conv") };
  }

  // Cross-lemma call: look up previously proved proposition
  const proved = ctx.provedCtx.get(name);
  if (proved) {
    const { type, unifCtx } = resolveImplicitCall(proved.params, proved.returnType, args, ctx);
    return { ok: true, type: normalize(zonk(type, unifCtx)) };
  }

  // Constructor application: infer type from data declaration
  // e.g., Succ(x) : Nat, Cons(h, t) : List, Zero : Nat (handled below for ident)
  const ctorInfo = ctx.constructorTyping.get(name);
  if (ctorInfo) {
    return { ok: true, type: constructorReturnType(ctorInfo) };
  }

  return { ok: false, error: `unknown proof combinator '${name}'` };
}

export function extractEq(
  type: AST.ProveExpr,
): { left: AST.ProveExpr; right: AST.ProveExpr } | null {
  if (type.kind === "call" && type.name === "Eq" && type.args.length === 2) {
    return { left: type.args[0], right: type.args[1] };
  }
  return null;
}

/** Extract any binary relation: R(a, b) → { rel: "R", left: a, right: b } */
function extractEquiv(
  type: AST.ProveExpr,
): { rel: string; left: AST.ProveExpr; right: AST.ProveExpr } | null {
  if (type.kind === "call" && type.args.length === 2) {
    return { rel: type.name, left: type.args[0], right: type.args[1] };
  }
  return null;
}

/** Check if a relation is Eq or a registered setoid */
function isEquivRelation(rel: string, setoids?: Map<string, unknown>): boolean {
  return rel === "Eq" || (setoids != null && setoids.has(rel));
}

// ─── Ring polynomial normalization ─────────────────────────────────
// Converts expressions over a commutative semiring (add, mul, zero, one)
// into canonical polynomial form (sorted sum of sorted monomials).
// Two expressions are ring-equal iff their polynomial forms are identical.

type RingInfo = { type: string; zero: string; one?: string; add: string; mul: string };

/** Canonical polynomial: Map from monomial-key → coefficient.
 *  Monomial key is sorted product of atom expression strings joined by "\0".
 *  Empty string represents the constant 1 (multiplicative unit). */
function exprToPolynomial(
  expr: AST.ProveExpr,
  ring: RingInfo,
): Map<string, number> {
  // Zero: empty polynomial (additive identity)
  if (expr.kind === "ident" && expr.name === ring.zero) {
    return new Map();
  }
  // One: constant monomial with coeff 1
  if (ring.one && expr.kind === "ident" && expr.name === ring.one) {
    return new Map([["", 1]]);
  }
  // Addition: merge polynomials
  if (expr.kind === "call" && expr.name === ring.add && expr.args.length === 2) {
    return addPolynomials(
      exprToPolynomial(expr.args[0], ring),
      exprToPolynomial(expr.args[1], ring),
    );
  }
  // Multiplication: distribute
  if (expr.kind === "call" && expr.name === ring.mul && expr.args.length === 2) {
    return mulPolynomials(
      exprToPolynomial(expr.args[0], ring),
      exprToPolynomial(expr.args[1], ring),
    );
  }
  // Atom: single monomial with the expression as the sole variable
  const atomKey = exprToString(expr);
  return new Map([[atomKey, 1]]);
}

function addPolynomials(a: Map<string, number>, b: Map<string, number>): Map<string, number> {
  const result = new Map(a);
  for (const [key, coeff] of b) {
    result.set(key, (result.get(key) ?? 0) + coeff);
  }
  // Remove zero-coefficient terms
  for (const [key, coeff] of result) {
    if (coeff === 0) result.delete(key);
  }
  return result;
}

function mulPolynomials(a: Map<string, number>, b: Map<string, number>): Map<string, number> {
  const result = new Map<string, number>();
  for (const [keyA, coeffA] of a) {
    for (const [keyB, coeffB] of b) {
      // Combine monomial keys by merging sorted atom lists
      const atomsA = keyA ? keyA.split("\0") : [];
      const atomsB = keyB ? keyB.split("\0") : [];
      const combined = [...atomsA, ...atomsB].sort().join("\0");
      result.set(combined, (result.get(combined) ?? 0) + coeffA * coeffB);
    }
  }
  for (const [key, coeff] of result) {
    if (coeff === 0) result.delete(key);
  }
  return result;
}

function polynomialEqual(a: Map<string, number>, b: Map<string, number>): boolean {
  if (a.size !== b.size) return false;
  for (const [key, coeff] of a) {
    if (b.get(key) !== coeff) return false;
  }
  return true;
}

/** Ring congruence: two expressions are ring-equal if their polynomial forms match,
 *  OR they have the same non-ring outermost constructor and all children are ring-equal. */
function ringCongruent(a: AST.ProveExpr, b: AST.ProveExpr, ring: RingInfo): boolean {
  // Try direct polynomial comparison first
  const pa = exprToPolynomial(a, ring);
  const pb = exprToPolynomial(b, ring);
  if (polynomialEqual(pa, pb)) return true;
  // Congruence: same constructor (not a ring op), same arity → recurse on children
  if (a.kind === "call" && b.kind === "call" && a.name === b.name &&
      a.name !== ring.add && a.name !== ring.mul &&
      a.args.length === b.args.length) {
    return a.args.every((ai, i) => ringCongruent(normalize(ai), normalize(b.args[i]), ring));
  }
  return false;
}

// Extract a declared Sigma type: Sigma(Domain, boundVar, Predicate)
function extractSigma(
  type: AST.ProveExpr,
): { domain: AST.ProveExpr; boundVar: string; predicate: AST.ProveExpr } | null {
  // First-class sigma kind: exists(x : A, B)
  if (type.kind === "sigma") {
    return { domain: type.domain, boundVar: type.param, predicate: type.codomain };
  }
  // Legacy call form: Sigma(A, x, P)
  if (
    type.kind === "call" && type.name === "Sigma" && type.args.length === 3 &&
    type.args[1].kind === "ident"
  ) {
    return {
      domain: type.args[0],
      boundVar: type.args[1].name,
      predicate: type.args[2],
    };
  }
  return null;
}

// Match an Eq type with refl handling: returns true when inferred matches required.
function eqTypeMatches(
  inferred: AST.ProveExpr,
  required: AST.ProveExpr,
): boolean {
  const infEq = extractEq(inferred);
  const reqEq = extractEq(required);
  if (!infEq || !reqEq) return false;
  // refl: Eq(_refl_a, _refl_a) — check required sides are equal
  if (
    infEq.left.kind === "ident" && infEq.left.name === "_refl_a" &&
    infEq.right.kind === "ident" && infEq.right.name === "_refl_a"
  ) {
    return convertible(reqEq.left, reqEq.right);
  }
  return convertible(infEq.left, reqEq.left) &&
    convertible(infEq.right, reqEq.right);
}

// ─── Proof search (auto-fill candidates) ──────────────────────────
// When a ? hole has a known expected type, try to find proof expressions
// that would satisfy the goal.  The search is bounded (depth ≤ 2).

function tryCandidateType(
  candidate: AST.ProveExpr,
  ctx: ProveCtx,
  goal: AST.ProveExpr,
): boolean {
  const result = inferType(candidate, ctx);
  return result.ok && eqTypeMatches(normalize(result.type), normalize(goal));
}

function searchCandidates(
  ctx: ProveCtx,
  goal: AST.ProveExpr,
): string[] {
  const goalEq = extractEq(normalize(goal));
  if (!goalEq) return [];

  const found: string[] = [];
  const seen = new Set<string>();
  const tryAdd = (expr: AST.ProveExpr) => {
    if (!tryCandidateType(expr, ctx, goal)) return;
    const s = exprToString(expr);
    if (!seen.has(s)) { seen.add(s); found.push(s); }
  };

  // 1. refl
  tryAdd(ident("refl"));

  // 2. IH calls
  const auxArgs = auxParams(ctx.prove.params).map((p) => ident(p.name));
  const allIHs = ctx.prove.returnType
    ? [...ctx.caseBindings.keys()].map((b) => app(ctx.prove.name, ident(b), ...auxArgs))
    : [];
  allIHs.forEach(tryAdd);

  // 3. Hint-DB lemmas (auto DB) — tried before general cross-lemma calls
  const availableVars = [
    ...[...ctx.caseBindings.keys()].map(ident),
    ...auxParams(ctx.prove.params).map((p) => ident(p.name)),
  ];
  const allLemmaCalls: AST.ProveExpr[] = [];
  const hintAutoNames = ctx.hints?.get("auto");
  if (hintAutoNames) {
    for (const lemmaName of hintAutoNames) {
      const lemma = ctx.provedCtx.get(lemmaName);
      if (!lemma) continue;
      if (lemma.params.length <= availableVars.length) {
        const call = app(lemmaName, ...availableVars.slice(0, lemma.params.length));
        allLemmaCalls.push(call);
        tryAdd(call);
      }
    }
  }

  // 4. Cross-lemma calls (remaining lemmas not already tried via hints)
  for (const [lemmaName, lemma] of ctx.provedCtx) {
    if (hintAutoNames?.has(lemmaName)) continue; // already tried above
    if (lemma.params.length <= availableVars.length) {
      const call = app(lemmaName, ...availableVars.slice(0, lemma.params.length));
      allLemmaCalls.push(call);
      tryAdd(call);
    }
  }

  // 5. sym wrappers
  for (const inner of [...allIHs, ...allLemmaCalls]) tryAdd(app("sym", inner));

  // 6. cong_X wrapping — if goal is Eq(X(...,a), X(...,b))
  if (goalEq.left.kind === "call" && goalEq.right.kind === "call" &&
      goalEq.left.name === goalEq.right.name &&
      goalEq.left.args.length === goalEq.right.args.length) {
    const suffix = goalEq.left.name.charAt(0).toLowerCase() + goalEq.left.name.slice(1);
    const congName = `cong_${suffix}`;
    const constants = goalEq.left.args.slice(0, -1);
    for (const inner of [ident("refl"), ...allIHs, ...allLemmaCalls]) {
      tryAdd(app(congName, inner, ...constants));
    }
    for (const inner of [...allIHs, ...allLemmaCalls]) {
      tryAdd(app(congName, app("sym", inner), ...constants));
    }
  }

  return found;
}

// ─── Proof tree builder ────────────────────────────────────────────
// Builds a ProofNode tree by walking the proof expression, mirroring inferType.
// The optional `expected` type enables goal-directed checking for ? holes.

function buildNode(
  expr: AST.ProveExpr,
  ctx: ProveCtx,
  expected?: AST.ProveExpr,
): ProofNode {
  // ? hole → show goal type from the expected type + search for candidates
  if (expr.kind === "hole") {
    const goalStr = expected ? exprToString(normalize(expected)) : "?";
    const suggestions = expected ? searchCandidates(ctx, expected) : [];
    return { rule: "goal", term: "?", conclusion: goalStr, children: [], isGoal: true, suggestions };
  }

  // metavar → leaf node (shouldn't appear in user-facing proofs)
  if (expr.kind === "metavar") {
    return { rule: "?", term: `?${expr.id}`, conclusion: "unsolved metavariable", children: [] };
  }

  // let → build sub-trees for value and body
  if (expr.kind === "let") {
    const valNode = buildNode(expr.value, ctx);
    const valResult = inferType(expr.value, ctx);
    const innerBindings = new Map(ctx.caseBindings);
    if (valResult.ok) innerBindings.set(expr.name, valResult.type);
    const innerCtx: ProveCtx = { ...ctx, caseBindings: innerBindings };
    const bodyNode = buildNode(expr.body, innerCtx, expected);
    const result = inferType(expr, ctx);
    const conclusion = result.ok ? exprToString(normalize(result.type)) : `✘ ${result.error}`;
    return { rule: "let", term: `let ${expr.name}`, conclusion, children: [valNode, bodyNode] };
  }

  // match → sub-trees for each case arm with per-arm expected type
  if (expr.kind === "match") {
    const children = expr.cases.map((c) => {
      const { bindings: newBindings, types: newTypes } = buildTypedBindings(c, ctx.constructorTyping);
      for (const [k, v] of ctx.caseBindings) {
        if (!newBindings.has(k)) newBindings.set(k, v);
      }
      const mergedTypes = new Map(ctx.bindingTypes);
      for (const [k, v] of newTypes) mergedTypes.set(k, v);
      const innerCtx: ProveCtx = { ...ctx, caseBindings: newBindings, bindingTypes: mergedTypes };
      let caseExpected = expected;
      if (expected) {
        const consExpr = c.bindings.length > 0
          ? app(c.pattern, ...c.bindings.map(ident))
          : ident(c.pattern);
        caseExpected = normalize(substitute(expected, expr.scrutinee, consExpr));
      }
      return buildNode(c.body, innerCtx, caseExpected);
    });
    const result = inferType(expr, ctx);
    const conclusion = result.ok ? exprToString(normalize(result.type)) : `✘ ${result.error}`;
    return { rule: "match", term: `match(${expr.scrutinee})`, conclusion, children };
  }

  const result = inferType(expr, ctx);
  const conclusion = result.ok
    ? exprToString(normalize(result.type))
    : `✘ ${result.error}`;
  const term = exprToString(expr);

  if (expr.kind === "ident" && expr.name === "refl") {
    return { rule: "refl", term, conclusion, children: [] };
  }
  if (expr.kind === "ident" && expr.name === "conv") {
    return { rule: "conv", term, conclusion, children: [] };
  }
  if (expr.kind === "ident" && expr.name === "simp") {
    return { rule: "simp", term, conclusion, children: [] };
  }
  if (expr.kind === "ident" && expr.name === "decide") {
    return { rule: "decide", term, conclusion, children: [] };
  }
  if (expr.kind === "ident" && expr.name === "omega") {
    return { rule: "omega", term, conclusion, children: [] };
  }
  if (expr.kind === "ident" && expr.name === "ring") {
    return { rule: "ring", term, conclusion, children: [] };
  }
  if (expr.kind === "ident" && expr.name === "auto") {
    return { rule: "auto", term, conclusion, children: [] };
  }
  if (expr.kind === "ident") {
    return { rule: "?", term, conclusion, children: [] };
  }

  if (expr.kind === "pi" || expr.kind === "sigma") {
    const domChild = buildNode(expr.domain, ctx, undefined);
    const codomChild = buildNode(expr.codomain, ctx, undefined);
    return { rule: expr.kind, term, conclusion, children: [domChild, codomChild] };
  }
  if (expr.kind === "lambda") {
    const bodyChild = buildNode(expr.body, ctx, undefined);
    return { rule: "lambda", term, conclusion, children: [bodyChild] };
  }

  const { name, args } = expr;

  // Goal-directed: propagate expected types into sub-expressions
  if (name.startsWith("cong_") && args.length >= 1) {
    // If expected is Eq(X(...,a), X(...,b)), inner goal is Eq(a, b)
    let innerExpected: AST.ProveExpr | undefined;
    if (expected) {
      const eq = extractEq(normalize(expected));
      if (eq) {
        const suffix = name.slice(5);
        const cons = suffix.charAt(0).toUpperCase() + suffix.slice(1);
        if (eq.left.kind === "call" && eq.left.name === cons &&
            eq.right.kind === "call" && eq.right.name === cons) {
          const last1 = eq.left.args[eq.left.args.length - 1];
          const last2 = eq.right.args[eq.right.args.length - 1];
          innerExpected = app("Eq", last1, last2);
        }
      }
    }
    return { rule: name, term, conclusion, children: [buildNode(args[0], ctx, innerExpected)] };
  }
  if (name === "sym" && args.length === 1) {
    // If expected is Eq(a, b), inner goal is Eq(b, a)
    let innerExpected: AST.ProveExpr | undefined;
    if (expected) {
      const eq = extractEq(normalize(expected));
      if (eq) innerExpected = app("Eq", eq.right, eq.left);
    }
    return { rule: "sym", term, conclusion, children: [buildNode(args[0], ctx, innerExpected)] };
  }
  if (name === "trans" && args.length === 2) {
    // Goal-directed for trans: propagate what we can
    // trans(p, q) : Eq(a, c) when p : Eq(a, b) and q : Eq(b, c)
    // If one arg is inferrable and the other is ?, we can compute the goal for ?
    let leftExpected: AST.ProveExpr | undefined;
    let rightExpected: AST.ProveExpr | undefined;
    if (expected) {
      const goalEq = extractEq(normalize(expected));
      if (goalEq) {
        // Try inferring the non-hole arg to determine the other's goal
        const t1 = args[0].kind !== "hole" ? inferType(args[0], ctx) : null;
        const t2 = args[1].kind !== "hole" ? inferType(args[1], ctx) : null;
        if (t2?.ok) {
          const eq2 = extractEq(normalize(t2.type));
          if (eq2) leftExpected = app("Eq", goalEq.left, eq2.left);
        }
        if (t1?.ok) {
          const eq1 = extractEq(normalize(t1.type));
          if (eq1) rightExpected = app("Eq", eq1.right, goalEq.right);
        }
      }
    }
    return {
      rule: "trans",
      term,
      conclusion,
      children: [buildNode(args[0], ctx, leftExpected), buildNode(args[1], ctx, rightExpected)],
    };
  }
  // pair(witness, proof) — ∃-introduction for Sigma types
  if (name === "pair" && args.length === 2) {
    let proofExpected: AST.ProveExpr | undefined;
    if (expected) {
      const sigma = extractSigma(normalize(expected));
      if (sigma) {
        proofExpected = normalize(substitute(sigma.predicate, sigma.boundVar, args[0]));
      }
    }
    return {
      rule: "∃-intro",
      term,
      conclusion,
      children: [buildNode(args[1], ctx, proofExpected)],
    };
  }
  // fst(p), snd(p) — Sigma elimination
  if ((name === "fst" || name === "snd") && args.length === 1) {
    return { rule: name, term, conclusion, children: [buildNode(args[0], ctx)] };
  }
  // subst(p, e) — transport / J elimination
  if (name === "subst" && args.length === 2) {
    return {
      rule: "subst",
      term,
      conclusion,
      children: [buildNode(args[0], ctx), buildNode(args[1], ctx)],
    };
  }
  // ── Tactic combinators ──
  if (name === "exact" && args.length === 1) {
    return { rule: "exact", term, conclusion, children: [buildNode(args[0], ctx, expected)] };
  }
  if (name === "apply" && args.length >= 1 && args[0].kind === "ident") {
    const desugared = app(args[0].name, ...args.slice(1));
    return buildNode(desugared, ctx, expected);
  }
  if (name === "rewrite" && args.length === 1) {
    return { rule: "rewrite", term, conclusion, children: [buildNode(args[0], ctx)] };
  }
  if (name === "calc" && args.length >= 2) {
    let acc = args[0];
    for (let i = 1; i < args.length; i++) acc = app("trans", acc, args[i]);
    return buildNode(acc, ctx, expected);
  }
  if (name === "conv" && args.length === 0) {
    return { rule: "conv", term, conclusion, children: [] };
  }
  if (name === ctx.prove.name) {
    return { rule: "IH", term, conclusion, children: [] };
  }
  if (ctx.provedCtx.has(name)) {
    return { rule: name, term, conclusion, children: [] };
  }
  return { rule: "?", term, conclusion, children: [] };
}

function nodeHasHoles(node: ProofNode): boolean {
  if (node.isGoal) return true;
  return node.children.some(nodeHasHoles);
}

// ─── Dependent pattern matching helpers ────────────────────────────

/** Resolve the type name of a scrutinee from prove params and binding types. */
function resolveScrutineeType(
  scrutinee: string,
  ctx: ProveCtx,
): string | null {
  // Check prove params first
  for (const p of ctx.prove.params) {
    if (p.name === scrutinee && p.type) {
      return p.type.kind === "ident" ? p.type.name :
             p.type.kind === "call" ? p.type.name : null;
    }
  }
  // Check binding types (populated from constructor field types)
  return ctx.bindingTypes.get(scrutinee) ?? null;
}

/** Build typed bindings for a case arm: maps binding names to ident(name)
 *  and collects constructor-field type names when available. */
function buildTypedBindings(
  caseArm: AST.ProveCase,
  constructorTyping: ConstructorTyping,
): { bindings: Map<string, AST.ProveExpr>; types: Map<string, string> } {
  const bindings = new Map<string, AST.ProveExpr>();
  const types = new Map<string, string>();
  const ctorInfo = constructorTyping.get(caseArm.pattern);
  for (let i = 0; i < caseArm.bindings.length; i++) {
    const b = caseArm.bindings[i];
    bindings.set(b, ident(b));
    if (ctorInfo && i < ctorInfo.fields.length) {
      const ft = ctorInfo.fields[i].type;
      const typeName = ft.kind === "ident" ? ft.name : ft.kind === "call" ? ft.name : null;
      if (typeName) types.set(b, typeName);
    }
  }
  return { bindings, types };
}

/** Check exhaustiveness of a match expression against known constructors. */
function checkMatchExhaustiveness(
  scrutineeType: string | null,
  cases: AST.ProveCase[],
  constructorsByType: Map<string, Set<string>> | undefined,
  prefix: string,
): string[] {
  if (!scrutineeType || !constructorsByType) return [];
  const knownConstructors = constructorsByType.get(scrutineeType);
  if (!knownConstructors || knownConstructors.size === 0) return [];
  const casePatterns = new Set(cases.map((c) => c.pattern));
  const missing = [...knownConstructors].filter((c) => !casePatterns.has(c));
  if (missing.length > 0) {
    return [
      `${prefix}: non-exhaustive match on type ${scrutineeType}\n` +
        `  missing: ${missing.join(", ")}`,
    ];
  }
  return [];
}

/** Build context and expected type for a case arm. */
function caseCtx(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  constructorTyping: ConstructorTyping = new Map(),
  constructorsByType?: Map<string, Set<string>>,
  hints?: Map<string, Set<string>>,
  instances?: import("./evaluator.ts").InstanceDef[],
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">,
): { ctx: ProveCtx; expectedType: AST.ProveExpr } {
  const consExpr: AST.ProveExpr = caseArm.bindings.length > 0
    ? app(caseArm.pattern, ...caseArm.bindings.map(ident))
    : ident(caseArm.pattern);
  // Build typed caseBindings: look up constructor field types when available
  const { bindings: caseBindings, types: bindingTypes } = buildTypedBindings(caseArm, constructorTyping);
  // Also add aux params so they're visible in case bodies (e.g., program returns)
  for (const p of auxParams(prove.params)) {
    if (!caseBindings.has(p.name)) {
      caseBindings.set(p.name, p.type ?? ident(p.name));
      if (p.type) {
        const tname = p.type.kind === "ident" ? p.type.name : p.type.kind === "call" ? p.type.name : null;
        if (tname) bindingTypes.set(p.name, tname);
      }
    }
  }
  return {
    ctx: {
      prove,
      caseBindings,
      bindingTypes,
      provedCtx,
      constructorTyping,
      constructorsByType,
      hints,
      instances,
      dataSorts,
    },
    expectedType: normalize(substitute(prove.returnType!, inductionParam(prove.params)!.name, consExpr)),
  };
}

/** Compute the goal type for a case arm (public API for tactic resolution). */
export function computeGoalType(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  constructorTyping?: ConstructorTyping,
): AST.ProveExpr {
  return caseCtx(prove, caseArm, provedCtx, constructorTyping).expectedType;
}

/**
 * Search the proof context for a proof term matching the given goal.
 * Used by CtxSearch meta-agent. Assumes withNormTable is already active.
 */
export function searchProofContext(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  goal: AST.ProveExpr,
): AST.ProveExpr | null {
  const { ctx } = caseCtx(prove, caseArm, provedCtx);
  const candidates = searchCandidates(ctx, goal);
  return candidates.length > 0 ? parseProofString(candidates[0]) : null;
}

// ─── Strategy primitives (Phase 38) ───────────────────────────────
// Each primitive wraps internal machinery for use by the strategy interpreter.

export type StrategyContext = {
  goal: AST.ProveExpr;
  _ctx: ProveCtx;
};

export function makeStrategyContext(
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  hints?: Map<string, Set<string>>,
  instances?: import("./evaluator.ts").InstanceDef[],
): StrategyContext {
  const { ctx, expectedType: goal } = caseCtx(prove, caseArm, provedCtx, new Map(), undefined, hints, instances);
  return { goal, _ctx: ctx };
}

export function primConv(sctx: StrategyContext): AST.ProveExpr | null {
  const goalEq = extractEq(normalize(sctx.goal));
  if (goalEq && convertible(goalEq.left, goalEq.right)) {
    return ident("refl");
  }
  return null;
}

export function primCtxSearch(sctx: StrategyContext): AST.ProveExpr | null {
  const candidates = searchCandidates(sctx._ctx, sctx.goal);
  return candidates.length > 0 ? parseProofString(candidates[0]) : null;
}

export function primRewrite(sctx: StrategyContext): AST.ProveExpr | null {
  const goalEq = extractEq(normalize(sctx.goal));
  if (!goalEq) return null;
  return trySimpRewrite(sctx._ctx, goalEq);
}

export function primGround(sctx: StrategyContext): AST.ProveExpr | null {
  const goalEq = extractEq(normalize(sctx.goal));
  if (!goalEq) return null;
  const lhs = normalize(goalEq.left);
  const rhs = normalize(goalEq.right);
  if (isGroundTerm(lhs, sctx._ctx.caseBindings) && isGroundTerm(rhs, sctx._ctx.caseBindings) && exprEqual(lhs, rhs)) {
    return ident("refl");
  }
  return null;
}

export function primSearch(sctx: StrategyContext, depth: number): AST.ProveExpr | null {
  return autoSearch(sctx.goal, sctx._ctx, depth);
}

export function primCong(
  ctor: string | undefined,
  sctx: StrategyContext,
): { subGoal: AST.ProveExpr; wrap: (proof: AST.ProveExpr) => AST.ProveExpr } | null {
  const goalEq = extractEq(normalize(sctx.goal));
  if (!goalEq) return null;
  const lhs = normalize(goalEq.left);
  const rhs = normalize(goalEq.right);
  if (lhs.kind !== "call" || rhs.kind !== "call") return null;
  if (ctor && lhs.name !== ctor) return null;
  if (!ctor && lhs.name !== rhs.name) return null;
  if (lhs.name !== rhs.name || lhs.args.length !== rhs.args.length) return null;
  const diffs: number[] = [];
  for (let i = 0; i < lhs.args.length; i++) {
    if (!convertible(lhs.args[i], rhs.args[i])) diffs.push(i);
  }
  if (diffs.length !== 1) return null;
  const idx = diffs[0];
  const subGoal = app("Eq", lhs.args[idx], rhs.args[idx]);
  const congName = `cong_${lhs.name.toLowerCase()}`;
  const constArgs = lhs.args.filter((_, i) => i !== idx);
  return {
    subGoal,
    wrap: (proof: AST.ProveExpr) => app(congName, proof, ...constArgs),
  };
}

/** Build a proof derivation tree for a typed prove block. */
export function buildProofTree(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext = new Map(),
  computeRules?: ComputeRule[],
  constructorTyping?: ConstructorTyping,
  recordDefs?: Map<string, import("./normalize.ts").RecordDef>,
): ProofTree | null {
  if (!prove.returnType) return null;

  return withNormTable(computeRules ?? [], () => {
  const ctorTyping = constructorTyping ?? new Map();
  const cases: ProofTree["cases"] = prove.cases.map((caseArm) => {
    const { ctx, expectedType } = caseCtx(prove, caseArm, provedCtx, ctorTyping);
    return {
      pattern: caseArm.pattern,
      bindings: caseArm.bindings,
      tree: buildNode(caseArm.body, ctx, expectedType),
    };
  });

  return {
    name: prove.name,
    proposition: exprToString(prove.returnType!),
    cases,
    hasHoles: cases.some((c) => nodeHasHoles(c.tree)),
  };
  }, undefined, recordDefs); // end withNormTable
}

// ─── Tactic sugar stripping ────────────────────────────────────────
// Recursively rewrites exact(e) → e, apply(f, a, b) → f(a, b),
// calc(p1, p2, ...) → trans(trans(p1, p2), ...).

function stripTacticSugar(expr: AST.ProveExpr): AST.ProveExpr {
  if (expr.kind === "let") {
    return { kind: "let", name: expr.name, value: stripTacticSugar(expr.value), body: stripTacticSugar(expr.body) };
  }
  if (expr.kind === "pi") {
    return { kind: "pi", param: expr.param, domain: stripTacticSugar(expr.domain), codomain: stripTacticSugar(expr.codomain) };
  }
  if (expr.kind === "sigma") {
    return { kind: "sigma", param: expr.param, domain: stripTacticSugar(expr.domain), codomain: stripTacticSugar(expr.codomain) };
  }
  if (expr.kind === "lambda") {
    return { kind: "lambda", param: expr.param, paramType: stripTacticSugar(expr.paramType), body: stripTacticSugar(expr.body) };
  }
  if (expr.kind === "match") {
    return { kind: "match", scrutinee: expr.scrutinee, cases: expr.cases.map((c) => ({ ...c, body: stripTacticSugar(c.body) })) };
  }
  if (expr.kind === "ident" && expr.name === "conv") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "simp") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "decide") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "omega") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "auto") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "ring") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind !== "call") return expr;
  // Strip tactic combinators: unwrap to inner content
  if (expr.name === "try" && expr.args.length === 1) return stripTacticSugar(expr.args[0]);
  if (expr.name === "first" && expr.args.length >= 1) return stripTacticSugar(expr.args[0]);
  if (expr.name === "repeat" && expr.args.length === 1) return stripTacticSugar(expr.args[0]);
  if ((expr.name === "then" || expr.name === "seq") && expr.args.length === 2) return stripTacticSugar(expr.args[1]);
  if (expr.name === "all" && expr.args.length === 1) return stripTacticSugar(expr.args[0]);
  if (expr.name === "exact" && expr.args.length === 1) return stripTacticSugar(expr.args[0]);
  if (expr.name === "apply" && expr.args.length >= 1 && expr.args[0].kind === "ident") {
    return { kind: "call", name: expr.args[0].name, args: expr.args.slice(1).map(stripTacticSugar) };
  }
  if (expr.name === "calc" && expr.args.length >= 2) {
    let acc = stripTacticSugar(expr.args[0]);
    for (let i = 1; i < expr.args.length; i++) {
      acc = { kind: "call", name: "trans", args: [acc, stripTacticSugar(expr.args[i])] };
    }
    return acc;
  }
  if (expr.name === "conv" && expr.args.length === 0) {
    return { kind: "ident", name: "refl" };
  }
  return { kind: "call", name: expr.name, args: expr.args.map(stripTacticSugar) };
}

// ─── Match expression type checker ─────────────────────────────────
// Validates each arm individually, substituting the scrutinee variable
// with the constructor expression in the expected type (dependent matching).
// Also performs exhaustiveness checking when the scrutinee type is known.

function typecheckMatchExpr(
  matchExpr: AST.ProveExpr & { kind: "match" },
  ctx: ProveCtx,
  requiredType: AST.ProveExpr,
  prefix: string,
): string[] {
  const errors: string[] = [];

  // Exhaustiveness: resolve scrutinee type and check all constructors covered
  const scrutType = resolveScrutineeType(matchExpr.scrutinee, ctx);
  errors.push(...checkMatchExhaustiveness(
    scrutType, matchExpr.cases, ctx.constructorsByType, prefix,
  ));
  // Overlap: detect redundant case arms (skip deep-pattern-refined constructors)
  const refined = new Set<string>();
  for (const arm of matchExpr.cases) {
    if (arm.bindings.some((b) => b.startsWith("_dp"))) refined.add(arm.pattern);
  }
  const matchSeen = new Map<string, number>();
  for (let i = 0; i < matchExpr.cases.length; i++) {
    const pat = matchExpr.cases[i].pattern;
    if (refined.has(pat)) continue;
    const prev = matchSeen.get(pat);
    if (prev !== undefined) {
      errors.push(`${prefix}: redundant match case ${pat} (already covered by case ${prev + 1})`);
    }
    matchSeen.set(pat, i + 1);
  }

  for (const arm of matchExpr.cases) {
    const consExpr: AST.ProveExpr = arm.bindings.length > 0
      ? app(arm.pattern, ...arm.bindings.map(ident))
      : ident(arm.pattern);
    const armReq = normalize(substitute(requiredType, matchExpr.scrutinee, consExpr));
    // Build typed bindings from constructor fields
    const { bindings: newBindings, types: newTypes } = buildTypedBindings(arm, ctx.constructorTyping);
    for (const [k, v] of ctx.caseBindings) {
      if (!newBindings.has(k)) newBindings.set(k, v);
    }
    const mergedTypes = new Map(ctx.bindingTypes);
    for (const [k, v] of newTypes) mergedTypes.set(k, v);
    const armCtx: ProveCtx = { ...ctx, caseBindings: newBindings, bindingTypes: mergedTypes };
    const armBody = stripTacticSugar(arm.body);

    if (armBody.kind === "match") {
      errors.push(...typecheckMatchExpr(armBody, armCtx, armReq, `${prefix}.${arm.pattern}`));
      continue;
    }
    const inferred = inferType(armBody, armCtx);
    if (!inferred.ok) {
      if (inferred.error !== "hole") errors.push(`${prefix}.${arm.pattern}: ${inferred.error}`);
      continue;
    }
    const reqEq = extractEq(armReq);
    const infEq = extractEq(inferred.type);
    if (reqEq && infEq) {
      if (!eqTypeMatches(inferred.type, armReq)) {
        errors.push(`${prefix}.${arm.pattern}: type mismatch\n  expected: ${exprToString(armReq)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
      }
    }
  }
  return errors;
}

// ─── Main type checker ─────────────────────────────────────────────

export function typecheckProve(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext = new Map(),
  constructorsByType?: Map<string, Set<string>>,
  computeRules?: ComputeRule[],
  constructorTyping?: ConstructorTyping,
  codataTypes?: Set<string>,
  coercions?: Map<string, Map<string, string>>,
  setoids?: Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>,
  rings?: Map<string, { type: string; zero: string; one?: string; add: string; mul: string }>,
  hints?: Map<string, Set<string>>,
  instances?: import("./evaluator.ts").InstanceDef[],
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">,
  canonicals?: import("./evaluator.ts").CanonicalDef[],
  recordDefs?: Map<string, import("./normalize.ts").RecordDef>,
): string[] {
  return withNormTable(computeRules ?? [], () => {
  const ctorTyping = constructorTyping ?? new Map();
  const exhaustErrors = constructorsByType
    ? checkExhaustiveness(prove, constructorsByType)
    : [];
  const overlapErrors = checkOverlap(prove);
  // For codata-returning proves, use productivity checking instead of termination
  const returnTypeName = prove.returnType
    ? (prove.returnType.kind === "ident" ? prove.returnType.name
       : prove.returnType.kind === "call" ? prove.returnType.name : null)
    : null;
  const isCodata = returnTypeName != null && codataTypes != null && codataTypes.has(returnTypeName);
  // Choose termination strategy: wf (trusted), measure, codata productivity, or structural
  const termErrors = prove.wf
    ? [] // wf: trusted — no termination check
    : prove.measure
    ? checkMeasureTermination(prove, prove.measure)
    : isCodata
    ? checkProductivity(prove, returnTypeName, constructorTyping)
    : checkTermination(prove);
  if (!prove.returnType) return [...exhaustErrors, ...termErrors];

  const errors: string[] = [];

  for (const caseArm of prove.cases) {
    const { ctx: baseCtx, expectedType: requiredType } = caseCtx(prove, caseArm, provedCtx, ctorTyping, constructorsByType, undefined, undefined, dataSorts);
    let ctx: ProveCtx = baseCtx;
    if (setoids) ctx = { ...ctx, setoids };
    if (hints) ctx = { ...ctx, hints };
    if (instances) ctx = { ...ctx, instances };
    const prefix = `prove ${prove.name}, case ${caseArm.pattern}`;
    const rawBody = caseArm.body;
    const reqEq = extractEq(requiredType);

    // SProp proof irrelevance: if the required type lives in SProp,
    // any proof term is definitionally equal — skip detailed checking
    const reqSort = sortOf(requiredType, dataSorts);
    if (reqSort === "SProp") continue;

    // Handle conv — goal proved by definitional equality (both sides normalize to same term)
    // Check on raw body BEFORE stripTacticSugar (which would convert conv → refl)
    if ((rawBody.kind === "ident" && rawBody.name === "conv") ||
        (rawBody.kind === "call" && rawBody.name === "conv" && rawBody.args.length === 0)) {
      if (reqEq && convertible(reqEq.left, reqEq.right)) continue;
      // Also handle setoid goals: conv proves R(a, a) when both sides normalize to the same term
      const reqEquivConv = extractEquiv(requiredType);
      if (reqEquivConv && isEquivRelation(reqEquivConv.rel, setoids) &&
          convertible(reqEquivConv.left, reqEquivConv.right)) continue;
      const convCheck = reqEq ? checkConvertible(reqEq.left, reqEq.right)
        : reqEquivConv ? checkConvertible(reqEquivConv.left, reqEquivConv.right) : null;
      const detail = convCheck && !convCheck.convertible
        ? `\n  lhs normalizes to: ${convCheck.lhsNorm}\n  rhs normalizes to: ${convCheck.rhsNorm}` : "";
      errors.push(`${prefix}: conv failed — sides are not definitionally equal\n  goal: ${exprToString(requiredType)}${detail}`);
      continue;
    }

    // Handle ring — goal proved by commutative ring normalization
    if ((rawBody.kind === "ident" && rawBody.name === "ring") ||
        (rawBody.kind === "call" && rawBody.name === "ring" && rawBody.args.length === 0)) {
      if (reqEq && rings && rings.size > 0) {
        const lhs = normalize(reqEq.left);
        const rhs = normalize(reqEq.right);
        let matched = false;
        for (const ring of rings.values()) {
          if (ringCongruent(lhs, rhs, ring)) { matched = true; break; }
        }
        if (matched) continue;
      }
      errors.push(`${prefix}: ring failed — sides are not equal as polynomials\n  goal: ${exprToString(requiredType)}`);
      continue;
    }

    // Handle simp — should have been resolved before type checking; if still present, it failed
    if (rawBody.kind === "ident" && rawBody.name === "simp") {
      errors.push(`${prefix}: simp failed — could not find a proof\n  goal: ${exprToString(requiredType)}`);
      continue;
    }

    // Handle decide — should have been resolved before type checking; if still present, it failed
    if (rawBody.kind === "ident" && rawBody.name === "decide") {
      errors.push(`${prefix}: decide failed — terms may not be ground or not equal\n  goal: ${exprToString(requiredType)}`);
      continue;
    }

    // Handle omega — should have been resolved before type checking; if still present, it failed
    if (rawBody.kind === "ident" && rawBody.name === "omega") {
      errors.push(`${prefix}: omega failed — not a linear arithmetic goal\n  goal: ${exprToString(requiredType)}`);
      continue;
    }

    // Handle auto — should have been resolved before type checking; if still present, it failed
    if (rawBody.kind === "ident" && rawBody.name === "auto") {
      errors.push(`${prefix}: auto failed — could not find a proof\n  goal: ${exprToString(requiredType)}`);
      continue;
    }

    // Handle failed tactic combinators (Phase 34)
    if (rawBody.kind === "call" && rawBody.name === "first") {
      const inner = rawBody.args.map((a) => a.kind === "ident" ? a.name : "...").join(", ");
      errors.push(`${prefix}: first(${inner}) failed — no alternative succeeded\n  goal: ${exprToString(requiredType)}`);
      continue;
    }
    if (rawBody.kind === "call" && rawBody.name === "repeat") {
      errors.push(`${prefix}: repeat failed — tactic could not make progress\n  goal: ${exprToString(requiredType)}`);
      continue;
    }
    if (rawBody.kind === "call" && rawBody.name === "all") {
      errors.push(`${prefix}: all failed — tactic could not resolve goal\n  goal: ${exprToString(requiredType)}`);
      continue;
    }

    const body = stripTacticSugar(rawBody);

    // Handle rewrite(proof) — contextual goal-rewriting check (Eq or setoid)
    if (body.kind === "call" && body.name === "rewrite" && body.args.length === 1) {
      const proofResult = inferType(body.args[0], ctx);
      if (!proofResult.ok) {
        if (proofResult.error !== "hole") errors.push(`${prefix}: ${proofResult.error}`);
        continue;
      }
      const proofEquiv = extractEquiv(normalize(proofResult.type));
      const reqEquiv = extractEquiv(normalize(requiredType));
      if (!proofEquiv || !reqEquiv) {
        errors.push(`${prefix}: rewrite requires equivalence types on both proof and goal`);
        continue;
      }
      if (proofEquiv.rel !== reqEquiv.rel) {
        errors.push(`${prefix}: rewrite relation mismatch: proof uses '${proofEquiv.rel}', goal uses '${reqEquiv.rel}'`);
        continue;
      }
      if (!isEquivRelation(proofEquiv.rel, ctx.setoids)) {
        errors.push(`${prefix}: rewrite: '${proofEquiv.rel}' is not Eq or a registered setoid`);
        continue;
      }
      const a = normalize(proofEquiv.left), b = normalize(proofEquiv.right);
      const lhs = normalize(reqEquiv.left), rhs = normalize(reqEquiv.right);
      if (exprEqual(normalize(substituteExprPattern(lhs, a, b)), rhs)) continue;
      if (exprEqual(normalize(substituteExprPattern(lhs, b, a)), rhs)) continue;
      errors.push(
        `${prefix}: rewrite failed\n  proof: ${exprToString(normalize(proofResult.type))}\n  goal: ${exprToString(requiredType)}`,
      );
      continue;
    }

    // Handle match expression — validate each arm against per-arm expected type
    if (body.kind === "match") {
      errors.push(...typecheckMatchExpr(body, ctx, requiredType, prefix));
      continue;
    }

    const inferred = inferType(body, ctx);
    if (!inferred.ok) {
      if (inferred.error !== "hole") errors.push(`${prefix}: ${inferred.error}`);
      continue;
    }

    const infEq = extractEq(inferred.type);
    const infEquiv = !infEq ? extractEquiv(inferred.type) : null;
    const reqEquiv2 = !reqEq ? extractEquiv(requiredType) : null;

    // Eq type matching (existing path)
    if (reqEq && infEq) {
      if (!eqTypeMatches(inferred.type, requiredType)) {
        errors.push(`${prefix}: type mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
      }
      continue;
    }

    // Setoid relation matching: both sides are the same registered setoid relation
    if (reqEquiv2 && infEquiv && reqEquiv2.rel === infEquiv.rel && isEquivRelation(reqEquiv2.rel, ctx.setoids)) {
      // Handle refl sentinel for setoid goals: R(_refl_a, _refl_a) matches R(a, a) when sides are equal
      if (infEquiv.left.kind === "ident" && infEquiv.left.name === "_refl_a" &&
          infEquiv.right.kind === "ident" && infEquiv.right.name === "_refl_a") {
        if (!convertible(reqEquiv2.left, reqEquiv2.right)) {
          errors.push(`${prefix}: type mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
        }
      } else if (!convertible(infEquiv.left, reqEquiv2.left) ||
                 !convertible(infEquiv.right, reqEquiv2.right)) {
        errors.push(`${prefix}: type mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);  
      }
      continue;
    }

    // refl (Eq sentinel) matches setoid reflexive goals: refl : R(a, a) when R is a setoid
    if (infEq && reqEquiv2 && isEquivRelation(reqEquiv2.rel, ctx.setoids)) {
      const isReflSentinel = infEq.left.kind === "ident" && infEq.left.name === "_refl_a" &&
                             infEq.right.kind === "ident" && infEq.right.name === "_refl_a";
      if (isReflSentinel) {
        if (!convertible(reqEquiv2.left, reqEquiv2.right)) {
          errors.push(`${prefix}: type mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
        }
        continue;
      }
    }

    if (reqEq || infEq) {
      errors.push(`${prefix}: type structure mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(inferred.type)}`);
      continue;
    }

    // Sigma types
    const reqSigma = extractSigma(requiredType);
    if (reqSigma && inferred.type.kind === "call" && inferred.type.name === "Sigma" &&
        inferred.type.args.length === 2) {
      const witness = inferred.type.args[0];
      const infProofType = inferred.type.args[1];
      const expectedPred = normalize(substitute(reqSigma.predicate, reqSigma.boundVar, witness));
      if (!eqTypeMatches(infProofType, expectedPred) && !convertible(infProofType, expectedPred)) {
        errors.push(`${prefix}: Sigma predicate mismatch\n  expected: ${exprToString(expectedPred)}\n  inferred: ${exprToString(normalize(infProofType))}`);
      }
      continue;
    }
    if (reqSigma || (inferred.type.kind === "call" && inferred.type.name === "Sigma")) {
      errors.push(`${prefix}: type structure mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
      continue;
    }

    // General type comparison for non-Eq, non-Sigma types
    const infNorm = normalize(inferred.type);
    const reqNorm = normalize(requiredType);
    if (!exprEqual(infNorm, reqNorm)) {
      const infName = topTypeName(infNorm);
      const reqName = topTypeName(reqNorm);
      // Same top-level constructor (e.g. Stream(A) vs Stream(Nat)) — accept;
      // parameter instantiation is handled elsewhere
      if (infName && reqName && infName === reqName) {
        continue;
      }
      // Check for implicit coercion
      if (coercions && infName && reqName && coercions.get(infName)?.has(reqName)) {
        continue;
      }
      errors.push(`${prefix}: type mismatch\n  expected: ${exprToString(reqNorm)}\n  inferred: ${exprToString(infNorm)}`);
    }
  }

  return [...exhaustErrors, ...overlapErrors, ...termErrors, ...errors];
  }, canonicals, recordDefs); // end withNormTable
}

/** Parse a simple proof-term string like "cong_succ(pzr(k))" into a ProveExpr. */
function parseProofString(s: string): AST.ProveExpr {
  let pos = 0;
  function parseExpr(): AST.ProveExpr {
    let name = "";
    while (pos < s.length && /[a-zA-Z0-9_]/.test(s[pos])) name += s[pos++];
    if (!name) return { kind: "hole" };
    if (pos < s.length && s[pos] === "(") {
      pos++; // skip (
      const args: AST.ProveExpr[] = [];
      while (pos < s.length && s[pos] !== ")") {
        if (args.length > 0 && s[pos] === ",") { pos++; while (s[pos] === " ") pos++; }
        args.push(parseExpr());
      }
      if (pos < s.length) pos++; // skip )
      return { kind: "call", name, args };
    }
    return { kind: "ident", name };
  }
  return parseExpr();
}

/** Collect equational lemmas available in a proof context.
 *  Priority: IH calls > simp-DB hints > general proved lemmas.
 *  Phase 35: factored out for reuse by multi-step simp. */
function collectEquationalLemmas(
  ctx: ProveCtx,
  rel: string = "Eq",
): { proof: AST.ProveExpr; left: AST.ProveExpr; right: AST.ProveExpr }[] {
  const lemmas: { proof: AST.ProveExpr; left: AST.ProveExpr; right: AST.ProveExpr }[] = [];

  // IH calls
  const auxArgs = auxParams(ctx.prove.params).map((p) => ident(p.name));
  for (const b of ctx.caseBindings.keys()) {
    const call = app(ctx.prove.name, ident(b), ...auxArgs);
    const r = inferType(call, ctx);
    if (r.ok) {
      const equiv = extractEquiv(normalize(r.type));
      if (equiv && equiv.rel === rel) lemmas.push({ proof: call, left: normalize(equiv.left), right: normalize(equiv.right) });
    }
  }

  // Available variables for argument instantiation
  const availableVars = [
    ...[...ctx.caseBindings.keys()].map(ident),
    ...auxParams(ctx.prove.params).map((p) => ident(p.name)),
  ];

  // Helper: try all argument orderings for a lemma with N explicit params.
  // For 0-1 params, there's only one ordering. For 2 params, try both permutations.
  // For 3+ params, try positional + each single-swap variant to keep combinatorics bounded.
  const tryLemmaInstantiations = (lemmaName: string, explicitParams: AST.ProveParam[]) => {
    const n = explicitParams.length;
    if (n === 0) {
      const call = app(lemmaName);
      const r = inferType(call, ctx);
      if (r.ok) {
        const equiv = extractEquiv(normalize(r.type));
        if (equiv && equiv.rel === rel) lemmas.push({ proof: call, left: normalize(equiv.left), right: normalize(equiv.right) });
      }
      return;
    }
    if (n > availableVars.length) return;

    // Positional: first n available vars
    const positional = app(lemmaName, ...availableVars.slice(0, n));
    const rPos = inferType(positional, ctx);
    if (rPos.ok) {
      const equiv = extractEquiv(normalize(rPos.type));
      if (equiv && equiv.rel === rel) lemmas.push({ proof: positional, left: normalize(equiv.left), right: normalize(equiv.right) });
    }

    // For 2 params: also try swapped order
    if (n === 2 && availableVars.length >= 2) {
      const swapped = app(lemmaName, availableVars[1], availableVars[0]);
      const rSwap = inferType(swapped, ctx);
      if (rSwap.ok) {
        const equiv = extractEquiv(normalize(rSwap.type));
        if (equiv && equiv.rel === rel) {
          const swapStr = exprToString(swapped);
          const posStr = exprToString(positional);
          if (swapStr !== posStr) lemmas.push({ proof: swapped, left: normalize(equiv.left), right: normalize(equiv.right) });
        }
      }
    }
  };

  // Hint-DB lemmas (simp DB) — priority
  const hintSimpNames = ctx.hints?.get("simp");
  if (hintSimpNames) {
    for (const lemmaName of hintSimpNames) {
      const lemma = ctx.provedCtx.get(lemmaName);
      if (!lemma) continue;
      const explicitParams = lemma.params.filter((p) => !p.implicit);
      tryLemmaInstantiations(lemmaName, explicitParams);
    }
  }

  // Cross-lemma calls (remaining lemmas not already tried via hints)
  for (const [lemmaName, lemma] of ctx.provedCtx) {
    if (hintSimpNames?.has(lemmaName)) continue;
    const explicitParams = lemma.params.filter((p) => !p.implicit);
    tryLemmaInstantiations(lemmaName, explicitParams);
  }

  return lemmas;
}

/** Try to close an equality goal by rewriting one side with available lemmas.
 *  Phase 35: multi-step rewriting — iterates up to 10 rewrite steps on the LHS,
 *  applying lemmas (L→R and R→L) and normalizing after each step, until LHS equals RHS.
 *  Builds a chain of rewrite proof terms: rewrite(lemma) or trans(step1, step2). */
function trySimpRewrite(
  ctx: ProveCtx,
  goalEq: { left: AST.ProveExpr; right: AST.ProveExpr },
  rel: string = "Eq",
): AST.ProveExpr | null {
  const lhs = normalize(goalEq.left);
  const rhs = normalize(goalEq.right);

  const lemmas = collectEquationalLemmas(ctx, rel);

  // Single-step rewriting (original behavior)
  for (const lem of lemmas) {
    const rewritten = normalize(substituteExprPattern(lhs, lem.left, lem.right));
    if (exprEqual(rewritten, rhs)) {
      return app("rewrite", lem.proof);
    }
  }
  for (const lem of lemmas) {
    const rewritten = normalize(substituteExprPattern(lhs, lem.right, lem.left));
    if (exprEqual(rewritten, rhs)) {
      return app("rewrite", app("sym", lem.proof));
    }
  }

  // Multi-step rewriting (Phase 35): iterate up to 10 steps
  let current = lhs;
  const proofSteps: AST.ProveExpr[] = [];
  for (let step = 0; step < 10; step++) {
    let advanced = false;
    // Try each lemma L→R
    for (const lem of lemmas) {
      const rewritten = normalize(substituteExprPattern(current, lem.left, lem.right));
      if (!exprEqual(rewritten, current)) {
        proofSteps.push(app("rewrite", lem.proof));
        current = rewritten;
        advanced = true;
        if (exprEqual(current, rhs)) {
          return chainProofSteps(proofSteps);
        }
        break; // restart lemma search after each successful step
      }
    }
    if (advanced) continue;
    // Try each lemma R→L
    for (const lem of lemmas) {
      const rewritten = normalize(substituteExprPattern(current, lem.right, lem.left));
      if (!exprEqual(rewritten, current)) {
        proofSteps.push(app("rewrite", app("sym", lem.proof)));
        current = rewritten;
        advanced = true;
        if (exprEqual(current, rhs)) {
          return chainProofSteps(proofSteps);
        }
        break;
      }
    }
    if (!advanced) break; // no lemma made progress — stop
  }

  return null;
}

/** Chain multiple proof steps using trans: trans(step1, trans(step2, step3)) */
function chainProofSteps(steps: AST.ProveExpr[]): AST.ProveExpr {
  if (steps.length === 1) return steps[0];
  let result = steps[steps.length - 1];
  for (let i = steps.length - 2; i >= 0; i--) {
    result = app("trans", steps[i], result);
  }
  return result;
}

function isGroundTerm(expr: AST.ProveExpr, caseBindings: Map<string, AST.ProveExpr>): boolean {
  if (expr.kind === "metavar") return false;
  if (expr.kind === "ident") return !caseBindings.has(expr.name);
  if (expr.kind === "call") return expr.args.every(a => isGroundTerm(a, caseBindings));
  if (expr.kind === "let") return isGroundTerm(expr.value, caseBindings) && isGroundTerm(expr.body, caseBindings);
  if (expr.kind === "pi" || expr.kind === "sigma") return isGroundTerm(expr.domain, caseBindings) && isGroundTerm(expr.codomain, caseBindings);
  if (expr.kind === "lambda") return isGroundTerm(expr.paramType, caseBindings) && isGroundTerm(expr.body, caseBindings);
  return false;
}

/** Try congruence on Succ: if Succ(a) = Succ(b) and IH gives a = b, return cong_succ(IH) */
function tryCongSucc(
  lhs: AST.ProveExpr,
  rhs: AST.ProveExpr,
  ctx: ProveCtx,
): AST.ProveExpr | null {
  if (lhs.kind !== "call" || lhs.name !== "Succ" || lhs.args.length !== 1) return null;
  if (rhs.kind !== "call" || rhs.name !== "Succ" || rhs.args.length !== 1) return null;
  const innerLhs = normalize(lhs.args[0]);
  const innerRhs = normalize(rhs.args[0]);
  if (exprEqual(innerLhs, innerRhs)) return app("cong_succ", ident("refl"));
  // Try IH: call prove with each binding variable
  const auxArgs = auxParams(ctx.prove.params).map((p) => ident(p.name));
  for (const b of ctx.caseBindings.keys()) {
    const ihCall = app(ctx.prove.name, ident(b), ...auxArgs);
    const r = inferType(ihCall, ctx);
    if (r.ok) {
      const eq = extractEq(normalize(r.type));
      if (eq && convertible(eq.left, innerLhs) && convertible(eq.right, innerRhs)) {
        return app("cong_succ", ihCall);
      }
      // Also try with sym
      if (eq && convertible(eq.left, innerRhs) && convertible(eq.right, innerLhs)) {
        return app("cong_succ", app("sym", ihCall));
      }
    }
  }
  return null;
}

function autoSearch(
  goal: AST.ProveExpr,
  ctx: ProveCtx,
  depth: number,
): AST.ProveExpr | null {
  if (depth <= 0) return null;

  const normGoal = normalize(goal);
  const goalEq = extractEq(normGoal);

  // 1. conv: definitional equality → refl
  if (goalEq && convertible(goalEq.left, goalEq.right)) {
    return ident("refl");
  }

  // 2. assumption search
  const candidates = searchCandidates(ctx, goal);
  if (candidates.length > 0) return parseProofString(candidates[0]);

  // 3. one-step rewrite (simp strategy)
  if (goalEq) {
    const rw = trySimpRewrite(ctx, goalEq);
    if (rw) return rw;
  }

  // 4. congruence: if Eq(F(a), F(b)), try cong_F(proof of Eq(a, b))
  if (goalEq && depth >= 2) {
    const congResult = tryCongAuto(goalEq.left, goalEq.right, ctx, depth);
    if (congResult) return congResult;
  }

  // 5. trans chaining at depth-1: try to split the goal via available lemmas
  if (goalEq && depth >= 2) {
    const lhs = normalize(goalEq.left);
    const rhs = normalize(goalEq.right);
    const auxArgs = auxParams(ctx.prove.params).map((p) => ident(p.name));
    // Try IH as first step, then recurse
    for (const b of ctx.caseBindings.keys()) {
      const ihCall = app(ctx.prove.name, ident(b), ...auxArgs);
      const r = inferType(ihCall, ctx);
      if (!r.ok) continue;
      const eq = extractEq(normalize(r.type));
      if (!eq) continue;
      // If IH proves Eq(A, B), and our goal is Eq(A, C), try trans(IH, Eq(B, C))
      const ihLhs = normalize(eq.left);
      const ihRhs = normalize(eq.right);
      if (exprEqual(ihLhs, lhs)) {
        const rest = autoSearch(app("Eq", ihRhs, rhs), ctx, depth - 1);
        if (rest) return app("trans", ihCall, rest);
      }
      if (exprEqual(ihRhs, rhs)) {
        const rest = autoSearch(app("Eq", lhs, ihLhs), ctx, depth - 1);
        if (rest) return app("trans", rest, ihCall);
      }
    }
  }

  return null;
}

/** Try congruence reasoning: if goal is Eq(F(a1,...), F(b1,...)), try cong_F for each differing argument. */
function tryCongAuto(
  lhs: AST.ProveExpr,
  rhs: AST.ProveExpr,
  ctx: ProveCtx,
  depth: number,
): AST.ProveExpr | null {
  const nlhs = normalize(lhs);
  const nrhs = normalize(rhs);
  if (nlhs.kind !== "call" || nrhs.kind !== "call") return null;
  if (nlhs.name !== nrhs.name || nlhs.args.length !== nrhs.args.length) return null;
  // Find the one differing argument position
  const diffs: number[] = [];
  for (let i = 0; i < nlhs.args.length; i++) {
    if (!convertible(nlhs.args[i], nrhs.args[i])) diffs.push(i);
  }
  // Standard cong applies to last differing argument
  if (diffs.length === 1 && diffs[0] === nlhs.args.length - 1) {
    const inner = autoSearch(
      app("Eq", nlhs.args[diffs[0]], nrhs.args[diffs[0]]),
      ctx,
      depth - 1,
    );
    if (inner) {
      const congName = `cong_${nlhs.name.toLowerCase()}`;
      const constArgs = nlhs.args.slice(0, -1);
      return app(congName, inner, ...constArgs);
    }
  }
  return null;
}
