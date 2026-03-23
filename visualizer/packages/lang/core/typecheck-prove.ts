// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Dependent Type Checker for prove blocks
//
// Verifies that each case arm in a typed `prove` block produces
// a proof term whose type matches the declared proposition.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { inductionParam, auxParams } from "./types.ts";

// Context of previously proved propositions for cross-lemma resolution
export type ProvedContext = Map<
  string,
  { params: AST.ProveParam[]; returnType: AST.ProveExpr }
>;

// ─── Compute rules (user-declared reduction equations) ─────────────

/** A user-declared reduction equation for the normalizer.
 *  Mirrors AST.ComputeDecl but may be inherited across system boundaries. */
export type ComputeRule = {
  funcName: string;
  args: AST.ComputePattern[];
  result: AST.ProveExpr;
};

/** Constructor typing info derived from data declarations.
 *  Maps constructor name → { typeName, params, indices, fields, returnIndices } */
export type ConstructorTyping = Map<string, {
  typeName: string;
  params: string[];
  indices: AST.DataIndex[];
  fields: { name: string; type: AST.ProveExpr }[];
  returnIndices?: AST.ProveExpr[];
}>;

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

function ident(name: string): AST.ProveExpr {
  return { kind: "ident", name };
}

function app(name: string, ...args: AST.ProveExpr[]): AST.ProveExpr {
  return { kind: "call", name, args };
}

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

function exprEqual(a: AST.ProveExpr, b: AST.ProveExpr): boolean {
  if (a.kind === "hole" || b.kind === "hole") return false;
  if (a.kind === "match" || b.kind === "match") return false;
  if (a.kind === "let" && b.kind === "let") {
    return a.name === b.name && exprEqual(a.value, b.value) && exprEqual(a.body, b.body);
  }
  if (a.kind === "let" || b.kind === "let") return false;
  if (a.kind === "pi" && b.kind === "pi") {
    return exprEqual(a.domain, b.domain) && exprEqual(substitute(a.codomain, a.param, ident(b.param)), b.codomain);
  }
  if (a.kind === "sigma" && b.kind === "sigma") {
    return exprEqual(a.domain, b.domain) && exprEqual(substitute(a.codomain, a.param, ident(b.param)), b.codomain);
  }
  if (a.kind === "lambda" && b.kind === "lambda") {
    return exprEqual(a.paramType, b.paramType) && exprEqual(substitute(a.body, a.param, ident(b.param)), b.body);
  }
  if (a.kind === "pi" || b.kind === "pi") return false;
  if (a.kind === "sigma" || b.kind === "sigma") return false;
  if (a.kind === "lambda" || b.kind === "lambda") return false;
  if (a.kind === "ident" && b.kind === "ident") return a.name === b.name;
  if (a.kind === "call" && b.kind === "call") {
    if (a.name !== b.name || a.args.length !== b.args.length) return false;
    return a.args.every((arg, i) => exprEqual(arg, b.args[i]));
  }
  return false;
}

const SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉";
function toSubscript(n: number): string {
  return String(n).split("").map((d) => SUBSCRIPTS[parseInt(d)]).join("");
}

function exprToString(e: AST.ProveExpr): string {
  if (e.kind === "hole") return "?";
  if (e.kind === "match") return `match(${e.scrutinee}) { ... }`;
  if (e.kind === "let") return `let ${e.name} = ${exprToString(e.value)} in ${exprToString(e.body)}`;
  if (e.kind === "pi") return `∀(${e.param} : ${exprToString(e.domain)}), ${exprToString(e.codomain)}`;
  if (e.kind === "sigma") return `Σ(${e.param} : ${exprToString(e.domain)}), ${exprToString(e.codomain)}`;
  if (e.kind === "lambda") return `λ(${e.param} : ${exprToString(e.paramType)}). ${exprToString(e.body)}`;
  if (e.kind === "ident") {
    if (e.name === "Type") return "Type" + toSubscript(0);
    const m = e.name.match(/^Type(\d+)$/);
    if (m) return "Type" + toSubscript(parseInt(m[1]));
    return e.name;
  }
  // Type(n) → Typeₙ (canonical form from normalize)
  if (e.name === "Type" && e.args.length === 1 &&
      e.args[0].kind === "ident" && /^\d+$/.test(e.args[0].name)) {
    return "Type" + toSubscript(parseInt(e.args[0].name));
  }
  return `${e.name}(${e.args.map(exprToString).join(", ")})`;
}

// ─── Substitution ──────────────────────────────────────────────────

function substitute(
  expr: AST.ProveExpr,
  varName: string,
  value: AST.ProveExpr,
): AST.ProveExpr {
  if (expr.kind === "hole") return expr;
  if (expr.kind === "ident") {
    return expr.name === varName ? value : expr;
  }
  if (expr.kind === "let") {
    const newValue = substitute(expr.value, varName, value);
    // Shadowing: if the let-bound name matches, don't substitute in body
    if (expr.name === varName) return { kind: "let", name: expr.name, value: newValue, body: expr.body };
    return { kind: "let", name: expr.name, value: newValue, body: substitute(expr.body, varName, value) };
  }
  if (expr.kind === "pi") {
    const newDomain = substitute(expr.domain, varName, value);
    if (expr.param === varName) return { kind: "pi", param: expr.param, domain: newDomain, codomain: expr.codomain };
    return { kind: "pi", param: expr.param, domain: newDomain, codomain: substitute(expr.codomain, varName, value) };
  }
  if (expr.kind === "sigma") {
    const newDomain = substitute(expr.domain, varName, value);
    if (expr.param === varName) return { kind: "sigma", param: expr.param, domain: newDomain, codomain: expr.codomain };
    return { kind: "sigma", param: expr.param, domain: newDomain, codomain: substitute(expr.codomain, varName, value) };
  }
  if (expr.kind === "lambda") {
    const newType = substitute(expr.paramType, varName, value);
    if (expr.param === varName) return { kind: "lambda", param: expr.param, paramType: newType, body: expr.body };
    return { kind: "lambda", param: expr.param, paramType: newType, body: substitute(expr.body, varName, value) };
  }
  if (expr.kind === "match") {
    return {
      kind: "match",
      scrutinee: expr.scrutinee === varName && value.kind === "ident" ? value.name : expr.scrutinee,
      cases: expr.cases.map((c) => ({ ...c, body: substitute(c.body, varName, value) })),
    };
  }
  // call: substitute in name if it matches (unlikely but handle), and all args
  const newArgs = expr.args.map((a) => substitute(a, varName, value));
  const newName = expr.name === varName && value.kind === "ident"
    ? value.name
    : expr.name;
  return { kind: "call", name: newName, args: newArgs };
}

// Simultaneous substitution — avoids variable capture when parameter
// names overlap with argument expressions (e.g. calling f(m, k) where
// f's params are (n, m) would corrupt m with sequential substitution).
function substituteAll(
  expr: AST.ProveExpr,
  bindings: Map<string, AST.ProveExpr>,
): AST.ProveExpr {
  if (expr.kind === "hole") return expr;
  if (expr.kind === "ident") {
    return bindings.get(expr.name) ?? expr;
  }
  if (expr.kind === "let") {
    const newValue = substituteAll(expr.value, bindings);
    // Shadowing: remove binding for the let-bound name in the body
    const innerBindings = new Map(bindings);
    innerBindings.delete(expr.name);
    return { kind: "let", name: expr.name, value: newValue, body: substituteAll(expr.body, innerBindings) };
  }
  if (expr.kind === "pi") {
    const newDomain = substituteAll(expr.domain, bindings);
    const innerBindings = new Map(bindings);
    innerBindings.delete(expr.param);
    return { kind: "pi", param: expr.param, domain: newDomain, codomain: substituteAll(expr.codomain, innerBindings) };
  }
  if (expr.kind === "sigma") {
    const newDomain = substituteAll(expr.domain, bindings);
    const innerBindings = new Map(bindings);
    innerBindings.delete(expr.param);
    return { kind: "sigma", param: expr.param, domain: newDomain, codomain: substituteAll(expr.codomain, innerBindings) };
  }
  if (expr.kind === "lambda") {
    const newType = substituteAll(expr.paramType, bindings);
    const innerBindings = new Map(bindings);
    innerBindings.delete(expr.param);
    return { kind: "lambda", param: expr.param, paramType: newType, body: substituteAll(expr.body, innerBindings) };
  }
  if (expr.kind === "match") {
    const replacement = bindings.get(expr.scrutinee);
    const newScrutinee = replacement?.kind === "ident" ? replacement.name : expr.scrutinee;
    return {
      kind: "match",
      scrutinee: newScrutinee,
      cases: expr.cases.map((c) => ({ ...c, body: substituteAll(c.body, bindings) })),
    };
  }
  const newArgs = expr.args.map((a) => substituteAll(a, bindings));
  const replacement = bindings.get(expr.name);
  const newName = replacement?.kind === "ident" ? replacement.name : expr.name;
  return { kind: "call", name: newName, args: newArgs };
}

// ─── Normalization ─────────────────────────────────────────────────
// Reduces type expressions using computational rules.
// Rules are table-driven: each entry matches on the function name and
// first-argument shape, producing a result from the normalized args.
//
// Built-in rules provide defaults (fst/snd for Sigma projections).
// User-declared `compute` rules extend/override the table dynamically.

type NormRule = {
  arity: number;
  /** Match when arg[0] is an ident with this name → return result */
  base?: Record<string, (args: AST.ProveExpr[]) => AST.ProveExpr>;
  /** Match when arg[0] is a call with this name → return result (given inner args + outer rest) */
  step?: Record<string, (inner: AST.ProveExpr[], rest: AST.ProveExpr[]) => AST.ProveExpr>;
};

type NormTable = Record<string, NormRule>;

// Built-in rules that are always available (Sigma projections).
const BUILTIN_NORM_RULES: NormTable = {
  fst: { arity: 1, step: { pair: (i) => i[0] } },
  snd: { arity: 1, step: { pair: (i) => i[1] } },
};

// ─── Dynamic norm-table building from ComputeRule[] ────────────────

function substituteComputeResult(
  expr: AST.ProveExpr,
  bindings: Map<string, AST.ProveExpr>,
): AST.ProveExpr {
  if (expr.kind === "hole" || expr.kind === "match") return expr;
  if (expr.kind === "ident") return bindings.get(expr.name) ?? expr;
  if (expr.kind === "let") {
    return { kind: "let", name: expr.name, value: substituteComputeResult(expr.value, bindings), body: substituteComputeResult(expr.body, bindings) };
  }
  if (expr.kind === "pi" || expr.kind === "sigma") {
    return { kind: expr.kind, param: expr.param, domain: substituteComputeResult(expr.domain, bindings), codomain: substituteComputeResult(expr.codomain, bindings) };
  }
  if (expr.kind === "lambda") {
    return { kind: "lambda", param: expr.param, paramType: substituteComputeResult(expr.paramType, bindings), body: substituteComputeResult(expr.body, bindings) };
  }
  const newArgs = expr.args.map((a) => substituteComputeResult(a, bindings));
  const replacement = bindings.get(expr.name);
  const newName = replacement?.kind === "ident" ? replacement.name : expr.name;
  return { kind: "call", name: newName, args: newArgs };
}

function buildNormTable(computeRules: ComputeRule[]): NormTable {
  const table: NormTable = { ...BUILTIN_NORM_RULES };

  // Group equations by function name
  const groups = new Map<string, ComputeRule[]>();
  for (const r of computeRules) {
    if (!groups.has(r.funcName)) groups.set(r.funcName, []);
    groups.get(r.funcName)!.push(r);
  }

  for (const [funcName, equations] of groups) {
    const arity = equations[0].args.length;
    const base: Record<string, (args: AST.ProveExpr[]) => AST.ProveExpr> = {};
    const step: Record<string, (inner: AST.ProveExpr[], rest: AST.ProveExpr[]) => AST.ProveExpr> = {};

    for (const eq of equations) {
      const firstArg = eq.args[0];
      if (firstArg.kind === "ctor") {
        if (firstArg.args.length === 0) {
          // Base case: nullary constructor (e.g., Zero, True, Nil)
          base[firstArg.name] = (matchedArgs: AST.ProveExpr[]) => {
            const bindings = new Map<string, AST.ProveExpr>();
            for (let i = 1; i < eq.args.length; i++) {
              if (eq.args[i].kind === "var") {
                bindings.set(eq.args[i].name, matchedArgs[i]);
              }
            }
            return substituteComputeResult(eq.result, bindings);
          };
        } else {
          // Step case: constructor with subcomponents (e.g., Succ(k), Cons(h,t))
          step[firstArg.name] = (inner: AST.ProveExpr[], rest: AST.ProveExpr[]) => {
            const bindings = new Map<string, AST.ProveExpr>();
            for (let i = 0; i < firstArg.args.length; i++) {
              bindings.set(firstArg.args[i], inner[i]);
            }
            for (let i = 1; i < eq.args.length; i++) {
              if (eq.args[i].kind === "var") {
                bindings.set(eq.args[i].name, rest[i - 1]);
              }
            }
            return substituteComputeResult(eq.result, bindings);
          };
        }
      }
    }

    // Merge with existing entry if present (e.g., user extending a built-in)
    const existing = table[funcName];
    if (existing) {
      table[funcName] = {
        arity: existing.arity,
        base: { ...existing.base, ...base },
        step: { ...existing.step, ...step },
      };
    } else {
      table[funcName] = { arity, base, step };
    }
  }

  return table;
}

// Module-level active norm table — set by entry points before type-checking.
// Safe because all type-checking is synchronous and single-threaded.
let activeNormTable: NormTable = BUILTIN_NORM_RULES;

export function withNormTable<T>(rules: ComputeRule[], fn: () => T): T {
  const prev = activeNormTable;
  activeNormTable = rules.length > 0 ? buildNormTable(rules) : BUILTIN_NORM_RULES;
  try { return fn(); }
  finally { activeNormTable = prev; }
}

function normalize(expr: AST.ProveExpr): AST.ProveExpr {
  // Universe level normalization: Type → Type(0), Type1 → Type(1), etc.
  if (expr.kind === "ident") {
    if (expr.name === "Type") return app("Type", ident("0"));
    const m = expr.name.match(/^Type(\d+)$/);
    if (m) return app("Type", ident(m[1]));
    return expr;
  }
  if (expr.kind === "hole" || expr.kind === "match") return expr;
  if (expr.kind === "let") {
    // Inline the let binding: let x = v in body → body[x := v]
    const normValue = normalize(expr.value);
    return normalize(substitute(expr.body, expr.name, normValue));
  }
  if (expr.kind === "pi") {
    return { kind: "pi", param: expr.param, domain: normalize(expr.domain), codomain: normalize(expr.codomain) };
  }
  if (expr.kind === "sigma") {
    return { kind: "sigma", param: expr.param, domain: normalize(expr.domain), codomain: normalize(expr.codomain) };
  }
  if (expr.kind === "lambda") {
    return { kind: "lambda", param: expr.param, paramType: normalize(expr.paramType), body: normalize(expr.body) };
  }

  const args = expr.args.map(normalize);
  const e: AST.ProveExpr = { kind: "call", name: expr.name, args };

  // Table-driven reduction (uses active norm table)
  const rule = activeNormTable[e.name];
  if (rule && e.args.length === rule.arity) {
    const a0 = e.args[0];
    if (a0.kind === "ident" && rule.base?.[a0.name]) {
      return normalize(rule.base[a0.name](e.args));
    }
    if (a0.kind === "call" && rule.step?.[a0.name]) {
      return normalize(rule.step[a0.name](a0.args, e.args.slice(1)));
    }
  }

  // wrec(sup(a₁,…,aₙ), step) → step(a₁,…,aₙ)
  if (
    e.name === "wrec" && e.args.length === 2 &&
    e.args[0].kind === "call" && (e.args[0].name === "sup" || e.args[0].name === "Sup") &&
    e.args[1].kind === "ident"
  ) {
    return normalize(app(e.args[1].name, ...e.args[0].args));
  }

  return e;
}

// ─── Universe levels ───────────────────────────────────────────────
// Cumulative universe hierarchy: Type₀ : Type₁ : Type₂ : …

/** Parse universe level from a type expression.
 *  Returns the level (≥ 0) if the expression is a universe, or -1 otherwise. */
export function universeLevel(type: AST.ProveExpr): number {
  const n = normalize(type);
  if (n.kind === "call" && n.name === "Type" && n.args.length === 1 &&
      n.args[0].kind === "ident" && /^\d+$/.test(n.args[0].name)) {
    return parseInt(n.args[0].name);
  }
  return -1;
}

/** Compute which universe level a type expression inhabits.
 *  Type₀ → 1, Type₁ → 2, Nat → 0, Eq(a,b) → 0, Sigma → max of components. */
export function typeUniverse(type: AST.ProveExpr): number {
  const uLevel = universeLevel(type);
  if (uLevel >= 0) return uLevel + 1;
  const n = normalize(type);
  if (n.kind === "ident") return 0;
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

// ─── Expression-level pattern substitution ────────────────────────
// Replaces all occurrences of `pattern` with `replacement` in `expr`.
// Used by subst/transport to rewrite types through equality proofs.

function substituteExprPattern(
  expr: AST.ProveExpr,
  pattern: AST.ProveExpr,
  replacement: AST.ProveExpr,
): AST.ProveExpr {
  if (exprEqual(expr, pattern)) return replacement;
  if (expr.kind === "let") {
    return {
      kind: "let",
      name: expr.name,
      value: substituteExprPattern(expr.value, pattern, replacement),
      body: substituteExprPattern(expr.body, pattern, replacement),
    };
  }
  if (expr.kind === "pi") {
    return {
      kind: "pi", param: expr.param,
      domain: substituteExprPattern(expr.domain, pattern, replacement),
      codomain: substituteExprPattern(expr.codomain, pattern, replacement),
    };
  }
  if (expr.kind === "sigma") {
    return {
      kind: "sigma", param: expr.param,
      domain: substituteExprPattern(expr.domain, pattern, replacement),
      codomain: substituteExprPattern(expr.codomain, pattern, replacement),
    };
  }
  if (expr.kind === "lambda") {
    return {
      kind: "lambda", param: expr.param,
      paramType: substituteExprPattern(expr.paramType, pattern, replacement),
      body: substituteExprPattern(expr.body, pattern, replacement),
    };
  }
  if (expr.kind === "match") {
    return {
      kind: "match",
      scrutinee: expr.scrutinee,
      cases: expr.cases.map((c) => ({ ...c, body: substituteExprPattern(c.body, pattern, replacement) })),
    };
  }
  if (expr.kind !== "call") return expr;
  const newArgs = expr.args.map((a) => substituteExprPattern(a, pattern, replacement));
  return { kind: "call", name: expr.name, args: newArgs };
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

  // Let → infer type of body with binding in scope
  if (expr.kind === "let") {
    const valResult = inferType(expr.value, ctx);
    if (!valResult.ok) return valResult;
    const innerBindings = new Map(ctx.caseBindings);
    innerBindings.set(expr.name, valResult.type);
    const innerCtx: ProveCtx = { ...ctx, caseBindings: innerBindings };
    return inferType(expr.body, innerCtx);
  }

  // Pi type → its type is a universe
  if (expr.kind === "pi") {
    return { ok: true, type: app("Type", ident("0")) };
  }

  // Sigma type → its type is a universe
  if (expr.kind === "sigma") {
    return { ok: true, type: app("Type", ident("0")) };
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

  // Generalized congruence: cong_X(proof, c1, ..., cn) where X is a constructor.
  // The proof applies to the LAST position; c1..cn are constants for earlier positions.
  //   cong_succ(p)       : Eq(Succ(a), Succ(b))       when p : Eq(a, b)
  //   cong_cons(p, h)    : Eq(Cons(h, a), Cons(h, b)) when p : Eq(a, b)
  //   cong_pair(p, q, v) : ... etc for any constructor
  if (name.startsWith("cong_") && args.length >= 1) {
    const suffix = name.slice(5);
    const constructorName = suffix.charAt(0).toUpperCase() + suffix.slice(1);
    const inner = inferType(args[0], ctx);
    if (!inner.ok) return inner;
    const eq = extractEq(inner.type);
    if (!eq) {
      return { ok: false, error: `${name} first argument must have Eq type, got ${exprToString(inner.type)}` };
    }
    const constants = args.slice(1);
    return {
      ok: true,
      type: app("Eq", app(constructorName, ...constants, eq.left), app(constructorName, ...constants, eq.right)),
    };
  }

  // sym(p) : Eq(b, a) when p : Eq(a, b)
  if (name === "sym" && args.length === 1) {
    const inner = inferType(args[0], ctx);
    if (!inner.ok) return inner;
    const eq = extractEq(inner.type);
    if (!eq) {
      return { ok: false, error: `sym argument must have Eq type, got ${exprToString(inner.type)}` };
    }
    return { ok: true, type: app("Eq", eq.right, eq.left) };
  }

  // trans(p, q) : Eq(a, c) when p : Eq(a, b), q : Eq(b, c)
  if (name === "trans" && args.length === 2) {
    const t1 = inferType(args[0], ctx);
    if (!t1.ok) return t1;
    const t2 = inferType(args[1], ctx);
    if (!t2.ok) return t2;
    const eq1 = extractEq(t1.type);
    const eq2 = extractEq(t2.type);
    if (!eq1 || !eq2) {
      return { ok: false, error: `trans arguments must have Eq types` };
    }
    // Check middle types match (after normalization)
    if (!exprEqual(normalize(eq1.right), normalize(eq2.left))) {
      return {
        ok: false,
        error: `trans: middle types don't match: ${exprToString(normalize(eq1.right))} vs ${exprToString(normalize(eq2.left))}`,
      };
    }
    return { ok: true, type: app("Eq", eq1.left, eq2.right) };
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

  // subst(p, e) : T[a := b]  where p : Eq(a, b) and e : T
  // Transport / J elimination: rewrites the type of e through equality p.
  if (name === "subst" && args.length === 2) {
    const pResult = inferType(args[0], ctx);
    if (!pResult.ok) return pResult;
    const eq = extractEq(normalize(pResult.type));
    if (!eq) {
      return { ok: false, error: `subst first argument must have Eq type, got ${exprToString(pResult.type)}` };
    }
    const eResult = inferType(args[1], ctx);
    if (!eResult.ok) return eResult;
    const a = normalize(eq.left);
    const b = normalize(eq.right);
    return { ok: true, type: normalize(substituteExprPattern(normalize(eResult.type), a, b)) };
  }

  // Recursive call to a prove-declared agent
  if (name === ctx.prove.name) {
    if (!ctx.prove.returnType) {
      return { ok: false, error: `recursive call to ${name} but no return type declared` };
    }
    // Substitute args into the declared proposition (simultaneous)
    // Only explicit params receive arguments; implicit ones are skipped.
    const bindings = new Map<string, AST.ProveExpr>();
    const explicitNames = ctx.prove.params.filter((p) => !p.implicit).map((p) => p.name);
    for (let i = 0; i < args.length && i < explicitNames.length; i++) {
      bindings.set(explicitNames[i], args[i]);
    }
    return { ok: true, type: normalize(substituteAll(ctx.prove.returnType, bindings)) };
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
    const bindings = new Map<string, AST.ProveExpr>();
    const explicitNames = proved.params.filter((p) => !p.implicit).map((p) => p.name);
    for (let i = 0; i < args.length && i < explicitNames.length; i++) {
      bindings.set(explicitNames[i], args[i]);
    }
    return { ok: true, type: normalize(substituteAll(proved.returnType, bindings)) };
  }

  // Constructor application: infer type from data declaration
  // e.g., Succ(x) : Nat, Cons(h, t) : List, Zero : Nat (handled below for ident)
  const ctorInfo = ctx.constructorTyping.get(name);
  if (ctorInfo) {
    return { ok: true, type: constructorReturnType(ctorInfo) };
  }

  return { ok: false, error: `unknown proof combinator '${name}'` };
}

function extractEq(
  type: AST.ProveExpr,
): { left: AST.ProveExpr; right: AST.ProveExpr } | null {
  if (type.kind === "call" && type.name === "Eq" && type.args.length === 2) {
    return { left: type.args[0], right: type.args[1] };
  }
  return null;
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
    return exprEqual(normalize(reqEq.left), normalize(reqEq.right));
  }
  return exprEqual(normalize(infEq.left), normalize(reqEq.left)) &&
    exprEqual(normalize(infEq.right), normalize(reqEq.right));
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

  // 3. Cross-lemma calls
  const availableVars = [
    ...[...ctx.caseBindings.keys()].map(ident),
    ...auxParams(ctx.prove.params).map((p) => ident(p.name)),
  ];
  const allLemmaCalls: AST.ProveExpr[] = [];
  for (const [lemmaName, lemma] of ctx.provedCtx) {
    if (lemma.params.length <= availableVars.length) {
      const call = app(lemmaName, ...availableVars.slice(0, lemma.params.length));
      allLemmaCalls.push(call);
      tryAdd(call);
    }
  }

  // 4. sym wrappers
  for (const inner of [...allIHs, ...allLemmaCalls]) tryAdd(app("sym", inner));

  // 5. cong_X wrapping — if goal is Eq(X(...,a), X(...,b))
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
): { ctx: ProveCtx; expectedType: AST.ProveExpr } {
  const consExpr: AST.ProveExpr = caseArm.bindings.length > 0
    ? app(caseArm.pattern, ...caseArm.bindings.map(ident))
    : ident(caseArm.pattern);
  // Build typed caseBindings: look up constructor field types when available
  const { bindings: caseBindings, types: bindingTypes } = buildTypedBindings(caseArm, constructorTyping);
  return {
    ctx: {
      prove,
      caseBindings,
      bindingTypes,
      provedCtx,
      constructorTyping,
      constructorsByType,
    },
    expectedType: normalize(substitute(prove.returnType!, inductionParam(prove.params)!.name, consExpr)),
  };
}

/** Build a proof derivation tree for a typed prove block. */
export function buildProofTree(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext = new Map(),
  computeRules?: ComputeRule[],
  constructorTyping?: ConstructorTyping,
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
  }); // end withNormTable
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
  if (expr.kind !== "call") return expr;  if (expr.name === "exact" && expr.args.length === 1) return stripTacticSugar(expr.args[0]);
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

// ─── Termination checking (structural recursion) ───────────────────
// Verifies that every recursive call in a prove body uses a
// structurally smaller argument — at least one explicit argument must
// be a case binding (a subcomponent of a matched variable).

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

function checkTermination(
  prove: AST.ProveDecl,
): string[] {
  const errors: string[] = [];
  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue;
    const topBindings = new Set(caseArm.bindings);
    const recCalls = collectRecursiveCalls(caseArm.body, prove.name, topBindings);
    for (const { call, bindings } of recCalls) {
      if (call.kind !== "call" || call.args.length === 0) continue;
      // At least one argument must be a case binding (structurally smaller)
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

// ─── Exhaustiveness checking ───────────────────────────────────────
// When the first param has a type annotation (e.g., n : Nat) and we
// know the constructors for that type, check that all are covered.

function checkExhaustiveness(
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
): string[] {
  return withNormTable(computeRules ?? [], () => {
  const ctorTyping = constructorTyping ?? new Map();
  const exhaustErrors = constructorsByType
    ? checkExhaustiveness(prove, constructorsByType)
    : [];
  const termErrors = checkTermination(prove);
  if (!prove.returnType) return [...exhaustErrors, ...termErrors];

  const errors: string[] = [];

  for (const caseArm of prove.cases) {
    const { ctx, expectedType: requiredType } = caseCtx(prove, caseArm, provedCtx, ctorTyping, constructorsByType);
    const prefix = `prove ${prove.name}, case ${caseArm.pattern}`;
    const rawBody = caseArm.body;
    const reqEq = extractEq(requiredType);

    // Handle conv — goal proved by definitional equality (both sides normalize to same term)
    // Check on raw body BEFORE stripTacticSugar (which would convert conv → refl)
    if ((rawBody.kind === "ident" && rawBody.name === "conv") ||
        (rawBody.kind === "call" && rawBody.name === "conv" && rawBody.args.length === 0)) {
      if (reqEq && exprEqual(normalize(reqEq.left), normalize(reqEq.right))) continue;
      errors.push(`${prefix}: conv failed — sides are not definitionally equal\n  goal: ${exprToString(requiredType)}`);
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

    const body = stripTacticSugar(rawBody);

    // Handle rewrite(proof) — contextual goal-rewriting check
    if (body.kind === "call" && body.name === "rewrite" && body.args.length === 1) {
      const proofResult = inferType(body.args[0], ctx);
      if (!proofResult.ok) {
        if (proofResult.error !== "hole") errors.push(`${prefix}: ${proofResult.error}`);
        continue;
      }
      const proofEq = extractEq(normalize(proofResult.type));
      if (!proofEq || !reqEq) {
        errors.push(`${prefix}: rewrite requires Eq types on both proof and goal`);
        continue;
      }
      const a = normalize(proofEq.left), b = normalize(proofEq.right);
      const lhs = normalize(reqEq.left), rhs = normalize(reqEq.right);
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
    if (reqEq && infEq) {
      if (!eqTypeMatches(inferred.type, requiredType)) {
        errors.push(`${prefix}: type mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
      }
      continue;
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
      if (!eqTypeMatches(infProofType, expectedPred) && !exprEqual(normalize(infProofType), expectedPred)) {
        errors.push(`${prefix}: Sigma predicate mismatch\n  expected: ${exprToString(expectedPred)}\n  inferred: ${exprToString(normalize(infProofType))}`);
      }
      continue;
    }
    if (reqSigma || (inferred.type.kind === "call" && inferred.type.name === "Sigma")) {
      errors.push(`${prefix}: type structure mismatch\n  expected: ${exprToString(requiredType)}\n  inferred: ${exprToString(normalize(inferred.type))}`);
    }
  }

  return [...exhaustErrors, ...termErrors, ...errors];
  }); // end withNormTable
}

// ─── Assumption resolution ─────────────────────────────────────────
// Resolves `assumption` in prove case bodies to the first matching proof term.
// Must be called BEFORE type-checking and desugaring.

export function resolveAssumptions(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveAssumptionExpr(caseArm.body, prove, caseArm, provedCtx);
    if (resolved !== caseArm.body) {
      changed = true;
      return { ...caseArm, body: resolved };
    }
    return caseArm;
  });
  return changed ? { ...prove, cases: newCases } : prove;
}

function resolveAssumptionExpr(
  expr: AST.ProveExpr,
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
): AST.ProveExpr {
  if (expr.kind === "ident" && expr.name === "assumption") {
    const { ctx, expectedType: goal } = caseCtx(prove, caseArm, provedCtx);
    const candidates = searchCandidates(ctx, goal);
    if (candidates.length > 0) return parseProofString(candidates[0]);
    return expr;
  }
  if (expr.kind === "match") {
    let changed = false;
    const newCases = expr.cases.map((c) => {
      const r = resolveAssumptionExpr(c.body, prove, caseArm, provedCtx);
      if (r !== c.body) changed = true;
      return { ...c, body: r };
    });
    return changed ? { kind: "match", scrutinee: expr.scrutinee, cases: newCases } : expr;
  }
  if (expr.kind === "call") {
    let changed = false;
    const newArgs = expr.args.map((a) => {
      const r = resolveAssumptionExpr(a, prove, caseArm, provedCtx);
      if (r !== a) changed = true;
      return r;
    });
    return changed ? { kind: "call", name: expr.name, args: newArgs } : expr;
  }
  return expr;
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

// ─── Simp resolution ───────────────────────────────────────────────
// Resolves `simp` in prove case bodies to a concrete proof term.
// Strategy: conv (definitional equality) → assumption search → rewrite with lemmas.
// Must be called BEFORE type-checking and desugaring.

export function resolveSimp(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[] = [],
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveSimpExpr(caseArm.body, prove, caseArm, provedCtx, computeRules);
    if (resolved !== caseArm.body) {
      changed = true;
      return { ...caseArm, body: resolved };
    }
    return caseArm;
  });
  return changed ? { ...prove, cases: newCases } : prove;
}

function resolveSimpExpr(
  expr: AST.ProveExpr,
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): AST.ProveExpr {
  if (expr.kind === "ident" && expr.name === "simp") {
    return withNormTable(computeRules, () => {
      const { ctx, expectedType: goal } = caseCtx(prove, caseArm, provedCtx);

      // 1. conv: if both sides normalize to same term → refl
      const goalEq = extractEq(normalize(goal));
      if (goalEq && exprEqual(normalize(goalEq.left), normalize(goalEq.right))) {
        return ident("refl") as AST.ProveExpr;
      }

      // 2. assumption-style search
      const candidates = searchCandidates(ctx, goal);
      if (candidates.length > 0) return parseProofString(candidates[0]);

      // 3. one-step rewrite with each available lemma
      if (goalEq) {
        const lemmaProof = trySimpRewrite(ctx, goalEq);
        if (lemmaProof) return lemmaProof;
      }

      return expr; // leave as simp — type checker will report the error
    });
  }
  if (expr.kind === "let") {
    const newValue = resolveSimpExpr(expr.value, prove, caseArm, provedCtx, computeRules);
    const newBody = resolveSimpExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newValue !== expr.value || newBody !== expr.body) return { kind: "let", name: expr.name, value: newValue, body: newBody };
    return expr;
  }
  if (expr.kind === "lambda") {
    const newBody = resolveSimpExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newBody !== expr.body) return { kind: "lambda", param: expr.param, paramType: expr.paramType, body: newBody };
    return expr;
  }
  if (expr.kind === "match") {
    let changed = false;
    const newCases = expr.cases.map((c) => {
      const r = resolveSimpExpr(c.body, prove, caseArm, provedCtx, computeRules);
      if (r !== c.body) changed = true;
      return { ...c, body: r };
    });
    return changed ? { kind: "match", scrutinee: expr.scrutinee, cases: newCases } : expr;
  }
  if (expr.kind === "call") {
    let changed = false;
    const newArgs = expr.args.map((a) => {
      const r = resolveSimpExpr(a, prove, caseArm, provedCtx, computeRules);
      if (r !== a) changed = true;
      return r;
    });
    return changed ? { kind: "call", name: expr.name, args: newArgs } : expr;
  }
  return expr;
}

/** Try to close an equality goal by rewriting one side with an available lemma,
 *  then checking if the result matches the other side after normalization. */
function trySimpRewrite(
  ctx: ProveCtx,
  goalEq: { left: AST.ProveExpr; right: AST.ProveExpr },
): AST.ProveExpr | null {
  const lhs = normalize(goalEq.left);
  const rhs = normalize(goalEq.right);

  // Collect all available equational lemmas as { call, left, right }
  const lemmas: { proof: AST.ProveExpr; left: AST.ProveExpr; right: AST.ProveExpr }[] = [];

  // IH calls
  const auxArgs = auxParams(ctx.prove.params).map((p) => ident(p.name));
  for (const b of ctx.caseBindings.keys()) {
    const call = app(ctx.prove.name, ident(b), ...auxArgs);
    const r = inferType(call, ctx);
    if (r.ok) {
      const eq = extractEq(normalize(r.type));
      if (eq) lemmas.push({ proof: call, left: normalize(eq.left), right: normalize(eq.right) });
    }
  }

  // Cross-lemma calls
  const availableVars = [
    ...[...ctx.caseBindings.keys()].map(ident),
    ...auxParams(ctx.prove.params).map((p) => ident(p.name)),
  ];
  for (const [lemmaName, lemma] of ctx.provedCtx) {
    const explicitParams = lemma.params.filter((p) => !p.implicit);
    if (explicitParams.length <= availableVars.length) {
      const call = app(lemmaName, ...availableVars.slice(0, explicitParams.length));
      const r = inferType(call, ctx);
      if (r.ok) {
        const eq = extractEq(normalize(r.type));
        if (eq) lemmas.push({ proof: call, left: normalize(eq.left), right: normalize(eq.right) });
      }
    }
  }

  // Try L→R rewriting on lhs to reach rhs
  for (const lem of lemmas) {
    const rewritten = normalize(substituteExprPattern(lhs, lem.left, lem.right));
    if (exprEqual(rewritten, rhs)) {
      // lhs[l↦r] = rhs, so: trans(rewrite(lemma, lhs_proof), ...) — but simpler: subst
      // Actually the simplest proof: the lemma itself rewrites the goal
      return app("rewrite", lem.proof);
    }
  }

  // Try R→L rewriting (sym) on lhs to reach rhs
  for (const lem of lemmas) {
    const rewritten = normalize(substituteExprPattern(lhs, lem.right, lem.left));
    if (exprEqual(rewritten, rhs)) {
      return app("rewrite", app("sym", lem.proof));
    }
  }

  return null;
}

// ─── Decide tactic ─────────────────────────────────────────────────
// Proves Eq(a, b) when both sides are ground (no free variables) and
// normalize to structurally identical terms.

export function resolveDecide(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[] = [],
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveDecideExpr(caseArm.body, prove, caseArm, provedCtx, computeRules);
    if (resolved !== caseArm.body) {
      changed = true;
      return { ...caseArm, body: resolved };
    }
    return caseArm;
  });
  return changed ? { ...prove, cases: newCases } : prove;
}

function isGroundTerm(expr: AST.ProveExpr, caseBindings: Map<string, AST.ProveExpr>): boolean {
  if (expr.kind === "ident") return !caseBindings.has(expr.name);
  if (expr.kind === "call") return expr.args.every(a => isGroundTerm(a, caseBindings));
  if (expr.kind === "let") return isGroundTerm(expr.value, caseBindings) && isGroundTerm(expr.body, caseBindings);
  if (expr.kind === "pi" || expr.kind === "sigma") return isGroundTerm(expr.domain, caseBindings) && isGroundTerm(expr.codomain, caseBindings);
  if (expr.kind === "lambda") return isGroundTerm(expr.paramType, caseBindings) && isGroundTerm(expr.body, caseBindings);
  return false;
}

function resolveDecideExpr(
  expr: AST.ProveExpr,
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): AST.ProveExpr {
  if (expr.kind === "ident" && expr.name === "decide") {
    return withNormTable(computeRules, () => {
      const { ctx, expectedType: goal } = caseCtx(prove, caseArm, provedCtx);
      const goalEq = extractEq(normalize(goal));
      if (goalEq) {
        const lhs = normalize(goalEq.left);
        const rhs = normalize(goalEq.right);
        if (isGroundTerm(lhs, ctx.caseBindings) && isGroundTerm(rhs, ctx.caseBindings) && exprEqual(lhs, rhs)) {
          return ident("refl") as AST.ProveExpr;
        }
      }
      return expr;
    });
  }
  if (expr.kind === "let") {
    const newValue = resolveDecideExpr(expr.value, prove, caseArm, provedCtx, computeRules);
    const newBody = resolveDecideExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newValue !== expr.value || newBody !== expr.body) return { kind: "let", name: expr.name, value: newValue, body: newBody };
    return expr;
  }
  if (expr.kind === "lambda") {
    const newBody = resolveDecideExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newBody !== expr.body) return { kind: "lambda", param: expr.param, paramType: expr.paramType, body: newBody };
    return expr;
  }
  if (expr.kind === "match") {
    let changed = false;
    const newCases = expr.cases.map((c) => {
      const r = resolveDecideExpr(c.body, prove, caseArm, provedCtx, computeRules);
      if (r !== c.body) changed = true;
      return { ...c, body: r };
    });    return changed ? { kind: "match", scrutinee: expr.scrutinee, cases: newCases } : expr;
  }
  if (expr.kind === "call") {
    let changed = false;
    const newArgs = expr.args.map((a) => {
      const r = resolveDecideExpr(a, prove, caseArm, provedCtx, computeRules);
      if (r !== a) changed = true;
      return r;
    });
    return changed ? { kind: "call", name: expr.name, args: newArgs } : expr;
  }
  return expr;
}

// ─── Omega tactic ──────────────────────────────────────────────────
// Proves Eq goals over Nat by normalizing both sides and checking if
// they match after compute-rule reduction. Falls back to congruence
// (cong_succ) with IH when direct normalization is insufficient.

export function resolveOmega(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[] = [],
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveOmegaExpr(caseArm.body, prove, caseArm, provedCtx, computeRules);
    if (resolved !== caseArm.body) {
      changed = true;
      return { ...caseArm, body: resolved };
    }
    return caseArm;
  });
  return changed ? { ...prove, cases: newCases } : prove;
}

function resolveOmegaExpr(
  expr: AST.ProveExpr,
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): AST.ProveExpr {
  if (expr.kind === "ident" && expr.name === "omega") {
    return withNormTable(computeRules, () => {
      const { ctx, expectedType: goal } = caseCtx(prove, caseArm, provedCtx);
      const goalEq = extractEq(normalize(goal));
      if (!goalEq) return expr;

      const lhs = normalize(goalEq.left);
      const rhs = normalize(goalEq.right);

      // 1. Direct normalization equality → refl
      if (exprEqual(lhs, rhs)) return ident("refl") as AST.ProveExpr;

      // 2. Try congruence: if both sides are Succ(X) and Succ(Y),
      //    try to prove Eq(X, Y) recursively
      const congResult = tryCongSucc(lhs, rhs, ctx);
      if (congResult) return congResult;

      // 3. Try IH application + rewrite
      const rwResult = trySimpRewrite(ctx, goalEq);
      if (rwResult) return rwResult;

      // 4. Try cong_succ(IH)
      if (lhs.kind === "call" && lhs.name === "Succ" && lhs.args.length === 1 &&
          rhs.kind === "call" && rhs.name === "Succ" && rhs.args.length === 1) {
        const innerGoal = app("Eq", lhs.args[0], rhs.args[0]);
        const innerRw = trySimpRewrite(ctx, { left: lhs.args[0], right: rhs.args[0] });
        if (innerRw) return app("cong_succ", innerRw);
      }

      return expr;
    });
  }
  if (expr.kind === "let") {
    const newValue = resolveOmegaExpr(expr.value, prove, caseArm, provedCtx, computeRules);
    const newBody = resolveOmegaExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newValue !== expr.value || newBody !== expr.body) return { kind: "let", name: expr.name, value: newValue, body: newBody };
    return expr;
  }
  if (expr.kind === "lambda") {
    const newBody = resolveOmegaExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newBody !== expr.body) return { kind: "lambda", param: expr.param, paramType: expr.paramType, body: newBody };
    return expr;
  }
  if (expr.kind === "match") {
    let changed = false;
    const newCases = expr.cases.map((c) => {
      const r = resolveOmegaExpr(c.body, prove, caseArm, provedCtx, computeRules);
      if (r !== c.body) changed = true;
      return { ...c, body: r };
    });
    return changed ? { kind: "match", scrutinee: expr.scrutinee, cases: newCases } : expr;
  }
  if (expr.kind === "call") {
    let changed = false;
    const newArgs = expr.args.map((a) => {
      const r = resolveOmegaExpr(a, prove, caseArm, provedCtx, computeRules);
      if (r !== a) changed = true;
      return r;
    });
    return changed ? { kind: "call", name: expr.name, args: newArgs } : expr;
  }
  return expr;
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
      if (eq && exprEqual(normalize(eq.left), innerLhs) && exprEqual(normalize(eq.right), innerRhs)) {
        return app("cong_succ", ihCall);
      }
      // Also try with sym
      if (eq && exprEqual(normalize(eq.left), innerRhs) && exprEqual(normalize(eq.right), innerLhs)) {
        return app("cong_succ", app("sym", ihCall));
      }
    }
  }
  return null;
}

// ─── Auto tactic ───────────────────────────────────────────────────
// Depth-bounded proof search combining conv, assumption, simp, and
// congruence reasoning. Tries progressively deeper strategies.

export function resolveAuto(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[] = [],
): AST.ProveDecl {
  if (!prove.returnType) return prove;

  let changed = false;
  const newCases = prove.cases.map((caseArm) => {
    const resolved = resolveAutoExpr(caseArm.body, prove, caseArm, provedCtx, computeRules);
    if (resolved !== caseArm.body) {
      changed = true;
      return { ...caseArm, body: resolved };
    }
    return caseArm;
  });
  return changed ? { ...prove, cases: newCases } : prove;
}

function resolveAutoExpr(
  expr: AST.ProveExpr,
  prove: AST.ProveDecl,
  caseArm: AST.ProveCase,
  provedCtx: ProvedContext,
  computeRules: ComputeRule[],
): AST.ProveExpr {
  if (expr.kind === "ident" && expr.name === "auto") {
    return withNormTable(computeRules, () => {
      const { ctx, expectedType: goal } = caseCtx(prove, caseArm, provedCtx);
      const result = autoSearch(goal, ctx, 3);
      return result ?? expr;
    });
  }
  if (expr.kind === "let") {
    const newValue = resolveAutoExpr(expr.value, prove, caseArm, provedCtx, computeRules);
    const newBody = resolveAutoExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newValue !== expr.value || newBody !== expr.body) return { kind: "let", name: expr.name, value: newValue, body: newBody };
    return expr;
  }
  if (expr.kind === "lambda") {
    const newBody = resolveAutoExpr(expr.body, prove, caseArm, provedCtx, computeRules);
    if (newBody !== expr.body) return { kind: "lambda", param: expr.param, paramType: expr.paramType, body: newBody };
    return expr;
  }
  if (expr.kind === "match") {
    let changed = false;
    const newCases = expr.cases.map((c) => {
      const r = resolveAutoExpr(c.body, prove, caseArm, provedCtx, computeRules);
      if (r !== c.body) changed = true;
      return { ...c, body: r };
    });
    return changed ? { kind: "match", scrutinee: expr.scrutinee, cases: newCases } : expr;
  }
  if (expr.kind === "call") {
    let changed = false;
    const newArgs = expr.args.map((a) => {
      const r = resolveAutoExpr(a, prove, caseArm, provedCtx, computeRules);
      if (r !== a) changed = true;
      return r;
    });
    return changed ? { kind: "call", name: expr.name, args: newArgs } : expr;
  }
  return expr;
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
  if (goalEq && exprEqual(normalize(goalEq.left), normalize(goalEq.right))) {
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
    if (!exprEqual(normalize(nlhs.args[i]), normalize(nrhs.args[i]))) diffs.push(i);
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
