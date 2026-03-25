// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Expression Normalization & Utilities
// Shared types, substitution, equality, and normalization engine.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { CanonicalDef } from "./evaluator.ts";
import { isVMEnabled, vmNormalize, setVMContext, resetVMContext } from "./vm-normalize.ts";

// ─── Record metadata (for eta-reduction of primitive projections) ──

/** Metadata for a record type: constructor name and ordered field (projection) names. */
export type RecordDef = { ctor: string; fields: string[] };

// ─── Shared types ──────────────────────────────────────────────────

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

// ─── ProveExpr helpers ─────────────────────────────────────────────

export function ident(name: string): AST.ProveExpr {
  return { kind: "ident", name };
}

export function app(name: string, ...args: AST.ProveExpr[]): AST.ProveExpr {
  return { kind: "call", name, args };
}

// ─── Substitution ──────────────────────────────────────────────────

export function substitute(
  expr: AST.ProveExpr,
  varName: string,
  value: AST.ProveExpr,
): AST.ProveExpr {
  if (expr.kind === "hole" || expr.kind === "metavar") return expr;
  if (expr.kind === "meta-app") {
    return { kind: "meta-app", id: expr.id, args: expr.args.map(a => substitute(a, varName, value)) };
  }
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
  // call: substitute in name if it matches, and all args
  const newArgs = expr.args.map((a) => substitute(a, varName, value));
  if (expr.name === varName && value.kind === "metavar") {
    return { kind: "meta-app", id: value.id, args: newArgs };
  }
  const newName = expr.name === varName && value.kind === "ident"
    ? value.name
    : expr.name;
  return { kind: "call", name: newName, args: newArgs };
}

// Simultaneous substitution — avoids variable capture when parameter
// names overlap with argument expressions (e.g. calling f(m, k) where
// f's params are (n, m) would corrupt m with sequential substitution).
export function substituteAll(
  expr: AST.ProveExpr,
  bindings: Map<string, AST.ProveExpr>,
): AST.ProveExpr {
  if (expr.kind === "hole" || expr.kind === "metavar") return expr;
  if (expr.kind === "meta-app") {
    return { kind: "meta-app", id: expr.id, args: expr.args.map(a => substituteAll(a, bindings)) };
  }
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
  // If function name maps to a metavar, produce a meta-app (HO applied metavar)
  if (replacement?.kind === "metavar") {
    return { kind: "meta-app", id: replacement.id, args: newArgs };
  }
  const newName = replacement?.kind === "ident" ? replacement.name : expr.name;
  return { kind: "call", name: newName, args: newArgs };
}

// ─── Expression equality (syntactic, after normalization) ──────────

export function exprEqual(a: AST.ProveExpr, b: AST.ProveExpr): boolean {
  if (a.kind === "hole" || b.kind === "hole") return false;
  if (a.kind === "match" || b.kind === "match") return false;
  if (a.kind === "metavar" && b.kind === "metavar") return a.id === b.id;
  if (a.kind === "metavar" || b.kind === "metavar") return false;
  if (a.kind === "meta-app" && b.kind === "meta-app") {
    return a.id === b.id && a.args.length === b.args.length && a.args.every((arg, i) => exprEqual(arg, b.args[i]));
  }
  if (a.kind === "meta-app" || b.kind === "meta-app") return false;
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

// ─── Conversion (definitional equality) ────────────────────────────

export type ConversionResult =
  | { convertible: true }
  | { convertible: false; syntacticallyEqual: boolean; lhsNorm: string; rhsNorm: string };

export function checkConvertible(a: AST.ProveExpr, b: AST.ProveExpr): ConversionResult {
  const synEq = exprEqual(a, b);
  const na = normalize(a);
  const nb = normalize(b);
  if (exprEqual(na, nb)) return { convertible: true };
  return { convertible: false, syntacticallyEqual: synEq, lhsNorm: exprToString(na), rhsNorm: exprToString(nb) };
}

export function convertible(a: AST.ProveExpr, b: AST.ProveExpr): boolean {
  return exprEqual(normalize(a), normalize(b));
}

/** Sort-aware conversion: if `sort` is "SProp", all terms are definitionally equal
 *  (strict proof irrelevance). Otherwise falls back to normal conversion. */
export function convertibleInSort(
  a: AST.ProveExpr,
  b: AST.ProveExpr,
  sort?: "Prop" | "SProp" | number,
): boolean {
  if (sort === "SProp") return true;
  return convertible(a, b);
}

// ─── Expression formatting ─────────────────────────────────────────

const SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉";
function toSubscript(n: number): string {
  return String(n).split("").map((d) => SUBSCRIPTS[parseInt(d)]).join("");
}

export function exprToString(e: AST.ProveExpr): string {
  if (e.kind === "hole") return "?";
  if (e.kind === "metavar") return `?${e.id}`;
  if (e.kind === "meta-app") return `?${e.id}(${e.args.map(exprToString).join(", ")})`;
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

// ─── Expression-level pattern substitution ─────────────────────────

export function substituteExprPattern(
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
  if (expr.kind === "meta-app") {
    return { kind: "meta-app", id: expr.id, args: expr.args.map(a => substituteExprPattern(a, pattern, replacement)) };
  }
  if (expr.kind !== "call") return expr;
  const newArgs = expr.args.map((a) => substituteExprPattern(a, pattern, replacement));
  return { kind: "call", name: expr.name, args: newArgs };
}

// ─── Normalization engine ──────────────────────────────────────────

type NormRule = {
  arity: number;
  base?: Record<string, (args: AST.ProveExpr[]) => AST.ProveExpr>;
  step?: Record<string, (inner: AST.ProveExpr[], rest: AST.ProveExpr[]) => AST.ProveExpr>;
};

type NormTable = Record<string, NormRule>;

export const BUILTIN_NORM_RULES: NormTable = {
  fst: { arity: 1, step: { pair: (i) => i[0] } },
  snd: { arity: 1, step: { pair: (i) => i[1] } },
};

function substituteComputeResult(
  expr: AST.ProveExpr,
  bindings: Map<string, AST.ProveExpr>,
): AST.ProveExpr {
  if (expr.kind === "hole" || expr.kind === "match" || expr.kind === "metavar") return expr;
  if (expr.kind === "meta-app") {
    return { kind: "meta-app", id: expr.id, args: expr.args.map(a => substituteComputeResult(a, bindings)) };
  }
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

export function buildNormTable(computeRules: ComputeRule[]): NormTable {
  const table: NormTable = { ...BUILTIN_NORM_RULES };

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

let activeNormTable: NormTable = BUILTIN_NORM_RULES;
let activeCanonicals: CanonicalDef[] = [];
let activeRecordDefs: Map<string, RecordDef> = new Map();

export function getActiveCanonicals(): CanonicalDef[] {
  return activeCanonicals;
}

export function getActiveRecordDefs(): Map<string, RecordDef> {
  return activeRecordDefs;
}

export function withNormTable<T>(rules: ComputeRule[], fn: () => T, canonicals?: CanonicalDef[], recordDefs?: Map<string, RecordDef>): T {
  const prev = activeNormTable;
  const prevCanonicals = activeCanonicals;
  const prevRecordDefs = activeRecordDefs;
  activeNormTable = rules.length > 0 ? buildNormTable(rules) : BUILTIN_NORM_RULES;
  activeCanonicals = canonicals ?? [];
  activeRecordDefs = recordDefs ?? prevRecordDefs;
  if (isVMEnabled()) setVMContext(rules, activeRecordDefs);
  try { return fn(); }
  finally {
    activeNormTable = prev;
    activeCanonicals = prevCanonicals;
    activeRecordDefs = prevRecordDefs;
    if (isVMEnabled()) {
      if (prev === BUILTIN_NORM_RULES) resetVMContext();
      // Rebuild VM context from restored state if non-builtin
      // (the previous withNormTable's rules are opaque, so we just reset)
    }
  }
}

export function normalize(expr: AST.ProveExpr): AST.ProveExpr {
  // Delegate to VM when enabled (bytecode + memoization)
  if (isVMEnabled()) return vmNormalize(expr);

  // Universe / sort normalization
  if (expr.kind === "ident") {
    if (expr.name === "Type") return app("Type", ident("0"));
    if (expr.name === "Set") return app("Type", ident("0")); // Set = Type₀
    if (expr.name === "Prop") return ident("Prop"); // Prop is a distinct sort
    const m = expr.name.match(/^Type(\d+)$/);
    if (m) return app("Type", ident(m[1]));
    return expr;
  }
  if (expr.kind === "hole" || expr.kind === "match" || expr.kind === "metavar") return expr;
  if (expr.kind === "meta-app") {
    return { kind: "meta-app", id: expr.id, args: expr.args.map(normalize) };
  }
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

  // Record eta-reduction: mkR(f1(x), f2(x), ..., fn(x)) → x
  // when mkR is a record constructor and f1..fn are its ordered projections
  // applied to the same argument x.
  const recDef = activeRecordDefs.get(e.name);
  if (recDef && recDef.ctor === e.name && e.args.length === recDef.fields.length && e.args.length > 0) {
    let base: AST.ProveExpr | null = null;
    let isEta = true;
    for (let i = 0; i < e.args.length; i++) {
      const ai = e.args[i];
      if (ai.kind !== "call" || ai.name !== recDef.fields[i] || ai.args.length !== 1) {
        isEta = false;
        break;
      }
      if (base === null) {
        base = ai.args[0];
      } else if (!exprEqual(base, ai.args[0])) {
        isEta = false;
        break;
      }
    }
    if (isEta && base) return base;
  }

  return e;
}
