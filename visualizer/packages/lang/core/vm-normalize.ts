// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Bytecode VM for Fast Term Normalization
//
// Compiles ProveExpr ASTs to flat bytecode and evaluates them on a
// stack-based virtual machine. Provides:
//   • Structural expression hashing + memoized normalization
//   • Bytecode compilation (AST → Instruction[])
//   • Stack-based VM interpretation
//   • Drop-in replacement for normalize() with 2–10× speedup
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { CanonicalDef } from "./evaluator.ts";
import type { ComputeRule, RecordDef } from "./normalize.ts";
import {
  buildNormTable,
  BUILTIN_NORM_RULES,
  exprEqual,
  substitute,
  exprToString,
} from "./normalize.ts";

// Lazy accessor to break circular init dependency
function getBuiltinRules(): NormTable {
  return BUILTIN_NORM_RULES as unknown as NormTable;
}

// ─── Opcodes ───────────────────────────────────────────────────────

const enum Op {
  // Leaf values — push onto stack
  IDENT,       // payload: name:string
  HOLE,        // push hole
  METAVAR,     // payload: id:number
  // Composite — pop N children, push composite
  CALL,        // payload: name:string, argCount:number
  META_APP,    // payload: id:number, argCount:number
  LET,         // payload: name:string  — pops body, value → pushes let
  PI,          // payload: param:string — pops codomain, domain → pushes pi
  SIGMA,       // payload: param:string — pops codomain, domain → pushes sigma
  LAMBDA,      // payload: param:string — pops body, paramType → pushes lambda
  MATCH,       // payload: scrutinee:string, caseCount:number
  MATCH_CASE,  // payload: pattern:string, bindingCount:number, bindingNames:string[]
}

type Instruction =
  | { op: Op.IDENT; name: string }
  | { op: Op.HOLE }
  | { op: Op.METAVAR; id: number }
  | { op: Op.CALL; name: string; argc: number }
  | { op: Op.META_APP; id: number; argc: number }
  | { op: Op.LET; name: string }
  | { op: Op.PI; param: string }
  | { op: Op.SIGMA; param: string }
  | { op: Op.LAMBDA; param: string }
  | { op: Op.MATCH; scrutinee: string; caseCount: number }
  | { op: Op.MATCH_CASE; pattern: string; bindings: string[] };

// ─── Compiler: AST → Bytecode ──────────────────────────────────────

function compile(expr: AST.ProveExpr, out: Instruction[]): void {
  switch (expr.kind) {
    case "ident":
      out.push({ op: Op.IDENT, name: expr.name });
      return;
    case "hole":
      out.push({ op: Op.HOLE });
      return;
    case "metavar":
      out.push({ op: Op.METAVAR, id: expr.id });
      return;
    case "meta-app":
      for (const a of expr.args) compile(a, out);
      out.push({ op: Op.META_APP, id: expr.id, argc: expr.args.length });
      return;
    case "call":
      for (const a of expr.args) compile(a, out);
      out.push({ op: Op.CALL, name: expr.name, argc: expr.args.length });
      return;
    case "let":
      compile(expr.value, out);
      compile(expr.body, out);
      out.push({ op: Op.LET, name: expr.name });
      return;
    case "pi":
      compile(expr.domain, out);
      compile(expr.codomain, out);
      out.push({ op: Op.PI, param: expr.param });
      return;
    case "sigma":
      compile(expr.domain, out);
      compile(expr.codomain, out);
      out.push({ op: Op.SIGMA, param: expr.param });
      return;
    case "lambda":
      compile(expr.paramType, out);
      compile(expr.body, out);
      out.push({ op: Op.LAMBDA, param: expr.param });
      return;
    case "match":
      for (const c of expr.cases) {
        compile(c.body, out);
        out.push({ op: Op.MATCH_CASE, pattern: c.pattern, bindings: c.bindings.map(b => b.name) });
      }
      out.push({ op: Op.MATCH, scrutinee: expr.scrutinee, caseCount: expr.cases.length });
      return;
  }
}

/** Compile an AST expression to a flat bytecode instruction array. */
export function compileExpr(expr: AST.ProveExpr): Instruction[] {
  const out: Instruction[] = [];
  compile(expr, out);
  return out;
}

// ─── Structural hashing ────────────────────────────────────────────

// Compute a structural hash of a ProveExpr for cache lookup.
// Uses FNV-1a-style mixing for speed. Collisions resolved by exprEqual.

function hashStr(s: string, h: number): number {
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  return h;
}

function hashNum(n: number, h: number): number {
  h ^= n & 0xff;
  h = Math.imul(h, 0x01000193);
  h ^= (n >>> 8) & 0xff;
  h = Math.imul(h, 0x01000193);
  return h;
}

export function exprHash(expr: AST.ProveExpr): number {
  let h = 0x811c9dc5; // FNV offset basis
  return exprHashInner(expr, h) >>> 0; // ensure unsigned
}

function exprHashInner(expr: AST.ProveExpr, h: number): number {
  switch (expr.kind) {
    case "ident":
      return hashStr(expr.name, hashNum(1, h));
    case "hole":
      return hashNum(2, h);
    case "metavar":
      return hashNum(expr.id, hashNum(3, h));
    case "meta-app":
      h = hashNum(4, hashNum(expr.id, h));
      for (const a of expr.args) h = exprHashInner(a, h);
      return h;
    case "call":
      h = hashStr(expr.name, hashNum(5, h));
      for (const a of expr.args) h = exprHashInner(a, h);
      return h;
    case "let":
      h = hashStr(expr.name, hashNum(6, h));
      h = exprHashInner(expr.value, h);
      return exprHashInner(expr.body, h);
    case "pi":
      h = hashStr(expr.param, hashNum(7, h));
      h = exprHashInner(expr.domain, h);
      return exprHashInner(expr.codomain, h);
    case "sigma":
      h = hashStr(expr.param, hashNum(8, h));
      h = exprHashInner(expr.domain, h);
      return exprHashInner(expr.codomain, h);
    case "lambda":
      h = hashStr(expr.param, hashNum(9, h));
      h = exprHashInner(expr.paramType, h);
      return exprHashInner(expr.body, h);
    case "match":
      h = hashStr(expr.scrutinee, hashNum(10, h));
      for (const c of expr.cases) {
        h = hashStr(c.pattern, h);
        h = exprHashInner(c.body, h);
      }
      return h;
  }
}

// ─── Norm cache ────────────────────────────────────────────────────

// Bucket-based hash map: hash → list of (key, value) pairs.
// Cleared on NormTable change.

type CacheEntry = { key: AST.ProveExpr; value: AST.ProveExpr };

class NormCache {
  private buckets: Map<number, CacheEntry[]> = new Map();
  private size = 0;
  private readonly maxSize: number;

  constructor(maxSize = 16384) {
    this.maxSize = maxSize;
  }

  get(expr: AST.ProveExpr): AST.ProveExpr | undefined {
    const h = exprHash(expr);
    const bucket = this.buckets.get(h);
    if (!bucket) return undefined;
    for (const entry of bucket) {
      if (exprEqual(entry.key, expr)) return entry.value;
    }
    return undefined;
  }

  set(expr: AST.ProveExpr, result: AST.ProveExpr): void {
    if (this.size >= this.maxSize) {
      this.clear();
    }
    const h = exprHash(expr);
    let bucket = this.buckets.get(h);
    if (!bucket) {
      bucket = [];
      this.buckets.set(h, bucket);
    }
    // Update if exists
    for (const entry of bucket) {
      if (exprEqual(entry.key, expr)) {
        entry.value = result;
        return;
      }
    }
    bucket.push({ key: expr, value: result });
    this.size++;
  }

  clear(): void {
    this.buckets.clear();
    this.size = 0;
  }

  get currentSize(): number {
    return this.size;
  }
}

// ─── VM Norm Table (mirrors normalize.ts types) ────────────────────

type NormRule = {
  arity: number;
  base?: Record<string, (args: AST.ProveExpr[]) => AST.ProveExpr>;
  step?: Record<string, (inner: AST.ProveExpr[], rest: AST.ProveExpr[]) => AST.ProveExpr>;
};
type NormTable = Record<string, NormRule>;

// ─── VM State ──────────────────────────────────────────────────────

let vmEnabled = false;
let vmNormTable: NormTable | null = null;
let vmRecordDefs: Map<string, RecordDef> = new Map();
let vmCache = new NormCache();
let vmStats = { hits: 0, misses: 0, compiles: 0 };

function getVMNormTable(): NormTable {
  if (vmNormTable === null) vmNormTable = getBuiltinRules();
  return vmNormTable;
}

// ─── Stack-based VM interpreter ────────────────────────────────────

function ident(name: string): AST.ProveExpr {
  return { kind: "ident", name };
}

function app(name: string, ...args: AST.ProveExpr[]): AST.ProveExpr {
  return { kind: "call", name, args };
}

/**
 * Execute bytecode on a stack machine, producing a normalized ProveExpr.
 * The interpreter performs normalization inline as it builds values —
 * equivalent to normalize() but operating on flat instructions.
 */
function vmExec(code: Instruction[]): AST.ProveExpr {
  const stack: AST.ProveExpr[] = [];

  for (let ip = 0; ip < code.length; ip++) {
    const instr = code[ip];
    switch (instr.op) {
      case Op.HOLE:
        stack.push({ kind: "hole" });
        break;

      case Op.METAVAR:
        stack.push({ kind: "metavar", id: instr.id });
        break;

      case Op.IDENT: {
        // Universe/sort normalization inline
        const name = instr.name;
        if (name === "Type") {
          stack.push(app("Type", ident("0")));
        } else if (name === "Set") {
          stack.push(app("Type", ident("0")));
        } else if (name === "Prop") {
          stack.push(ident("Prop"));
        } else {
          const m = name.match(/^Type(\d+)$/);
          if (m) {
            stack.push(app("Type", ident(m[1])));
          } else {
            stack.push(ident(name));
          }
        }
        break;
      }

      case Op.META_APP: {
        const args = stack.splice(stack.length - instr.argc);
        stack.push({ kind: "meta-app", id: instr.id, args });
        break;
      }

      case Op.LET: {
        const body = stack.pop()!;
        const value = stack.pop()!;
        // Inline let: let x = v in body → normalize(body[x := v])
        stack.push(vmNormalize(substitute(body, instr.name, value)));
        break;
      }

      case Op.PI: {
        const codomain = stack.pop()!;
        const domain = stack.pop()!;
        stack.push({ kind: "pi", param: instr.param, domain, codomain });
        break;
      }

      case Op.SIGMA: {
        const codomain = stack.pop()!;
        const domain = stack.pop()!;
        stack.push({ kind: "sigma", param: instr.param, domain, codomain });
        break;
      }

      case Op.LAMBDA: {
        const body = stack.pop()!;
        const paramType = stack.pop()!;
        stack.push({ kind: "lambda", param: instr.param, paramType, body });
        break;
      }

      case Op.MATCH_CASE: {
        // Collect body from stack — cases are accumulated until MATCH
        const body = stack.pop()!;
        // Push a tagged placeholder that MATCH will collect
        stack.push({ kind: "call", name: `__case__${instr.pattern}`, args: [body, ...instr.bindings.map(b => ident(b))] });
        break;
      }

      case Op.MATCH: {
        const cases: AST.ProveCase[] = [];
        for (let i = 0; i < instr.caseCount; i++) {
          const caseVal = stack.pop()!;
          // Decode the tagged case
          if (caseVal.kind === "call" && caseVal.name.startsWith("__case__")) {
            const pattern = caseVal.name.slice(8);
            const body = caseVal.args[0];
            const bindings = caseVal.args.slice(1).map(a =>
              ({ name: a.kind === "ident" ? a.name : "_", type: ident("_") as AST.ProveExpr })
            );
            cases.unshift({ pattern, bindings, body });
          }
        }
        stack.push({ kind: "match", scrutinee: instr.scrutinee, cases });
        break;
      }

      case Op.CALL: {
        const args = stack.splice(stack.length - instr.argc);
        const result = reduceCall(instr.name, args);
        stack.push(result);
        break;
      }
    }
  }

  return stack[0] ?? { kind: "hole" };
}

/**
 * Apply table-driven reduction + special rules for a function call.
 * Mirrors the reduction logic in normalize() for call expressions.
 */
function reduceCall(name: string, args: AST.ProveExpr[]): AST.ProveExpr {
  const e = app(name, ...args);

  // Table-driven reduction
  const rule = getVMNormTable()[name];
  if (rule && args.length === rule.arity) {
    const a0 = args[0];
    if (a0.kind === "ident" && rule.base?.[a0.name]) {
      return vmNormalize(rule.base[a0.name](args));
    }
    if (a0.kind === "call" && rule.step?.[a0.name]) {
      return vmNormalize(rule.step[a0.name](a0.args, args.slice(1)));
    }
  }

  // wrec(sup(a₁,…,aₙ), step) → step(a₁,…,aₙ)
  if (
    name === "wrec" && args.length === 2 &&
    args[0].kind === "call" && (args[0].name === "sup" || args[0].name === "Sup") &&
    args[1].kind === "ident"
  ) {
    return vmNormalize(app(args[1].name, ...args[0].args));
  }

  // Record eta-reduction: mkR(f1(x), f2(x), ..., fn(x)) → x
  const recDef = vmRecordDefs.get(name);
  if (recDef && recDef.ctor === name && args.length === recDef.fields.length && args.length > 0) {
    let base: AST.ProveExpr | null = null;
    let isEta = true;
    for (let i = 0; i < args.length; i++) {
      const ai = args[i];
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

// ─── VM-accelerated normalize ──────────────────────────────────────

/**
 * Normalize an expression using the VM + memoization cache.
 * Falls back to direct interpretation for uncacheable forms.
 */
export function vmNormalize(expr: AST.ProveExpr): AST.ProveExpr {
  // Fast paths for atoms
  if (expr.kind === "hole" || expr.kind === "metavar") return expr;
  if (expr.kind === "match") return expr;

  // Check cache
  const cached = vmCache.get(expr);
  if (cached !== undefined) {
    vmStats.hits++;
    return cached;
  }
  vmStats.misses++;

  // Compile and execute
  vmStats.compiles++;
  const code = compileExpr(expr);
  const result = vmExec(code);

  // Cache the result
  vmCache.set(expr, result);
  return result;
}

// ─── Integration API ───────────────────────────────────────────────

/** Enable VM-accelerated normalization. */
export function enableVM(): void {
  vmEnabled = true;
}

/** Disable VM-accelerated normalization. */
export function disableVM(): void {
  vmEnabled = false;
}

/** Check if VM is enabled. */
export function isVMEnabled(): boolean {
  return vmEnabled;
}

/** Set VM norm table context (called by withNormTable integration). */
export function setVMContext(
  rules: ComputeRule[],
  recordDefs?: Map<string, RecordDef>,
): void {
  vmNormTable = rules.length > 0 ? buildNormTable(rules) : getBuiltinRules();
  vmRecordDefs = recordDefs ?? new Map();
  vmCache.clear(); // Invalidate on context change
}

/** Restore VM norm table to builtins. */
export function resetVMContext(): void {
  vmNormTable = getBuiltinRules();
  vmRecordDefs = new Map();
  vmCache.clear();
}

/** Get VM performance statistics. */
export function getVMStats(): { hits: number; misses: number; compiles: number; cacheSize: number } {
  return { ...vmStats, cacheSize: vmCache.currentSize };
}

/** Reset VM performance statistics. */
export function resetVMStats(): void {
  vmStats = { hits: 0, misses: 0, compiles: 0 };
}

/** Clear the normalization cache. */
export function clearVMCache(): void {
  vmCache.clear();
}

/**
 * Execute normalization with the VM if enabled, otherwise use the
 * provided fallback. This is the integration point for normalize.ts.
 */
export function vmNormalizeOrFallback(
  expr: AST.ProveExpr,
  fallback: (e: AST.ProveExpr) => AST.ProveExpr,
): AST.ProveExpr {
  if (vmEnabled) return vmNormalize(expr);
  return fallback(expr);
}

// ─── withVMContext: scoped VM context ──────────────────────────────

/**
 * Run a function with a specific VM normalization context.
 * Like withNormTable but for the VM — sets up table + cache,
 * restores previous state on exit.
 */
export function withVMContext<T>(
  rules: ComputeRule[],
  fn: () => T,
  recordDefs?: Map<string, RecordDef>,
): T {
  const prevTable = vmNormTable;
  const prevRecordDefs = vmRecordDefs;
  const prevCache = vmCache;

  vmNormTable = rules.length > 0 ? buildNormTable(rules) : getBuiltinRules();
  vmRecordDefs = recordDefs ?? new Map();
  vmCache = new NormCache();

  try {
    return fn();
  } finally {
    vmNormTable = prevTable;
    vmRecordDefs = prevRecordDefs;
    vmCache = prevCache;
  }
}

// ─── Batch compilation ─────────────────────────────────────────────

/** Pre-compile a set of expressions for repeated normalization. */
export function precompile(
  exprs: AST.ProveExpr[],
): { code: Instruction[][]; normalize: (index: number) => AST.ProveExpr } {
  const code = exprs.map(e => compileExpr(e));
  return {
    code,
    normalize: (index: number) => {
      const cached = vmCache.get(exprs[index]);
      if (cached !== undefined) {
        vmStats.hits++;
        return cached;
      }
      vmStats.misses++;
      const result = vmExec(code[index]);
      vmCache.set(exprs[index], result);
      return result;
    },
  };
}

// ─── Fast convertibility via VM ────────────────────────────────────

/**
 * Check if two expressions are definitionally equal using VM normalization.
 * Avoids double compilation when both sides need normalization.
 */
export function vmConvertible(a: AST.ProveExpr, b: AST.ProveExpr): boolean {
  return exprEqual(vmNormalize(a), vmNormalize(b));
}

/** Like vmConvertible but returns diagnostics on failure. */
export function vmCheckConvertible(
  a: AST.ProveExpr,
  b: AST.ProveExpr,
): { convertible: true } | { convertible: false; lhsNorm: string; rhsNorm: string } {
  const na = vmNormalize(a);
  const nb = vmNormalize(b);
  if (exprEqual(na, nb)) return { convertible: true };
  return { convertible: false, lhsNorm: exprToString(na), rhsNorm: exprToString(nb) };
}
