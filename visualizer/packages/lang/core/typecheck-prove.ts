// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Dependent Type Checker for prove blocks
//
// Verifies that each case arm in a typed `prove` block produces
// a proof term whose type matches the declared proposition.
//
// Type inference rules (hard-coded for the Eq/Nat proof system):
//   refl            : Eq(a, a)       for any a
//   cong_X(p, ...)  : Eq(X(...,a), X(...,b)) when p : Eq(a, b)  (generalized)
//   sym(p)          : Eq(b, a)       when p : Eq(a, b)
//   trans(p, q)     : Eq(a, c)       when p : Eq(a, b), q : Eq(b, c)
//   pair(w, p)      : Sigma(w, T)    when p : T  (∃-introduction)
//   subst(p, e)     : T[a := b]      when p : Eq(a, b), e : T  (transport/J)
//   recursive(args) : substitute args into declared proposition
//
// Normalization rules (computes with types):
//   add(Zero, y)    → y
//   add(Succ(k), y) → Succ(add(k, y))
//   fst(pair(a, b)) → a
//   snd(pair(a, b)) → b
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";

// Context of previously proved propositions for cross-lemma resolution
export type ProvedContext = Map<
  string,
  { params: AST.ProveParam[]; returnType: AST.ProveExpr }
>;

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

function exprEqual(a: AST.ProveExpr, b: AST.ProveExpr): boolean {
  if (a.kind === "hole" || b.kind === "hole") return false;
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
  const newArgs = expr.args.map((a) => substituteAll(a, bindings));
  const replacement = bindings.get(expr.name);
  const newName = replacement?.kind === "ident" ? replacement.name : expr.name;
  return { kind: "call", name: newName, args: newArgs };
}

// ─── Normalization ─────────────────────────────────────────────────
// Reduces type expressions using computational rules.

function normalize(expr: AST.ProveExpr): AST.ProveExpr {
  // ── Universe level normalization ──
  // Type → Type(0), Type0 → Type(0), Type1 → Type(1), etc.
  if (expr.kind === "ident") {
    if (expr.name === "Type") return app("Type", ident("0"));
    const m = expr.name.match(/^Type(\d+)$/);
    if (m) return app("Type", ident(m[1]));
    return expr;
  }
  if (expr.kind === "hole") return expr;

  // Normalize children first
  const args = expr.args.map(normalize);
  const e: AST.ProveExpr = { kind: "call", name: expr.name, args };

  // add(Zero, y) → y
  if (
    e.name === "add" && e.args.length === 2 &&
    e.args[0].kind === "ident" && e.args[0].name === "Zero"
  ) {
    return e.args[1];
  }

  // add(Succ(k), y) → Succ(add(k, y))
  if (
    e.name === "add" && e.args.length === 2 &&
    e.args[0].kind === "call" && e.args[0].name === "Succ" &&
    e.args[0].args.length === 1
  ) {
    const k = e.args[0].args[0];
    return normalize(app("Succ", app("add", k, e.args[1])));
  }

  // ── Bool ──

  // not(True) → False, not(False) → True
  if (e.name === "not" && e.args.length === 1 && e.args[0].kind === "ident") {
    if (e.args[0].name === "True") return ident("False");
    if (e.args[0].name === "False") return ident("True");
  }

  // and(True, x) → x, and(False, x) → False
  if (e.name === "and" && e.args.length === 2 && e.args[0].kind === "ident") {
    if (e.args[0].name === "True") return e.args[1];
    if (e.args[0].name === "False") return ident("False");
  }

  // or(True, x) → True, or(False, x) → x
  if (e.name === "or" && e.args.length === 2 && e.args[0].kind === "ident") {
    if (e.args[0].name === "True") return ident("True");
    if (e.args[0].name === "False") return e.args[1];
  }

  // ── List ──

  // append(Nil, ys) → ys
  if (
    e.name === "append" && e.args.length === 2 &&
    e.args[0].kind === "ident" && e.args[0].name === "Nil"
  ) {
    return e.args[1];
  }

  // append(Cons(h, t), ys) → Cons(h, append(t, ys))
  if (
    e.name === "append" && e.args.length === 2 &&
    e.args[0].kind === "call" && e.args[0].name === "Cons" &&
    e.args[0].args.length === 2
  ) {
    const [h, t] = e.args[0].args;
    return normalize(app("Cons", h, app("append", t, e.args[1])));
  }

  // length(Nil) → Zero
  if (
    e.name === "length" && e.args.length === 1 &&
    e.args[0].kind === "ident" && e.args[0].name === "Nil"
  ) {
    return ident("Zero");
  }

  // length(Cons(h, t)) → Succ(length(t))
  if (
    e.name === "length" && e.args.length === 1 &&
    e.args[0].kind === "call" && e.args[0].name === "Cons" &&
    e.args[0].args.length === 2
  ) {
    return normalize(app("Succ", app("length", e.args[0].args[1])));
  }

  // ── Sigma (dependent pairs) ──

  // fst(pair(a, b)) → a
  if (
    e.name === "fst" && e.args.length === 1 &&
    e.args[0].kind === "call" && e.args[0].name === "pair" &&
    e.args[0].args.length === 2
  ) {
    return e.args[0].args[0];
  }

  // snd(pair(a, b)) → b
  if (
    e.name === "snd" && e.args.length === 1 &&
    e.args[0].kind === "call" && e.args[0].name === "pair" &&
    e.args[0].args.length === 2
  ) {
    return e.args[0].args[1];
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
  if (expr.kind !== "call") return expr;
  const newArgs = expr.args.map((a) => substituteExprPattern(a, pattern, replacement));
  return { kind: "call", name: expr.name, args: newArgs };
}

// ─── Type inference ────────────────────────────────────────────────
// Infers the Eq-type of a proof expression given the prove context.

type ProveCtx = {
  prove: AST.ProveDecl;
  caseBindings: Map<string, AST.ProveExpr>; // binding name → type var
  provedCtx: ProvedContext; // previously proved propositions
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

  // refl → Eq(a, a) where 'a' is determined from context
  if (expr.kind === "ident" && expr.name === "refl") {
    return { ok: true, type: app("Eq", ident("_refl_a"), ident("_refl_a")) };
  }

  if (expr.kind === "ident") {
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
    const bindings = new Map<string, AST.ProveExpr>();
    const paramNames = ctx.prove.params.map((p) => p.name);
    for (let i = 0; i < args.length && i < paramNames.length; i++) {
      bindings.set(paramNames[i], args[i]);
    }
    return { ok: true, type: normalize(substituteAll(ctx.prove.returnType, bindings)) };
  }

  // Cross-lemma call: look up previously proved proposition
  const proved = ctx.provedCtx.get(name);
  if (proved) {
    const bindings = new Map<string, AST.ProveExpr>();
    const paramNames = proved.params.map((p) => p.name);
    for (let i = 0; i < args.length && i < paramNames.length; i++) {
      bindings.set(paramNames[i], args[i]);
    }
    return { ok: true, type: normalize(substituteAll(proved.returnType, bindings)) };
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
  if (!result.ok) return false;
  const goalEq = extractEq(normalize(goal));
  const infEq = extractEq(normalize(result.type));
  if (!goalEq || !infEq) return false;
  // refl produces Eq(_refl_a, _refl_a) — check that goal sides are equal
  if (infEq.left.kind === "ident" && infEq.left.name === "_refl_a" &&
      infEq.right.kind === "ident" && infEq.right.name === "_refl_a") {
    return exprEqual(normalize(goalEq.left), normalize(goalEq.right));
  }
  return exprEqual(normalize(infEq.left), normalize(goalEq.left)) &&
         exprEqual(normalize(infEq.right), normalize(goalEq.right));
}

function searchCandidates(
  ctx: ProveCtx,
  goal: AST.ProveExpr,
): string[] {
  const goalEq = extractEq(normalize(goal));
  if (!goalEq) return [];

  const found: string[] = [];
  const seen = new Set<string>();
  const add = (expr: AST.ProveExpr) => {
    const s = exprToString(expr);
    if (!seen.has(s)) { seen.add(s); found.push(s); }
  };

  // 1. refl — if both sides are equal
  if (tryCandidateType(ident("refl"), ctx, goal)) add(ident("refl"));

  // Collect ALL possible IH expressions (not filtered by goal match yet)
  const allIHs: AST.ProveExpr[] = [];
  if (ctx.prove.returnType) {
    for (const [binding] of ctx.caseBindings) {
      const auxArgs = ctx.prove.params.slice(1).map((p) => ident(p.name));
      allIHs.push(app(ctx.prove.name, ident(binding), ...auxArgs));
    }
  }

  // 2. IH — check which ones directly match the goal
  for (const ih of allIHs) {
    if (tryCandidateType(ih, ctx, goal)) add(ih);
  }

  // 3. Cross-lemma calls — collect all, check which match
  const availableVars = [
    ...Array.from(ctx.caseBindings.keys()).map(ident),
    ...ctx.prove.params.slice(1).map((p) => ident(p.name)),
  ];
  const allLemmaCalls: AST.ProveExpr[] = [];
  for (const [lemmaName, lemma] of ctx.provedCtx) {
    if (lemma.params.length <= availableVars.length) {
      const call = app(lemmaName, ...availableVars.slice(0, lemma.params.length));
      allLemmaCalls.push(call);
      if (tryCandidateType(call, ctx, goal)) add(call);
    }
  }

  // 4. Depth-2: sym wrappers on all IH and lemma calls
  const depth1Exprs = [...allIHs, ...allLemmaCalls];
  for (const inner of depth1Exprs) {
    const symExpr = app("sym", inner);
    if (tryCandidateType(symExpr, ctx, goal)) add(symExpr);
  }

  // 5. cong_X wrapping — if goal is Eq(X(...,a), X(...,b))
  if (goalEq.left.kind === "call" && goalEq.right.kind === "call" &&
      goalEq.left.name === goalEq.right.name &&
      goalEq.left.args.length === goalEq.right.args.length) {
    const cons = goalEq.left.name;
    const suffix = cons.charAt(0).toLowerCase() + cons.slice(1);
    const congName = `cong_${suffix}`;
    const constants = goalEq.left.args.slice(0, -1);
    // Try wrapping all candidates (refl, IH, lemma, sym(...))
    const innerCandidates = [ident("refl"), ...allIHs, ...allLemmaCalls];
    for (const inner of innerCandidates) {
      const congExpr = app(congName, inner, ...constants);
      if (tryCandidateType(congExpr, ctx, goal)) add(congExpr);
    }
    for (const inner of depth1Exprs) {
      const congExpr = app(congName, app("sym", inner), ...constants);
      if (tryCandidateType(congExpr, ctx, goal)) add(congExpr);
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

  const result = inferType(expr, ctx);
  const conclusion = result.ok
    ? exprToString(normalize(result.type))
    : `✘ ${result.error}`;
  const term = exprToString(expr);

  if (expr.kind === "ident" && expr.name === "refl") {
    return { rule: "refl", term, conclusion, children: [] };
  }
  if (expr.kind === "ident") {
    return { rule: "?", term, conclusion, children: [] };
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
  // subst(p, e) — transport / J elimination
  if (name === "subst" && args.length === 2) {
    return {
      rule: "subst",
      term,
      conclusion,
      children: [buildNode(args[0], ctx), buildNode(args[1], ctx)],
    };
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

/** Build a proof derivation tree for a typed prove block. */
export function buildProofTree(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext = new Map(),
): ProofTree | null {
  if (!prove.returnType) return null;

  const cases: ProofTree["cases"] = [];
  for (const caseArm of prove.cases) {
    const ctx: ProveCtx = {
      prove,
      caseBindings: new Map(caseArm.bindings.map((b) => [b, ident(b)])),
      provedCtx,
    };

    // Compute expected type for this case arm
    const consExpr: AST.ProveExpr = caseArm.bindings.length > 0
      ? app(caseArm.pattern, ...caseArm.bindings.map(ident))
      : ident(caseArm.pattern);
    const principalName = prove.params[0].name;
    const expectedType = normalize(substitute(prove.returnType, principalName, consExpr));

    cases.push({
      pattern: caseArm.pattern,
      bindings: caseArm.bindings,
      tree: buildNode(caseArm.body, ctx, expectedType),
    });
  }

  const hasHoles = cases.some((c) => nodeHasHoles(c.tree));

  return {
    name: prove.name,
    proposition: exprToString(prove.returnType),
    cases,
    hasHoles,
  };
}

// ─── Main type checker ─────────────────────────────────────────────

export function typecheckProve(
  prove: AST.ProveDecl,
  provedCtx: ProvedContext = new Map(),
): string[] {
  if (!prove.returnType) return []; // no annotation → skip checking

  const errors: string[] = [];

  for (const caseArm of prove.cases) {
    // Build the constructor expression for this case
    const consExpr: AST.ProveExpr = caseArm.bindings.length > 0
      ? app(caseArm.pattern, ...caseArm.bindings.map(ident))
      : ident(caseArm.pattern);

    // Substitute the principal parameter with the constructor
    const principalName = prove.params[0].name;
    const requiredType = normalize(
      substitute(prove.returnType, principalName, consExpr),
    );

    // Infer the type of the proof term
    const ctx: ProveCtx = {
      prove,
      caseBindings: new Map(
        caseArm.bindings.map((b) => [b, ident(b)]),
      ),
      provedCtx,
    };
    const inferred = inferType(caseArm.body, ctx);

    if (!inferred.ok) {
      // Holes are not errors — they're open goals
      if (inferred.error !== "hole") {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: ${inferred.error}`,
        );
      }
      continue;
    }

    // Special case: refl matches any Eq(a, a) — check that required has equal sides
    const reqEq = extractEq(requiredType);
    const infEq = extractEq(inferred.type);

    if (reqEq && infEq) {
      if (!eqTypeMatches(inferred.type, requiredType)) {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: type mismatch\n` +
            `  expected: ${exprToString(requiredType)}\n` +
            `  inferred: ${exprToString(normalize(inferred.type))}`,
        );
      }
      continue;
    } else if (reqEq || infEq) {
      errors.push(
        `prove ${prove.name}, case ${caseArm.pattern}: type structure mismatch\n` +
          `  expected: ${exprToString(requiredType)}\n` +
          `  inferred: ${exprToString(inferred.type)}`,
      );
      continue;
    }

    // Sigma types: required = Sigma(A, x, P), inferred = Sigma(witness, proofType)
    const reqSigma = extractSigma(requiredType);
    if (reqSigma && inferred.type.kind === "call" && inferred.type.name === "Sigma" &&
        inferred.type.args.length === 2) {
      const witness = inferred.type.args[0];
      const infProofType = inferred.type.args[1];
      // Expected predicate with bound var replaced by the witness
      const expectedPred = normalize(substitute(reqSigma.predicate, reqSigma.boundVar, witness));
      if (!eqTypeMatches(infProofType, expectedPred) && !exprEqual(normalize(infProofType), expectedPred)) {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: Sigma predicate mismatch\n` +
            `  expected: ${exprToString(expectedPred)}\n` +
            `  inferred: ${exprToString(normalize(infProofType))}`,
        );
      }
      continue;
    }
    if (reqSigma || (inferred.type.kind === "call" && inferred.type.name === "Sigma")) {
      errors.push(
        `prove ${prove.name}, case ${caseArm.pattern}: type structure mismatch\n` +
          `  expected: ${exprToString(requiredType)}\n` +
          `  inferred: ${exprToString(normalize(inferred.type))}`,
      );
    }
  }

  return errors;
}
