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
//   recursive(args) : substitute args into declared proposition
//
// Normalization rules (computes with types):
//   add(Zero, y)    → y
//   add(Succ(k), y) → Succ(add(k, y))
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

function exprToString(e: AST.ProveExpr): string {
  if (e.kind === "hole") return "?";
  if (e.kind === "ident") return e.name;
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
  if (expr.kind === "ident" || expr.kind === "hole") return expr;

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

  return e;
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

// ─── Proof tree builder ────────────────────────────────────────────
// Builds a ProofNode tree by walking the proof expression, mirroring inferType.
// The optional `expected` type enables goal-directed checking for ? holes.

function buildNode(
  expr: AST.ProveExpr,
  ctx: ProveCtx,
  expected?: AST.ProveExpr,
): ProofNode {
  // ? hole → show goal type from the expected type
  if (expr.kind === "hole") {
    const goalStr = expected ? exprToString(normalize(expected)) : "?";
    return { rule: "goal", term: "?", conclusion: goalStr, children: [], isGoal: true };
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
      // For refl: infEq has placeholder _refl_a — check required sides are equal
      if (
        infEq.left.kind === "ident" && infEq.left.name === "_refl_a" &&
        infEq.right.kind === "ident" && infEq.right.name === "_refl_a"
      ) {
        // This is refl — check that the required type's sides are equal
        if (!exprEqual(normalize(reqEq.left), normalize(reqEq.right))) {
          errors.push(
            `prove ${prove.name}, case ${caseArm.pattern}: refl requires equal sides, ` +
              `but got Eq(${exprToString(normalize(reqEq.left))}, ${exprToString(normalize(reqEq.right))})`,
          );
        }
        continue;
      }

      // General case: check inferred type matches required type
      if (
        !exprEqual(normalize(infEq.left), normalize(reqEq.left)) ||
        !exprEqual(normalize(infEq.right), normalize(reqEq.right))
      ) {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: type mismatch\n` +
            `  expected: ${exprToString(requiredType)}\n` +
            `  inferred: ${exprToString(normalize(inferred.type))}`,
        );
      }
    } else if (reqEq || infEq) {
      errors.push(
        `prove ${prove.name}, case ${caseArm.pattern}: type structure mismatch\n` +
          `  expected: ${exprToString(requiredType)}\n` +
          `  inferred: ${exprToString(inferred.type)}`,
      );
    }
  }

  return errors;
}
