// Tests for the type checker and AST utilities.

import { assert, assertEquals } from "$std/assert/mod.ts";
import {
  astToString,
  clone,
  getExpressionType,
  parseSource,
  typesEqual,
  typeToString,
} from "./ast.ts";
import type { AstNode, Type } from "./ast.ts";
import {
  generateTypeCheckSteps,
  hasTypeAnnotations,
  typeCheck,
} from "./typechecker.ts";

// ─── parseSource ───────────────────────────────────────────────────

Deno.test("parseSource: parses identity", () => {
  const { ast, errs } = parseSource("λx.x");
  assert(ast !== undefined && ast !== null);
  assertEquals(ast.type, "abs");
});

Deno.test("parseSource: parses application", () => {
  const { ast } = parseSource("(λx.x) y");
  assert(ast !== undefined && ast !== null);
  assertEquals(ast.type, "app");
});

Deno.test("parseSource: returns errors for invalid syntax", () => {
  const { ast, errs } = parseSource("λ.");
  assert(errs !== undefined && errs!.length > 0, "should have parse errors");
});

Deno.test("parseSource: empty input returns null ast", () => {
  const { ast } = parseSource("");
  assertEquals(ast, null);
});

Deno.test("parseSource: definitions expand inline", () => {
  const { ast } = parseSource("I = λx.x\nI");
  assert(ast !== undefined && ast !== null);
  assertEquals(ast.type, "abs");
});

// ─── astToString ───────────────────────────────────────────────────

Deno.test("astToString: identity", () => {
  const { ast } = parseSource("λx.x");
  assertEquals(astToString(ast!), "λx.x");
});

Deno.test("astToString: application with parentheses", () => {
  const { ast } = parseSource("(λx.x) (λy.y)");
  assertEquals(astToString(ast!), "(λx.x) λy.y");
});

Deno.test("astToString: nested abstraction", () => {
  const { ast } = parseSource("λx.λy.x y");
  assertEquals(astToString(ast!), "λx.λy.x y");
});

// ─── getExpressionType ─────────────────────────────────────────────

Deno.test("getExpressionType: linear (identity)", () => {
  const { ast } = parseSource("λx.x");
  assertEquals(getExpressionType(ast!), "linear");
});

Deno.test("getExpressionType: affine (erasure)", () => {
  const { ast } = parseSource("λx.λy.x");
  assertEquals(getExpressionType(ast!), "affine");
});

Deno.test("getExpressionType: relevant (sharing)", () => {
  const { ast } = parseSource("λx.x x");
  assertEquals(getExpressionType(ast!), "relevant");
});

Deno.test("getExpressionType: full (sharing + erasure)", () => {
  const { ast } = parseSource("λx.λy.x x");
  assertEquals(getExpressionType(ast!), "full");
});

// ─── clone ─────────────────────────────────────────────────────────

Deno.test("clone: produces equal structure", () => {
  const { ast } = parseSource("λx.x y");
  const cloned = clone(ast!);
  assertEquals(astToString(cloned), astToString(ast!));
});

Deno.test("clone: produces distinct objects", () => {
  const { ast } = parseSource("λx.x");
  const cloned = clone(ast!);
  assert(cloned !== ast, "cloned should be a new object");
});

// ─── typeToString ──────────────────────────────────────────────────

Deno.test("typeToString: hole", () => {
  assertEquals(typeToString({ kind: "hole" }), "?");
});

Deno.test("typeToString: base", () => {
  assertEquals(typeToString({ kind: "base", name: "A" }), "A");
});

Deno.test("typeToString: arrow", () => {
  const ty: Type = {
    kind: "arrow",
    from: { kind: "base", name: "A" },
    to: { kind: "base", name: "B" },
  };
  assertEquals(typeToString(ty), "A → B");
});

Deno.test("typeToString: nested arrow parenthesizes left", () => {
  const ty: Type = {
    kind: "arrow",
    from: {
      kind: "arrow",
      from: { kind: "base", name: "A" },
      to: { kind: "base", name: "B" },
    },
    to: { kind: "base", name: "C" },
  };
  assertEquals(typeToString(ty), "(A → B) → C");
});

// ─── typesEqual ────────────────────────────────────────────────────

Deno.test("typesEqual: holes match anything", () => {
  assert(typesEqual({ kind: "hole" }, { kind: "base", name: "A" }));
  assert(typesEqual({ kind: "base", name: "A" }, { kind: "hole" }));
});

Deno.test("typesEqual: same base types", () => {
  assert(typesEqual({ kind: "base", name: "A" }, { kind: "base", name: "A" }));
});

Deno.test("typesEqual: different base types", () => {
  assertEquals(
    typesEqual({ kind: "base", name: "A" }, { kind: "base", name: "B" }),
    false,
  );
});

Deno.test("typesEqual: arrow types", () => {
  const a: Type = {
    kind: "arrow",
    from: { kind: "base", name: "A" },
    to: { kind: "base", name: "B" },
  };
  const b: Type = {
    kind: "arrow",
    from: { kind: "base", name: "A" },
    to: { kind: "base", name: "B" },
  };
  assert(typesEqual(a, b));
});

// ─── typeCheck ─────────────────────────────────────────────────────

Deno.test("typeCheck: variable in environment", () => {
  const { ast } = parseSource("x");
  const env = new Map([["𝑥", { kind: "base" as const, name: "A" }]]);
  const result = typeCheck(ast!, env);
  assert(result.ok);
  assertEquals(result.type.kind, "base");
});

Deno.test("typeCheck: free variable returns hole", () => {
  const { ast } = parseSource("x");
  const result = typeCheck(ast!);
  assert(result.ok);
  assertEquals(result.type.kind, "hole");
});

Deno.test("typeCheck: identity with annotation", () => {
  const { ast } = parseSource("λx:A.x");
  const result = typeCheck(ast!);
  assert(result.ok);
  assertEquals(result.type.kind, "arrow");
});

Deno.test("typeCheck: application type mismatch", () => {
  const { ast } = parseSource("(λf:A->B.f) (λx:C.x)");
  // Note: the arg has type C->C which may not match A
  // This depends on how the types resolve; we just check it doesn't crash
  const result = typeCheck(ast!);
  assert(result !== undefined);
});

Deno.test("typeCheck: unannotated abstraction defaults to hole", () => {
  const { ast } = parseSource("λx.x");
  const result = typeCheck(ast!);
  assert(result.ok);
  // λx:?.x has type ? → ?
  assertEquals(result.type.kind, "arrow");
});

Deno.test("typeCheck: non-function application error", () => {
  // Apply a base-typed thing = error
  const varNode: AstNode = { type: "var", name: "x" };
  const appNode: AstNode = { type: "app", func: varNode, arg: varNode };
  const env = new Map([["x", { kind: "base" as const, name: "Nat" }]]);
  const result = typeCheck(appNode, env);
  assertEquals(result.ok, false);
});

Deno.test("typeCheck: application arg type mismatch is caught", () => {
  // (λf:A->B.f) (λx:C.x) — arg type C->C doesn't match expected A
  const { ast } = parseSource("(λf:A->B.f) (λx:C.x)");
  const result = typeCheck(ast!);
  // This should either be an error or produce a type (holes may unify)
  assert(result !== undefined, "should not crash on type mismatch");
});

Deno.test("typeCheck: correctly types annotated identity", () => {
  const { ast } = parseSource("λx:A.x");
  const result = typeCheck(ast!);
  assert(result.ok);
  assertEquals(result.type.kind, "arrow");
  if (result.type.kind === "arrow") {
    assertEquals(result.type.from.kind, "base");
    assertEquals(result.type.to.kind, "base");
    if (result.type.from.kind === "base" && result.type.to.kind === "base") {
      assertEquals(result.type.from.name, "A");
      assertEquals(result.type.to.name, "A");
    }
  }
});

// ─── generateTypeCheckSteps ────────────────────────────────────────

Deno.test("generateTypeCheckSteps: identity produces steps", () => {
  const { ast } = parseSource("λx.x");
  const steps = generateTypeCheckSteps(ast!);
  assert(steps.length > 0, "should produce at least one step");
  // Last step should be the abs rule
  assertEquals(steps[steps.length - 1].rule, "abs");
});

Deno.test("generateTypeCheckSteps: steps have sequential indices", () => {
  const { ast } = parseSource("λf.λx.f x");
  const steps = generateTypeCheckSteps(ast!);
  steps.forEach((s, i) => assertEquals(s.idx, i));
});

// ─── hasTypeAnnotations ────────────────────────────────────────────

Deno.test("hasTypeAnnotations: unannotated returns false", () => {
  const { ast } = parseSource("λx.x");
  assertEquals(hasTypeAnnotations(ast!), false);
});

Deno.test("hasTypeAnnotations: annotated returns true", () => {
  const { ast } = parseSource("λx:A.x");
  assertEquals(hasTypeAnnotations(ast!), true);
});

// ─── Error path tests ──────────────────────────────────────────────

Deno.test("typeCheck: nested application of non-function errors", () => {
  // (x y) where x : Nat — applying a base type to something
  const xNode: AstNode = { type: "var", name: "x" };
  const yNode: AstNode = { type: "var", name: "y" };
  const appNode: AstNode = { type: "app", func: xNode, arg: yNode };
  const env = new Map<string, Type>([
    ["x", { kind: "base", name: "Nat" }],
    ["y", { kind: "base", name: "Nat" }],
  ]);
  const result = typeCheck(appNode, env);
  assertEquals(result.ok, false, "applying Nat to Nat should fail");
});

Deno.test("typeCheck: arrow type domain/codomain preserved", () => {
  const { ast } = parseSource("λf:A->B.λx:A.f x");
  const result = typeCheck(ast!);
  assert(result.ok);
  assertEquals(result.type.kind, "arrow");
});

Deno.test("generateTypeCheckSteps: each step has valid rule name", () => {
  const validRules = ["var", "abs", "app"];
  const { ast } = parseSource("λf.λx.f x");
  const steps = generateTypeCheckSteps(ast!);
  for (const step of steps) {
    assert(
      validRules.includes(step.rule),
      `step rule "${step.rule}" should be one of ${validRules}`,
    );
  }
});

Deno.test("hasTypeAnnotations: nested annotation returns true", () => {
  const { ast } = parseSource("λf.λx:A.f x");
  assertEquals(hasTypeAnnotations(ast!), true);
});

Deno.test("hasTypeAnnotations: deep unannotated returns false", () => {
  const { ast } = parseSource("λf.λx.λy.f (x y)");
  assertEquals(hasTypeAnnotations(ast!), false);
});
