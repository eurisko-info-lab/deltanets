// Type checker for the simply-typed lambda calculus (STLC).
// Works with optional type annotations — fully annotated terms are checked,
// unannotated terms are left untyped.

import type { AstNode, Type } from "../ast.ts";
import { typeToString, typesEqual } from "../ast.ts";

export type TypeEnv = Map<string, Type>;

export type TypeResult =
  | { ok: true; type: Type }
  | { ok: false; error: string };

// Type-checks an AST node under a typing environment.
// Returns the inferred type on success, or an error message on failure.
// Unannotated abstractions default to Hole type (gradual typing).
export function typeCheck(ast: AstNode, env: TypeEnv = new Map()): TypeResult {
  if (ast.type === "var") {
    const ty = env.get(ast.name);
    if (ty) return { ok: true, type: ty };
    // Free variables get Hole type
    return { ok: true, type: { kind: "hole" } };
  }
  if (ast.type === "abs") {
    const paramType: Type = ast.typeAnnotation ?? { kind: "hole" };
    const newEnv = new Map(env);
    newEnv.set(ast.name, paramType);
    const bodyResult = typeCheck(ast.body, newEnv);
    if (!bodyResult.ok) return bodyResult;
    return { ok: true, type: { kind: "arrow", from: paramType, to: bodyResult.type } };
  }
  if (ast.type === "app") {
    const funcResult = typeCheck(ast.func, env);
    if (!funcResult.ok) return funcResult;
    const argResult = typeCheck(ast.arg, env);
    if (!argResult.ok) return argResult;
    // Hole-typed function: result is Hole
    if (funcResult.type.kind === "hole") {
      return { ok: true, type: { kind: "hole" } };
    }
    if (funcResult.type.kind !== "arrow") {
      return { ok: false, error: `Expected function type, got ${typeToString(funcResult.type)}` };
    }
    if (!typesEqual(funcResult.type.from, argResult.type)) {
      return { ok: false, error: `Type mismatch: expected ${typeToString(funcResult.type.from)}, got ${typeToString(argResult.type)}` };
    }
    return { ok: true, type: funcResult.type.to };
  }
  return { ok: false, error: "Unknown node type" };
}

// Returns true if any abstraction in the AST has a type annotation.
export function hasTypeAnnotations(ast: AstNode): boolean {
  if (ast.type === "abs") {
    return ast.typeAnnotation !== undefined || hasTypeAnnotations(ast.body);
  }
  if (ast.type === "app") {
    return hasTypeAnnotations(ast.func) || hasTypeAnnotations(ast.arg);
  }
  return false;
}
