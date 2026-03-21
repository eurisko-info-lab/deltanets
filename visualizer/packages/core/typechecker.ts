// Type checker for the simply-typed lambda calculus (STLC).
// Works with optional type annotations — fully annotated terms are checked,
// unannotated terms are left untyped.

import type { AstNode, Type } from "./ast.ts";
import { typesEqual, typeToString } from "./ast.ts";
import { nameToFancyName } from "./util.ts";

export type TypeEnv = Map<string, Type>;

export type TypeResult =
  | { ok: true; type: Type }
  | { ok: false; error: string };

// A single step in the type checking derivation.
export type TypeCheckStep = {
  // Index of this step (0-based, assigned post-order)
  idx: number;
  // The AST node being checked
  node: AstNode;
  // The typing rule applied
  rule: "var" | "abs" | "app";
  // The typing environment at this point
  env: TypeEnv;
  // The result of checking this node
  result: TypeResult;
  // Human-readable typing judgment
  judgment: string;
};

function envToString(env: TypeEnv): string {
  if (env.size === 0) return "∅";
  return Array.from(env.entries())
    .map(([name, ty]) => `${nameToFancyName(name)}:${typeToString(ty)}`)
    .join(", ");
}

function nodeToString(node: AstNode): string {
  if (node.type === "var") return nameToFancyName(node.name);
  if (node.type === "abs") return `λ${nameToFancyName(node.name)}…`;
  return `(… …)`;
}

// Generates a sequence of type checking steps by walking the AST post-order.
// Each step corresponds to one typing rule application.
export function generateTypeCheckSteps(ast: AstNode): TypeCheckStep[] {
  const steps: TypeCheckStep[] = [];
  let idx = 0;

  function walk(node: AstNode, env: TypeEnv): TypeResult {
    if (node.type === "var") {
      const ty = env.get(node.name);
      const result: TypeResult = ty
        ? { ok: true, type: ty }
        : { ok: true, type: { kind: "hole" } };
      const envStr = envToString(env);
      const typeStr = result.ok ? typeToString(result.type) : "?";
      steps.push({
        idx: idx++,
        node,
        rule: "var",
        env: new Map(env),
        result,
        judgment: `${envStr} ⊢ ${nameToFancyName(node.name)} : ${typeStr}`,
      });
      return result;
    }
    if (node.type === "abs") {
      const paramType: Type = node.typeAnnotation ?? { kind: "hole" };
      const newEnv = new Map(env);
      newEnv.set(node.name, paramType);
      const bodyResult = walk(node.body, newEnv);
      if (!bodyResult.ok) {
        steps.push({
          idx: idx++,
          node,
          rule: "abs",
          env: new Map(env),
          result: bodyResult,
          judgment: `✘ ${bodyResult.error}`,
        });
        return bodyResult;
      }
      const result: TypeResult = {
        ok: true,
        type: { kind: "arrow", from: paramType, to: bodyResult.type },
      };
      const envStr = envToString(env);
      steps.push({
        idx: idx++,
        node,
        rule: "abs",
        env: new Map(env),
        result,
        judgment: `${envStr} ⊢ λ${nameToFancyName(node.name)} : ${
          typeToString(result.type)
        }`,
      });
      return result;
    }
    if (node.type === "app") {
      const funcResult = walk(node.func, env);
      if (!funcResult.ok) {
        steps.push({
          idx: idx++,
          node,
          rule: "app",
          env: new Map(env),
          result: funcResult,
          judgment: `✘ ${funcResult.error}`,
        });
        return funcResult;
      }
      const argResult = walk(node.arg, env);
      if (!argResult.ok) {
        steps.push({
          idx: idx++,
          node,
          rule: "app",
          env: new Map(env),
          result: argResult,
          judgment: `✘ ${argResult.error}`,
        });
        return argResult;
      }
      let result: TypeResult;
      if (funcResult.type.kind === "hole") {
        result = { ok: true, type: { kind: "hole" } };
      } else if (funcResult.type.kind !== "arrow") {
        result = {
          ok: false,
          error: `Expected function type, got ${typeToString(funcResult.type)}`,
        };
      } else if (!typesEqual(funcResult.type.from, argResult.type)) {
        result = {
          ok: false,
          error: `Type mismatch: expected ${
            typeToString(funcResult.type.from)
          }, got ${typeToString(argResult.type)}`,
        };
      } else {
        result = { ok: true, type: funcResult.type.to };
      }
      const envStr = envToString(env);
      const typeStr = result.ok ? typeToString(result.type) : result.error;
      steps.push({
        idx: idx++,
        node,
        rule: "app",
        env: new Map(env),
        result,
        judgment: result.ok
          ? `${envStr} ⊢ ${nodeToString(node)} : ${typeStr}`
          : `✘ ${result.error}`,
      });
      return result;
    }
    return { ok: false, error: "Unknown node type" };
  }

  walk(ast, new Map());
  return steps;
}

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
    return {
      ok: true,
      type: { kind: "arrow", from: paramType, to: bodyResult.type },
    };
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
      return {
        ok: false,
        error: `Expected function type, got ${typeToString(funcResult.type)}`,
      };
    }
    if (!typesEqual(funcResult.type.from, argResult.type)) {
      return {
        ok: false,
        error: `Type mismatch: expected ${
          typeToString(funcResult.type.from)
        }, got ${typeToString(argResult.type)}`,
      };
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

// Sets `extra.typeCheckIdx` on each AST node in post-order.
// This assigns the same indices used by generateTypeCheckSteps,
// enabling renderers to identify which step corresponds to each node.
export function tagAstWithTypeCheckIndices(ast: AstNode): void {
  let idx = 0;
  function walk(node: AstNode): void {
    if (node.type === "var") {
      node.extra = { ...node.extra, typeCheckIdx: idx++ };
    } else if (node.type === "abs") {
      walk(node.body);
      node.extra = { ...node.extra, typeCheckIdx: idx++ };
    } else if (node.type === "app") {
      walk(node.func);
      walk(node.arg);
      node.extra = { ...node.extra, typeCheckIdx: idx++ };
    }
  }
  walk(ast);
}
