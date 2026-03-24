// ═══════════════════════════════════════════════════════════════════
// Code Extraction — Generate TypeScript from verified INet programs
//
// Translates a compiled SystemDef into executable TypeScript code,
// erasing Prop-typed definitions (proofs) and keeping only
// computationally relevant (Set/Type) content.
//
// Pipeline:
//   SystemDef → extractSystem() → ExtractionResult → renderTypeScript()
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { SystemDef } from "./evaluator.ts";
import type { ComputeRule, ConstructorTyping } from "./normalize.ts";
import { exprToString } from "./normalize.ts";

// ─── Types ─────────────────────────────────────────────────────────

/** A single extracted data type. */
export type ExtractedType = {
  name: string;
  params: string[];
  constructors: { name: string; fields: { name: string; type: string }[] }[];
};

/** A single extracted function (from compute rules). */
export type ExtractedFunction = {
  name: string;
  arity: number;
  clauses: { patterns: string[]; body: string }[];
};

/** Full extraction result for a system. */
export type ExtractionResult = {
  systemName: string;
  types: ExtractedType[];
  functions: ExtractedFunction[];
  erased: string[]; // names of Prop-erased definitions
  constructorFields: Map<string, string[]>; // ctor name → field names
};

// ─── Prop Erasure ──────────────────────────────────────────────────

/** Known proof-only agent names that should always be erased. */
const PROOF_AGENTS = new Set([
  "refl", "sym", "trans", "subst", "cong", "cong_succ", "cong_cons",
  "J", "K", "UIP",
]);

/** Determine whether a type name is proof-irrelevant (lives in Prop). */
function isPropType(
  name: string,
  dataSorts?: Map<string, "Prop" | "Set">,
): boolean {
  if (name === "Eq" || name === "Acc" || name === "exist") return true;
  return dataSorts?.get(name) === "Prop";
}

/** Check if a compute rule is proof-only (should be erased). */
function isProofRule(
  rule: ComputeRule,
  dataSorts?: Map<string, "Prop" | "Set">,
): boolean {
  if (PROOF_AGENTS.has(rule.funcName)) return true;
  if (isPropType(rule.funcName, dataSorts)) return true;
  return false;
}

/** Check if a proved definition is computational (not just a proof). */
function isComputationalProve(
  name: string,
  params: AST.ProveParam[],
  returnType: AST.ProveExpr | undefined,
  dataSorts?: Map<string, "Prop" | "Set">,
): boolean {
  if (PROOF_AGENTS.has(name)) return false;
  if (returnType) {
    const rtName = returnType.kind === "ident" ? returnType.name
      : returnType.kind === "call" ? returnType.name : undefined;
    if (rtName && isPropType(rtName, dataSorts)) return false;
  }
  return true;
}

// ─── Expression rendering (ProveExpr → TypeScript string) ──────────

function renderExpr(expr: AST.ProveExpr): string {
  if (expr.kind === "ident") return tsName(expr.name);
  if (expr.kind === "call") {
    if (expr.args.length === 0) return tsName(expr.name);
    return `${tsName(expr.name)}(${expr.args.map(renderExpr).join(", ")})`;
  }
  if (expr.kind === "lambda") {
    return `(${tsName(expr.param)}) => ${renderExpr(expr.body)}`;
  }
  if (expr.kind === "let") {
    return `(() => { const ${tsName(expr.name)} = ${renderExpr(expr.value)}; return ${renderExpr(expr.body)}; })()`;
  }
  if (expr.kind === "match") {
    // match in extraction context shouldn't appear in compute rule results
    return `/* match ${expr.scrutinee} */`;
  }
  if (expr.kind === "hole") return `undefined /* hole */`;
  if (expr.kind === "metavar" || expr.kind === "meta-app") return `undefined /* meta */`;
  if (expr.kind === "pi" || expr.kind === "sigma") return `undefined /* type */`;
  return `undefined`;
}

/** Convert INet names to valid TypeScript identifiers. */
function tsName(name: string): string {
  // Reserved words
  if (name === "default" || name === "delete" || name === "return"
    || name === "switch" || name === "class" || name === "const"
    || name === "let" || name === "var" || name === "function"
    || name === "new" || name === "typeof" || name === "void"
    || name === "in" || name === "of") {
    return name + "_";
  }
  return name;
}

// ─── Pattern rendering ─────────────────────────────────────────────

function renderPattern(pat: AST.ComputePattern): string {
  if (pat.kind === "var") return tsName(pat.name);
  if (pat.args.length === 0) return `"${pat.name}"`;
  return `{ tag: "${pat.name}", ${pat.args.map((a, i) => `${tsName(a)}`).join(", ")} }`;
}

/** Build a TypeScript match condition from patterns. */
function patternCondition(
  paramNames: string[],
  patterns: AST.ComputePattern[],
): { condition: string; bindings: string[] } {
  const conditions: string[] = [];
  const bindings: string[] = [];

  for (let i = 0; i < patterns.length; i++) {
    const pat = patterns[i];
    const param = paramNames[i] ?? `_arg${i}`;
    if (pat.kind === "var") {
      // Variable pattern — always matches, just binds the name
      if (pat.name !== param) bindings.push(`const ${tsName(pat.name)} = ${tsName(param)};`);
    } else {
      // Constructor pattern
      conditions.push(`${tsName(param)}.tag === "${pat.name}"`);
      for (const field of pat.args) {
        bindings.push(`const ${tsName(field)} = ${tsName(param)}.${tsName(field)};`);
      }
    }
  }

  return {
    condition: conditions.length === 0 ? "true" : conditions.join(" && "),
    bindings,
  };
}

// ─── Type extraction ───────────────────────────────────────────────

function extractTypes(
  constructorsByType: Map<string, Set<string>>,
  constructorTyping: ConstructorTyping,
  dataSorts?: Map<string, "Prop" | "Set">,
): { types: ExtractedType[]; erased: string[] } {
  const types: ExtractedType[] = [];
  const erased: string[] = [];

  for (const [typeName, ctorNames] of constructorsByType) {
    // Skip Prop types
    if (isPropType(typeName, dataSorts)) {
      erased.push(typeName);
      continue;
    }

    const ctors = [...ctorNames];
    const firstCtor = ctors[0] ? constructorTyping.get(ctors[0]) : undefined;
    const params = firstCtor?.params ?? [];

    const constructors = ctors.map((ctorName) => {
      const info = constructorTyping.get(ctorName);
      const fields = (info?.fields ?? [])
        .filter((f) => !isPropType(fieldTypeName(f.type), dataSorts))
        .map((f) => ({
          name: f.name,
          type: renderTypeExpr(f.type),
        }));
      return { name: ctorName, fields };
    });

    types.push({ name: typeName, params, constructors });
  }

  return { types, erased };
}

function fieldTypeName(type: AST.ProveExpr): string {
  if (type.kind === "ident") return type.name;
  if (type.kind === "call") return type.name;
  return "";
}

function renderTypeExpr(type: AST.ProveExpr): string {
  if (type.kind === "ident") return tsName(type.name);
  if (type.kind === "call") {
    if (type.args.length === 0) return tsName(type.name);
    return `${tsName(type.name)}<${type.args.map(renderTypeExpr).join(", ")}>`;
  }
  return "unknown";
}

// ─── Function extraction ───────────────────────────────────────────

function extractFunctions(
  computeRules: ComputeRule[],
  dataSorts?: Map<string, "Prop" | "Set">,
): { functions: ExtractedFunction[]; erased: string[] } {
  const erased: string[] = [];

  // Group compute rules by function name
  const byFunc = new Map<string, ComputeRule[]>();
  for (const rule of computeRules) {
    if (isProofRule(rule, dataSorts)) {
      if (!erased.includes(rule.funcName)) erased.push(rule.funcName);
      continue;
    }
    const existing = byFunc.get(rule.funcName);
    if (existing) existing.push(rule);
    else byFunc.set(rule.funcName, [rule]);
  }

  const functions: ExtractedFunction[] = [];
  for (const [name, rules] of byFunc) {
    const arity = rules[0].args.length;
    const clauses = rules.map((r) => ({
      patterns: r.args.map(renderComputePattern),
      body: renderExpr(r.result),
    }));
    functions.push({ name, arity, clauses });
  }

  return { functions, erased };
}

function renderComputePattern(pat: AST.ComputePattern): string {
  if (pat.kind === "var") return pat.name;
  if (pat.args.length === 0) return pat.name;
  return `${pat.name}(${pat.args.join(", ")})`;
}

// ─── Main extraction ───────────────────────────────────────────────

/** Extract computational content from a compiled system. */
export function extractSystem(sys: SystemDef): ExtractionResult {
  const { types, erased: erasedTypes } = extractTypes(
    sys.constructorsByType,
    sys.constructorTyping,
    sys.dataSorts,
  );

  const { functions, erased: erasedFuncs } = extractFunctions(
    sys.computeRules,
    sys.dataSorts,
  );

  // Build constructor → field names mapping
  const constructorFields = new Map<string, string[]>();
  if (sys.constructorTyping) {
    for (const [ctorName, info] of sys.constructorTyping) {
      constructorFields.set(ctorName, info.fields.map(f => f.name));
    }
  }

  return {
    systemName: sys.name,
    types,
    functions,
    erased: [...erasedTypes, ...erasedFuncs],
    constructorFields,
  };
}

// ─── TypeScript code generation ────────────────────────────────────

/** Render an ExtractionResult as executable TypeScript source code. */
export function renderTypeScript(result: ExtractionResult): string {
  const lines: string[] = [];
  lines.push(`// Extracted from system "${result.systemName}"`);
  lines.push(`// Prop-erased: ${result.erased.join(", ") || "(none)"}`);
  lines.push("");

  // ── Type definitions ──
  for (const t of result.types) {
    const typeParams = t.params.length > 0 ? `<${t.params.join(", ")}>` : "";

    if (t.constructors.length === 0) {
      lines.push(`export type ${tsName(t.name)}${typeParams} = never;`);
      lines.push("");
      continue;
    }

    // Tagged union type
    const variants: string[] = [];
    for (const ctor of t.constructors) {
      const fieldStr = ctor.fields.length > 0
        ? `, ${ctor.fields.map((f) => `${tsName(f.name)}: ${f.type}`).join(", ")}`
        : "";
      variants.push(`{ tag: "${ctor.name}"${fieldStr} }`);
    }
    lines.push(`export type ${tsName(t.name)}${typeParams} = ${variants.join(" | ")};`);
    lines.push("");

    // Constructor functions
    for (const ctor of t.constructors) {
      if (ctor.fields.length === 0) {
        lines.push(`export const ${tsName(ctor.name)}: ${tsName(t.name)}${typeParams ? "<any>" : ""} = { tag: "${ctor.name}" };`);
      } else {
        const params = ctor.fields.map((f) => `${tsName(f.name)}: ${f.type}`).join(", ");
        lines.push(`export function ${tsName(ctor.name)}${typeParams}(${params}): ${tsName(t.name)}${typeParams || ""} {`);
        lines.push(`  return { tag: "${ctor.name}", ${ctor.fields.map((f) => tsName(f.name)).join(", ")} };`);
        lines.push(`}`);
      }
    }
    lines.push("");
  }

  // ── Function definitions ──
  for (const fn of result.functions) {
    const paramNames = generateParamNames(fn.arity);
    const params = paramNames.map((p) => `${p}: any`).join(", ");

    lines.push(`export function ${tsName(fn.name)}(${params}): any {`);

    for (const clause of fn.clauses) {
      const { condition, bindings } = buildClauseCondition(
        paramNames,
        clause.patterns,
        fn.clauses.indexOf(clause) === fn.clauses.length - 1,
        result.constructorFields,
      );

      if (condition === "true" && fn.clauses.length === 1) {
        // Single catch-all clause — no condition needed
        for (const b of bindings) lines.push(`  ${b}`);
        lines.push(`  return ${clause.body};`);
      } else if (condition === "true") {
        // Catch-all clause (last)
        for (const b of bindings) lines.push(`  ${b}`);
        lines.push(`  return ${clause.body};`);
      } else {
        lines.push(`  if (${condition}) {`);
        for (const b of bindings) lines.push(`    ${b}`);
        lines.push(`    return ${clause.body};`);
        lines.push(`  }`);
      }
    }

    lines.push(`}`);
    lines.push("");
  }

  return lines.join("\n");
}

function generateParamNames(arity: number): string[] {
  if (arity === 1) return ["x"];
  if (arity === 2) return ["x", "y"];
  if (arity === 3) return ["x", "y", "z"];
  return Array.from({ length: arity }, (_, i) => `_arg${i}`);
}

function buildClauseCondition(
  paramNames: string[],
  patternDescs: string[],
  isLast: boolean,
  constructorFields?: Map<string, string[]>,
): { condition: string; bindings: string[] } {
  // Parse pattern descriptions back to conditions
  const conditions: string[] = [];
  const bindings: string[] = [];

  for (let i = 0; i < patternDescs.length; i++) {
    const desc = patternDescs[i];
    const param = paramNames[i] ?? `_arg${i}`;

    // Check if it's a constructor pattern: "Name" or "Name(args...)"
    const ctorMatch = desc.match(/^([A-Z]\w*)(?:\(([^)]*)\))?$/);
    if (ctorMatch) {
      const ctorName = ctorMatch[1];
      conditions.push(`${param}.tag === "${ctorName}"`);
      if (ctorMatch[2]) {
        const args = ctorMatch[2].split(/,\s*/);
        const fieldNames = constructorFields?.get(ctorName);
        for (let j = 0; j < args.length; j++) {
          const varName = args[j].trim();
          const fieldName = fieldNames?.[j] ?? varName;
          bindings.push(`const ${tsName(varName)} = ${param}.${tsName(fieldName)};`);
        }
      }
    }
    // Otherwise it's a variable pattern — bind if different from param name
    else if (desc !== param) {
      bindings.push(`const ${tsName(desc)} = ${param};`);
    }
  }

  return {
    condition: conditions.length === 0 ? "true" : conditions.join(" && "),
    bindings,
  };
}

// ─── JavaScript code generation (no types) ─────────────────────────

/** Render an ExtractionResult as plain JavaScript. */
export function renderJavaScript(result: ExtractionResult): string {
  // Reuse TypeScript renderer, strip type annotations
  const ts = renderTypeScript(result);
  return ts
    .replace(/export type [^;]+;/g, "")
    .replace(/: any/g, "")
    .replace(/: \w+(<[^>]+>)?/g, "")
    .replace(/<[^>]+>/g, "")
    .replace(/\n{3,}/g, "\n\n")
    .trim() + "\n";
}
