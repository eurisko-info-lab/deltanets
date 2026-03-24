// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Data/Record/Codata Desugaring
// Expands data, record, codata declarations into agents + rules.
// Also: evalAgent, mutual positivity/termination, eliminators.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, RuleDef, SystemDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import type { ComputeRule, ConstructorTyping } from "./normalize.ts";

// ─── Agent evaluation ──────────────────────────────────────────────

export function evalAgent(decl: AST.AgentDecl): AgentDef {
  const portIndex = new Map<string, number>();
  decl.ports.forEach((p, i) => portIndex.set(p.name, i));
  return { name: decl.name, ports: decl.ports, portIndex };
}

// ─── Expression pretty-printing (for error messages) ───────────────

function exprToString(e: AST.ProveExpr): string {
  if (e.kind === "ident") return e.name;
  if (e.kind === "call") return `${e.name}(${e.args.map(exprToString).join(", ")})`;
  if (e.kind === "hole") return "?";
  if (e.kind === "pi") return `(${e.param} : ${exprToString(e.domain)}) -> ${exprToString(e.codomain)}`;
  return e.kind;
}

// ─── Data desugaring ───────────────────────────────────────────────

/** Extract the base type name from a field type expression (lowercase). */
function fieldTypeBaseName(type: AST.ProveExpr): string {
  if (type.kind === "ident") return type.name.toLowerCase();
  if (type.kind === "call") return type.name.toLowerCase();
  return "unknown";
}

export function desugarData(
  decl: AST.DataDecl,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  constructorsByType: Map<string, Set<string>>,
): void {
  constructorsByType.set(decl.name, new Set(decl.constructors.map((c) => c.name)));

  for (const ctor of decl.constructors) {
    const ports: AST.PortDef[] = [
      { name: "principal", variadic: false },
      ...ctor.fields.map((f) => ({ name: f.name, variadic: false })),
    ];
    const agentDecl: AST.AgentDecl = { kind: "agent", name: ctor.name, ports };
    agents.set(ctor.name, evalAgent(agentDecl));
  }

  const dupName = `dup_${decl.name.toLowerCase()}`;
  const dupPorts: AST.PortDef[] = [
    { name: "principal", variadic: false },
    { name: "copy1", variadic: false },
    { name: "copy2", variadic: false },
  ];
  agents.set(dupName, evalAgent({ kind: "agent", name: dupName, ports: dupPorts }));

  for (const ctor of decl.constructors) {
    rules.push({
      agentA: dupName,
      agentB: ctor.name,
      action: buildDupRule(ctor, decl.name),
    });
  }
}

function buildDupRule(ctor: AST.DataConstructor, typeName: string): AST.CustomAction {
  const stmts: AST.RuleStmt[] = [];
  stmts.push({ kind: "let", varName: "_c1", agentType: ctor.name });
  stmts.push({ kind: "let", varName: "_c2", agentType: ctor.name });
  stmts.push({ kind: "relink", portA: { node: "left", port: "copy1" }, portB: { node: "_c1", port: "principal" } });
  stmts.push({ kind: "relink", portA: { node: "left", port: "copy2" }, portB: { node: "_c2", port: "principal" } });

  for (let i = 0; i < ctor.fields.length; i++) {
    const field = ctor.fields[i];
    const subDup = `dup_${fieldTypeBaseName(field.type)}`;
    const varName = `_d${i}`;
    stmts.push({ kind: "let", varName, agentType: subDup });
    stmts.push({ kind: "relink", portA: { node: "right", port: field.name }, portB: { node: varName, port: "principal" } });
    stmts.push({ kind: "wire", portA: { node: varName, port: "copy1" }, portB: { node: "_c1", port: field.name } });
    stmts.push({ kind: "wire", portA: { node: varName, port: "copy2" }, portB: { node: "_c2", port: field.name } });
  }

  return { kind: "custom", body: stmts };
}

// ─── Auto-generated eliminators ────────────────────────────────────

export function generateEliminatorRules(decl: AST.DataDecl): ComputeRule[] {
  const rules: ComputeRule[] = [];
  const recName = `${decl.name}_rec`;
  const methodNames = decl.constructors.map((_, i) => `_m${i}`);

  for (let ci = 0; ci < decl.constructors.length; ci++) {
    const ctor = decl.constructors[ci];
    const fieldVars = ctor.fields.map((f, fi) => `_f${fi}`);
    const isRecursive = ctor.fields.map((f) => {
      const baseName = f.type.kind === "ident" ? f.type.name : f.type.kind === "call" ? f.type.name : "";
      return baseName === decl.name;
    });

    const scrutineePattern: AST.ComputePattern = {
      kind: "ctor" as const,
      name: ctor.name,
      args: fieldVars,
    };
    const methodPatterns: AST.ComputePattern[] = methodNames.map((n) => ({
      kind: "var" as const,
      name: n,
    }));
    const args = [scrutineePattern, ...methodPatterns];

    const resultArgs: AST.ProveExpr[] = [];
    for (let fi = 0; fi < ctor.fields.length; fi++) {
      if (isRecursive[fi]) {
        const recCall: AST.ProveExpr = {
          kind: "call",
          name: recName,
          args: [
            { kind: "ident", name: fieldVars[fi] },
            ...methodNames.map((n): AST.ProveExpr => ({ kind: "ident", name: n })),
          ],
        };
        resultArgs.push(recCall);
      } else {
        resultArgs.push({ kind: "ident", name: fieldVars[fi] });
      }
    }

    const result: AST.ProveExpr = resultArgs.length > 0
      ? { kind: "call", name: methodNames[ci], args: resultArgs }
      : { kind: "ident", name: methodNames[ci] };

    rules.push({ funcName: recName, args, result });
  }
  return rules;
}

// ─── Mutual eliminator generation ──────────────────────────────────

export function generateMutualEliminatorRules(group: AST.DataDecl[]): ComputeRule[] {
  const rules: ComputeRule[] = [];
  const groupNames = new Set(group.map((d) => d.name));

  const allMethods: string[] = [];
  for (const decl of group) {
    for (let ci = 0; ci < decl.constructors.length; ci++) {
      allMethods.push(`_m${allMethods.length}`);
    }
  }
  const methodPatterns: AST.ComputePattern[] = allMethods.map((n) => ({
    kind: "var" as const,
    name: n,
  }));

  let methodIdx = 0;
  for (const decl of group) {
    const recName = `${decl.name}_rec`;
    for (let ci = 0; ci < decl.constructors.length; ci++) {
      const ctor = decl.constructors[ci];
      const fieldVars = ctor.fields.map((_, fi) => `_f${fi}`);

      const scrutineePattern: AST.ComputePattern = {
        kind: "ctor" as const,
        name: ctor.name,
        args: fieldVars,
      };
      const args = [scrutineePattern, ...methodPatterns];

      const mi = allMethods[methodIdx + ci];
      const resultArgs: AST.ProveExpr[] = [];
      for (let fi = 0; fi < ctor.fields.length; fi++) {
        const f = ctor.fields[fi];
        const baseName = f.type.kind === "ident"
          ? f.type.name
          : f.type.kind === "call"
          ? f.type.name
          : "";
        if (groupNames.has(baseName)) {
          const crossRec: AST.ProveExpr = {
            kind: "call",
            name: `${baseName}_rec`,
            args: [
              { kind: "ident", name: fieldVars[fi] },
              ...allMethods.map((n): AST.ProveExpr => ({ kind: "ident", name: n })),
            ],
          };
          resultArgs.push(crossRec);
        } else {
          resultArgs.push({ kind: "ident", name: fieldVars[fi] });
        }
      }

      const result: AST.ProveExpr = resultArgs.length > 0
        ? { kind: "call", name: mi, args: resultArgs }
        : { kind: "ident", name: mi };

      rules.push({ funcName: recName, args, result });
    }
    methodIdx += decl.constructors.length;
  }
  return rules;
}

// ─── Joint positivity checking ─────────────────────────────────────

export function checkMutualPositivity(group: AST.DataDecl[]): string[] {
  const errors: string[] = [];
  const groupNames = new Set(group.map((d) => d.name));

  function occursNegative(expr: AST.ProveExpr, names: Set<string>): boolean {
    if (expr.kind === "ident") return false;
    if (expr.kind === "call") {
      return expr.args.some((a) => occursNegative(a, names));
    }
    if (expr.kind === "pi" || expr.kind === "sigma") {
      if (mentionsAny(expr.domain, names)) return true;
      return occursNegative(expr.codomain, names);
    }
    if (expr.kind === "lambda") {
      if (mentionsAny(expr.paramType, names)) return true;
      return occursNegative(expr.body, names);
    }
    return false;
  }

  function mentionsAny(expr: AST.ProveExpr, names: Set<string>): boolean {
    if (expr.kind === "ident") return names.has(expr.name);
    if (expr.kind === "call") {
      return names.has(expr.name) || expr.args.some((a) => mentionsAny(a, names));
    }
    if (expr.kind === "pi" || expr.kind === "sigma") {
      return mentionsAny(expr.domain, names) || mentionsAny(expr.codomain, names);
    }
    if (expr.kind === "lambda") {
      return mentionsAny(expr.paramType, names) || mentionsAny(expr.body, names);
    }
    if (expr.kind === "let") {
      return mentionsAny(expr.value, names) || mentionsAny(expr.body, names);
    }
    if (expr.kind === "match") {
      return expr.cases.some((c) => mentionsAny(c.body, names));
    }
    return false;
  }

  for (const decl of group) {
    for (const ctor of decl.constructors) {
      for (const field of ctor.fields) {
        if (occursNegative(field.type, groupNames)) {
          errors.push(
            `mutual positivity: type ${decl.name}, constructor ${ctor.name}, ` +
            `field ${field.name} — a mutual type appears in negative position in ${exprToString(field.type)}`,
          );
        }
      }
    }
  }
  return errors;
}

// ─── Mutual termination checking ───────────────────────────────────

export function checkMutualTermination(
  prove: AST.ProveDecl,
  mutualNames: Set<string>,
): string[] {
  if (prove.wf) return [];
  const errors: string[] = [];
  const siblings = new Set([...mutualNames].filter((n) => n !== prove.name));
  if (siblings.size === 0) return errors;

  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue;
    const topBindings = new Set(caseArm.bindings);
    const calls = collectCrossRecCalls(caseArm.body, siblings, topBindings);
    for (const { call, bindings } of calls) {
      if (call.kind !== "call" || call.args.length === 0) continue;
      const hasDecreasing = call.args.some(
        (a) => a.kind === "ident" && bindings.has(a.name),
      );
      if (!hasDecreasing) {
        errors.push(
          `prove ${prove.name}, case ${caseArm.pattern}: mutual call ` +
          `${call.name}(${call.args.map(exprToString).join(", ")}) ` +
          `is not structurally decreasing — at least one argument must be a case binding` +
          (bindings.size > 0 ? ` (${[...bindings].join(", ")})` : ``),
        );
      }
    }
  }
  return errors;
}

function collectCrossRecCalls(
  expr: AST.ProveExpr,
  funcNames: Set<string>,
  activeBindings: Set<string>,
): { call: AST.ProveExpr; bindings: Set<string> }[] {
  const calls: { call: AST.ProveExpr; bindings: Set<string> }[] = [];
  function walk(e: AST.ProveExpr, bindings: Set<string>) {
    if (e.kind === "call") {
      if (funcNames.has(e.name)) calls.push({ call: e, bindings });
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

// ─── Record desugaring ─────────────────────────────────────────────

export function desugarRecord(
  decl: AST.RecordDecl,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  constructorsByType: Map<string, Set<string>>,
  computeRules: ComputeRule[],
  constructorTyping: ConstructorTyping,
): void {
  const ctorName = `mk${decl.name}`;

  const dataDecl: AST.DataDecl = {
    kind: "data",
    name: decl.name,
    params: decl.params,
    indices: [],
    constructors: [{ name: ctorName, fields: decl.fields }],
  };
  desugarData(dataDecl, agents, rules, constructorsByType);

  for (let i = 0; i < decl.fields.length; i++) {
    const field = decl.fields[i];
    const projPorts: AST.PortDef[] = [
      { name: "principal", variadic: false },
      { name: "result", variadic: false },
    ];
    agents.set(field.name, evalAgent({ kind: "agent", name: field.name, ports: projPorts }));

    const stmts: AST.RuleStmt[] = [];
    stmts.push({
      kind: "relink",
      portA: { node: "left", port: "result" },
      portB: { node: "right", port: field.name },
    });
    for (let j = 0; j < decl.fields.length; j++) {
      if (j !== i) {
        stmts.push({ kind: "erase-stmt", port: { node: "right", port: decl.fields[j].name } });
      }
    }
    rules.push({
      agentA: field.name,
      agentB: ctorName,
      action: { kind: "custom", body: stmts },
    });
  }
}

// ─── Codata desugaring ─────────────────────────────────────────────

export function desugarCodata(
  decl: AST.CodataDecl,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  constructorsByType: Map<string, Set<string>>,
): void {
  const guardName = `guard_${decl.name.toLowerCase()}`;

  const dataDecl: AST.DataDecl = {
    kind: "data",
    name: decl.name,
    params: decl.params,
    indices: [],
    constructors: [{ name: guardName, fields: decl.fields }],
  };
  desugarData(dataDecl, agents, rules, constructorsByType);

  for (let i = 0; i < decl.fields.length; i++) {
    const field = decl.fields[i];
    const obsPorts: AST.PortDef[] = [
      { name: "principal", variadic: false },
      { name: "result", variadic: false },
    ];
    agents.set(field.name, evalAgent({ kind: "agent", name: field.name, ports: obsPorts }));

    const stmts: AST.RuleStmt[] = [];
    stmts.push({
      kind: "relink",
      portA: { node: "left", port: "result" },
      portB: { node: "right", port: field.name },
    });
    for (let j = 0; j < decl.fields.length; j++) {
      if (j !== i) {
        stmts.push({ kind: "erase-stmt", port: { node: "right", port: decl.fields[j].name } });
      }
    }
    rules.push({
      agentA: field.name,
      agentB: guardName,
      action: { kind: "custom", body: stmts },
    });
  }
}

// ─── Projection / observation compute rules ────────────────────────

export function generateProjectionRules(decl: AST.RecordDecl): ComputeRule[] {
  const ctorName = `mk${decl.name}`;
  const rules: ComputeRule[] = [];
  const fieldVars = decl.fields.map((_, fi) => `_f${fi}`);

  for (let i = 0; i < decl.fields.length; i++) {
    const field = decl.fields[i];
    rules.push({
      funcName: field.name,
      args: [{
        kind: "ctor",
        name: ctorName,
        args: fieldVars,
      }],
      result: { kind: "ident", name: fieldVars[i] },
    });
  }
  return rules;
}

export function generateObservationRules(decl: AST.CodataDecl): ComputeRule[] {
  const guardName = `guard_${decl.name.toLowerCase()}`;
  const rules: ComputeRule[] = [];
  const fieldVars = decl.fields.map((_, fi) => `_f${fi}`);

  for (let i = 0; i < decl.fields.length; i++) {
    const field = decl.fields[i];
    rules.push({
      funcName: field.name,
      args: [{
        kind: "ctor",
        name: guardName,
        args: fieldVars,
      }],
      result: { kind: "ident", name: fieldVars[i] },
    });
  }
  return rules;
}

// ─── Open/Export helpers ───────────────────────────────────────────

export function getVisibleAgents(source: SystemDef, selectNames?: string[]): Set<string> {
  let visible = new Set(source.agents.keys());
  if (source.exports) {
    visible = new Set([...visible].filter(n => source.exports!.has(n)));
  }
  if (selectNames) {
    visible = new Set(selectNames.filter(n => visible.has(n)));
  }
  return visible;
}

// ─── Compute rule conversion ───────────────────────────────────────

export function astComputeToRule(decl: AST.ComputeDecl, knownAgents: Set<string>): ComputeRule {
  const resolvedArgs = decl.args.map((pat): AST.ComputePattern => {
    if (pat.kind === "var" && knownAgents.has(pat.name)) {
      return { kind: "ctor", name: pat.name, args: [] };
    }
    return pat;
  });
  return {
    funcName: decl.funcName,
    args: resolvedArgs,
    result: decl.result,
  };
}
