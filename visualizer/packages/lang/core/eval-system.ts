// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, ModeDef, RuleDef, SystemDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import { buildProofTree, type ProvedContext, type ProofTree, resolveAssumptions, typecheckProve, withNormTable } from "./typecheck-prove.ts";
import type { ComputeRule, ConstructorTyping } from "./typecheck-prove.ts";

export function evalSystem(decl: AST.SystemDecl): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping } = evalBodyInto(decl.body, agents, rules, modes);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping }, proofTrees };
}

// Helper: evaluate a system body (agents/rules/modes/prove) and merge into
// existing collections, used by extend and compose.
// Returns any proof trees generated from typed prove blocks.
export function evalBodyInto(
  body: AST.SystemBody[],
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  modes: Map<string, ModeDef>,
  initialCtx?: ProvedContext,
  inheritedConstructors?: Map<string, Set<string>>,
  inheritedCompute?: ComputeRule[],
  inheritedCtorTyping?: ConstructorTyping,
): { proofTrees: ProofTree[]; provedCtx: ProvedContext; constructorsByType: Map<string, Set<string>>; computeRules: ComputeRule[]; constructorTyping: ConstructorTyping } {
  const provedCtx: ProvedContext = new Map(initialCtx);
  const proofTrees: ProofTree[] = [];
  const computeRules: ComputeRule[] = [...(inheritedCompute ?? [])];
  // Pre-scan: collect constructor families and compute rules before processing
  // Inherit from parent systems if available
  const constructorsByType = new Map<string, Set<string>>();
  const constructorTyping: ConstructorTyping = new Map(inheritedCtorTyping);
  if (inheritedConstructors) {
    for (const [type, ctors] of inheritedConstructors) {
      constructorsByType.set(type, new Set(ctors));
    }
  }
  for (const item of body) {
    if (item.kind === "data") {
      constructorsByType.set(item.name, new Set(item.constructors.map((c) => c.name)));
      // Build constructor typing for the type checker
      for (const ctor of item.constructors) {
        constructorTyping.set(ctor.name, { typeName: item.name, fields: ctor.fields });
      }
    } else if (item.kind === "prove") {
      const firstParam = item.params[0];
      if (firstParam?.type) {
        const typeName = firstParam.type.kind === "ident"
          ? firstParam.type.name
          : firstParam.type.kind === "call"
          ? firstParam.type.name
          : null;
        if (typeName) {
          if (!constructorsByType.has(typeName)) {
            constructorsByType.set(typeName, new Set());
          }
          const set = constructorsByType.get(typeName)!;
          for (const c of item.cases) set.add(c.pattern);
        }
      }
    }
  }
  // Pre-scan: collect all agent names (both explicit and from data) + inherited
  const knownAgents = new Set(agents.keys());
  for (const item of body) {
    if (item.kind === "agent") knownAgents.add(item.name);
    if (item.kind === "data") {
      for (const ctor of item.constructors) knownAgents.add(ctor.name);
    }
  }
  // Pre-scan: collect compute rules so they're available for type checking
  for (const item of body) {
    if (item.kind === "compute") {
      computeRules.push(astComputeToRule(item, knownAgents));
    }
  }

  for (const item of body) {
    switch (item.kind) {
      case "agent": {
        const agent = evalAgent(item);
        agents.set(agent.name, agent);
        break;
      }
      case "rule": {
        rules.push({
          agentA: item.agentA,
          agentB: item.agentB,
          action: item.action,
        });
        break;
      }
      case "mode": {
        modes.set(item.name, {
          name: item.name,
          excludedAgents: item.exclude,
        });
        break;
      }
      case "data": {
        // Sugar: desugar data declaration into constructor agents +
        // duplicator agent + duplicator rules, and register constructors.
        desugarData(item, agents, rules, constructorsByType);
        break;
      }
      case "prove": {
        // Expand induction(var) tactic into case arms with ? holes
        let prove = item;
        if (item.induction && item.cases.length === 0) {
          prove = expandInduction(item, agents, constructorsByType);
        }
        // Resolve assumption tactic to concrete proof terms
        prove = withNormTable(computeRules, () => resolveAssumptions(prove, provedCtx));
        const hasHoles = proveContainsHole(prove);
        const hasRewrites = proveContainsRewrite(prove);
        // Only generate agent + rules for complete proofs (no ? holes or rewrites)
        if (!hasHoles && !hasRewrites) {
          const stripped = stripProveTactics(prove);
          const { agentDecl, ruleDecls } = desugarProve(stripped, agents);
          const agent = evalAgent(agentDecl);
          agents.set(agent.name, agent);
          for (const r of ruleDecls) {
            rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
          }
        }
        // Mode-aware linearity check: error if prove needs erase/dup incompatible with modes
        const linearityErrors = checkProveLinearity(prove, agents, modes);
        // Type check if return type is annotated
        const typeErrors = typecheckProve(prove, provedCtx, constructorsByType, computeRules, constructorTyping);
        const allErrors = [...linearityErrors, ...typeErrors];
        if (allErrors.length > 0) {
          throw new EvalError(allErrors.join("\n"));
        }
        // Build proof derivation tree
        const tree = buildProofTree(prove, provedCtx, computeRules, constructorTyping);
        if (tree) proofTrees.push(tree);
        // Register this prove's type for cross-lemma resolution
        if (prove.returnType) {
          provedCtx.set(prove.name, {
            params: item.params,
            returnType: item.returnType!,
          });
        }
        break;
      }
      case "compute": {
        // Already pre-scanned into computeRules above
        break;
      }
    }
  }
  return { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping };
}

// ─── Extend: system "B" extends "A" with additional declarations ──

export function evalExtend(
  decl: AST.ExtendDecl,
  systems: Map<string, SystemDef>,
): { sys: SystemDef; proofTrees: ProofTree[] } {
  const base = systems.get(decl.base);
  if (!base) throw new EvalError(`Cannot extend unknown system '${decl.base}'`);

  // Copy base system contents
  const agents = new Map(base.agents);
  const rules = [...base.rules];
  const modes = new Map(base.modes);

  // Merge new declarations — inherit base system's proved propositions and constructors
  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping } = evalBodyInto(decl.body, agents, rules, modes, base.provedCtx, base.constructorsByType, base.computeRules, base.constructorTyping);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping }, proofTrees };
}

// ─── Compose (pushout): union of component systems + cross-rules ──

export function evalCompose(
  decl: AST.ComposeDecl,
  systems: Map<string, SystemDef>,
): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();
  const mergedCtx: ProvedContext = new Map();
  const mergedConstructors = new Map<string, Set<string>>();
  const mergedCompute: ComputeRule[] = [];
  const mergedCtorTyping: ConstructorTyping = new Map();

  // Union: merge all agents, rules, modes, proved context from each component
  for (const compName of decl.components) {
    const comp = systems.get(compName);
    if (!comp) {
      throw new EvalError(`Cannot compose unknown system '${compName}'`);
    }

    // Agents: shared agents (same name) are identified (pushout colimit)
    for (const [name, agent] of comp.agents) {
      agents.set(name, agent);
    }

    // Rules: collect all, dedup by (agentA, agentB) pair
    for (const rule of comp.rules) {
      const dup = rules.some(
        (r) =>
          (r.agentA === rule.agentA && r.agentB === rule.agentB) ||
          (r.agentA === rule.agentB && r.agentB === rule.agentA),
      );
      if (!dup) rules.push(rule);
    }

    // Modes: merge
    for (const [name, mode] of comp.modes) {
      modes.set(name, mode);
    }

    // Proved context: merge
    for (const [name, entry] of comp.provedCtx) {
      mergedCtx.set(name, entry);
    }

    // Constructors: merge
    for (const [type, ctors] of comp.constructorsByType) {
      if (!mergedConstructors.has(type)) mergedConstructors.set(type, new Set());
      for (const c of ctors) mergedConstructors.get(type)!.add(c);
    }

    // Compute rules: merge
    mergedCompute.push(...comp.computeRules);

    // Constructor typing: merge
    for (const [name, info] of comp.constructorTyping) {
      mergedCtorTyping.set(name, info);
    }
  }

  // Add cross-interaction rules from the compose body (the pushout span)
  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping } = evalBodyInto(decl.body, agents, rules, modes, mergedCtx, mergedConstructors, mergedCompute, mergedCtorTyping);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping }, proofTrees };
}

// ─── Agent evaluation ──────────────────────────────────────────────

export function evalAgent(decl: AST.AgentDecl): AgentDef {
  const portIndex = new Map<string, number>();
  decl.ports.forEach((p, i) => portIndex.set(p.name, i));
  return { name: decl.name, ports: decl.ports, portIndex };
}

// ─── Prove desugaring ──────────────────────────────────────────────
// Translates a `prove` declaration into an agent + rules.

function desugarProve(
  prove: AST.ProveDecl,
  agents: Map<string, AgentDef>,
): { agentDecl: AST.AgentDecl; ruleDecls: AST.RuleDecl[] } {
  const auxParams = prove.params.slice(1).map((p) => p.name);
  const ports: AST.PortDef[] = [
    { name: "principal", variadic: false },
    { name: "result", variadic: false },
    ...auxParams.map((p) => ({ name: p, variadic: false })),
  ];
  const agentDecl: AST.AgentDecl = { kind: "agent", name: prove.name, ports };
  agents.set(prove.name, evalAgent(agentDecl));

  const ruleDecls: AST.RuleDecl[] = [];

  for (const caseArm of prove.cases) {
    const consDef = agents.get(caseArm.pattern);
    if (!consDef) throw new EvalError(`prove ${prove.name}: unknown constructor '${caseArm.pattern}'`);
    const consAuxPorts = consDef.ports.slice(1);
    if (caseArm.bindings.length > consAuxPorts.length) {
      throw new EvalError(`prove ${prove.name}: too many bindings for ${caseArm.pattern}`);
    }

    // Variable map: binding/param → port reference
    const varMap = new Map<string, AST.PortRef>();
    for (let i = 0; i < caseArm.bindings.length; i++) {
      varMap.set(caseArm.bindings[i], { node: "right", port: consAuxPorts[i].name });
    }
    for (const p of auxParams) varMap.set(p, { node: "left", port: p });

    const usedVars = new Set<string>();
    let counter = 0;
    const stmts: AST.RuleStmt[] = [];

    // Connect src→dst, choosing relink vs wire based on pre-existing status
    function connect(src: AST.PortRef, dst: AST.PortRef) {
      const kind = isPreExisting(src) || isPreExisting(dst) ? "relink" : "wire";
      stmts.push({ kind, portA: src, portB: dst } as AST.RuleStmt);
    }

    // Auto-duplication: build dup chains for multi-use variables
    const copyQueues = new Map<string, AST.PortRef[]>();
    const varNames = new Set(varMap.keys());
    for (const [varName, count] of countVarUses(caseArm.body, varNames)) {
      if (count <= 1) continue;
      const paramInfo = prove.params.find((p) => p.name === varName);
      const typeExpr = paramInfo?.type ?? prove.params[0]?.type;
      const typeName = typeExpr?.kind === "ident" ? typeExpr.name
        : typeExpr?.kind === "call" ? typeExpr.name : null;
      if (!typeName) throw new EvalError(
        `prove ${prove.name}: variable '${varName}' used ${count} times but no type annotation for duplication`);
      const dupAgent = `dup_${typeName.toLowerCase()}`;
      if (!agents.has(dupAgent)) throw new EvalError(
        `prove ${prove.name}: duplicator '${dupAgent}' required for multi-use variable '${varName}' but not defined`);

      const queue: AST.PortRef[] = [];
      let input = varMap.get(varName)!;
      for (let remaining = count; remaining > 1; remaining--) {
        const label = `_d${counter++}`;
        stmts.push({ kind: "let", varName: label, agentType: dupAgent });
        connect(input, { node: label, port: "principal" });
        queue.push({ node: label, port: "copy1" });
        input = remaining > 2 ? { node: label, port: "copy2" } : input;
        if (remaining === 2) queue.push({ node: label, port: "copy2" });
      }
      copyQueues.set(varName, queue);
      usedVars.add(varName);
    }

    function translateExpr(expr: AST.ProveExpr): AST.PortRef {
      if (expr.kind === "hole") throw new EvalError(`prove ${prove.name}: unexpected ? hole in desugaring`);
      if (expr.kind === "ident") {
        if (copyQueues.has(expr.name)) { usedVars.add(expr.name); return copyQueues.get(expr.name)!.shift()!; }
        if (varMap.has(expr.name)) { usedVars.add(expr.name); return varMap.get(expr.name)!; }
        const label = `_p${counter++}`;
        stmts.push({ kind: "let", varName: label, agentType: expr.name });
        return { node: label, port: "principal" };
      }
      const agentDef = agents.get(expr.name);
      if (!agentDef) throw new EvalError(`prove ${prove.name}: unknown agent '${expr.name}'`);
      const label = `_p${counter++}`;
      stmts.push({ kind: "let", varName: label, agentType: expr.name });
      const hasResult = agentDef.ports.length > 1 && agentDef.ports[1].name === "result";
      const argPorts = hasResult
        ? [agentDef.ports[0].name, ...agentDef.ports.slice(2).map((p) => p.name)]
        : agentDef.ports.slice(1).map((p) => p.name);
      for (let i = 0; i < expr.args.length; i++) {
        connect(translateExpr(expr.args[i]), { node: label, port: argPorts[i] });
      }
      return { node: label, port: hasResult ? "result" : "principal" };
    }

    connect(translateExpr(caseArm.body), { node: "left", port: "result" });

    // Erase unused variables
    for (const p of auxParams) {
      if (!usedVars.has(p)) stmts.push({ kind: "erase-stmt", port: { node: "left", port: p } });
    }
    for (let i = 0; i < caseArm.bindings.length; i++) {
      if (!usedVars.has(caseArm.bindings[i])) {
        stmts.push({ kind: "erase-stmt", port: { node: "right", port: consAuxPorts[i].name } });
      }
    }

    ruleDecls.push({ kind: "rule", agentA: prove.name, agentB: caseArm.pattern, action: { kind: "custom", body: stmts } });
  }

  return { agentDecl, ruleDecls };
}

/** Expand induction(var) into case arms with ? holes for each constructor. */
function expandInduction(
  prove: AST.ProveDecl,
  agents: Map<string, AgentDef>,
  constructorsByType: Map<string, Set<string>>,
): AST.ProveDecl {
  const varName = prove.induction!;
  const param = prove.params.find((p) => p.name === varName);
  if (!param?.type) {
    throw new EvalError(
      `prove ${prove.name}: induction variable '${varName}' has no type annotation`,
    );
  }
  const typeName = param.type.kind === "ident"
    ? param.type.name
    : param.type.kind === "call"
    ? param.type.name
    : null;
  if (!typeName || !constructorsByType.has(typeName)) {
    throw new EvalError(
      `prove ${prove.name}: no constructors known for type '${typeName ?? "?"}'`,
    );
  }
  const constructors = constructorsByType.get(typeName)!;
  const cases: AST.ProveCase[] = [];
  for (const consName of constructors) {
    const consDef = agents.get(consName);
    // Aux ports = all ports except principal (index 0)
    const auxPorts = consDef ? consDef.ports.slice(1) : [];
    const bindings = auxPorts.map((p) => p.name);
    cases.push({ pattern: consName, bindings, body: { kind: "hole" } });
  }
  return { ...prove, cases, induction: undefined };
}

function isPreExisting(ref: AST.PortRef): boolean {
  return ref.node === "left" || ref.node === "right";
}

// ─── Mode-aware linearity checking ────────────────────────────────
// Check whether a prove block's variable usage is compatible with all declared
// modes in the system.  Returns warning strings (non-fatal).

export function checkProveLinearity(
  prove: AST.ProveDecl,
  agents: Map<string, AgentDef>,
  modes: Map<string, ModeDef>,
): string[] {
  if (modes.size === 0) return [];
  if (prove.cases.length === 0) return [];

  // Determine which modes forbid erase and which forbid duplication
  const modesExcludingErase: string[] = [];
  const modesExcludingDup: string[] = [];

  for (const [modeName, mode] of modes) {
    if (mode.excludedAgents.some((a) => a === "era" || a.startsWith("era"))) {
      modesExcludingErase.push(modeName);
    }
    if (mode.excludedAgents.some((a) => a.startsWith("dup_") || a.startsWith("rep"))) {
      modesExcludingDup.push(modeName);
    }
  }

  if (modesExcludingErase.length === 0 && modesExcludingDup.length === 0) return [];

  const auxParamNames = prove.params.slice(1).map((p) => p.name);
  const warnings: string[] = [];

  for (const caseArm of prove.cases) {
    if (caseArm.body.kind === "hole") continue; // skip incomplete cases

    const allVars = new Set<string>([
      ...caseArm.bindings,
      ...auxParamNames,
    ]);
    const useCounts = countVarUses(caseArm.body, allVars);

    // Check for unused variables (would require erase)
    if (modesExcludingErase.length > 0) {
      const unused: string[] = [];
      for (const v of allVars) {
        if ((useCounts.get(v) ?? 0) === 0) unused.push(v);
      }
      if (unused.length > 0) {
        warnings.push(
          `prove ${prove.name}, case ${caseArm.pattern}: ` +
            `unused variable(s) ${unused.join(", ")} require implicit erasure ` +
            `(incompatible with mode${modesExcludingErase.length > 1 ? "s" : ""} ${modesExcludingErase.join(", ")})`,
        );
      }
    }

    // Check for multi-use variables (would require duplication)
    if (modesExcludingDup.length > 0) {
      const multiUse: string[] = [];
      for (const [v, count] of useCounts) {
        if (count > 1) multiUse.push(`${v} (×${count})`);
      }
      if (multiUse.length > 0) {
        warnings.push(
          `prove ${prove.name}, case ${caseArm.pattern}: ` +
            `multi-use variable(s) ${multiUse.join(", ")} require implicit duplication ` +
            `(incompatible with mode${modesExcludingDup.length > 1 ? "s" : ""} ${modesExcludingDup.join(", ")})`,
        );
      }
    }
  }
  return warnings;
}

// Count how many times each variable from `vars` appears in expr
function countVarUses(
  expr: AST.ProveExpr,
  vars: Set<string>,
): Map<string, number> {
  const counts = new Map<string, number>();
  function walk(e: AST.ProveExpr) {
    if (e.kind === "ident" && vars.has(e.name)) {
      counts.set(e.name, (counts.get(e.name) || 0) + 1);
    } else if (e.kind === "call") {
      for (const arg of e.args) walk(arg);
    }
  }
  walk(expr);
  return counts;
}

function exprContainsHole(e: AST.ProveExpr): boolean {
  if (e.kind === "hole") return true;
  if (e.kind === "call") return e.args.some(exprContainsHole);
  return false;
}

function proveContainsHole(prove: AST.ProveDecl): boolean {
  return prove.cases.some((c) => exprContainsHole(c.body));
}

function exprContainsRewrite(e: AST.ProveExpr): boolean {
  if (e.kind === "call" && e.name === "rewrite") return true;
  if (e.kind === "call") return e.args.some(exprContainsRewrite);
  return false;
}

function proveContainsRewrite(prove: AST.ProveDecl): boolean {
  return prove.cases.some((c) => exprContainsRewrite(c.body));
}

/** Strip exact/apply tactic sugar from prove bodies for desugaring. */
function stripProveTactics(prove: AST.ProveDecl): AST.ProveDecl {
  return {
    ...prove,
    cases: prove.cases.map((c) => ({ ...c, body: normalizeProofExpr(stripExprTactics(c.body)) })),
  };
}

/** Normalize proof-level projections: fst(pair(a,b))→a, snd(pair(a,b))→b. */
function normalizeProofExpr(expr: AST.ProveExpr): AST.ProveExpr {
  if (expr.kind !== "call") return expr;
  const args = expr.args.map(normalizeProofExpr);
  const e: AST.ProveExpr = { kind: "call", name: expr.name, args };
  if (e.name === "fst" && e.args.length === 1 &&
      e.args[0].kind === "call" && e.args[0].name === "pair" && e.args[0].args.length === 2) {
    return e.args[0].args[0];
  }
  if (e.name === "snd" && e.args.length === 1 &&
      e.args[0].kind === "call" && e.args[0].name === "pair" && e.args[0].args.length === 2) {
    return e.args[0].args[1];
  }
  return e;
}

function stripExprTactics(expr: AST.ProveExpr): AST.ProveExpr {
  if (expr.kind !== "call") return expr;
  if (expr.name === "exact" && expr.args.length === 1) return stripExprTactics(expr.args[0]);
  if (expr.name === "apply" && expr.args.length >= 1 && expr.args[0].kind === "ident") {
    return { kind: "call", name: expr.args[0].name, args: expr.args.slice(1).map(stripExprTactics) };
  }
  return { kind: "call", name: expr.name, args: expr.args.map(stripExprTactics) };
}

// ─── Data desugaring (syntactic sugar) ─────────────────────────────
// Expands a `data` declaration into constructor agents, a duplicator
// agent, and one duplicator rule per constructor.
//
// Example:  data Nat { | Zero | Succ(pred : Nat) }
// Produces:
//   agent Zero(principal)
//   agent Succ(principal, pred)
//   agent dup_nat(principal, copy1, copy2)
//   rule dup_nat <> Zero -> { ... }
//   rule dup_nat <> Succ -> { ... }

function desugarData(
  decl: AST.DataDecl,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  constructorsByType: Map<string, Set<string>>,
): void {
  // 1. Register constructor families
  constructorsByType.set(decl.name, new Set(decl.constructors.map((c) => c.name)));

  // 2. Emit constructor agents
  for (const ctor of decl.constructors) {
    const ports: AST.PortDef[] = [
      { name: "principal", variadic: false },
      ...ctor.fields.map((f) => ({ name: f.name, variadic: false })),
    ];
    const agentDecl: AST.AgentDecl = { kind: "agent", name: ctor.name, ports };
    agents.set(ctor.name, evalAgent(agentDecl));
  }

  // 3. Emit dup_<type> agent + one rule per constructor
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

/** Build the custom rule body for `dup_<type> <> Constructor`. */
function buildDupRule(ctor: AST.DataConstructor, typeName: string): AST.CustomAction {
  const stmts: AST.RuleStmt[] = [];
  // Let: create two fresh copies of the constructor
  stmts.push({ kind: "let", varName: "_c1", agentType: ctor.name });
  stmts.push({ kind: "let", varName: "_c2", agentType: ctor.name });
  // Relink: copy1 ← _c1.principal, copy2 ← _c2.principal
  stmts.push({ kind: "relink", portA: { node: "left", port: "copy1" }, portB: { node: "_c1", port: "principal" } });
  stmts.push({ kind: "relink", portA: { node: "left", port: "copy2" }, portB: { node: "_c2", port: "principal" } });

  // For each field: create a sub-duplicator and wire it through
  for (let i = 0; i < ctor.fields.length; i++) {
    const field = ctor.fields[i];
    const subDup = `dup_${field.type.toLowerCase()}`;
    const varName = `_d${i}`;
    stmts.push({ kind: "let", varName, agentType: subDup });
    stmts.push({ kind: "relink", portA: { node: "right", port: field.name }, portB: { node: varName, port: "principal" } });
    stmts.push({ kind: "wire", portA: { node: varName, port: "copy1" }, portB: { node: "_c1", port: field.name } });
    stmts.push({ kind: "wire", portA: { node: varName, port: "copy2" }, portB: { node: "_c2", port: field.name } });
  }

  return { kind: "custom", body: stmts };
}

// ─── Compute rule conversion ───────────────────────────────────────
// Converts an AST ComputeDecl into the internal ComputeRule format
// used by the type checker's normalizer.

function astComputeToRule(decl: AST.ComputeDecl, knownAgents: Set<string>): ComputeRule {
  // Resolve var patterns: if a "var" pattern name matches a known agent,
  // upgrade it to a nullary ctor pattern (e.g., Zero, True, Nil).
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
