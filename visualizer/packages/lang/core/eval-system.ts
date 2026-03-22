// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, ModeDef, RuleDef, SystemDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import { buildProofTree, type ProvedContext, type ProofTree, resolveAssumptions, typecheckProve } from "./typecheck-prove.ts";

export function evalSystem(decl: AST.SystemDecl): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  const { proofTrees, provedCtx, constructorsByType } = evalBodyInto(decl.body, agents, rules, modes);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType }, proofTrees };
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
): { proofTrees: ProofTree[]; provedCtx: ProvedContext; constructorsByType: Map<string, Set<string>> } {
  const provedCtx: ProvedContext = new Map(initialCtx);
  const proofTrees: ProofTree[] = [];
  // Pre-scan: collect constructor families from ALL prove blocks before processing
  // Inherit from parent systems if available
  const constructorsByType = new Map<string, Set<string>>();
  if (inheritedConstructors) {
    for (const [type, ctors] of inheritedConstructors) {
      constructorsByType.set(type, new Set(ctors));
    }
  }
  for (const item of body) {
    if (item.kind === "prove") {
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
      case "prove": {
        // Expand induction(var) tactic into case arms with ? holes
        let prove = item;
        if (item.induction && item.cases.length === 0) {
          prove = expandInduction(item, agents, constructorsByType);
        }
        // Resolve assumption tactic to concrete proof terms
        prove = resolveAssumptions(prove, provedCtx);
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
        const typeErrors = typecheckProve(prove, provedCtx, constructorsByType);
        const allErrors = [...linearityErrors, ...typeErrors];
        if (allErrors.length > 0) {
          throw new EvalError(allErrors.join("\n"));
        }
        // Build proof derivation tree
        const tree = buildProofTree(prove, provedCtx);
        if (tree) proofTrees.push(tree);
        // Register this prove's type for cross-lemma resolution
        if (prove.returnType) {
          provedCtx.set(prove.name, {
            params: item.params,
            returnType: item.returnType,
          });
        }
        break;
      }
    }
  }
  return { proofTrees, provedCtx, constructorsByType };
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
  const { proofTrees, provedCtx, constructorsByType } = evalBodyInto(decl.body, agents, rules, modes, base.provedCtx, base.constructorsByType);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType }, proofTrees };
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
  }

  // Add cross-interaction rules from the compose body (the pushout span)
  const { proofTrees, provedCtx, constructorsByType } = evalBodyInto(decl.body, agents, rules, modes, mergedCtx, mergedConstructors);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType }, proofTrees };
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
  // Build agent: (principal, result, ...auxParams)
  const auxParamNames = prove.params.slice(1).map((p) => p.name);
  const ports: AST.PortDef[] = [
    { name: "principal", variadic: false },
    { name: "result", variadic: false },
    ...auxParamNames.map((p) => ({ name: p, variadic: false })),
  ];
  const agentDecl: AST.AgentDecl = { kind: "agent", name: prove.name, ports };

  // Register the agent so recursive calls can resolve ports
  const selfAgent = evalAgent(agentDecl);
  agents.set(prove.name, selfAgent);

  const ruleDecls: AST.RuleDecl[] = [];

  for (const caseArm of prove.cases) {
    const consDef = agents.get(caseArm.pattern);
    if (!consDef) {
      throw new EvalError(
        `prove ${prove.name}: unknown constructor '${caseArm.pattern}'`,
      );
    }

    // Map case bindings to right.portName
    // Constructor ports: [principal, ...auxPorts]
    // Bindings map to aux ports in order
    const consAuxPorts = consDef.ports.slice(1); // skip principal
    if (caseArm.bindings.length > consAuxPorts.length) {
      throw new EvalError(
        `prove ${prove.name}: too many bindings for ${caseArm.pattern}`,
      );
    }

    // Build variable map: varName → PortRef
    const varMap = new Map<string, AST.PortRef>();
    for (let i = 0; i < caseArm.bindings.length; i++) {
      varMap.set(caseArm.bindings[i], {
        node: "right",
        port: consAuxPorts[i].name,
      });
    }
    for (const p of auxParamNames) {
      varMap.set(p, { node: "left", port: p });
    }

    // Track variable usage for erase detection
    const usedVars = new Set<string>();
    let counter = 0;

    // Translate proof expression to rule body
    const stmts: AST.RuleStmt[] = [];

    // ── Auto-duplication for multi-use variables ──
    // Count how many times each variable appears in the proof term
    const varNames = new Set<string>([...varMap.keys()]);
    const useCounts = countVarUses(caseArm.body, varNames);

    // For variables used > 1 time, insert dup chains
    const copyQueues = new Map<string, AST.PortRef[]>();

    for (const [varName, count] of useCounts) {
      if (count <= 1) continue;

      // Determine type for duplicator: check param annotation, fall back to principal type
      const paramInfo = prove.params.find((p) => p.name === varName);
      const typeExpr = paramInfo?.type ?? prove.params[0]?.type;
      const typeName = typeExpr?.kind === "ident" ? typeExpr.name : null;

      if (!typeName) {
        throw new EvalError(
          `prove ${prove.name}: variable '${varName}' used ${count} times ` +
            `but no type annotation available for auto-duplication`,
        );
      }

      const dupAgentName = `dup_${typeName.toLowerCase()}`;
      if (!agents.has(dupAgentName)) {
        throw new EvalError(
          `prove ${prove.name}: duplicator '${dupAgentName}' required ` +
            `for multi-use variable '${varName}' but not defined`,
        );
      }

      const originalPort = varMap.get(varName)!;
      const queue: AST.PortRef[] = [];
      let currentInput = originalPort;
      let remaining = count;

      while (remaining > 1) {
        const label = `_d${counter++}`;
        stmts.push({ kind: "let", varName: label, agentType: dupAgentName });

        // Connect input to dup principal
        if (isPreExisting(currentInput)) {
          stmts.push({
            kind: "relink",
            portA: currentInput,
            portB: { node: label, port: "principal" },
          });
        } else {
          stmts.push({
            kind: "wire",
            portA: currentInput,
            portB: { node: label, port: "principal" },
          });
        }

        queue.push({ node: label, port: "copy1" });
        remaining--;

        if (remaining === 1) {
          queue.push({ node: label, port: "copy2" });
        } else {
          currentInput = { node: label, port: "copy2" };
        }
      }

      copyQueues.set(varName, queue);
      usedVars.add(varName); // original port consumed by dup chain
    }

    function translateExpr(expr: AST.ProveExpr): AST.PortRef {
      if (expr.kind === "hole") {
        // Should never reach here — proveContainsHole guards the call
        throw new EvalError(`prove ${prove.name}: unexpected ? hole in desugaring`);
      }
      if (expr.kind === "ident") {
        // Variable with dup copies
        if (copyQueues.has(expr.name)) {
          const queue = copyQueues.get(expr.name)!;
          usedVars.add(expr.name);
          return queue.shift()!;
        }
        // Variable reference or nullary agent
        if (varMap.has(expr.name)) {
          usedVars.add(expr.name);
          return varMap.get(expr.name)!;
        }
        // Nullary agent (like refl)
        const label = `_p${counter++}`;
        stmts.push({ kind: "let", varName: label, agentType: expr.name });
        return { node: label, port: "principal" };
      }

      // Call: agent(arg1, arg2, ...)
      const agentDef = agents.get(expr.name);
      if (!agentDef) {
        throw new EvalError(
          `prove ${prove.name}: unknown agent '${expr.name}'`,
        );
      }

      const label = `_p${counter++}`;
      stmts.push({ kind: "let", varName: label, agentType: expr.name });

      // Detect whether this agent is a proof combinator (has "result" port at index 1)
      // vs a data constructor (no "result" port — e.g. pair, Succ, Cons).
      const hasResult = agentDef.ports.length > 1 && agentDef.ports[1].name === "result";

      // Map args to agent ports:
      //   Proof agents: args[0]→principal, args[1]→port[2], args[2]→port[3], ...
      //   Constructors: args[0]→port[1], args[1]→port[2], ... (skip principal)
      const argPorts = hasResult
        ? [agentDef.ports[0].name, ...agentDef.ports.slice(2).map((p) => p.name)]
        : agentDef.ports.slice(1).map((p) => p.name);

      for (let i = 0; i < expr.args.length; i++) {
        const argOutput = translateExpr(expr.args[i]);
        const targetPort: AST.PortRef = { node: label, port: argPorts[i] };
        // Use relink when at least one port is pre-existing, wire when both new
        if (isPreExisting(argOutput)) {
          stmts.push({ kind: "relink", portA: argOutput, portB: targetPort });
        } else if (isPreExisting(targetPort)) {
          stmts.push({ kind: "relink", portA: targetPort, portB: argOutput });
        } else {
          stmts.push({ kind: "wire", portA: argOutput, portB: targetPort });
        }
      }

      // Output: "result" port for proof agents, "principal" for constructors
      return { node: label, port: hasResult ? "result" : "principal" };
    }

    const outputPort = translateExpr(caseArm.body);

    // Connect output to left.result
    const resultRef: AST.PortRef = { node: "left", port: "result" };
    if (isPreExisting(outputPort)) {
      stmts.push({ kind: "relink", portA: resultRef, portB: outputPort });
    } else {
      stmts.push({ kind: "relink", portA: resultRef, portB: outputPort });
    }

    // Erase unused auxiliary parameters
    for (const p of auxParamNames) {
      if (!usedVars.has(p)) {
        stmts.push({ kind: "erase-stmt", port: { node: "left", port: p } });
      }
    }
    // Erase unused constructor bindings
    for (let i = 0; i < caseArm.bindings.length; i++) {
      if (!usedVars.has(caseArm.bindings[i])) {
        stmts.push({
          kind: "erase-stmt",
          port: { node: "right", port: consAuxPorts[i].name },
        });
      }
    }

    ruleDecls.push({
      kind: "rule",
      agentA: prove.name,
      agentB: caseArm.pattern,
      action: { kind: "custom", body: stmts },
    });
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
