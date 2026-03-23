// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { inductionParam, auxParams as getAuxParams } from "./types.ts";
import type { AgentDef, ModeDef, RuleDef, SystemDef, TacticDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import { buildProofTree, type ProvedContext, type ProofTree, typecheckProve, withNormTable } from "./typecheck-prove.ts";
import type { ComputeRule, ConstructorTyping } from "./typecheck-prove.ts";
import { registerQuotationAgents, quoteExpr, containsQuote, QUOTE_AGENTS } from "./quotation.ts";
import { registerMetaAgents, META_AGENTS } from "./meta-agents.ts";
import { registerBuiltinTactics, compileTactic, resolveAllTactics, TACTIC_AGENTS } from "./tactics.ts";

export function evalSystem(decl: AST.SystemDecl, systems?: Map<string, SystemDef>): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics } = evalBodyInto(decl.body, agents, rules, modes, undefined, undefined, undefined, undefined, systems);

  const sys: SystemDef = { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics: tactics.size > 0 ? tactics : undefined };
  return { sys, proofTrees };
}

// Helper: evaluate a system body (agents/rules/modes/prove) and merge into
// existing collections, used by extend and compose.
// Returns any proof trees generated from typed prove blocks.
// ─── Section expansion ──────────────────────────────────────────
// Flatten section declarations, prepending section variables as implicit
// params on prove/data/mutual items inside the section.
function expandSections(
  body: AST.SystemBody[],
  sectionVars: AST.SectionVariable[] = [],
): AST.SystemBody[] {
  const result: AST.SystemBody[] = [];
  for (const item of body) {
    if (item.kind === "section") {
      // Accumulate section variables, then recurse into body
      const combined = [...sectionVars, ...item.variables];
      result.push(...expandSections(item.body, combined));
    } else if (sectionVars.length > 0) {
      // Prepend section variables as implicit params
      if (item.kind === "prove") {
        const implicitParams: AST.ProveParam[] = sectionVars.map((v) => ({
          name: v.name,
          type: v.type,
          implicit: true,
        }));
        result.push({ ...item, params: [...implicitParams, ...item.params] });
      } else if (item.kind === "data") {
        const extraParams = sectionVars.map((v) => v.name);
        result.push({ ...item, params: [...extraParams, ...item.params] });
      } else if (item.kind === "mutual") {
        const expandedData = item.data.map((d) => ({
          ...d,
          params: [...sectionVars.map((v) => v.name), ...d.params],
        }));
        const expandedProves = item.proves.map((p) => ({
          ...p,
          params: [
            ...sectionVars.map((v): AST.ProveParam => ({
              name: v.name,
              type: v.type,
              implicit: true,
            })),
            ...p.params,
          ],
        }));
        result.push({ ...item, data: expandedData, proves: expandedProves });
      } else {
        result.push(item);
      }
    } else {
      result.push(item);
    }
  }
  return result;
}

export function evalBodyInto(
  rawBody: AST.SystemBody[],
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  modes: Map<string, ModeDef>,
  initialCtx?: ProvedContext,
  inheritedConstructors?: Map<string, Set<string>>,
  inheritedCompute?: ComputeRule[],
  inheritedCtorTyping?: ConstructorTyping,
  systems?: Map<string, SystemDef>,
): { proofTrees: ProofTree[]; provedCtx: ProvedContext; constructorsByType: Map<string, Set<string>>; computeRules: ComputeRule[]; constructorTyping: ConstructorTyping; exports?: Set<string>; tactics: Map<string, TacticDef> } {
  const body = expandSections(rawBody);
  const provedCtx: ProvedContext = new Map(initialCtx);
  const proofTrees: ProofTree[] = [];
  const computeRules: ComputeRule[] = [...(inheritedCompute ?? [])];
  const tactics = new Map<string, TacticDef>();
  const coercions = new Map<string, Map<string, string>>(); // from → to → func
  // Pre-scan: collect constructor families and compute rules before processing
  // Inherit from parent systems if available
  const constructorsByType = new Map<string, Set<string>>();
  const codataTypes = new Set<string>();
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
        constructorTyping.set(ctor.name, {
          typeName: item.name,
          params: item.params,
          indices: item.indices,
          fields: ctor.fields,
          returnIndices: ctor.returnIndices,
        });
      }
    } else if (item.kind === "mutual") {
      for (const d of item.data) {
        constructorsByType.set(d.name, new Set(d.constructors.map((c) => c.name)));
        for (const ctor of d.constructors) {
          constructorTyping.set(ctor.name, {
            typeName: d.name,
            params: d.params,
            indices: d.indices,
            fields: ctor.fields,
            returnIndices: ctor.returnIndices,
          });
        }
      }
      for (const p of item.proves) {
        const firstParam = inductionParam(p.params);
        if (firstParam?.type) {
          const typeName = firstParam.type.kind === "ident"
            ? firstParam.type.name
            : firstParam.type.kind === "call"
            ? firstParam.type.name
            : null;
          if (typeName) {
            if (!constructorsByType.has(typeName)) constructorsByType.set(typeName, new Set());
            const set = constructorsByType.get(typeName)!;
            for (const c of p.cases) set.add(c.pattern);
          }
        }
      }
    } else if (item.kind === "record") {
      const ctorName = `mk${item.name}`;
      constructorsByType.set(item.name, new Set([ctorName]));
      constructorTyping.set(ctorName, {
        typeName: item.name,
        params: item.params,
        indices: [],
        fields: item.fields,
      });
    } else if (item.kind === "codata") {
      const guardName = `guard_${item.name.toLowerCase()}`;
      codataTypes.add(item.name);
      constructorsByType.set(item.name, new Set([guardName]));
      constructorTyping.set(guardName, {
        typeName: item.name,
        params: item.params,
        indices: [],
        fields: item.fields,
      });
    } else if (item.kind === "prove") {
      const firstParam = inductionParam(item.params);
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
    if (item.kind === "mutual") {
      for (const d of item.data) {
        for (const ctor of d.constructors) knownAgents.add(ctor.name);
      }
      for (const p of item.proves) knownAgents.add(p.name);
    }
    if (item.kind === "record") {
      knownAgents.add(`mk${item.name}`);
      for (const f of item.fields) knownAgents.add(f.name);
    }
    if (item.kind === "codata") {
      knownAgents.add(`guard_${item.name.toLowerCase()}`);
      for (const f of item.fields) knownAgents.add(f.name);
    }
    if (item.kind === "open" && item.system === "Quote") {
      for (const name of QUOTE_AGENTS) knownAgents.add(name);
    }
    if (item.kind === "open" && item.system === "Meta") {
      for (const name of META_AGENTS) knownAgents.add(name);
    }
    if (item.kind === "open" && item.system === "Tactics") {
      for (const name of TACTIC_AGENTS) knownAgents.add(name);
    }
    if (item.kind === "tactic") {
      knownAgents.add(item.name);
      for (const sub of item.body) {
        if (sub.kind === "agent") knownAgents.add(sub.name);
      }
    }
    if (item.kind === "open" && systems) {
      const source = systems.get(item.system);
      if (source) {
        const visible = getVisibleAgents(source, item.names);
        for (const name of source.agents.keys()) {
          if (visible.has(name)) knownAgents.add(name);
        }
        // Also pre-populate constructorsByType from opened system
        for (const [type, ctors] of source.constructorsByType) {
          if (!constructorsByType.has(type)) constructorsByType.set(type, new Set());
          for (const c of ctors) {
            if (visible.has(c)) constructorsByType.get(type)!.add(c);
          }
        }
        // Pre-populate constructorTyping from opened system
        for (const [name, info] of source.constructorTyping) {
          if (visible.has(name)) constructorTyping.set(name, info);
        }
      }
    }
  }
  // Pre-scan: collect compute rules so they're available for type checking
  for (const item of body) {
    if (item.kind === "compute") {
      computeRules.push(astComputeToRule(item, knownAgents));
    }
  }
  // Auto-generate eliminators after explicit compute rules
  for (const item of body) {
    if (item.kind === "data") {
      computeRules.push(...generateEliminatorRules(item));
    }
    if (item.kind === "mutual" && item.data.length > 0) {
      computeRules.push(...generateMutualEliminatorRules(item.data));
    }
  }
  // Auto-generate projection compute rules for records
  for (const item of body) {
    if (item.kind === "record") {
      computeRules.push(...generateProjectionRules(item));
    }
    if (item.kind === "codata") {
      computeRules.push(...generateObservationRules(item));
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
      case "record": {
        // Sugar: desugar record into data type + projection compute rules.
        desugarRecord(item, agents, rules, constructorsByType, computeRules, constructorTyping);
        break;
      }
      case "codata": {
        // Sugar: desugar codata into guard agent + observation agents + rules.
        desugarCodata(item, agents, rules, constructorsByType);
        break;
      }
      case "prove": {
        // Expand induction(var) tactic into case arms with ? holes
        let prove = item;
        if (item.induction && item.cases.length === 0) {
          prove = expandInduction(item, agents, constructorsByType);
        }
        // Resolve all tactics (built-in + user-defined) in a single pass
        prove = withNormTable(computeRules, () => resolveAllTactics(prove, provedCtx, computeRules, tactics, agents, rules));
        const hasHoles = proveContainsHole(prove);
        const hasRewrites = proveContainsRewrite(prove);
        const hasMatch = proveContainsMatch(prove);
        // Only generate agent + rules for complete proofs (no ? holes, rewrites, or match)
        if (!hasHoles && !hasRewrites && !hasMatch) {
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
        const typeErrors = typecheckProve(prove, provedCtx, constructorsByType, computeRules, constructorTyping, codataTypes, coercions);
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
      case "notation": {
        // Notations are applied during parsing; nothing to do at eval time
        break;
      }
      case "coercion": {
        // Register implicit type conversion
        if (!coercions.has(item.from)) coercions.set(item.from, new Map());
        coercions.get(item.from)!.set(item.to, item.func);
        break;
      }
      case "open": {
        // Built-in "Quote" system: register quotation agents
        if (item.system === "Quote") {
          registerQuotationAgents(agents, rules);
          break;
        }
        // Built-in "Meta" system: register meta-agents with handlers
        if (item.system === "Meta") {
          registerMetaAgents(agents, rules, computeRules);
          break;
        }
        // Built-in "Tactics" system: register built-in tactic agents
        if (item.system === "Tactics") {
          registerBuiltinTactics(agents, rules, provedCtx, computeRules);
          break;
        }
        // Import agents/rules/etc from another system
        if (!systems) throw new EvalError(`Cannot use 'open' without access to systems`);
        const source = systems.get(item.system);
        if (!source) throw new EvalError(`Cannot open unknown system '${item.system}'`);
        const visible = getVisibleAgents(source, item.names);
        for (const [name, agent] of source.agents) {
          if (visible.has(name)) agents.set(name, agent);
        }
        for (const rule of source.rules) {
          if (visible.has(rule.agentA) && visible.has(rule.agentB)) {
            rules.push(rule);
          }
        }
        for (const [name, mode] of source.modes) {
          modes.set(name, mode);
        }
        for (const [name, entry] of source.provedCtx) {
          provedCtx.set(name, entry);
        }
        for (const [type, ctors] of source.constructorsByType) {
          if (!constructorsByType.has(type)) constructorsByType.set(type, new Set());
          for (const c of ctors) {
            if (visible.has(c)) constructorsByType.get(type)!.add(c);
          }
        }
        for (const cr of source.computeRules) {
          computeRules.push(cr);
        }
        for (const [name, info] of source.constructorTyping) {
          if (visible.has(name)) constructorTyping.set(name, info);
        }
        break;
      }
      case "export": {
        // Handled below after loop
        break;
      }
      case "tactic": {
        const tacDef = compileTactic(item, agents);
        tactics.set(tacDef.name, tacDef);
        // Also add tactic rules to the system rules
        for (const r of tacDef.rules) rules.push(r);
        break;
      }
      case "mutual": {
        // Phase 21: mutual inductive types and mutual prove blocks

        // 1. Joint positivity check on data declarations
        if (item.data.length > 0) {
          const posErrors = checkMutualPositivity(item.data);
          if (posErrors.length > 0) throw new EvalError(posErrors.join("\n"));
        }

        // 2. Desugar all data types in the group
        for (const d of item.data) {
          desugarData(d, agents, rules, constructorsByType);
        }

        // 3. Register all mutual prove signatures BEFORE type-checking any
        const mutualNames = new Set<string>();
        for (const p of item.proves) {
          mutualNames.add(p.name);
          if (p.returnType) {
            provedCtx.set(p.name, {
              params: p.params,
              returnType: p.returnType,
            });
          }
          // Pre-register agent stub so cross-prove references resolve during desugaring
          const auxParams = getAuxParams(p.params).map((pp) => pp.name);
          const ports: AST.PortDef[] = [
            { name: "principal", variadic: false },
            { name: "result", variadic: false },
            ...auxParams.map((n) => ({ name: n, variadic: false })),
          ];
          agents.set(p.name, evalAgent({ kind: "agent", name: p.name, ports }));
        }

        // 4. Process each prove in the group
        for (const p of item.proves) {
          let prove = p;
          if (p.induction && p.cases.length === 0) {
            prove = expandInduction(p, agents, constructorsByType);
          }
          prove = withNormTable(computeRules, () => resolveAllTactics(prove, provedCtx, computeRules, tactics, agents, rules));
          const hasHoles = proveContainsHole(prove);
          const hasRewrites = proveContainsRewrite(prove);
          const hasMatch = proveContainsMatch(prove);
          if (!hasHoles && !hasRewrites && !hasMatch) {
            const stripped = stripProveTactics(prove);
            const { agentDecl, ruleDecls } = desugarProve(stripped, agents);
            const agent = evalAgent(agentDecl);
            agents.set(agent.name, agent);
            for (const r of ruleDecls) {
              rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
            }
          }
          const linearityErrors = checkProveLinearity(prove, agents, modes);
          const typeErrors = typecheckProve(prove, provedCtx, constructorsByType, computeRules, constructorTyping, codataTypes, coercions);
          const termErrors = checkMutualTermination(prove, mutualNames);
          const allErrors = [...linearityErrors, ...typeErrors, ...termErrors];
          if (allErrors.length > 0) {
            throw new EvalError(allErrors.join("\n"));
          }
          const tree = buildProofTree(prove, provedCtx, computeRules, constructorTyping);
          if (tree) proofTrees.push(tree);
        }
        break;
      }
    }
  }
  // Collect export declarations
  const exportNames = body.filter((b): b is AST.ExportDecl => b.kind === "export");
  const exports = exportNames.length > 0
    ? new Set(exportNames.flatMap(e => e.names))
    : undefined;
  return { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics };
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
  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics } = evalBodyInto(decl.body, agents, rules, modes, base.provedCtx, base.constructorsByType, base.computeRules, base.constructorTyping, systems);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics: tactics.size > 0 ? tactics : undefined }, proofTrees };
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
  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics } = evalBodyInto(decl.body, agents, rules, modes, mergedCtx, mergedConstructors, mergedCompute, mergedCtorTyping, systems);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics: tactics.size > 0 ? tactics : undefined }, proofTrees };
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
  const auxParams = getAuxParams(prove.params).map((p) => p.name);
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
      const typeExpr = paramInfo?.type ?? inductionParam(prove.params)?.type;
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
      if (expr.kind === "metavar") throw new EvalError(`prove ${prove.name}: unsolved metavariable ?${expr.id} in desugaring`);
      if (expr.kind === "match") throw new EvalError(`prove ${prove.name}: match expressions cannot be desugared into agents`);
      if (expr.kind === "let") {
        const valPort = translateExpr(expr.value);
        varMap.set(expr.name, valPort);
        return translateExpr(expr.body);
      }
      if (expr.kind === "pi" || expr.kind === "sigma" || expr.kind === "lambda") {
        throw new EvalError(`prove ${prove.name}: ${expr.kind} expressions cannot be desugared into agents yet`);
      }
      // quote(body) → build Tm* agent net representing the quoted term
      if (expr.kind === "call" && expr.name === "quote" && expr.args.length === 1) {
        registerQuotationAgents(agents, []);
        const qCounter = { value: counter };
        const result = quoteExpr(expr.args[0], qCounter);
        counter = qCounter.value;
        stmts.push(...result.stmts);
        return result.root;
      }
      // unquote(quote(body)) → collapse to body (compile-time roundtrip)
      if (expr.kind === "call" && expr.name === "unquote" && expr.args.length === 1) {
        const inner = expr.args[0];
        if (inner.kind === "call" && inner.name === "quote" && inner.args.length === 1) {
          return translateExpr(inner.args[0]);
        }
        throw new EvalError(`prove ${prove.name}: unquote requires a quote(...) argument at compile time`);
      }
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

  const auxParamNames = getAuxParams(prove.params).map((p) => p.name);
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
    } else if (e.kind === "let") {
      walk(e.value);
      walk(e.body);
    } else if (e.kind === "pi" || e.kind === "sigma") {
      walk(e.domain);
      walk(e.codomain);
    } else if (e.kind === "lambda") {
      walk(e.paramType);
      walk(e.body);
    } else if (e.kind === "match") {
      if (vars.has(e.scrutinee)) counts.set(e.scrutinee, (counts.get(e.scrutinee) || 0) + 1);
      for (const c of e.cases) walk(c.body);
    }
  }
  walk(expr);
  return counts;
}

function exprContainsHole(e: AST.ProveExpr): boolean {
  if (e.kind === "hole") return true;
  if (e.kind === "call") return e.args.some(exprContainsHole);
  if (e.kind === "let") return exprContainsHole(e.value) || exprContainsHole(e.body);
  if (e.kind === "pi" || e.kind === "sigma") return exprContainsHole(e.domain) || exprContainsHole(e.codomain);
  if (e.kind === "lambda") return exprContainsHole(e.paramType) || exprContainsHole(e.body);
  if (e.kind === "match") return e.cases.some((c) => exprContainsHole(c.body));
  return false;
}

function proveContainsHole(prove: AST.ProveDecl): boolean {
  return prove.cases.some((c) => exprContainsHole(c.body));
}

function exprContainsRewrite(e: AST.ProveExpr): boolean {
  if (e.kind === "call" && e.name === "rewrite") return true;
  if (e.kind === "call") return e.args.some(exprContainsRewrite);
  if (e.kind === "let") return exprContainsRewrite(e.value) || exprContainsRewrite(e.body);
  if (e.kind === "pi" || e.kind === "sigma") return exprContainsRewrite(e.domain) || exprContainsRewrite(e.codomain);
  if (e.kind === "lambda") return exprContainsRewrite(e.paramType) || exprContainsRewrite(e.body);
  if (e.kind === "match") return e.cases.some((c) => exprContainsRewrite(c.body));
  return false;
}

function proveContainsRewrite(prove: AST.ProveDecl): boolean {
  return prove.cases.some((c) => exprContainsRewrite(c.body));
}

function exprContainsMatch(e: AST.ProveExpr): boolean {
  if (e.kind === "match") return true;
  if (e.kind === "call") return e.args.some(exprContainsMatch);
  if (e.kind === "let") return exprContainsMatch(e.value) || exprContainsMatch(e.body);
  if (e.kind === "pi" || e.kind === "sigma") return exprContainsMatch(e.domain) || exprContainsMatch(e.codomain);
  if (e.kind === "lambda") return exprContainsMatch(e.paramType) || exprContainsMatch(e.body);
  return false;
}

function proveContainsMatch(prove: AST.ProveDecl): boolean {
  return prove.cases.some((c) => exprContainsMatch(c.body));
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
  if (expr.kind === "pi" || expr.kind === "sigma") {
    return { kind: expr.kind, param: expr.param, domain: normalizeProofExpr(expr.domain), codomain: normalizeProofExpr(expr.codomain) };
  }
  if (expr.kind === "lambda") {
    return { kind: "lambda", param: expr.param, paramType: normalizeProofExpr(expr.paramType), body: normalizeProofExpr(expr.body) };
  }
  if (expr.kind !== "call" && expr.kind !== "match" && expr.kind !== "let") return expr;
  if (expr.kind === "let") {
    return { kind: "let", name: expr.name, value: normalizeProofExpr(expr.value), body: normalizeProofExpr(expr.body) };
  }
  if (expr.kind === "match") {
    return { kind: "match", scrutinee: expr.scrutinee, cases: expr.cases.map((c) => ({ ...c, body: normalizeProofExpr(c.body) })) };
  }
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
  if (expr.kind === "pi" || expr.kind === "sigma") {
    return { kind: expr.kind, param: expr.param, domain: stripExprTactics(expr.domain), codomain: stripExprTactics(expr.codomain) };
  }
  if (expr.kind === "lambda") {
    return { kind: "lambda", param: expr.param, paramType: stripExprTactics(expr.paramType), body: stripExprTactics(expr.body) };
  }
  if (expr.kind === "let") {
    return { kind: "let", name: expr.name, value: stripExprTactics(expr.value), body: stripExprTactics(expr.body) };
  }
  if (expr.kind === "match") {
    return { kind: "match", scrutinee: expr.scrutinee, cases: expr.cases.map((c) => ({ ...c, body: stripExprTactics(c.body) })) };
  }
  if (expr.kind === "ident" && expr.name === "conv") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "simp") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "decide") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "omega") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind === "ident" && expr.name === "auto") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind !== "call") return expr;
  if (expr.name === "exact" && expr.args.length === 1) return stripExprTactics(expr.args[0]);
  if (expr.name === "apply" && expr.args.length >= 1 && expr.args[0].kind === "ident") {
    return { kind: "call", name: expr.args[0].name, args: expr.args.slice(1).map(stripExprTactics) };
  }
  if (expr.name === "calc" && expr.args.length >= 2) {
    let acc = stripExprTactics(expr.args[0]);
    for (let i = 1; i < expr.args.length; i++) {
      acc = { kind: "call", name: "trans", args: [acc, stripExprTactics(expr.args[i])] };
    }
    return acc;
  }
  if (expr.name === "conv" && expr.args.length === 0) {
    return { kind: "ident", name: "refl" };
  }
  return { kind: "call", name: expr.name, args: expr.args.map(stripExprTactics) };
}

// ─── Expression pretty-printing (for error messages) ───────────────
function exprToString(e: AST.ProveExpr): string {
  if (e.kind === "ident") return e.name;
  if (e.kind === "call") return `${e.name}(${e.args.map(exprToString).join(", ")})`;
  if (e.kind === "hole") return "?";
  if (e.kind === "pi") return `(${e.param} : ${exprToString(e.domain)}) -> ${exprToString(e.codomain)}`;
  return e.kind;
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

/** Extract the base type name from a field type expression (lowercase). */
function fieldTypeBaseName(type: AST.ProveExpr): string {
  if (type.kind === "ident") return type.name.toLowerCase();
  if (type.kind === "call") return type.name.toLowerCase();
  return "unknown";
}

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
// For each data declaration, generate compute rules that define the
// recursor (e.g., Nat_rec) as reduction equations — scrutinee first:
//   compute Nat_rec(Zero, base, step) = base
//   compute Nat_rec(Succ(k), base, step) = step(k, Nat_rec(k, base, step))

function generateEliminatorRules(decl: AST.DataDecl): ComputeRule[] {
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

    // Args: Constructor(f0, f1, ...), method0, method1, ...
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

    // Result: method_i(f0, ..., Nat_rec(fk_recursive, m0, m1, ...), ...)
    // For nullary constructors with no fields: result = method_i
    const resultArgs: AST.ProveExpr[] = [];
    for (let fi = 0; fi < ctor.fields.length; fi++) {
      if (isRecursive[fi]) {
        // Induction hypothesis: recursive call on the recursive field
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
// Cross-type aware eliminators: each recursor takes methods for ALL
// constructors across the entire mutual group.
//   Even_rec(EZero, ez_m, es_m, os_m)      = ez_m
//   Even_rec(ESucc(p), ez_m, es_m, os_m)    = es_m(p, Odd_rec(p, ez_m, es_m, os_m))
//   Odd_rec(OSucc(p), ez_m, es_m, os_m)     = os_m(p, Even_rec(p, ez_m, es_m, os_m))

function generateMutualEliminatorRules(group: AST.DataDecl[]): ComputeRule[] {
  const rules: ComputeRule[] = [];
  const groupNames = new Set(group.map((d) => d.name));

  // Collect method names across all constructors in all types
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

      // Method for this constructor
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
          // Cross-type (or self) recursive field: call baseName_rec
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
// Verifies that none of the type names in the mutual group appear in
// a negative position (left side of Pi/→) in any constructor field.

function checkMutualPositivity(group: AST.DataDecl[]): string[] {
  const errors: string[] = [];
  const groupNames = new Set(group.map((d) => d.name));

  function occursNegative(expr: AST.ProveExpr, names: Set<string>): boolean {
    if (expr.kind === "ident") return false;
    if (expr.kind === "call") {
      // args are type parameters, not function arguments → still positive
      return expr.args.some((a) => occursNegative(a, names));
    }
    if (expr.kind === "pi" || expr.kind === "sigma") {
      // domain is negative position; check if any group name appears there
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
// Checks that cross-calls within a mutual prove group use at least
// one structurally decreasing argument (a case binding).

function checkMutualTermination(
  prove: AST.ProveDecl,
  mutualNames: Set<string>,
): string[] {
  if (prove.wf) return []; // trusted — skip mutual termination check
  const errors: string[] = [];
  // Sibling names: all mutual names except self (self is handled by regular checkTermination)
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
// Expands a `record` declaration into:
//   1. A data type with one constructor (mkName)
//   2. Projection agents (one per field)
//   3. Projection rules: proj <> mkName → relink/erase

function desugarRecord(
  decl: AST.RecordDecl,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  constructorsByType: Map<string, Set<string>>,
  computeRules: ComputeRule[],
  constructorTyping: ConstructorTyping,
): void {
  const ctorName = `mk${decl.name}`;

  // Synthesize a DataDecl and delegate constructor + dup generation to desugarData
  const dataDecl: AST.DataDecl = {
    kind: "data",
    name: decl.name,
    params: decl.params,
    indices: [],
    constructors: [{ name: ctorName, fields: decl.fields }],
  };
  desugarData(dataDecl, agents, rules, constructorsByType);

  // Generate projection agents + rules
  for (let i = 0; i < decl.fields.length; i++) {
    const field = decl.fields[i];
    // Agent: fieldName(principal, result)
    const projPorts: AST.PortDef[] = [
      { name: "principal", variadic: false },
      { name: "result", variadic: false },
    ];
    agents.set(field.name, evalAgent({ kind: "agent", name: field.name, ports: projPorts }));

    // Rule: fieldName <> mkName → relink result to field[i], erase others
    const stmts: AST.RuleStmt[] = [];
    stmts.push({
      kind: "relink",
      portA: { node: "left", port: "result" },
      portB: { node: "right", port: field.name },
    });
    // Erase all other fields
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

/** Desugar a codata declaration into a guard agent + observation agents + interaction rules.
 *  codata Stream(A) { head : A, tail : Stream(A) }
 *  →  guard_stream(principal, head, tail)          -- guard agent
 *     head(principal, result), tail(principal, result)   -- observation agents
 *     head <> guard_stream → relink result↔head, erase tail
 *     tail <> guard_stream → relink result↔tail, erase head
 *     dup_stream <> guard_stream → dup each field     */
function desugarCodata(
  decl: AST.CodataDecl,
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  constructorsByType: Map<string, Set<string>>,
): void {
  const guardName = `guard_${decl.name.toLowerCase()}`;

  // Synthesize a DataDecl with a single constructor (the guard) and delegate to desugarData
  const dataDecl: AST.DataDecl = {
    kind: "data",
    name: decl.name,
    params: decl.params,
    indices: [],
    constructors: [{ name: guardName, fields: decl.fields }],
  };
  desugarData(dataDecl, agents, rules, constructorsByType);

  // Generate observation agents + interaction rules (same as record projections)
  for (let i = 0; i < decl.fields.length; i++) {
    const field = decl.fields[i];
    // Agent: fieldName(principal, result)
    const obsPorts: AST.PortDef[] = [
      { name: "principal", variadic: false },
      { name: "result", variadic: false },
    ];
    agents.set(field.name, evalAgent({ kind: "agent", name: field.name, ports: obsPorts }));

    // Rule: fieldName <> guard_name → relink result to field[i], erase others
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

/** Generate compute rules for record projections:
 *  fieldName(mkName(f0, f1, ...)) = fi */
function generateProjectionRules(decl: AST.RecordDecl): ComputeRule[] {
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

/** Generate compute rules for codata observations:
 *  fieldName(guard_name(f0, f1, ...)) = fi */
function generateObservationRules(decl: AST.CodataDecl): ComputeRule[] {
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

/** Get the set of agent names visible from a system, respecting exports and selective open. */
function getVisibleAgents(source: SystemDef, selectNames?: string[]): Set<string> {
  // Start with all agent names from the source
  let visible = new Set(source.agents.keys());
  // If the source has export restrictions, apply them
  if (source.exports) {
    visible = new Set([...visible].filter(n => source.exports!.has(n)));
  }
  // If selective import (open "X" use A, B), filter further
  if (selectNames) {
    visible = new Set(selectNames.filter(n => visible.has(n)));
  }
  return visible;
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
