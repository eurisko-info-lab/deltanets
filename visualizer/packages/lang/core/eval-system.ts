// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import { inductionParam, auxParams as getAuxParams } from "./types.ts";
import type { AgentDef, CanonicalDef, ClassDef, InstanceDef, ModeDef, RuleDef, SystemDef, TacticDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import { buildProofTree, type ProofTree, typecheckProve } from "./typecheck-prove.ts";
import { withNormTable, type ProvedContext, type ComputeRule, type ConstructorTyping } from "./normalize.ts";
import { evalAgent, desugarData, desugarRecord, desugarCodata, generateEliminatorRules, generateMutualEliminatorRules, checkMutualPositivity, checkMutualTermination, generateProjectionRules, generateObservationRules, getVisibleAgents, astComputeToRule } from "./desugar.ts";
import { registerQuotationAgents, quoteExpr, containsQuote, QUOTE_AGENTS } from "./quotation.ts";
import { registerMetaAgents, META_AGENTS, STRAT_AGENTS } from "./meta-agents.ts";
import { compileTactic, resolveAllTactics } from "./tactics.ts";

export function evalSystem(decl: AST.SystemDecl, systems?: Map<string, SystemDef>): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics, strategies, setoids, rings, classes, instances, hints, canonicals, dataSorts } = evalBodyInto(decl.body, agents, rules, modes, undefined, undefined, undefined, undefined, systems);

  const sys: SystemDef = { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics: tactics.size > 0 ? tactics : undefined, strategies: strategies.size > 0 ? strategies : undefined, setoids: setoids.size > 0 ? setoids : undefined, rings: rings.size > 0 ? rings : undefined, classes: classes.size > 0 ? classes : undefined, instances: instances.length > 0 ? instances : undefined, hints: hints.size > 0 ? hints : undefined, canonicals: canonicals.length > 0 ? canonicals : undefined, dataSorts: dataSorts.size > 0 ? dataSorts : undefined };
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
      if (item.kind === "prove" || item.kind === "program") {
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
  inheritedSetoids?: Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>,
  inheritedRings?: Map<string, { type: string; zero: string; one?: string; add: string; mul: string }>,
  inheritedClasses?: Map<string, ClassDef>,
  inheritedInstances?: InstanceDef[],
  inheritedHints?: Map<string, Set<string>>,
  inheritedCanonicals?: CanonicalDef[],
  inheritedStrategies?: Map<string, AST.StrategyExpr>,
): { proofTrees: ProofTree[]; provedCtx: ProvedContext; constructorsByType: Map<string, Set<string>>; computeRules: ComputeRule[]; constructorTyping: ConstructorTyping; exports?: Set<string>; tactics: Map<string, TacticDef>; strategies: Map<string, AST.StrategyExpr>; setoids: Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>; rings: Map<string, { type: string; zero: string; one?: string; add: string; mul: string }>; classes: Map<string, ClassDef>; instances: InstanceDef[]; hints: Map<string, Set<string>>; canonicals: CanonicalDef[]; dataSorts: Map<string, "Prop" | "Set" | "SProp">; recordDefs: Map<string, import("./normalize.ts").RecordDef> } {
  const body = expandSections(rawBody);
  const provedCtx: ProvedContext = new Map(initialCtx);
  const proofTrees: ProofTree[] = [];
  const computeRules: ComputeRule[] = [...(inheritedCompute ?? [])];
  const tactics = new Map<string, TacticDef>();
  const strategies = new Map<string, AST.StrategyExpr>(inheritedStrategies);
  const coercions = new Map<string, Map<string, string>>(); // from → to → func
  const setoids = new Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>(inheritedSetoids); // relation name → setoid def
  const rings = new Map<string, { type: string; zero: string; one?: string; add: string; mul: string }>(inheritedRings); // type name → ring def
  const classes = new Map<string, ClassDef>(inheritedClasses); // class name → class def
  const instances: InstanceDef[] = [...(inheritedInstances ?? [])]; // typeclass instances
  const canonicals: CanonicalDef[] = [...(inheritedCanonicals ?? [])]; // canonical structures
  const hints = new Map<string, Set<string>>(); // hint databases: db name → lemma names
  const dataSorts = new Map<string, "Prop" | "Set" | "SProp">(); // type name → declared sort
  const recordDefs = new Map<string, import("./normalize.ts").RecordDef>(); // ctor name → record metadata
  if (inheritedHints) {
    for (const [db, lemmas] of inheritedHints) hints.set(db, new Set(lemmas));
  }
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
            for (const c of p.cases) if (c.pattern !== "_") set.add(c.pattern);
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
      recordDefs.set(ctorName, { ctor: ctorName, fields: item.fields.map(f => f.name) });
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
    } else if (item.kind === "prove" || item.kind === "program") {
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
          for (const c of item.cases) if (c.pattern !== "_") set.add(c.pattern);
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
    if (item.kind === "program") {
      knownAgents.add(item.name);
      for (const ob of item.obligations) knownAgents.add(ob.name);
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
      for (const name of STRAT_AGENTS) knownAgents.add(name);
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
  // Handle opaque/transparent declarations (toggle unfolding of compute rules)
  for (const item of body) {
    if (item.kind === "opaque") {
      const isOpaque = !item.transparent;
      for (const rule of computeRules) {
        if (rule.funcName === item.name) rule.opaque = isOpaque;
      }
    }
  }
  // Handle arguments declarations (override implicit/explicit param bindings)
  const argumentsOverrides = new Map<string, { name: string; implicit: boolean }[]>();
  for (const item of body) {
    if (item.kind === "arguments") {
      argumentsOverrides.set(item.name, item.params);
    }
  }

  // Shared prove-processing pipeline: expand induction, resolve tactics,
  // desugar, type-check, build proof tree, register in provedCtx.
  function processProve(decl: AST.ProveDecl, regParams: AST.ProveParam[], regReturnType?: AST.ProveExpr) {
    let prove = decl;
    if (decl.induction && decl.cases.length === 0) {
      prove = expandInduction(decl, agents, constructorsByType);
    }
    // Expand wildcard "_" pattern into per-constructor cases
    if (prove.cases.length === 1 && prove.cases[0].pattern === "_") {
      prove = expandWildcard(prove, agents, constructorsByType);
    }
    prove = withNormTable(computeRules, () => resolveAllTactics(prove, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies));
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
    const typeErrors = typecheckProve(prove, provedCtx, constructorsByType, computeRules, constructorTyping, codataTypes, coercions, setoids, rings, hints, instances, dataSorts, canonicals, recordDefs);
    const allErrors = [...linearityErrors, ...typeErrors];
    if (allErrors.length > 0) {
      throw new EvalError(allErrors.join("\n"));
    }
    const tree = buildProofTree(prove, provedCtx, computeRules, constructorTyping, recordDefs);
    if (tree) proofTrees.push(tree);
    if (prove.returnType && regReturnType) {
      provedCtx.set(prove.name, { params: regParams, returnType: regReturnType });
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
        if (item.sort) dataSorts.set(item.name, item.sort);
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
        processProve(item, item.params, item.returnType);
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
      case "alias": {
        // alias newName = existingAgent — creates a new agent with same ports
        const target = agents.get(item.target);
        if (!target) throw new EvalError(`alias '${item.name}': unknown agent '${item.target}'`);
        agents.set(item.name, { ...target, name: item.name });
        // Copy all rules involving the target — create parallel rules for the alias
        for (const r of [...rules]) {
          if (r.agentA === item.target) {
            rules.push({ agentA: item.name, agentB: r.agentB, action: r.action });
          }
          if (r.agentB === item.target) {
            rules.push({ agentA: r.agentA, agentB: item.name, action: r.action });
          }
        }
        break;
      }
      case "coercion": {
        // Register implicit type conversion
        if (!coercions.has(item.from)) coercions.set(item.from, new Map());
        coercions.get(item.from)!.set(item.to, item.func);
        break;
      }
      case "setoid": {
        // Register binary relation as equivalence relation
        setoids.set(item.name, { name: item.name, type: item.type, refl: item.refl, sym: item.sym, trans: item.trans });
        break;
      }
      case "ring": {
        // Register commutative semiring structure
        rings.set(item.type, { type: item.type, zero: item.zero, one: item.one, add: item.add, mul: item.mul });
        break;
      }
      case "class": {
        // Register typeclass: store method signatures
        classes.set(item.name, {
          name: item.name,
          params: item.params,
          methods: item.methods.map((m) => ({ name: m.name, type: m.type })),
        });
        break;
      }
      case "instance": {
        // Register typeclass instance and generate compute rules for method dispatch
        const classDef = classes.get(item.className);
        if (!classDef) throw new EvalError(`instance: unknown class '${item.className}'`);
        const methodMap = new Map<string, string>();
        for (const m of item.methods) {
          const defined = classDef.methods.some((cm) => cm.name === m.name);
          if (!defined) throw new EvalError(`instance ${item.className}(${item.args.join(", ")}): unknown method '${m.name}'`);
          methodMap.set(m.name, m.value);
        }
        // Verify all class methods are implemented
        for (const cm of classDef.methods) {
          if (!methodMap.has(cm.name)) {
            throw new EvalError(`instance ${item.className}(${item.args.join(", ")}): missing method '${cm.name}'`);
          }
        }
        instances.push({ className: item.className, args: item.args, methods: methodMap });
        // Generate compute rules: methodName(TypeArg, ...) = implAgent(...)
        for (const [methodName, implName] of methodMap) {
          computeRules.push({
            head: methodName,
            patterns: item.args.map((a) => ({ kind: "ident" as const, name: a })),
            body: { kind: "ident" as const, name: implName },
          });
        }
        break;
      }
      case "hint": {
        // Register lemma in a named hint database
        if (!hints.has(item.db)) hints.set(item.db, new Set());
        hints.get(item.db)!.add(item.lemma);
        break;
      }
      case "canonical": {
        // Register canonical structure instance
        const projMap = new Map<string, string>();
        for (const f of item.fields) projMap.set(f.name, f.value);
        canonicals.push({ name: item.name, structName: item.structName, projections: projMap });
        break;
      }
      case "program": {
        // Lower program to prove with wf termination, then process obligations
        const mainProve: AST.ProveDecl = {
          kind: "prove",
          name: item.name,
          params: item.params,
          returnType: item.returnType,
          cases: item.cases,
          wf: item.wf ?? (item.measure ? undefined : "_"),
          measure: item.measure,
          attributes: item.attributes,
        };
        processProve(mainProve, item.params, item.returnType);
        // Process each obligation as a separate prove
        for (const ob of item.obligations) {
          const obProve: AST.ProveDecl = {
            kind: "prove",
            name: ob.name,
            params: ob.params,
            returnType: ob.returnType,
            cases: ob.cases,
            termination: "structural",
          };
          processProve(obProve, ob.params, ob.returnType);
        }
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
        if (source.recordDefs) {
          for (const [name, def] of source.recordDefs) recordDefs.set(name, def);
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
      case "strategy": {
        strategies.set(item.name, item.body);
        break;
      }
      case "opaque": {
        // Already handled in pre-scan above
        break;
      }
      case "arguments": {
        // Apply arguments override to provedCtx entry
        const entry = provedCtx.get(item.name);
        if (entry) {
          const newParams = entry.params.map((p, i) => {
            const override = item.params[i];
            if (override) return { ...p, implicit: override.implicit };
            return p;
          });
          provedCtx.set(item.name, { ...entry, params: newParams });
        }
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
          if (prove.cases.length === 1 && prove.cases[0].pattern === "_") {
            prove = expandWildcard(prove, agents, constructorsByType);
          }
          prove = withNormTable(computeRules, () => resolveAllTactics(prove, provedCtx, computeRules, tactics, agents, rules, hints, instances, strategies));
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
          const typeErrors = typecheckProve(prove, provedCtx, constructorsByType, computeRules, constructorTyping, codataTypes, coercions, setoids, rings, hints, instances, dataSorts, canonicals, recordDefs);
          const termErrors = checkMutualTermination(prove, mutualNames);
          const allErrors = [...linearityErrors, ...typeErrors, ...termErrors];
          if (allErrors.length > 0) {
            throw new EvalError(allErrors.join("\n"));
          }
          const tree = buildProofTree(prove, provedCtx, computeRules, constructorTyping, recordDefs);
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
  return { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics, strategies, setoids, rings, classes, instances, hints, canonicals, dataSorts, recordDefs };
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
  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics, strategies, setoids, rings, classes, instances, hints, canonicals, dataSorts, recordDefs } = evalBodyInto(decl.body, agents, rules, modes, base.provedCtx, base.constructorsByType, base.computeRules, base.constructorTyping, systems, base.setoids, base.rings, base.classes, base.instances, base.hints, base.canonicals, base.strategies);

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics: tactics.size > 0 ? tactics : undefined, strategies: strategies.size > 0 ? strategies : undefined, setoids: setoids.size > 0 ? setoids : undefined, rings: rings.size > 0 ? rings : undefined, classes: classes.size > 0 ? classes : undefined, instances: instances.length > 0 ? instances : undefined, hints: hints.size > 0 ? hints : undefined, canonicals: canonicals.length > 0 ? canonicals : undefined, dataSorts: dataSorts.size > 0 ? dataSorts : undefined, recordDefs: recordDefs.size > 0 ? recordDefs : undefined }, proofTrees };
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
  const mergedSetoids = new Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>();
  const mergedRings = new Map<string, { type: string; zero: string; one?: string; add: string; mul: string }>();
  const mergedClasses = new Map<string, ClassDef>();
  const mergedInstances: InstanceDef[] = [];
  const mergedHints = new Map<string, Set<string>>();
  const mergedCanonicals: CanonicalDef[] = [];
  const mergedStrategies = new Map<string, AST.StrategyExpr>();
  const mergedRecordDefs = new Map<string, import("./normalize.ts").RecordDef>();

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

    // Setoids: merge
    if (comp.setoids) {
      for (const [name, s] of comp.setoids) mergedSetoids.set(name, s);
    }

    // Rings: merge
    if (comp.rings) {
      for (const [name, r] of comp.rings) mergedRings.set(name, r);
    }

    // Classes: merge
    if (comp.classes) {
      for (const [name, c] of comp.classes) mergedClasses.set(name, c);
    }

    // Instances: merge
    if (comp.instances) {
      mergedInstances.push(...comp.instances);
    }

    // Hints: merge
    if (comp.hints) {
      for (const [db, lemmas] of comp.hints) {
        if (!mergedHints.has(db)) mergedHints.set(db, new Set());
        for (const l of lemmas) mergedHints.get(db)!.add(l);
      }
    }

    // Canonicals: merge
    if (comp.canonicals) {
      mergedCanonicals.push(...comp.canonicals);
    }

    // Strategies: merge
    if (comp.strategies) {
      for (const [name, s] of comp.strategies) mergedStrategies.set(name, s);
    }

    // RecordDefs: merge
    if (comp.recordDefs) {
      for (const [name, def] of comp.recordDefs) mergedRecordDefs.set(name, def);
    }
  }

  // Add cross-interaction rules from the compose body (the pushout span)
  const { proofTrees, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics, strategies, setoids, rings, classes, instances, hints, canonicals, dataSorts, recordDefs } = evalBodyInto(decl.body, agents, rules, modes, mergedCtx, mergedConstructors, mergedCompute, mergedCtorTyping, systems, mergedSetoids, mergedRings, mergedClasses, mergedInstances, mergedHints, mergedCanonicals, mergedStrategies);
  // Merge component recordDefs into body recordDefs
  for (const [name, def] of mergedRecordDefs) {
    if (!recordDefs.has(name)) recordDefs.set(name, def);
  }

  return { sys: { name: decl.name, agents, rules, modes, provedCtx, constructorsByType, computeRules, constructorTyping, exports, tactics: tactics.size > 0 ? tactics : undefined, strategies: strategies.size > 0 ? strategies : undefined, setoids: setoids.size > 0 ? setoids : undefined, rings: rings.size > 0 ? rings : undefined, classes: classes.size > 0 ? classes : undefined, instances: instances.length > 0 ? instances : undefined, hints: hints.size > 0 ? hints : undefined, canonicals: canonicals.length > 0 ? canonicals : undefined, dataSorts: dataSorts.size > 0 ? dataSorts : undefined, recordDefs: recordDefs.size > 0 ? recordDefs : undefined }, proofTrees };
}

// Re-export evalAgent from desugar.ts for backward compatibility.
export { evalAgent } from "./desugar.ts";

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

/** Expand a wildcard "_" pattern into per-constructor cases (for direct proof terms). */
function expandWildcard(
  prove: AST.ProveDecl,
  agents: Map<string, AgentDef>,
  constructorsByType: Map<string, Set<string>>,
): AST.ProveDecl {
  const body = prove.cases[0].body;
  const indParam = inductionParam(prove.params);
  if (!indParam?.type) {
    return prove;
  }
  const typeName = indParam.type.kind === "ident"
    ? indParam.type.name
    : indParam.type.kind === "call"
    ? indParam.type.name
    : null;
  if (!typeName || !constructorsByType.has(typeName)) {
    return prove;
  }
  const constructors = constructorsByType.get(typeName)!;
  const cases: AST.ProveCase[] = [];
  for (const consName of constructors) {
    const consDef = agents.get(consName);
    const auxPorts = consDef ? consDef.ports.slice(1) : [];
    const bindings = auxPorts.map((p) => p.name);
    cases.push({ pattern: consName, bindings, body });
  }
  return { ...prove, cases };
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
  if (expr.kind === "ident" && expr.name === "ring") {
    return { kind: "ident", name: "refl" };
  }
  if (expr.kind !== "call") return expr;
  // Strip tactic combinators: unwrap to inner content
  if (expr.name === "try" && expr.args.length === 1) return stripExprTactics(expr.args[0]);
  if (expr.name === "first" && expr.args.length >= 1) return stripExprTactics(expr.args[0]);
  if (expr.name === "repeat" && expr.args.length === 1) return stripExprTactics(expr.args[0]);
  if ((expr.name === "then" || expr.name === "seq") && expr.args.length === 2) return stripExprTactics(expr.args[1]);
  if (expr.name === "all" && expr.args.length === 1) return stripExprTactics(expr.args[0]);
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

