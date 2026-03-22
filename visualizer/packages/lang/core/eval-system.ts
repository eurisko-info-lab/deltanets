// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, ModeDef, RuleDef, SystemDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import { buildProofTree, type ProvedContext, type ProofTree, typecheckProve } from "./typecheck-prove.ts";

export function evalSystem(decl: AST.SystemDecl): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  const proofTrees = evalBodyInto(decl.body, agents, rules, modes);

  return { sys: { name: decl.name, agents, rules, modes }, proofTrees };
}

// Helper: evaluate a system body (agents/rules/modes/prove) and merge into
// existing collections, used by extend and compose.
// Returns any proof trees generated from typed prove blocks.
export function evalBodyInto(
  body: AST.SystemBody[],
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  modes: Map<string, ModeDef>,
): ProofTree[] {
  const provedCtx: ProvedContext = new Map();
  const proofTrees: ProofTree[] = [];

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
        const hasHoles = proveContainsHole(item);
        // Only generate agent + rules for complete proofs (no ? holes)
        if (!hasHoles) {
          const { agentDecl, ruleDecls } = desugarProve(item, agents);
          const agent = evalAgent(agentDecl);
          agents.set(agent.name, agent);
          for (const r of ruleDecls) {
            rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
          }
        }
        // Type check if return type is annotated
        const typeErrors = typecheckProve(item, provedCtx);
        if (typeErrors.length > 0) {
          throw new EvalError(typeErrors.join("\n"));
        }
        // Build proof derivation tree
        const tree = buildProofTree(item, provedCtx);
        if (tree) proofTrees.push(tree);
        // Register this prove's type for cross-lemma resolution
        if (item.returnType) {
          provedCtx.set(item.name, {
            params: item.params,
            returnType: item.returnType,
          });
        }
        break;
      }
    }
  }
  return proofTrees;
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

  // Merge new declarations
  const proofTrees = evalBodyInto(decl.body, agents, rules, modes);

  return { sys: { name: decl.name, agents, rules, modes }, proofTrees };
}

// ─── Compose (pushout): union of component systems + cross-rules ──

export function evalCompose(
  decl: AST.ComposeDecl,
  systems: Map<string, SystemDef>,
): { sys: SystemDef; proofTrees: ProofTree[] } {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  // Union: merge all agents, rules, modes from each component
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
  }

  // Add cross-interaction rules from the compose body (the pushout span)
  const proofTrees = evalBodyInto(decl.body, agents, rules, modes);

  return { sys: { name: decl.name, agents, rules, modes }, proofTrees };
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

function isPreExisting(ref: AST.PortRef): boolean {
  return ref.node === "left" || ref.node === "right";
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
