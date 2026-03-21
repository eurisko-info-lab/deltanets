// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, ModeDef, RuleDef, SystemDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";
import { typecheckProve } from "./typecheck-prove.ts";

export function evalSystem(decl: AST.SystemDecl): SystemDef {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  evalBodyInto(decl.body, agents, rules, modes);

  return { name: decl.name, agents, rules, modes };
}

// Helper: evaluate a system body (agents/rules/modes/prove) and merge into
// existing collections, used by extend and compose.
export function evalBodyInto(
  body: AST.SystemBody[],
  agents: Map<string, AgentDef>,
  rules: RuleDef[],
  modes: Map<string, ModeDef>,
): void {
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
        const { agentDecl, ruleDecls } = desugarProve(item, agents);
        const agent = evalAgent(agentDecl);
        agents.set(agent.name, agent);
        for (const r of ruleDecls) {
          rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
        }
        // Type check if return type is annotated
        const typeErrors = typecheckProve(item);
        if (typeErrors.length > 0) {
          throw new EvalError(typeErrors.join("\n"));
        }
        break;
      }
    }
  }
}

// ─── Extend: system "B" extends "A" with additional declarations ──

export function evalExtend(
  decl: AST.ExtendDecl,
  systems: Map<string, SystemDef>,
): SystemDef {
  const base = systems.get(decl.base);
  if (!base) throw new EvalError(`Cannot extend unknown system '${decl.base}'`);

  // Copy base system contents
  const agents = new Map(base.agents);
  const rules = [...base.rules];
  const modes = new Map(base.modes);

  // Merge new declarations
  evalBodyInto(decl.body, agents, rules, modes);

  return { name: decl.name, agents, rules, modes };
}

// ─── Compose (pushout): union of component systems + cross-rules ──

export function evalCompose(
  decl: AST.ComposeDecl,
  systems: Map<string, SystemDef>,
): SystemDef {
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
  evalBodyInto(decl.body, agents, rules, modes);

  return { name: decl.name, agents, rules, modes };
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

    function translateExpr(expr: AST.ProveExpr): AST.PortRef {
      if (expr.kind === "ident") {
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

      // Map args to agent ports: args[0]→principal, args[1]→aux1, ...
      // Agent ports: [principal, result, aux1, aux2, ...]
      const argPorts = [
        agentDef.ports[0].name,
        ...agentDef.ports.slice(2).map((p) => p.name),
      ];

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

      // Output is the result port
      return { node: label, port: "result" };
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
