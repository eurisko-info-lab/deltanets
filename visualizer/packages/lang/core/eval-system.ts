// ═══════════════════════════════════════════════════════════════════
// INet Core Language — System Evaluation Helpers
// evalSystem, evalExtend, evalCompose, evalAgent, evalBodyInto
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AgentDef, ModeDef, RuleDef, SystemDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";

export function evalSystem(decl: AST.SystemDecl): SystemDef {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  for (const item of decl.body) {
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
    }
  }

  return { name: decl.name, agents, rules, modes };
}

// Helper: evaluate a system body (agents/rules/modes) and merge into
// existing collections, used by extend and compose.
export function evalBodyInto(
  body: (AST.AgentDecl | AST.RuleDecl | AST.ModeDecl)[],
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
