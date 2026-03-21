// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Evaluator
// Walks the AST and produces: agent definitions, rule specs, graphs,
// and lambda definitions that integrate with the core library.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AstNode } from "@deltanets/core";
import type { Graph } from "@deltanets/core";
import { evalSystem, evalExtend, evalCompose, evalAgent } from "./eval-system.ts";
import { evalGraph } from "./eval-graph.ts";

// ─── Output types ──────────────────────────────────────────────────

export type AgentDef = {
  name: string;
  ports: { name: string; variadic: boolean }[];
  portIndex: Map<string, number>;   // port name → index
};

export type RuleDef = {
  agentA: string;
  agentB: string;
  action: AST.RuleAction;
};

export type ModeDef = {
  name: string;
  excludedAgents: string[];
};

export type SystemDef = {
  name: string;
  agents: Map<string, AgentDef>;
  rules: RuleDef[];
  modes: Map<string, ModeDef>;
};

export type GraphDef =
  | { kind: "from-term"; name: string; astNode: AstNode }
  | { kind: "explicit"; name: string; graph: Graph };

export type CoreResult = {
  systems: Map<string, SystemDef>;
  graphs: Map<string, GraphDef>;
  definitions: Map<string, AST.LamExpr>;
  errors: string[];
};

// ─── Errors ────────────────────────────────────────────────────────

export class EvalError extends Error {
  constructor(msg: string) {
    super(`Eval error: ${msg}`);
  }
}

// ─── Main evaluator ────────────────────────────────────────────────

export function evaluate(program: AST.Program): CoreResult {
  const systems = new Map<string, SystemDef>();
  const graphs = new Map<string, GraphDef>();
  const definitions = new Map<string, AST.LamExpr>();
  const errors: string[] = [];

  // Ambient (top-level) agents/rules/modes not inside a system block
  const ambientAgents = new Map<string, AgentDef>();
  const ambientRules: RuleDef[] = [];
  const ambientModes = new Map<string, ModeDef>();

  for (const stmt of program) {
    try {
      switch (stmt.kind) {
        case "system": {
          const sys = evalSystem(stmt);
          systems.set(sys.name, sys);
          break;
        }
        case "extend": {
          const sys = evalExtend(stmt, systems);
          systems.set(sys.name, sys);
          break;
        }
        case "compose": {
          const sys = evalCompose(stmt, systems);
          systems.set(sys.name, sys);
          break;
        }
        case "agent": {
          const agent = evalAgent(stmt);
          ambientAgents.set(agent.name, agent);
          break;
        }
        case "rule": {
          ambientRules.push({
            agentA: stmt.agentA,
            agentB: stmt.agentB,
            action: stmt.action,
          });
          break;
        }
        case "mode": {
          ambientModes.set(stmt.name, {
            name: stmt.name,
            excludedAgents: stmt.exclude,
          });
          break;
        }
        case "graph":
        case "graph-explicit": {
          // Merge ambient agents with all system agents for port resolution
          const allAgents = new Map(ambientAgents);
          for (const sys of systems.values()) {
            for (const [name, agent] of sys.agents) {
              if (!allAgents.has(name)) allAgents.set(name, agent);
            }
          }
          const g = evalGraph(stmt, definitions, allAgents);
          graphs.set(g.name, g);
          break;
        }
        case "def": {
          definitions.set(stmt.name, stmt.expr);
          break;
        }
      }
    } catch (e) {
      errors.push((e as Error).message);
    }
  }

  // Package ambient declarations as a system if any exist
  if (ambientAgents.size > 0 || ambientRules.length > 0) {
    systems.set("default", {
      name: "default",
      agents: ambientAgents,
      rules: ambientRules,
      modes: ambientModes,
    });
  }

  return { systems, graphs, definitions, errors };
}
