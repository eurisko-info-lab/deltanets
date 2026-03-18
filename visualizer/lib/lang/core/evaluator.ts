// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Evaluator
// Walks the AST and produces: agent definitions, rule specs, graphs,
// and lambda definitions that integrate with the core library.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { Graph, Node, NodePort } from "../../core/types.ts";
import { link } from "../../core/graph.ts";
import type { AstNode, Type } from "../../ast.ts";

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
          const g = evalGraph(stmt, definitions, ambientAgents);
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

// ─── System evaluation ─────────────────────────────────────────────

function evalSystem(decl: AST.SystemDecl): SystemDef {
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
function evalBodyInto(
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

function evalExtend(
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

function evalCompose(
  decl: AST.ComposeDecl,
  systems: Map<string, SystemDef>,
): SystemDef {
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  // Union: merge all agents, rules, modes from each component
  for (const compName of decl.components) {
    const comp = systems.get(compName);
    if (!comp) throw new EvalError(`Cannot compose unknown system '${compName}'`);

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

function evalAgent(decl: AST.AgentDecl): AgentDef {
  const portIndex = new Map<string, number>();
  decl.ports.forEach((p, i) => portIndex.set(p.name, i));
  return { name: decl.name, ports: decl.ports, portIndex };
}

// ─── Lambda expression → AstNode ──────────────────────────────────
// Converts our LamExpr AST to the existing AstNode format used by
// the core library (deltanets.buildGraph, lambdacalc, etc.)

function lamExprToAstNode(
  expr: AST.LamExpr,
  defs: Map<string, AST.LamExpr>,
  parent?: AstNode,
): AstNode {
  switch (expr.kind) {
    case "lam": {
      const node: any = { type: "abs", name: expr.param, body: null, parent };
      if (expr.typeAnnotation) {
        node.typeAnnotation = typeExprToType(expr.typeAnnotation);
      }
      node.body = lamExprToAstNode(expr.body, defs, node);
      return node;
    }
    case "app": {
      const node: any = { type: "app", func: null, arg: null, parent };
      node.func = lamExprToAstNode(expr.func, defs, node);
      node.arg = lamExprToAstNode(expr.arg, defs, node);
      return node;
    }
    case "var": {
      // Expand definitions (macro-style)
      const def = defs.get(expr.name);
      if (def) {
        return lamExprToAstNode(def, defs, parent);
      }
      return { type: "var", name: expr.name, parent } as AstNode;
    }
  }
}

// Convert a TypeExpr AST node to the core Type representation.
function typeExprToType(texpr: AST.TypeExpr): Type {
  switch (texpr.kind) {
    case "type-base":  return { kind: "base", name: texpr.name };
    case "type-arrow": return { kind: "arrow", from: typeExprToType(texpr.from), to: typeExprToType(texpr.to) };
    case "type-hole":  return { kind: "hole" };
  }
}

// ─── Graph evaluation ──────────────────────────────────────────────

function evalGraph(
  decl: AST.GraphDecl,
  defs: Map<string, AST.LamExpr>,
  agents: Map<string, AgentDef>,
): GraphDef {
  if (decl.kind === "graph") {
    // Graph from lambda term → produce an AstNode for the caller to feed
    // into an InteractionSystem.buildGraph or TreeSystem
    const astNode = lamExprToAstNode(decl.term, defs);
    return { kind: "from-term", name: decl.name, astNode };
  } else {
    // Explicit graph construction
    const graph = buildExplicitGraph(decl.body, agents);
    return { kind: "explicit", name: decl.name, graph };
  }
}

// ─── Explicit graph builder ────────────────────────────────────────

function buildExplicitGraph(
  body: (AST.LetStmt | AST.WireStmt)[],
  agents: Map<string, AgentDef>,
): Graph {
  const graph: Graph = [];
  const env = new Map<string, Node>();

  for (const stmt of body) {
    switch (stmt.kind) {
      case "let": {
        const node: Node = {
          type: stmt.agentType,
          label: stmt.label ?? stmt.agentType,
          ports: [],
        };
        graph.push(node);
        env.set(stmt.varName, node);
        break;
      }
      case "wire": {
        const nodeA = env.get(stmt.portA.node);
        const nodeB = env.get(stmt.portB.node);
        if (!nodeA) throw new EvalError(`Unknown node '${stmt.portA.node}'`);
        if (!nodeB) throw new EvalError(`Unknown node '${stmt.portB.node}'`);
        const portIdxA = resolvePort(stmt.portA.port, nodeA, agents);
        const portIdxB = resolvePort(stmt.portB.port, nodeB, agents);
        link({ node: nodeA, port: portIdxA }, { node: nodeB, port: portIdxB });
        break;
      }
    }
  }

  return graph;
}

// ─── Port resolution ───────────────────────────────────────────────
// Resolves a port name to a numeric index, checking both agent
// definitions and well-known port names from the core type system.

const WELL_KNOWN_PORTS: Record<string, Record<string, number>> = {
  abs:        { principal: 0, body: 1, bind: 2, type: 3 },
  app:        { func: 0, result: 1, arg: 2 },
  "rep-in":   { principal: 0 },
  "rep-out":  { principal: 0 },
  era:        { principal: 0 },
  var:        { principal: 0 },
  root:       { principal: 0 },
  "type-base":  { principal: 0 },
  "type-arrow": { principal: 0, domain: 1, codomain: 2 },
  "type-hole":  { principal: 0 },
};

function resolvePort(
  portName: string,
  node: Node,
  agents: Map<string, AgentDef>,
): number {
  // Numeric port
  const num = parseInt(portName);
  if (!isNaN(num)) return num;

  // Agent definition lookup
  const agentDef = agents.get(node.type);
  if (agentDef) {
    const idx = agentDef.portIndex.get(portName);
    if (idx !== undefined) return idx;
  }

  // Well-known ports
  const wk = WELL_KNOWN_PORTS[node.type];
  if (wk && wk[portName] !== undefined) return wk[portName];

  throw new EvalError(`Unknown port '${portName}' on agent type '${node.type}'`);
}
