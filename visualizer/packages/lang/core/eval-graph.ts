// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Graph Evaluation Helpers
// evalGraph, lamExprToAstNode, typeExprToType,
// buildExplicitGraph, resolvePort, WELL_KNOWN_PORTS
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { Graph, Node } from "@deltanets/core";
import { link } from "@deltanets/core";
import type { AstNode, Type } from "@deltanets/core";
import type { AgentDef, GraphDef } from "./evaluator.ts";
import { EvalError } from "./evaluator.ts";

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
    case "type-base":
      return { kind: "base", name: texpr.name };
    case "type-arrow":
      return {
        kind: "arrow",
        from: typeExprToType(texpr.from),
        to: typeExprToType(texpr.to),
      };
    case "type-hole":
      return { kind: "hole" };
  }
}

// ─── Graph evaluation ──────────────────────────────────────────────

export function evalGraph(
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
  abs: { principal: 0, body: 1, bind: 2, type: 3 },
  app: { func: 0, result: 1, arg: 2 },
  "rep-in": { principal: 0 },
  "rep-out": { principal: 0 },
  era: { principal: 0 },
  var: { principal: 0 },
  root: { principal: 0 },
  "type-base": { principal: 0 },
  "type-arrow": { principal: 0, domain: 1, codomain: 2 },
  "type-hole": { principal: 0 },
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

  throw new EvalError(
    `Unknown port '${portName}' on agent type '${node.type}'`,
  );
}
