// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Evaluator
// Walks the AST and produces: agent definitions, rule specs, graphs,
// and lambda definitions that integrate with the core library.
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";
import type { AstNode } from "@deltanets/core";
import type { Graph } from "@deltanets/core";
import {
  evalAgent,
  evalBodyInto,
  evalCompose,
  evalExtend,
  evalSystem,
} from "./eval-system.ts";
import { evalGraph } from "./eval-graph.ts";
import { PRELUDE_SOURCE } from "./prelude.ts";
import { tokenize } from "./lexer.ts";
import { parse } from "./parser.ts";

// ─── Output types ──────────────────────────────────────────────────

export type AgentDef = {
  name: string;
  ports: { name: string; variadic: boolean }[];
  portIndex: Map<string, number>; // port name → index
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
  provedCtx: import("./typecheck-prove.ts").ProvedContext;
  constructorsByType: Map<string, Set<string>>;
  computeRules: import("./typecheck-prove.ts").ComputeRule[];
  constructorTyping: import("./typecheck-prove.ts").ConstructorTyping;
  exports?: Set<string>; // if set, only these agents are visible to open/extend
  tactics?: Map<string, TacticDef>; // user-defined tactics
  setoids?: Map<string, { name: string; type: string; refl: string; sym: string; trans: string }>; // registered setoid relations
  rings?: Map<string, { type: string; zero: string; one?: string; add: string; mul: string }>; // registered ring structures
};

export type TacticDef = {
  name: string;
  agents: Map<string, AgentDef>;
  rules: RuleDef[];
};

export type GraphDef =
  | { kind: "from-term"; name: string; astNode: AstNode }
  | { kind: "explicit"; name: string; graph: Graph };

// ─── Lane view output types ────────────────────────────────────────

export type LaneViewDef = {
  name: string;
  lanes: { name: string; props: Record<string, string | number> }[];
  items: {
    position: number;
    lane: string;
    label: string;
    duration: number;
  }[];
  markers: { position: number; label?: string }[];
  links: { from: string; to: string; label?: string }[];
};

import type { ProofTree } from "./typecheck-prove.ts";

export type CoreResult = {
  systems: Map<string, SystemDef>;
  graphs: Map<string, GraphDef>;
  laneViews: Map<string, LaneViewDef>;
  proofTrees: Map<string, ProofTree>;
  definitions: Map<string, AST.LamExpr>;
  errors: string[];
};

// ─── Errors ────────────────────────────────────────────────────────

export class EvalError extends Error {
  constructor(msg: string) {
    super(`Eval error: ${msg}`);
  }
}

// ─── Include resolution ────────────────────────────────────────────

/** Resolves an include path to .inet source code, or null if not found. */
export type IncludeResolver = (path: string) => string | null;

/** Built-in resolver that handles `include "prelude"`. */
function builtinResolver(path: string): string | null {
  if (path === "prelude") return PRELUDE_SOURCE;
  return null;
}

/** Expand all include statements by inlining their parsed AST. */
function expandIncludes(
  program: AST.Program,
  resolver: IncludeResolver | undefined,
  included: Set<string>,
): { stmts: AST.Statement[]; errors: string[] } {
  const stmts: AST.Statement[] = [];
  const errors: string[] = [];
  for (const stmt of program) {
    if (stmt.kind === "include") {
      if (included.has(stmt.path)) continue; // skip circular
      included.add(stmt.path);
      const source = resolver?.(stmt.path) ?? builtinResolver(stmt.path);
      if (source === null) {
        errors.push(`Cannot resolve include '${stmt.path}'`);
        continue;
      }
      const tokens = tokenize(source);
      const sub = parse(tokens);
      const expanded = expandIncludes(sub, resolver, included);
      stmts.push(...expanded.stmts);
      errors.push(...expanded.errors);
    } else {
      stmts.push(stmt);
    }
  }
  return { stmts, errors };
}

// ─── Main evaluator ────────────────────────────────────────────────

export function evaluate(
  program: AST.Program,
  resolver?: IncludeResolver,
): CoreResult {
  const { stmts, errors: includeErrors } = expandIncludes(
    program,
    resolver,
    new Set(),
  );
  const systems = new Map<string, SystemDef>();
  const graphs = new Map<string, GraphDef>();
  const laneViews = new Map<string, LaneViewDef>();
  const proofTrees = new Map<string, import("./typecheck-prove.ts").ProofTree>();
  const definitions = new Map<string, AST.LamExpr>();
  const errors: string[] = [...includeErrors];

  // Ambient (top-level) agents/rules/modes not inside a system block
  const ambientAgents = new Map<string, AgentDef>();
  const ambientRules: RuleDef[] = [];
  const ambientModes = new Map<string, ModeDef>();
  const ambientComputeRules: import("./typecheck-prove.ts").ComputeRule[] = [];
  const ambientCtorTyping: import("./typecheck-prove.ts").ConstructorTyping = new Map();

  for (const stmt of stmts) {
    try {
      switch (stmt.kind) {
        case "system": {
          const { sys, proofTrees: trees } = evalSystem(stmt, systems);
          systems.set(sys.name, sys);
          for (const t of trees) proofTrees.set(t.name, t);
          break;
        }
        case "extend": {
          const { sys, proofTrees: trees } = evalExtend(stmt, systems);
          systems.set(sys.name, sys);
          for (const t of trees) proofTrees.set(t.name, t);
          break;
        }
        case "compose": {
          const { sys, proofTrees: trees } = evalCompose(stmt, systems);
          systems.set(sys.name, sys);
          for (const t of trees) proofTrees.set(t.name, t);
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
        case "compute": {
          // Top-level compute: collect for ambient system
          // Resolve var patterns that match known agents to ctor patterns
          const resolvedArgs = stmt.args.map((pat: import("./types.ts").ComputePattern): import("./types.ts").ComputePattern => {
            if (pat.kind === "var" && ambientAgents.has(pat.name)) {
              return { kind: "ctor", name: pat.name, args: [] };
            }
            return pat;
          });
          ambientComputeRules.push({
            funcName: stmt.funcName,
            args: resolvedArgs,
            result: stmt.result,
          });
          break;
        }
        case "data": {
          // Top-level data: desugar into agents/rules and populate ctor typing
          const result = evalBodyInto([stmt], ambientAgents, ambientRules, ambientModes);
          // Merge constructorTyping from the desugared data decl
          for (const [k, v] of result.constructorTyping) {
            ambientCtorTyping.set(k, v);
          }
          break;
        }
        case "prove": {
          // Top-level prove: desugar using ambient + system agents
          const allAgents = new Map(ambientAgents);
          for (const sys of systems.values()) {
            for (const [name, agent] of sys.agents) {
              if (!allAgents.has(name)) allAgents.set(name, agent);
            }
          }
          const result = evalBodyInto([stmt], allAgents, ambientRules, ambientModes, undefined, undefined, ambientComputeRules, ambientCtorTyping);
          for (const t of result.proofTrees) proofTrees.set(t.name, t);
          // Copy back newly created agents
          for (const [name, agent] of allAgents) {
            if (!ambientAgents.has(name)) ambientAgents.set(name, agent);
          }
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
        case "lanes": {
          const view = evalLaneView(stmt);
          laneViews.set(view.name, view);
          break;
        }
        case "tactic": {
          // Top-level tactic: process via evalBodyInto
          evalBodyInto([stmt], ambientAgents, ambientRules, ambientModes);
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
      provedCtx: new Map(),
      constructorsByType: new Map(),
      computeRules: ambientComputeRules,
      constructorTyping: ambientCtorTyping,
    });
  }

  return { systems, graphs, laneViews, proofTrees, definitions, errors };
}

// ─── Lane view evaluation ──────────────────────────────────────────

function evalLaneView(decl: AST.LanesDecl): LaneViewDef {
  const lanes: LaneViewDef["lanes"] = [];
  const items: LaneViewDef["items"] = [];
  const markers: LaneViewDef["markers"] = [];
  const links: LaneViewDef["links"] = [];
  for (const stmt of decl.body) {
    switch (stmt.kind) {
      case "lane-def":
        lanes.push({ name: stmt.name, props: stmt.props });
        break;
      case "lane-item":
        items.push({
          position: stmt.position,
          lane: stmt.lane,
          label: stmt.label,
          duration: stmt.duration,
        });
        break;
      case "lane-marker":
        markers.push({ position: stmt.position, label: stmt.label });
        break;
      case "lane-link":
        links.push({ from: stmt.from, to: stmt.to, label: stmt.label });
        break;
    }
  }
  return { name: decl.name, lanes, items, markers, links };
}
