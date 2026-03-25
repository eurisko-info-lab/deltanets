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
import { STDLIB_SOURCE, STDLIB_NAT, STDLIB_BOOL, STDLIB_EQ, STDLIB_OPTION, STDLIB_LIST, STDLIB_SIGMA, STDLIB_Z, STDLIB_STREAM, STDLIB_Q } from "./stdlib.ts";
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
  fields?: Map<string, { type: string; zero: string; one: string; add: string; mul: string; neg: string; inv: string }>; // registered field structures
  classes?: Map<string, ClassDef>; // typeclass declarations
  instances?: InstanceDef[]; // typeclass instances
  hints?: Map<string, Set<string>>; // hint databases: db name → lemma names
  canonicals?: CanonicalDef[]; // canonical structure instances
  dataSorts?: Map<string, "Prop" | "Set" | "SProp">; // type name → declared sort (Prop, Set, or SProp)
  recordDefs?: Map<string, import("./normalize.ts").RecordDef>; // ctor name → record metadata for eta
  strategies?: Map<string, import("./types.ts").StrategyExpr>; // named proof strategies
};

export type ClassDef = {
  name: string;
  params: string[];
  methods: { name: string; type: import("./types.ts").ProveExpr }[];
};

export type InstanceDef = {
  className: string;
  args: string[];
  methods: Map<string, string>; // method name → implementation agent name
};

export type CanonicalDef = {
  name: string;         // instance name
  structName: string;   // structure/record name
  projections: Map<string, string>; // projection (field) name → concrete value
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

export type ModuleTypeDef = {
  name: string;
  specs: { name: string; arity: number }[];
};

export type FunctorDef = {
  name: string;
  params: { name: string; sig: string }[];
  base?: string;
  body: AST.SystemBody[];
};

export type CoreResult = {
  systems: Map<string, SystemDef>;
  graphs: Map<string, GraphDef>;
  laneViews: Map<string, LaneViewDef>;
  proofTrees: Map<string, ProofTree>;
  definitions: Map<string, AST.LamExpr>;
  moduleTypes: Map<string, ModuleTypeDef>;
  functors: Map<string, FunctorDef>;
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
  if (path === "stdlib") return STDLIB_SOURCE;
  if (path === "stdlib/nat") return `include "prelude"\n${STDLIB_NAT}`;
  if (path === "stdlib/bool") return `include "prelude"\n${STDLIB_BOOL}`;
  if (path === "stdlib/eq") return `include "prelude"\n${STDLIB_EQ}`;
  if (path === "stdlib/option") return `include "prelude"\n${STDLIB_OPTION}`;
  if (path === "stdlib/list") return `include "prelude"\n${STDLIB_LIST}`;
  if (path === "stdlib/sigma") return `include "prelude"\n${STDLIB_SIGMA}`;
  if (path === "stdlib/z") return `include "prelude"\n${STDLIB_Z}`;
  if (path === "stdlib/stream") return `include "prelude"\n${STDLIB_STREAM}`;
  if (path === "stdlib/q") return `include "prelude"\n${STDLIB_Q}`;
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
  const moduleTypes = new Map<string, ModuleTypeDef>();
  const functors = new Map<string, FunctorDef>();
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
          if (stmt.sig) applySeal(sys, stmt.sig, moduleTypes, errors);
          systems.set(sys.name, sys);
          for (const t of trees) proofTrees.set(t.name, t);
          break;
        }
        case "extend": {
          const { sys, proofTrees: trees } = evalExtend(stmt, systems);
          if (stmt.sig) applySeal(sys, stmt.sig, moduleTypes, errors);
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
        case "module-type": {
          const mt: ModuleTypeDef = {
            name: stmt.name,
            specs: stmt.specs.map(s => ({ name: s.name, arity: s.ports.length })),
          };
          moduleTypes.set(mt.name, mt);
          break;
        }
        case "functor": {
          functors.set(stmt.name, {
            name: stmt.name,
            params: stmt.params,
            base: stmt.base,
            body: stmt.body,
          });
          break;
        }
        case "functor-app": {
          const result = evalFunctorApp(stmt, functors, systems, moduleTypes);
          if (typeof result === "string") {
            errors.push(result);
          } else {
            systems.set(result.sys.name, result.sys);
            for (const t of result.proofTrees) proofTrees.set(t.name, t);
          }
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
        case "prove":
        case "program": {
          // Top-level prove/program: desugar using ambient + system agents
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

  return { systems, graphs, laneViews, proofTrees, definitions, moduleTypes, functors, errors };
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

// ─── Module system helpers ─────────────────────────────────────────

/** Check a system against a module type, set exports to sig names. */
function applySeal(
  sys: SystemDef,
  sigName: string,
  moduleTypes: Map<string, ModuleTypeDef>,
  errors: string[],
): void {
  const sig = moduleTypes.get(sigName);
  if (!sig) {
    errors.push(`Eval error: unknown module type '${sigName}'`);
    return;
  }
  for (const spec of sig.specs) {
    const agent = sys.agents.get(spec.name);
    if (!agent) {
      errors.push(`Eval error: system '${sys.name}' missing agent '${spec.name}' required by '${sigName}'`);
    } else {
      // arity = number of auxiliary ports (total ports minus 1 for principal)
      const auxCount = agent.ports.length - 1;
      const sigAux = spec.arity - 1;
      if (auxCount !== sigAux) {
        errors.push(`Eval error: agent '${spec.name}' in '${sys.name}' has ${agent.ports.length} ports, signature requires ${spec.arity}`);
      }
    }
  }
  // Seal: only expose signature agents
  sys.exports = new Set(sig.specs.map(s => s.name));
}

/** Instantiate a functor with concrete arguments. */
function evalFunctorApp(
  decl: AST.FunctorAppDecl,
  functors: Map<string, FunctorDef>,
  systems: Map<string, SystemDef>,
  moduleTypes: Map<string, ModuleTypeDef>,
): { sys: SystemDef; proofTrees: import("./typecheck-prove.ts").ProofTree[] } | string {
  const functor = functors.get(decl.functor);
  if (!functor) return `Eval error: unknown functor '${decl.functor}'`;
  if (decl.args.length !== functor.params.length) {
    return `Eval error: functor '${decl.functor}' expects ${functor.params.length} arguments, got ${decl.args.length}`;
  }

  // Start with base system if functor has one
  const agents = new Map<string, AgentDef>();
  const rules: RuleDef[] = [];
  const modes = new Map<string, ModeDef>();

  if (functor.base) {
    const base = systems.get(functor.base);
    if (!base) return `Eval error: functor base '${functor.base}' not found`;
    for (const [n, a] of base.agents) agents.set(n, a);
    rules.push(...base.rules);
    for (const [n, m] of base.modes) modes.set(n, m);
  }

  // Merge each argument's agents (only sig-visible ones)
  for (let i = 0; i < functor.params.length; i++) {
    const argName = decl.args[i];
    const paramSigName = functor.params[i].sig;
    const arg = systems.get(argName);
    if (!arg) return `Eval error: functor argument '${argName}' not found`;
    const sig = moduleTypes.get(paramSigName);
    if (!sig) return `Eval error: unknown module type '${paramSigName}'`;

    // Check argument satisfies signature
    for (const spec of sig.specs) {
      const agent = arg.agents.get(spec.name);
      if (!agent) {
        return `Eval error: argument '${argName}' missing agent '${spec.name}' required by '${paramSigName}'`;
      }
    }

    // Inject sig-visible agents and all rules between them
    const sigNames = new Set(sig.specs.map(s => s.name));
    for (const [n, a] of arg.agents) {
      if (sigNames.has(n)) agents.set(n, a);
    }
    for (const r of arg.rules) {
      if (sigNames.has(r.agentA) || sigNames.has(r.agentB)) {
        rules.push(r);
      }
    }
  }

  // Evaluate the functor body on top
  const extendDecl: AST.ExtendDecl = {
    kind: "extend",
    name: decl.name,
    base: "__functor_base__",
    body: functor.body,
  };

  // Register the synthesized base as a temporary system
  const tempBase: SystemDef = {
    name: "__functor_base__",
    agents,
    rules,
    modes,
    provedCtx: new Map(),
    constructorsByType: new Map(),
    computeRules: [],
    constructorTyping: new Map(),
  };

  // Merge inherited context from base and args
  if (functor.base) {
    const base = systems.get(functor.base)!;
    for (const [k, v] of base.provedCtx) tempBase.provedCtx.set(k, v);
    for (const [k, v] of base.constructorsByType) tempBase.constructorsByType.set(k, new Set(v));
    tempBase.computeRules.push(...base.computeRules);
    for (const [k, v] of base.constructorTyping) tempBase.constructorTyping.set(k, v);
  }
  for (let i = 0; i < functor.params.length; i++) {
    const arg = systems.get(decl.args[i])!;
    for (const [k, v] of arg.provedCtx) tempBase.provedCtx.set(k, v);
    for (const [k, v] of arg.constructorsByType) {
      if (!tempBase.constructorsByType.has(k)) tempBase.constructorsByType.set(k, new Set());
      for (const c of v) tempBase.constructorsByType.get(k)!.add(c);
    }
    tempBase.computeRules.push(...arg.computeRules);
    for (const [k, v] of arg.constructorTyping) tempBase.constructorTyping.set(k, v);
  }

  const tempSystems = new Map(systems);
  tempSystems.set("__functor_base__", tempBase);

  const result = evalExtend(extendDecl, tempSystems);
  return result;
}
