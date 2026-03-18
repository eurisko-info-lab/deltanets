// ═══════════════════════════════════════════════════════════════════
// INet Language Bridge
// Connects the .inet/.iview compilers to the visualizer pipeline.
// Detects .inet source, compiles it, and extracts graph definitions
// that can feed into the existing buildGraph / render flow.
// ═══════════════════════════════════════════════════════════════════

import { compile as compileCore } from "./core/index.ts";
import { compile as compileView } from "./view/index.ts";
import type { CoreResult, GraphDef } from "./core/index.ts";
import type { ViewResult } from "./view/index.ts";
import type { AstNode } from "../ast.ts";
import type { Graph } from "../core/types.ts";

// ─── Format detection ──────────────────────────────────────────────

// Keywords that indicate .inet format (as first non-comment token)
const INET_KEYWORDS = /^(?:\s*(?:#[^\n]*)?\n)*\s*(?:system|agent|rule|mode|graph|def)\b/;

/** Returns true if the source looks like .inet format rather than raw lambda calculus. */
export function isINetSource(source: string): boolean {
  return INET_KEYWORDS.test(source);
}

// ─── Compilation result ────────────────────────────────────────────

export type BridgeResult = {
  core: CoreResult;
  graphNames: string[];     // ordered list of graph names
  errors: string[];
};

/** Compile .inet source and extract graph names. */
export function compileINet(source: string): BridgeResult {
  const core = compileCore(source);
  const graphNames = [...core.graphs.keys()];
  return { core, graphNames, errors: core.errors };
}

// ─── Graph extraction ──────────────────────────────────────────────

export type ExtractedGraph =
  | { kind: "ast"; ast: AstNode }
  | { kind: "graph"; graph: Graph };

/**
 * Extract a renderable graph from a CoreResult by name.
 * Returns an AstNode (for from-term graphs) or a Graph (for explicit graphs).
 */
export function extractGraph(core: CoreResult, name: string): ExtractedGraph | null {
  const graphDef = core.graphs.get(name);
  if (!graphDef) return null;

  if (graphDef.kind === "from-term") {
    return { kind: "ast", ast: graphDef.astNode };
  } else {
    return { kind: "graph", graph: graphDef.graph };
  }
}

// ─── View compilation ──────────────────────────────────────────────

/** Compile .iview source for visual configuration. */
export function compileIView(source: string): ViewResult {
  return compileView(source);
}

// ─── Default .iview registry ───────────────────────────────────────
// Embedded .iview sources for browser-side compilation.
// These match the system names used in .inet files.

import type { AgentStyleDef } from "./view/index.ts";

const DEFAULT_IVIEW: Record<string, string> = {
  "delta-nets": `
render abs {
  shape: fan(up)
  role: binder
  level: expr
  fill: level-color
  z: 2
}
render app {
  shape: fan(down)
  role: applicator
  level: expr
  fill: level-color
  z: 2
}
render rep-in {
  shape: replicator(up)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render rep-out {
  shape: replicator(down)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render era {
  shape: eraser
  role: leaf
  level: expr
  fill: #888888
  z: 0
}
render var {
  shape: circle
  role: leaf
  level: expr
  fill: #cccccc
  z: 1
}
render root {
  shape: circle
  role: leaf
  level: expr
  fill: wire-color
  z: 3
}
render type-base {
  shape: rect
  role: leaf
  level: type
  fill: #b0bec5
  z: 1
}
render type-arrow {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #90a4ae
  z: 1
}
render type-hole {
  shape: circle
  role: leaf
  level: type
  fill: #78909c
  z: 1
}
`,
  "lambda-calculus": `
render abs {
  shape: fan(up)
  role: binder
  level: expr
  fill: #5c6bc0
  z: 2
}
render app {
  shape: fan(down)
  role: applicator
  level: expr
  fill: #26a69a
  z: 2
}
render var {
  shape: circle
  role: leaf
  level: expr
  fill: #ef5350
  z: 1
}
render root {
  shape: circle
  role: leaf
  level: expr
  fill: wire-color
  z: 3
}
`,
  "lambda-cube": `
render abs {
  shape: fan(up)
  role: binder
  level: expr
  fill: level-color
  z: 2
}
render app {
  shape: fan(down)
  role: applicator
  level: expr
  fill: level-color
  z: 2
}
render var {
  shape: circle
  role: leaf
  level: expr
  fill: #cccccc
  z: 1
}
render era {
  shape: eraser
  role: leaf
  level: expr
  fill: #888888
  z: 0
}
render root {
  shape: circle
  role: leaf
  level: expr
  fill: wire-color
  z: 3
}
render type-base {
  shape: circle
  role: leaf
  level: type
  fill: #b0bec5
  z: 1
}
render type-arrow {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #90a4ae
  z: 1
}
render type-hole {
  shape: circle
  role: leaf
  level: type
  fill: #78909c
  z: 1
}
render rep-in {
  shape: replicator(up)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render rep-out {
  shape: replicator(down)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render tyabs {
  shape: fan(up)
  role: binder
  level: type
  fill: #7986cb
  z: 2
}
render tyapp {
  shape: fan(down)
  role: applicator
  level: type
  fill: #7986cb
  z: 2
}
render forall {
  shape: fan(up)
  role: binder
  level: type
  fill: #9fa8da
  z: 1
}
render pi {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #80cbc4
  z: 1
}
render sigma {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #80cbc4
  z: 1
}
render pair {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #80cbc4
  z: 1
}
render fst {
  shape: fan(down)
  role: destructor
  level: type
  fill: #a5d6a7
  z: 1
}
render snd {
  shape: fan(down)
  role: destructor
  level: type
  fill: #a5d6a7
  z: 1
}
render type-abs {
  shape: fan(up)
  role: binder
  level: type
  fill: #ce93d8
  z: 2
}
render type-app {
  shape: fan(down)
  role: applicator
  level: type
  fill: #ce93d8
  z: 2
}
render kind-star {
  shape: circle
  role: leaf
  level: type
  fill: #e1bee7
  z: 1
}
render kind-arrow {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #e1bee7
  z: 1
}
`,
};

// Cache compiled view results
const viewCache = new Map<string, ViewResult>();

/**
 * Resolve agent styles for all systems defined in a CoreResult.
 * Compiles matching .iview defaults and merges all agent styles into one map.
 */
export function resolveAgentStyles(core: CoreResult): Map<string, AgentStyleDef> {
  const styles = new Map<string, AgentStyleDef>();
  for (const systemName of core.systems.keys()) {
    const iviewSource = DEFAULT_IVIEW[systemName];
    if (!iviewSource) continue;
    let viewResult = viewCache.get(systemName);
    if (!viewResult) {
      viewResult = compileView(iviewSource);
      if (viewResult.errors.length === 0) {
        viewCache.set(systemName, viewResult);
      }
    }
    for (const [agent, style] of viewResult.styles) {
      styles.set(agent, style);
    }
  }
  return styles;
}
