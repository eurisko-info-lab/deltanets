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
