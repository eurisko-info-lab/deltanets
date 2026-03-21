// ═══════════════════════════════════════════════════════════════════
// INet Language Bridge
// Connects the .inet/.iview compilers to the visualizer pipeline.
// Detects .inet source, compiles it, and extracts graph definitions
// that can feed into the existing buildGraph / render flow.
// ═══════════════════════════════════════════════════════════════════

import { compile as compileCore } from "./core/index.ts";
import { compile as compileView } from "./view/index.ts";
import type {
  CoreResult,
  IncludeResolver,
  LaneViewDef,
} from "./core/index.ts";
import type { ViewResult } from "./view/index.ts";
import type { AstNode } from "@deltanets/core";
import type { Graph } from "@deltanets/core";

// ─── Format detection ──────────────────────────────────────────────

// Keywords that indicate .inet format (as first non-comment token)
const INET_KEYWORDS =
  /^(?:\s*(?:#[^\n]*)?\n)*\s*(?:system|agent|rule|mode|graph|def|include|lanes)\b/;

/** Returns true if the source looks like .inet format rather than raw lambda calculus. */
export function isINetSource(source: string): boolean {
  return INET_KEYWORDS.test(source);
}

// ─── Compilation result ────────────────────────────────────────────

export type BridgeResult = {
  core: CoreResult;
  graphNames: string[]; // ordered list of graph names
  errors: string[];
};

/** Prefix used to tag lane view names in the graph selector. */
export const LANE_VIEW_PREFIX = "lanes:";

/** Compile .inet source and extract graph names. */
export function compileINet(
  source: string,
  resolver?: IncludeResolver,
): BridgeResult {
  const core = compileCore(source, resolver);
  const graphNames = [
    ...core.graphs.keys(),
    ...[...core.laneViews.keys()].map((n) => LANE_VIEW_PREFIX + n),
  ];
  return { core, graphNames, errors: core.errors };
}

// ─── Graph extraction ──────────────────────────────────────────────

export type ExtractedGraph =
  | { kind: "ast"; ast: AstNode }
  | { kind: "graph"; graph: Graph }
  | { kind: "lane-view"; laneView: LaneViewDef };

/**
 * Extract a renderable graph from a CoreResult by name.
 * Returns an AstNode (for from-term graphs) or a Graph (for explicit graphs).
 */
export function extractGraph(
  core: CoreResult,
  name: string,
): ExtractedGraph | null {
  // Check for lane view (prefixed name)
  if (name.startsWith(LANE_VIEW_PREFIX)) {
    const viewName = name.slice(LANE_VIEW_PREFIX.length);
    const laneView = core.laneViews.get(viewName);
    return laneView ? { kind: "lane-view", laneView } : null;
  }

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
import { DEFAULT_IVIEW } from "./defaults.ts";

// Cache compiled view results
const viewCache = new Map<string, ViewResult>();

/**
 * Resolve agent styles for all systems defined in a CoreResult.
 * Compiles matching .iview defaults and merges all agent styles into one map.
 */
export function resolveAgentStyles(
  core: CoreResult,
): Map<string, AgentStyleDef> {
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
