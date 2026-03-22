import { batch, signal } from "@preact/signals";
import { IS_BROWSER } from "$fresh/runtime.ts";
import {
  AstNode,
  type AgentPortDefs,
  getExpressionType,
  type InteractionRule,
  parseSource,
  SystemType,
} from "@deltanets/core";
import {
  generateTypeCheckSteps,
  hasTypeAnnotations,
  tagAstWithTypeCheckIndices,
  typeCheck,
} from "@deltanets/core";
import type { TypeCheckStep, TypeResult } from "@deltanets/core";
import {
  type LaneViewInput,
  Node2D,
  Pos,
  renderLaneView,
  renderProofTree,
} from "@deltanets/render";
import { METHODS } from "@deltanets/methods";
import { agentStyles, typeReductionMode } from "@deltanets/methods";
import {
  compileINet,
  extractGraph,
  isINetSource,
  LANE_VIEW_PREFIX,
  PROOF_TREE_PREFIX,
  resolveAgentStyles,
} from "@deltanets/lang";
import type { CoreResult } from "@deltanets/lang";
import type { ProofNode, ProofTree } from "@deltanets/lang";
import { MAX_AUTO_SCALE, MIN_PANE_SIZE, STORAGE_KEYS } from "./config.ts";

// Re-export for consumers that imported from here.
export { MAX_AUTO_SCALE, MIN_PANE_SIZE } from "./config.ts";

export const TITLE = "Interactive λ-Reduction";

// --- Signals ---

// Expression has error
export const exprError = signal<boolean>(false);

// Parse error messages for display
export const parseErrors = signal<string[]>([]);

// Reduction method
const storedMethod = IS_BROWSER &&
  window.localStorage.getItem(STORAGE_KEYS.method);
export const method = signal<string>(storedMethod || Object.keys(METHODS)[0]);
export const systemType = signal<SystemType>("full");
export const selectedSystemType = signal<SystemType>("full");
export const relativeLevel = signal<boolean>(false);

// Theme
const storedTheme = IS_BROWSER &&
  window.localStorage.getItem(STORAGE_KEYS.theme);
export const theme = signal<"light" | "dark">(
  (storedTheme as "light" | "dark") || "dark",
);

const storedEditorWidth = IS_BROWSER &&
  window.localStorage.getItem(STORAGE_KEYS.editorWidth);
export const editorWidth = signal<number>(
  parseFloat(storedEditorWidth || "500"),
);

// AST
export const ast = signal<AstNode | null>(null);

// Type checking result
export const typeResult = signal<TypeResult | null>(null);

// Scene to render
export const scene = signal<Node2D | null>(null);

// Whether to automatically center the graph
const storedCenter = IS_BROWSER &&
  window.localStorage.getItem(STORAGE_KEYS.center);
export const center = signal<boolean>(
  storedCenter !== null ? storedCenter === "true" : true,
);

// Whether to render debugging helpers
const storedDebug = IS_BROWSER &&
  window.localStorage.getItem(STORAGE_KEYS.debug);
export const debug = signal<boolean>(
  storedDebug !== null ? storedDebug === "true" : false,
);

// Type check stepping mode
export const typeCheckMode = signal<boolean>(false);
export const typeCheckSteps = signal<TypeCheckStep[]>([]);
export const typeCheckStepIdx = signal<number>(-1);

// Graph translation and scale
export const translate = signal<Pos>({ x: 0, y: 0 });
export const scale = signal<number>(1);

// Keep track of first load to make sure we always center on first load
export const isFirstLoad = signal<boolean>(true);

// .inet language support
export const inetMode = signal<boolean>(false);
export const inetCore = signal<CoreResult | null>(null);
export const inetGraphNames = signal<string[]>([]);
export const inetSelectedGraph = signal<string>("");
export const isLaneView = signal<boolean>(false);
export const currentLaneView = signal<LaneViewInput | null>(null);

// Keep track of whether the splitter is being dragged
export const isDraggingSplitter = signal<boolean>(false);

// Mutable ref for the Monaco editor instance
// deno-lint-ignore no-explicit-any
export const codeEditorRef: { current: any } = { current: null };

// --- Inline goal hints ---

/** Track previous decoration IDs so we can replace them. */
let goalDecorationIds: string[] = [];

/** Stored hole→suggestion data for click-to-fill. */
let holeEntries: { line: number; col: number; suggestions: string[] }[] = [];

/** Find positions of standalone `?` tokens in .inet source (skipping comments and strings). */
function findHolePositions(source: string): { line: number; col: number }[] {
  const positions: { line: number; col: number }[] = [];
  let line = 1, col = 1;
  let inComment = false;
  let inString = false;
  for (let i = 0; i < source.length; i++) {
    const ch = source[i];
    if (ch === "\n") {
      line++;
      col = 1;
      inComment = false;
      continue;
    }
    if (inComment) { col++; continue; }
    if (ch === "#") { inComment = true; col++; continue; }
    if (ch === '"' && !inString) { inString = true; col++; continue; }
    if (ch === '"' && inString) { inString = false; col++; continue; }
    if (!inString && ch === "?") {
      positions.push({ line, col });
    }
    col++;
  }
  return positions;
}

/** Collect all goal nodes from proof trees in DFS source order. */
function collectGoals(proofTrees: Map<string, ProofTree>): { conclusion: string; suggestions: string[] }[] {
  const goals: { conclusion: string; suggestions: string[] }[] = [];
  function walk(node: ProofNode) {
    if (node.isGoal) {
      goals.push({ conclusion: node.conclusion, suggestions: node.suggestions || [] });
    }
    for (const child of node.children) walk(child);
  }
  for (const tree of proofTrees.values()) {
    for (const c of tree.cases) walk(c.tree);
  }
  return goals;
}

/** Update Monaco editor decorations to show goal types inline next to `?` holes. */
function updateGoalHints(source: string, proofTrees: Map<string, ProofTree>) {
  const editor = codeEditorRef.current;
  if (!editor) { holeEntries = []; return; }

  const holes = findHolePositions(source);
  const goals = collectGoals(proofTrees);

  // deno-lint-ignore no-explicit-any
  const decorations: any[] = [];
  const entries: typeof holeEntries = [];
  const count = Math.min(holes.length, goals.length);
  for (let i = 0; i < count; i++) {
    const { line, col } = holes[i];
    const { conclusion, suggestions } = goals[i];
    entries.push({ line, col, suggestions });
    let hint = ` : ${conclusion}`;
    if (suggestions.length > 0) {
      hint += `  [click ? or try: ${suggestions.join(", ")}]`;
    }
    decorations.push({
      range: { startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 1 },
      options: {
        after: {
          content: hint,
          inlineClassName: "goal-hint-text",
        },
        className: suggestions.length > 0 ? "goal-hole-clickable" : undefined,
      },
    });
  }

  holeEntries = entries;
  goalDecorationIds = editor.deltaDecorations(goalDecorationIds, decorations);
}

/** Clear all goal hint decorations. */
function clearGoalHints() {
  const editor = codeEditorRef.current;
  if (!editor) return;
  holeEntries = [];
  if (goalDecorationIds.length > 0) {
    goalDecorationIds = editor.deltaDecorations(goalDecorationIds, []);
  }
}

/** Try to fill a `?` hole at (line, col) with its first suggestion. Returns true if filled. */
export function fillHoleAtPosition(line: number, col: number): boolean {
  const editor = codeEditorRef.current;
  if (!editor) return false;
  const entry = holeEntries.find((h) => h.line === line && h.col === col);
  if (!entry || entry.suggestions.length === 0) return false;
  const range = { startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 1 };
  editor.executeEdits("fill-hole", [{ range, text: entry.suggestions[0], forceMoveMarkers: true }]);
  return true;
}

// --- Internal helpers ---

/** Set AST and compute type-checking state from it (call inside batch). */
const applyAst = (astNode: AstNode | null) => {
  isLaneView.value = false;
  currentLaneView.value = null;
  ast.value = astNode;
  if (astNode) {
    systemType.value = getExpressionType(astNode);
    selectedSystemType.value = systemType.value;
    typeResult.value = typeCheck(astNode);
    tagAstWithTypeCheckIndices(astNode);
    typeCheckSteps.value = generateTypeCheckSteps(astNode);
  } else {
    typeResult.value = null;
    typeCheckSteps.value = [];
  }
  typeCheckMode.value = false;
  typeCheckStepIdx.value = -1;
};

/** Set state for a graph extracted from .inet (no AST, deltanets method). Call inside batch. */
const applyINetGraph = (
  graph: Parameters<NonNullable<typeof METHODS.deltanets.initFromGraph>>[0],
  rules?: InteractionRule[],
  agentPorts?: AgentPortDefs,
) => {
  const initFromGraph = METHODS.deltanets.initFromGraph;
  if (!initFromGraph) return false;
  isLaneView.value = false;
  currentLaneView.value = null;
  ast.value = null;
  typeResult.value = { ok: true, type: { kind: "hole" } };
  typeCheckSteps.value = [];
  typeCheckMode.value = false;
  typeCheckStepIdx.value = -1;
  method.value = "deltanets";
  METHODS.deltanets.state.value = initFromGraph(graph, rules, agentPorts);
  return true;
};

/** Render a lane view directly to the scene (no method state). Call inside batch. */
const applyLaneView = (laneView: Parameters<typeof renderLaneView>[0]) => {
  isLaneView.value = true;
  currentLaneView.value = laneView;
  ast.value = null;
  typeResult.value = null;
  typeCheckSteps.value = [];
  typeCheckMode.value = false;
  typeCheckStepIdx.value = -1;
  scene.value = renderLaneView(laneView);
};

/** Render a proof derivation tree directly to the scene. Call inside batch. */
const applyProofTree = (proofTree: ProofTree) => {
  isLaneView.value = true; // reuse lane-view mode (non-interactive scene)
  currentLaneView.value = null;
  ast.value = null;
  typeResult.value = null;
  typeCheckSteps.value = [];
  typeCheckMode.value = false;
  typeCheckStepIdx.value = -1;
  scene.value = renderProofTree(proofTree as Parameters<typeof renderProofTree>[0]);
};

/** Format mixed error values into display strings. */
const formatErrors = (errs: unknown[]): string[] =>
  errs.map((e) =>
    typeof e === "string" ? e : (e as { message?: string }).message ?? String(e)
  );

/** Collect all interaction rules from all systems in a CoreResult. */
const collectRules = (core: CoreResult): InteractionRule[] => {
  const rules: InteractionRule[] = [];
  for (const sys of core.systems.values()) {
    for (const r of sys.rules) {
      rules.push({ agentA: r.agentA, agentB: r.agentB, action: r.action });
    }
  }
  return rules;
};

/** Collect port-name → index maps for all agents across all systems. */
const collectAgentPorts = (core: CoreResult): AgentPortDefs => {
  const defs: AgentPortDefs = new Map();
  for (const sys of core.systems.values()) {
    for (const [name, agent] of sys.agents) {
      if (!defs.has(name)) {
        defs.set(name, agent.portIndex);
      }
    }
  }
  return defs;
};

// --- Functions ---

export const updateAst = (source: string) => {
  window.localStorage.setItem(STORAGE_KEYS.source, source);

  if (source.length === 0) {
    scene.value = null;
    clearGoalHints();
    return;
  }

  // Try .inet format first
  if (isINetSource(source)) {
    const result = compileINet(source);
    if (result.errors.length === 0 && result.graphNames.length > 0) {
      agentStyles.value = resolveAgentStyles(result.core);
      updateGoalHints(source, result.core.proofTrees);

      const graphName = inetSelectedGraph.peek() &&
          result.graphNames.includes(inetSelectedGraph.peek())
        ? inetSelectedGraph.peek()
        : result.graphNames[result.graphNames.length - 1];
      const extracted = extractGraph(result.core, graphName);

      if (extracted && extracted.kind === "ast") {
        batch(() => {
          inetMode.value = true;
          inetCore.value = result.core;
          inetGraphNames.value = result.graphNames;
          inetSelectedGraph.value = graphName;
          exprError.value = false;
          parseErrors.value = [];
          applyAst(extracted.ast);
        });
        return;
      }
      if (extracted && extracted.kind === "graph") {
        const rules = collectRules(result.core);
        const ports = collectAgentPorts(result.core);
        batch(() => {
          inetMode.value = true;
          inetCore.value = result.core;
          inetGraphNames.value = result.graphNames;
          inetSelectedGraph.value = graphName;
          exprError.value = false;
          parseErrors.value = [];
          applyINetGraph(extracted.graph, rules, ports);
        });
        return;
      }
      if (extracted && extracted.kind === "lane-view") {
        batch(() => {
          inetMode.value = true;
          inetCore.value = result.core;
          inetGraphNames.value = result.graphNames;
          inetSelectedGraph.value = graphName;
          exprError.value = false;
          parseErrors.value = [];
          applyLaneView(extracted.laneView);
        });
        return;
      }
      if (extracted && extracted.kind === "proof-tree") {
        batch(() => {
          inetMode.value = true;
          inetCore.value = result.core;
          inetGraphNames.value = result.graphNames;
          inetSelectedGraph.value = graphName;
          exprError.value = false;
          parseErrors.value = [];
          applyProofTree(extracted.proofTree);
        });
        return;
      }
    }
    if (result.errors.length > 0) {
      console.warn("INet Parsing Error(s):", result.errors);
      exprError.value = true;
      parseErrors.value = formatErrors(result.errors);
      inetMode.value = false;
      clearGoalHints();
      return;
    }
  }

  // Fall back to standard lambda calculus parser
  clearGoalHints();
  inetMode.value = false;
  inetCore.value = null;
  inetGraphNames.value = [];
  inetSelectedGraph.value = "";

  const newAst = parseSource(source);
  if (newAst === undefined || newAst.errs !== undefined) {
    exprError.value = true;
    parseErrors.value = formatErrors(newAst?.errs ?? []);
    console.warn("Parsing Error(s):", newAst?.errs);
  } else {
    batch(() => {
      exprError.value = false;
      parseErrors.value = [];
      applyAst(newAst.ast ?? null);
      typeReductionMode.value = false;
    });
  }
};

// When a different .inet graph is selected, re-extract and update AST
export const selectINetGraph = (graphName: string) => {
  const core = inetCore.peek();
  if (!core) return;
  const extracted = extractGraph(core, graphName);

  const withCenterReset = (fn: () => void) => {
    const originalCenter = center.peek();
    center.value = true;
    fn();
    center.value = originalCenter;
  };

  if (extracted && extracted.kind === "ast") {
    withCenterReset(() =>
      batch(() => {
        inetSelectedGraph.value = graphName;
        applyAst(extracted.ast);
        typeReductionMode.value = false;
        isFirstLoad.value = true;
      })
    );
  } else if (extracted && extracted.kind === "graph") {
    const rules = collectRules(core);
    const ports = collectAgentPorts(core);
    withCenterReset(() =>
      batch(() => {
        inetSelectedGraph.value = graphName;
        applyINetGraph(extracted.graph, rules, ports);
        typeReductionMode.value = false;
        isFirstLoad.value = true;
      })
    );
  } else if (extracted && extracted.kind === "lane-view") {
    withCenterReset(() =>
      batch(() => {
        inetSelectedGraph.value = graphName;
        applyLaneView(extracted.laneView);
        isFirstLoad.value = true;
      })
    );
  } else if (extracted && extracted.kind === "proof-tree") {
    withCenterReset(() =>
      batch(() => {
        inetSelectedGraph.value = graphName;
        applyProofTree(extracted.proofTree);
        isFirstLoad.value = true;
      })
    );
  }
};

// Initialize `METHODS` signals for all methods with the provided AST
export const initializeStates = (astValue: AstNode | null) => {
  if (astValue === null) {
    return;
  }
  const core = inetCore.peek();
  const rules = core ? collectRules(core) : undefined;
  const ports = core ? collectAgentPorts(core) : undefined;
  batch(() =>
    Object.keys(METHODS).forEach((m) => {
      METHODS[m].state.value = METHODS[m].init(
        astValue,
        selectedSystemType.value,
        relativeLevel.value,
        rules,
        ports,
      );
    })
  );
};

// Enter type check stepping mode
export const enterTypeCheckMode = () => {
  const steps = typeCheckSteps.peek();
  if (steps.length === 0) return;
  // Tag lambdacalc clone at step 0 for highlighting
  const lcState = METHODS.lambdacalc.state.peek();
  if (lcState?.stack[0]) {
    tagAstWithTypeCheckIndices(lcState.stack[0]);
  }
  batch(() => {
    typeCheckMode.value = true;
    typeCheckStepIdx.value = 0;
    const ms = METHODS[method.peek()].state.peek()!;
    if (ms.reset) {
      ms.reset();
    } else {
      METHODS[method.peek()].state.value = { ...ms };
    }
  });
};

// Exit type check stepping mode
export const exitTypeCheckMode = () => {
  batch(() => {
    typeCheckMode.value = false;
    typeCheckStepIdx.value = -1;
    const ms = METHODS[method.peek()].state.peek()!;
    METHODS[method.peek()].state.value = { ...ms };
  });
};

export const centerGraph = (node2D: Node2D) => {
  const graphEl = document.getElementById("graph");
  if (!graphEl) return;
  const rect = graphEl.getBoundingClientRect();
  const s = Math.min(
    rect.width / node2D.getWidth(),
    rect.height / node2D.getHeight(),
  );
  batch(() => {
    scale.value = Math.min(s, MAX_AUTO_SCALE);
    translate.value = { x: -node2D.bounds.min.x, y: -node2D.bounds.min.y };
    isFirstLoad.value = false;
  });
};
