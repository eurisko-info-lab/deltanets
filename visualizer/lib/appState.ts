import { batch, signal } from "@preact/signals";
import { IS_BROWSER } from "$fresh/runtime.ts";
import {
  AstNode,
  getExpressionType,
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
import { Node2D, Pos } from "@deltanets/render";
import { METHODS } from "@deltanets/methods";
import { agentStyles, typeReductionMode } from "@deltanets/methods";
import {
  compileINet,
  extractGraph,
  isINetSource,
  resolveAgentStyles,
} from "@deltanets/lang";
import type { CoreResult } from "@deltanets/lang";
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

// Keep track of whether the splitter is being dragged
export const isDraggingSplitter = signal<boolean>(false);

// Mutable ref for the Monaco editor instance
// deno-lint-ignore no-explicit-any
export const codeEditorRef: { current: any } = { current: null };

// --- Internal helpers ---

/** Set AST and compute type-checking state from it (call inside batch). */
const applyAst = (astNode: AstNode | null) => {
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
) => {
  const initFromGraph = METHODS.deltanets.initFromGraph;
  if (!initFromGraph) return false;
  ast.value = null;
  typeResult.value = { ok: true, type: { kind: "hole" } };
  typeCheckSteps.value = [];
  typeCheckMode.value = false;
  typeCheckStepIdx.value = -1;
  method.value = "deltanets";
  METHODS.deltanets.state.value = initFromGraph(graph);
  return true;
};

/** Format mixed error values into display strings. */
const formatErrors = (errs: unknown[]): string[] =>
  errs.map((e) =>
    typeof e === "string" ? e : (e as { message?: string }).message ?? String(e)
  );

// --- Functions ---

export const updateAst = (source: string) => {
  window.localStorage.setItem(STORAGE_KEYS.source, source);

  if (source.length === 0) {
    scene.value = null;
    return;
  }

  // Try .inet format first
  if (isINetSource(source)) {
    const result = compileINet(source);
    if (result.errors.length === 0 && result.graphNames.length > 0) {
      agentStyles.value = resolveAgentStyles(result.core);

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
        batch(() => {
          inetMode.value = true;
          inetCore.value = result.core;
          inetGraphNames.value = result.graphNames;
          inetSelectedGraph.value = graphName;
          exprError.value = false;
          parseErrors.value = [];
          applyINetGraph(extracted.graph);
        });
        return;
      }
    }
    if (result.errors.length > 0) {
      console.warn("INet Parsing Error(s):", result.errors);
      exprError.value = true;
      parseErrors.value = formatErrors(result.errors);
      inetMode.value = false;
      return;
    }
  }

  // Fall back to standard lambda calculus parser
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
    withCenterReset(() =>
      batch(() => {
        inetSelectedGraph.value = graphName;
        applyINetGraph(extracted.graph);
        typeReductionMode.value = false;
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
  batch(() =>
    Object.keys(METHODS).forEach((m) => {
      METHODS[m].state.value = METHODS[m].init(
        astValue,
        selectedSystemType.value,
        relativeLevel.value,
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
