import { batch, signal } from "@preact/signals";
import { IS_BROWSER } from "$fresh/runtime.ts";
import { AstNode, getExpressionType, parseSource, SystemType } from "./ast.ts";
import { typeCheck, hasTypeAnnotations, generateTypeCheckSteps, tagAstWithTypeCheckIndices } from "./core/index.ts";
import type { TypeResult, TypeCheckStep } from "./core/index.ts";
import { Node2D, Pos } from "./render.ts";
import { METHODS } from "./methods/index.ts";
import { typeReductionMode, agentStyles } from "./methods/deltanets/index.ts";
import { isINetSource, compileINet, extractGraph, resolveAgentStyles } from "./lang/bridge.ts";
import type { CoreResult } from "./lang/core/index.ts";

// Constants
export const TITLE = "Interactive λ-Reduction";
export const MAX_AUTO_SCALE = 1.5;
export const MIN_PANE_SIZE = 200;

// --- Signals ---

// DEPRECATED - remove when possible
export const lastExpression = signal<string>("");

// Expression has error
export const exprError = signal<boolean>(false);

// Reduction method
const storedMethod = IS_BROWSER && window.localStorage.getItem("method");
export const method = signal<string>(storedMethod || Object.keys(METHODS)[0]);
export const systemType = signal<SystemType>("full");
export const selectedSystemType = signal<SystemType>("full");
export const relativeLevel = signal<boolean>(false);

// Theme
const storedTheme = IS_BROWSER && window.localStorage.getItem("theme");
export const theme = signal<"light" | "dark">(
  (storedTheme as "light" | "dark") || "dark",
);

const storedEditorWidth = IS_BROWSER && window.localStorage.getItem("editorWidth");
export const editorWidth = signal<number>(parseFloat(storedEditorWidth || "500"));

// AST
export const ast = signal<AstNode | null>(null);

// Type checking result
export const typeResult = signal<TypeResult | null>(null);

// Scene to render
export const scene = signal<Node2D | null>(null);

// Whether to automatically center the graph
const storedCenter = IS_BROWSER && window.localStorage.getItem("center");
export const center = signal<boolean>(storedCenter !== null ? storedCenter === "true" : true);

// Whether to render debugging helpers
const storedDebug = IS_BROWSER && window.localStorage.getItem("debug");
export const debug = signal<boolean>(storedDebug !== null ? storedDebug === "true" : false);

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
export const codeEditorRef: { current: any } = { current: null };

// --- Functions ---

export const updateAst = (source: string) => {
  window.localStorage.setItem("source", source);

  // Clear graph if empty expression
  if (source.length === 0) {
    scene.value = null;
    return;
  }

  // Try .inet format first
  if (isINetSource(source)) {
    const result = compileINet(source);
    if (result.errors.length === 0 && result.graphNames.length > 0) {
      // Resolve .iview styles for all systems in this source
      agentStyles.value = resolveAgentStyles(result.core);

      const graphName = inetSelectedGraph.peek() && result.graphNames.includes(inetSelectedGraph.peek())
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
          ast.value = extracted.ast;
          systemType.value = getExpressionType(extracted.ast);
          selectedSystemType.value = systemType.value;
          typeResult.value = typeCheck(extracted.ast);
          if (extracted.ast) {
            tagAstWithTypeCheckIndices(extracted.ast);
            typeCheckSteps.value = generateTypeCheckSteps(extracted.ast);
          } else {
            typeCheckSteps.value = [];
          }
          typeCheckMode.value = false;
          typeCheckStepIdx.value = -1;
        });
        return;
      }
      if (extracted && extracted.kind === "graph") {
        const initFromGraph = METHODS.deltanets.initFromGraph;
        if (initFromGraph) {
          batch(() => {
            inetMode.value = true;
            inetCore.value = result.core;
            inetGraphNames.value = result.graphNames;
            inetSelectedGraph.value = graphName;
            exprError.value = false;
            ast.value = null;
            typeResult.value = { ok: true, type: { kind: "hole" } };
            typeCheckSteps.value = [];
            typeCheckMode.value = false;
            typeCheckStepIdx.value = -1;
            method.value = "deltanets";
            METHODS.deltanets.state.value = initFromGraph(extracted.graph);
          });
          return;
        }
      }
    }
    if (result.errors.length > 0) {
      console.warn("INet Parsing Error(s):", result.errors);
      exprError.value = true;
      inetMode.value = false;
      return;
    }
  }

  // Fall back to standard lambda calculus parser
  inetMode.value = false;
  inetCore.value = null;
  inetGraphNames.value = [];
  inetSelectedGraph.value = "";

  // Update AST
  const newAst = parseSource(source);
  // Update AST or exprError
  if (newAst === undefined || newAst.errs !== undefined) {
    exprError.value = true;
    // Show parsing errors in the console if any (only if expression changed)
    console.warn("Parsing Error(s):", newAst?.errs);
  } else {
    batch(() => {
      exprError.value = false;
      ast.value = newAst.ast ?? null;
      systemType.value = getExpressionType(ast.value!);
      selectedSystemType.value = systemType.value;
      typeResult.value = ast.value ? typeCheck(ast.value) : null;
      // Generate type check steps and tag AST nodes with indices
      if (ast.value) {
        tagAstWithTypeCheckIndices(ast.value);
        typeCheckSteps.value = generateTypeCheckSteps(ast.value);
      } else {
        typeCheckSteps.value = [];
      }
      typeCheckMode.value = false;
      typeCheckStepIdx.value = -1;
      typeReductionMode.value = false;
    });
  }
};

// When a different .inet graph is selected, re-extract and update AST
export const selectINetGraph = (graphName: string) => {
  const core = inetCore.peek();
  if (!core) return;
  const extracted = extractGraph(core, graphName);
  if (extracted && extracted.kind === "ast") {
    const originalCenter = center.peek();
    center.value = true;
    batch(() => {
      inetSelectedGraph.value = graphName;
      ast.value = extracted.ast;
      systemType.value = getExpressionType(extracted.ast);
      selectedSystemType.value = systemType.value;
      typeResult.value = typeCheck(extracted.ast);
      if (extracted.ast) {
        tagAstWithTypeCheckIndices(extracted.ast);
        typeCheckSteps.value = generateTypeCheckSteps(extracted.ast);
      } else {
        typeCheckSteps.value = [];
      }
      typeCheckMode.value = false;
      typeCheckStepIdx.value = -1;
      typeReductionMode.value = false;
      isFirstLoad.value = true;
    });
    center.value = originalCenter;
  } else if (extracted && extracted.kind === "graph") {
    const initFromGraph = METHODS.deltanets.initFromGraph;
    if (initFromGraph) {
      const originalCenter = center.peek();
      center.value = true;
      batch(() => {
        inetSelectedGraph.value = graphName;
        ast.value = null;
        typeResult.value = { ok: true, type: { kind: "hole" } };
        typeCheckSteps.value = [];
        typeCheckMode.value = false;
        typeCheckStepIdx.value = -1;
        typeReductionMode.value = false;
        method.value = "deltanets";
        METHODS.deltanets.state.value = initFromGraph(extracted.graph);
        isFirstLoad.value = true;
      });
      center.value = originalCenter;
    }
  }
};

// Initialize `METHODS` signals for all methods with the provided AST
export const initializeStates = (astValue: AstNode | null) => {
  if (astValue === null) {
    return;
  }
  batch(() =>
    Object.keys(METHODS).forEach((m) => {
      METHODS[m].state.value = METHODS[m].init(astValue, selectedSystemType.value, relativeLevel.value);
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
  const graphEl = document.getElementById("graph")!;
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
