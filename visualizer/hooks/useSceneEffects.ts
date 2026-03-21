import { Signal, useSignalEffect } from "@preact/signals";
import { AstNode } from "@deltanets/core";
import { Node2D, render } from "@deltanets/render";
import { METHODS } from "@deltanets/methods";
import type { MethodState } from "@deltanets/methods";
import {
  method, ast, scene, center, debug, theme,
  typeCheckMode, typeCheckSteps, typeCheckStepIdx,
  isFirstLoad, lastExpression, selectedSystemType, relativeLevel,
  initializeStates, centerGraph,
} from "../lib/appState.ts";

/** All reactive scene effects: init states, update scene, center, and SVG rendering. */
export function useSceneEffects() {
  // Initialize `METHODS` signals (for all methods) when `ast` changes
  useSignalEffect(() => initializeStates(ast.value));

  // Update `scene` when `METHODS`, `method`, or type check state changes
  useSignalEffect(() => {
    // Subscribe to type check signals to re-render when stepping
    const tcMode = typeCheckMode.value;
    const tcIdx = typeCheckStepIdx.value;

    const currentMethod = METHODS[method.value];
    const currentState = currentMethod.state;
    if (currentState.value === null) {
      scene.value = null;
      return;
    }

    // Apply type check highlights to graph/AST nodes before rendering
    const item = currentState.value.stack[currentState.value.idx];
    if (method.value === "deltanets") {
      for (const node of item) {
        if (tcMode && node.astRef?.extra?.typeCheckIdx !== undefined) {
          const nIdx = node.astRef.extra.typeCheckIdx;
          const step = typeCheckSteps.peek()[nIdx];
          if (nIdx < tcIdx) {
            node.typeCheckState = step?.result.ok ? "checked" : "error";
          } else if (nIdx === tcIdx) {
            node.typeCheckState = step?.result.ok ? "checking" : "error";
          } else {
            node.typeCheckState = undefined;
          }
        } else {
          node.typeCheckState = undefined;
        }
      }
    } else {
      const walkAst = (aNode: AstNode) => {
        if (aNode.extra?.typeCheckIdx !== undefined) {
          const nIdx = aNode.extra.typeCheckIdx;
          if (tcMode) {
            const step = typeCheckSteps.peek()[nIdx];
            if (nIdx < tcIdx) {
              aNode.extra.typeCheckState = step?.result.ok ? "checked" : "error";
            } else if (nIdx === tcIdx) {
              aNode.extra.typeCheckState = step?.result.ok ? "checking" : "error";
            } else {
              aNode.extra.typeCheckState = undefined;
            }
          } else {
            aNode.extra.typeCheckState = undefined;
          }
        }
        if (aNode.type === "abs") walkAst(aNode.body);
        if (aNode.type === "app") { walkAst(aNode.func); walkAst(aNode.arg); }
      };
      walkAst(item);
    }

    // Log current state
    const stateStack = currentState.value.stack;
    console.log(
      `${currentMethod.name} (${currentState.value.idx}/${stateStack.length - 1
      }):`,
      stateStack[currentState.value.idx],
    );

    // Render graph and update scene
    const node2D = currentMethod.render(
      currentState as Signal<MethodState<any, any>>,
      lastExpression,
      selectedSystemType.value,
      relativeLevel.value,
    );
    scene.value = node2D;
  });

  // Center graph when scene changes if auto-centering is enabled or if on first load
  useSignalEffect(() => {
    const node2D = scene.value;
    if (node2D !== null && (center.value || isFirstLoad.peek())) {
      centerGraph(node2D);
    }
  });

  // Rerender when `scene` or `theme` changes
  useSignalEffect(() => {
    if (scene.value === null) {
      return;
    }
    const zSVGs = scene.value.render(theme.value, debug.value);
    const SVGs = render(zSVGs);
    const root = document.getElementById("root");
    if (root) root.replaceChildren(...SVGs);
  });
}
