import { Signal, useSignalEffect } from "@preact/signals";
import { Graph as LambdaGraph } from "./Graph.tsx";
import { Head } from "$fresh/runtime.ts";
import { AstNode } from "../lib/ast.ts";
import { Node2D, render } from "../lib/render.ts";
import { useEffect } from "preact/hooks";
import loader, { type Monaco } from "@monaco-editor/loader";
import examples from "../lib/examples.ts";
import { METHODS } from "../lib/methods/index.ts";
import type { MethodState } from "../lib/methods/index.ts";
import Toolbar from "../components/Toolbar.tsx";
import {
  TITLE, MIN_PANE_SIZE,
  method, theme, editorWidth, ast, scene, center, debug,
  typeCheckMode, typeCheckSteps, typeCheckStepIdx,
  translate, scale, isFirstLoad,
  isDraggingSplitter, codeEditorRef,
  lastExpression, selectedSystemType, relativeLevel,
  updateAst, initializeStates, centerGraph,
} from "../lib/appState.ts";

export default function App() {
  // Initialize Monaco editor
  useEffect(() => {
    (loader as any).init().then((monaco: Monaco) => {
      // Initialize the editor content with the source code stored in local storage or the starter example if local storage is empty
      const source = window.localStorage.getItem("source") ?? examples[0].code;

      // Create code editor
      codeEditorRef.current = monaco.editor.create(
        document.getElementById("editor")!,
        {
          value: source,
          // Elixir syntax highlighting works perfectly for our purposes
          language: "elixir",
          fontSize: 17,
          theme: theme.value === "light" ? "vs" : "vs-dark",
          minimap: {
            enabled: false,
          },
          lineNumbersMinChars: 2,
          wordWrap: "on",
          scrollBeyondLastLine: false,
          dimension: {
            height: window.innerHeight - 44 - 3 * 8 - 2,
            width: editorWidth.value,
          },
        },
      );

      // Update AST based on the initial expression
      // This is done after the editor is created to center the graph on first load
      updateAst(source);

      // Listen for changes to the editor content
      codeEditorRef.current.onDidChangeModelContent((e: any) => {
        if (codeEditorRef.current === null) {
          return;
        }
        // Set isFirstLoad to true to force centering when user types (nice-to-have)
        isFirstLoad.value = true;
        // Update the AST based on the new expression
        updateAst(codeEditorRef.current.getValue());
      });

      // Replace backslashes with lambdas
      codeEditorRef.current.onKeyDown((e: any) => {
        if (e.keyCode === monaco.KeyCode.Backslash) {
          // Intercept the backslash key
          e.preventDefault(); // Prevent the default key behavior

          const selection = codeEditorRef.current.getSelection(); // Get the current selection
          const range = new monaco.Range(
            selection.startLineNumber,
            selection.startColumn,
            selection.endLineNumber,
            selection.endColumn,
          );

          // Replace the selection (if exists) with the 'λ' character
          codeEditorRef.current.executeEdits("", [
            {
              range: range,
              text: "λ",
              forceMoveMarkers: true,
            },
          ]);

          // Optionally move the cursor after the inserted character
          codeEditorRef.current.setPosition({
            lineNumber: range.endLineNumber,
            column: range.startColumn + 1,
          });
        }
      });
    });

    // Set up keyboard listeners for arrow keys to trigger back / forward
    const onKey = (e: any) => {
      if (
        document.activeElement?.tagName === "TEXTAREA" ||
        document.activeElement?.tagName === "INPUT"
      ) {
        return;
      }
      e.preventDefault();
      e.stopPropagation();
      // Type check mode: step through typing derivation
      if (typeCheckMode.peek()) {
        const steps = typeCheckSteps.peek();
        const idx = typeCheckStepIdx.peek();
        if (e.code === "ArrowLeft") {
          if (e.getModifierState("Shift")) {
            typeCheckStepIdx.value = 0;
          } else if (idx > 0) {
            typeCheckStepIdx.value = idx - 1;
          }
        } else if (e.code === "ArrowRight") {
          if (e.getModifierState("Shift")) {
            typeCheckStepIdx.value = steps.length - 1;
          } else if (idx < steps.length - 1) {
            typeCheckStepIdx.value = idx + 1;
          }
        }
        return;
      }
      if (e.code === "ArrowLeft") {
        if (e.getModifierState("Shift")) {
          METHODS[method.value].state.value?.reset?.();
        } else {
          METHODS[method.value].state.value?.back?.();
        }
      } else if (e.code === "ArrowRight") {
        if (e.getModifierState("Control")) {
          METHODS[method.value].state.value?.forwardParallel?.();
        } else if (e.getModifierState("Shift")) {
          METHODS[method.value].state.value?.last?.();
        } else {
          METHODS[method.value].state.value?.forward?.();
        }
      }
    };
    addEventListener("keydown", onKey);
    return () => {
      removeEventListener("keydown", onKey);
    };
  }, []);

  // Initialize `METHODS` signals (for all methods) when `ast` changes
  useSignalEffect(() => initializeStates(ast.value));

  // Update `scene` when `METHODS`, `method`, or type check state changes
  // (`METHODS`, `method`, `typeCheckMode`, `typeCheckStepIdx`) -> `scene`
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

  // Rerender when `scene` or `theme` changes.
  // (`scene`, `theme`) -> render()
  useSignalEffect(() => {
    if (scene.value === null) {
      return;
    }
    const zSVGs = scene.value.render(theme.value, debug.value);
    const SVGs = render(zSVGs);
    document.getElementById("root")!.replaceChildren(...SVGs);
  });

  // Set up callbacks
  useEffect(() => {
    // Resize the editor when the window size changes
    const handleResize = () => {
      if (codeEditorRef.current !== null) {
        const newEditorWidth = Math.min(
          Math.max(editorWidth.value, MIN_PANE_SIZE),
          (window.innerWidth - MIN_PANE_SIZE) - 3 * 8 - 4,
        );
        editorWidth.value = newEditorWidth;
        window.localStorage.setItem("editorWidth", newEditorWidth.toString());
        codeEditorRef.current.layout({
          height: window.innerHeight - 44 - 3 * 8 - 2,
          width: newEditorWidth,
        });
      }
    };
    addEventListener("resize", handleResize);

    // Resize the editor when the mouse moves and is dragging the splitter
    const onMouseMove = (e: MouseEvent) => {
      if (isDraggingSplitter.value) {
        const newEditorWidth = Math.min(
          Math.max(e.clientX - 8 - 6, MIN_PANE_SIZE),
          (window.innerWidth - MIN_PANE_SIZE) - 3 * 8 - 4,
        );
        editorWidth.value = newEditorWidth;
        window.localStorage.setItem("editorWidth", newEditorWidth.toString());
        codeEditorRef.current.layout({
          height: window.innerHeight - 44 - 3 * 8 - 2,
          width: newEditorWidth,
        });

        // Recenter graph if center is enabled
        if (center.value) {
          centerGraph(scene.peek()!);
        }
      }
    };
    addEventListener("mousemove", onMouseMove);

    const onMouseUp = () => {
      isDraggingSplitter.value = false;
    };
    addEventListener("mouseup", onMouseUp);

    return () => {
      removeEventListener("resize", handleResize);
      removeEventListener("mousemove", onMouseMove);
      removeEventListener("mouseup", onMouseUp);
    };
  }, []);

  // Change the editor theme when the theme changes
  useSignalEffect(() => {
    const newTheme = theme.value;
    if (codeEditorRef.current !== null) {
      codeEditorRef.current.updateOptions({
        theme: newTheme === "light" ? "default" : "vs-dark",
      });
    }
  });

  return (
    <>
      <Head>
        <title>{TITLE}</title>
      </Head>
      <div
        id="main"
        class="w-screen h-[100dvh] p-2 flex flex-col gap-[8px]"
        style={{
          color: theme.value === "light" ? "#000D" : "#FFFD",
          background: theme.value === "light" ? "#FAFAFA" : "#222",
          fontFamily: "OpenSans",
        }}
      >
        <Toolbar />
        <div
          style={{
            display: "flex",
            flexDirection: "row",
            alignItems: "stretch",
            flex: 1,
          }}
        >
          <div
            id="editor-container"
            class="border-1 rounded"
            style={{
              overflow: "hidden",
              borderColor: theme.value === "light" ? "#000D" : "#FFF6",
            }}
          >
            <div id="editor"></div>
          </div>
          <div
            id="splitter"
            class={`hover:(bg-[${theme.value === "light" ? "white" : "#2A2A2A"
              }] cursor-ew-resize)`}
            style={{ width: "8px" }}
            onDragStart={(e) => {
              e.preventDefault();
              isDraggingSplitter.value = true;
            }}
            onMouseDown={(e) => {
              e.preventDefault();
              isDraggingSplitter.value = true;
            }}
          />
          <div class="flex-1">
            <LambdaGraph
              theme={theme.value}
              translate={translate}
              scale={scale}
              center={center}
            />
          </div>
        </div>
      </div>
    </>
  );
}
