import { useEffect } from "preact/hooks";
import loader, { type Monaco } from "@monaco-editor/loader";
import examples from "../lib/examples.ts";
import { METHODS } from "../lib/methods/index.ts";
import {
  method, theme, editorWidth, isFirstLoad,
  typeCheckMode, typeCheckSteps, typeCheckStepIdx,
  codeEditorRef, updateAst,
} from "../lib/appState.ts";

/** Monaco editor initialization, content-change listener, backslash→λ key, and keyboard navigation. */
export function useCodeEditor() {
  useEffect(() => {
    (loader as any).init().then((monaco: Monaco) => {
      const source = window.localStorage.getItem("source") ?? examples[0].code;

      codeEditorRef.current = monaco.editor.create(
        document.getElementById("editor")!,
        {
          value: source,
          language: "elixir",
          fontSize: 17,
          theme: theme.value === "light" ? "vs" : "vs-dark",
          minimap: { enabled: false },
          lineNumbersMinChars: 2,
          wordWrap: "on",
          scrollBeyondLastLine: false,
          dimension: {
            height: window.innerHeight - 44 - 3 * 8 - 2,
            width: editorWidth.value,
          },
        },
      );

      // Parse initial source after editor is created (centers graph on first load)
      updateAst(source);

      // Re-parse on every edit
      codeEditorRef.current.onDidChangeModelContent(() => {
        if (codeEditorRef.current === null) return;
        isFirstLoad.value = true;
        updateAst(codeEditorRef.current.getValue());
      });

      // Replace backslashes with λ
      codeEditorRef.current.onKeyDown((e: any) => {
        if (e.keyCode === monaco.KeyCode.Backslash) {
          e.preventDefault();
          const selection = codeEditorRef.current.getSelection();
          const range = new monaco.Range(
            selection.startLineNumber,
            selection.startColumn,
            selection.endLineNumber,
            selection.endColumn,
          );
          codeEditorRef.current.executeEdits("", [
            { range, text: "λ", forceMoveMarkers: true },
          ]);
          codeEditorRef.current.setPosition({
            lineNumber: range.endLineNumber,
            column: range.startColumn + 1,
          });
        }
      });
    });

    // Arrow-key navigation for reduction stepping / type-check stepping
    const onKey = (e: any) => {
      if (
        document.activeElement?.tagName === "TEXTAREA" ||
        document.activeElement?.tagName === "INPUT"
      ) {
        return;
      }
      e.preventDefault();
      e.stopPropagation();

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
}
