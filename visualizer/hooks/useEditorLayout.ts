import { useEffect } from "preact/hooks";
import { useSignalEffect } from "@preact/signals";
import {
  MIN_PANE_SIZE,
  theme, editorWidth, scene, center,
  isDraggingSplitter, codeEditorRef,
  centerGraph,
} from "../lib/appState.ts";

/** Window resize handling, splitter drag tracking, and Monaco theme sync. */
export function useEditorLayout() {
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
}
