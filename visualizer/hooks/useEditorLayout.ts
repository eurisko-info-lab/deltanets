import { useEffect } from "preact/hooks";
import { useSignalEffect } from "@preact/signals";
import {
  center,
  centerGraph,
  codeEditorRef,
  editorWidth,
  isDraggingSplitter,
  MIN_PANE_SIZE,
  scene,
  theme,
} from "../lib/appState.ts";
import { STORAGE_KEYS } from "../lib/config.ts";

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
        window.localStorage.setItem(
          STORAGE_KEYS.editorWidth,
          newEditorWidth.toString(),
        );
        codeEditorRef.current.layout({
          height: window.innerHeight - 44 - 3 * 8 - 2,
          width: newEditorWidth,
        });
      }
    };
    addEventListener("resize", handleResize);

    // Resize the editor when the mouse moves and is dragging the splitter
    const resizeTo = (clientX: number) => {
      const newEditorWidth = Math.min(
        Math.max(clientX - 8 - 6, MIN_PANE_SIZE),
        (window.innerWidth - MIN_PANE_SIZE) - 3 * 8 - 4,
      );
      editorWidth.value = newEditorWidth;
      window.localStorage.setItem(
        STORAGE_KEYS.editorWidth,
        newEditorWidth.toString(),
      );
      codeEditorRef.current.layout({
        height: window.innerHeight - 44 - 3 * 8 - 2,
        width: newEditorWidth,
      });

      if (center.value) {
        centerGraph(scene.peek()!);
      }
    };
    const onMouseMove = (e: MouseEvent) => {
      if (isDraggingSplitter.value) resizeTo(e.clientX);
    };
    addEventListener("mousemove", onMouseMove);

    const onTouchMove = (e: TouchEvent) => {
      if (isDraggingSplitter.value) {
        e.preventDefault();
        resizeTo(e.touches[0].clientX);
      }
    };
    addEventListener("touchmove", onTouchMove, { passive: false });

    const onPointerUp = () => {
      isDraggingSplitter.value = false;
    };
    addEventListener("mouseup", onPointerUp);
    addEventListener("touchend", onPointerUp);

    return () => {
      removeEventListener("resize", handleResize);
      removeEventListener("mousemove", onMouseMove);
      removeEventListener("touchmove", onTouchMove);
      removeEventListener("mouseup", onPointerUp);
      removeEventListener("touchend", onPointerUp);
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
