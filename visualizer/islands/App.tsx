import { Graph as LambdaGraph } from "./Graph.tsx";
import { Head } from "$fresh/runtime.ts";
import Toolbar from "../components/Toolbar.tsx";
import { useCodeEditor } from "../hooks/useCodeEditor.ts";
import { useSceneEffects } from "../hooks/useSceneEffects.ts";
import { useEditorLayout } from "../hooks/useEditorLayout.ts";
import {
  TITLE, theme, translate, scale, center, isDraggingSplitter,
} from "../lib/appState.ts";

export default function App() {
  useCodeEditor();
  useSceneEffects();
  useEditorLayout();

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
