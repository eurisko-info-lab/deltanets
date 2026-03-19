import { batch } from "@preact/signals";
import {
  method, theme, center, debug, selectedSystemType, systemType,
  relativeLevel, typeResult, typeCheckMode, typeCheckStepIdx, typeCheckSteps,
  ast, inetMode, inetGraphNames, inetSelectedGraph, isFirstLoad, scene,
  codeEditorRef, updateAst, selectINetGraph, enterTypeCheckMode, exitTypeCheckMode,
} from "../lib/appState.ts";
import { OPTIMAL_HIGHLIGHT_COLOR } from "../lib/render.ts";
import { typeToString } from "../lib/ast.ts";
import { hasTypeAnnotations } from "../lib/core/index.ts";
import { METHODS } from "../lib/methods/index.ts";
import { typeReductionMode } from "../lib/methods/deltanets.ts";
import examples from "../lib/examples.ts";

import IconArrowBarToLeft from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/arrow-bar-to-left.tsx";
import IconArrowLeft from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/arrow-left.tsx";
import IconArrowRight from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/arrow-right.tsx";
import IconArrowRightToArc from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/arrow-right-to-arc.tsx";
import IconArrowBarToRight from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/arrow-bar-to-right.tsx";
import IconFocusCentered from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/focus-centered.tsx";
import IconMaximize from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/maximize.tsx";
import IconDownload from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/download.tsx";
import IconBug from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/bug.tsx";
import IconBugOff from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/bug-off.tsx";

export default function Toolbar() {
  const deltaNetsData = METHODS[method.value].state.value?.data;
  const isDeltaFinalStep = method.value === "deltanets" && deltaNetsData?.isFinalStep && !deltaNetsData.appliedFinalStep;

  const tcActive = typeCheckMode.value;
  const tcIdx = tcActive ? typeCheckStepIdx.value : -1;
  const tcLen = typeCheckSteps.value.length;

  const squareButtonClass =
    `border-1 rounded p-2 text-xl min-h-[44px] min-w-[44px] bg-inherit flex flex-row justify-center items-center disabled:opacity-[0.4] disabled:cursor-not-allowed hover:bg-[${theme.value === "light" ? "white" : "#2A2A2A"
    }] disabled:bg-transparent`;

  return (
    <div
      class="flex flex-row bg-inherit gap-[8px]"
      style={{
        overflowX: "scroll",
        scrollbarWidth: "none",
      }}
    >
      <select
        onChange={(e) => {
          const selectedExampleIndex = parseInt(
            (e?.target as HTMLSelectElement).value,
          );
          const newCode = examples[selectedExampleIndex].code;

          // Prevent the selected item from changing (we're using this <select> as a dropdown menu)
          (e?.target as HTMLSelectElement).value = "examples";

          // Trigger centering (but store original value)
          const originalCenter = center.peek();
          center.value = true;

          // Update the editor content
          if (codeEditorRef.current !== null) {
            codeEditorRef.current.setValue(newCode);
          }

          // Update expression and AST
          updateAst(newCode);

          // Reset centering
          center.value = originalCenter;
        }}
        class={`border-1 rounded px-1 text-xl min-h-[44px] bg-inherit w-[120px] bg-transparent hover:bg-[${theme.value === "light" ? "white" : "#2A2A2A"
          }] disabled:bg-transparent`}
        style={{
          borderColor: theme.value === "light" ? "#FAFAFA" : "#222",
        }}
      >
        <option
          value="examples"
          disabled
          selected
          style={{ display: "none" }}
        >
          Examples
        </option>
        {examples.map((ex, i) => (
          <option value={i}>
            {ex.name}
          </option>
        ))}
      </select>
      {inetMode.value && inetGraphNames.value.length > 1 && (
        <select
          onChange={(e) => {
            selectINetGraph((e?.target as HTMLSelectElement).value);
          }}
          value={inetSelectedGraph.value}
          class="border-1 rounded px-1 text-xl min-h-[44px] bg-inherit"
          style={{
            borderColor: theme.value === "light" ? "#000D" : "#FFF6",
            background: theme.value === "light" ? "white" : "#1A1A1A",
          }}
        >
          {inetGraphNames.value.map((name) => (
            <option key={name} value={name}>
              {name}
            </option>
          ))}
        </select>
      )}
      <select
        onChange={(e) => {
          const newMethod = (e?.target as HTMLSelectElement).value;
          window.localStorage.setItem("method", newMethod);
          batch(() => {
            method.value = newMethod;
            selectedSystemType.value = systemType.value;
            // Set isFirstLoad to true to force centering when method changes
            isFirstLoad.value = true;
          });
        }}
        tabIndex={-1}
        onFocus={(e) => {
          e.preventDefault();
          e.stopPropagation();
        }}
        value={method.value}
        class="border-1 rounded px-1 text-xl min-h-[44px] bg-inherit flex-1"
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          background: theme.value === "light" ? "white" : "#1A1A1A",
        }}
      >
        {Object.entries(METHODS).map(([methodKey, methodData]) => (
          <option key={methodKey} value={methodKey}>
            {methodData.name}
          </option>
        ))}
      </select>
      {method.value === "deltanets" && <select
        value={relativeLevel.value ? "relative" : "absolute"}
        onChange={(e) => {
          const newRelativeLevel = (e?.target as HTMLSelectElement).value === "relative";
          relativeLevel.value = newRelativeLevel;
        }}
        class="border-1 rounded px-1 text-xl min-h-[44px] bg-inherit"
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          background: theme.value === "light" ? "white" : "#1A1A1A",
        }}>
        <option value="absolute">Absolute levels (default)</option>
        <option value="relative">Relative levels</option>
      </select>}
      {typeResult.value && (
        <div
          title={tcActive
            ? (typeCheckSteps.value[tcIdx]?.judgment ?? "Type check mode")
            : typeReductionMode.value
              ? "Type reduction mode — click to switch to expression reduction"
              : (typeResult.value.ok
                ? `Type: ${typeToString(typeResult.value.type)} — click to switch to type reduction`
                : `Type error: ${typeResult.value.error}`)}
          class="border-1 rounded px-2 text-sm min-h-[44px] bg-inherit flex flex-row items-center whitespace-nowrap select-none"
          style={{
            borderColor: (tcActive || typeReductionMode.value)
              ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
              : (theme.value === "light" ? "#000D" : "#FFF6"),
            color: (tcActive || typeReductionMode.value)
              ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
              : (typeResult.value.ok
                ? (!ast.value || hasTypeAnnotations(ast.value) ? (theme.value === "light" ? "#2563eb" : "#60a5fa") : (theme.value === "light" ? "#666" : "#888"))
                : (theme.value === "light" ? "#dc2626" : "#f87171")),
            maxWidth: "360px",
            overflow: "hidden",
            textOverflow: "ellipsis",
            cursor: typeResult.value.ok ? "pointer" : "default",
            background: (tcActive || typeReductionMode.value)
              ? (theme.value === "light" ? "#2563eb10" : "#60a5fa10")
              : "transparent",
          }}
          onClick={() => {
            if (!typeResult.value?.ok) return;
            if (ast.value && hasTypeAnnotations(ast.value)) {
              // From-term graph with type annotations: toggle type check stepping
              if (typeCheckMode.value) {
                exitTypeCheckMode();
                typeReductionMode.value = false;
              } else {
                enterTypeCheckMode();
                typeReductionMode.value = true;
              }
            } else {
              // Explicit graph or no type annotations: toggle type reduction mode
              typeReductionMode.value = !typeReductionMode.value;
              const ms = METHODS[method.peek()].state.peek();
              if (ms) METHODS[method.peek()].state.value = { ...ms };
            }
          }}
        >
          {tcActive
            ? (typeCheckSteps.value[tcIdx]?.judgment ?? "⊢")
            : (typeResult.value.ok
              ? `⊢ ${typeToString(typeResult.value.type)}`
              : `✘ ${typeResult.value.error}`)}
        </div>
      )}
      <select
        // This select is just an indicator in the lambda calculus method
        disabled={method.value === "lambdacalc"}
        onChange={(e) => {
          const newSystemType = (e?.target as HTMLSelectElement).value;
          selectedSystemType.value = newSystemType as any;
        }}
        tabIndex={-1}
        onFocus={(e) => {
          e.preventDefault();
          e.stopPropagation();
        }}
        value={selectedSystemType.value}
        class="border-1 rounded px-1 text-xl min-h-[44px] bg-inherit"
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          background: theme.value === "light" ? "white" : "#1A1A1A",
        }}>
        <option value="linear" disabled={systemType.value !== "linear"}>Linear (L)</option>
        <option value="affine" disabled={systemType.value === "relevant" || systemType.value === "full"}>Affine (A)</option>
        <option value="relevant" disabled={systemType.value === "affine" || systemType.value === "full"}>Relevant (I)</option>
        <option value="full">Full (K)</option>
      </select>
      <button
        type="button"
        title="Return to the beginning. Keyboard shortcut: Shift + left arrow key."
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={tcActive ? (() => { typeCheckStepIdx.value = 0; }) : METHODS[method.value].state.value?.reset}
        disabled={tcActive ? tcIdx <= 0 : !METHODS[method.value].state.value?.reset}
      >
        <IconArrowBarToLeft />
      </button>
      <button
        type="button"
        title="Step backwards in history. Keyboard shortcut: left arrow key."
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={tcActive ? (() => { typeCheckStepIdx.value = Math.max(0, typeCheckStepIdx.peek() - 1); }) : METHODS[method.value].state.value?.back}
        disabled={tcActive ? tcIdx <= 0 : !METHODS[method.value].state.value?.back}
      >
        <IconArrowLeft />
      </button>
      <div
        class="border-0 rounded text-xl min-h-[44px] bg-inherit flex flex-row justify-center items-end font-mono p-1"
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          color: tcActive ? (theme.value === "light" ? "#2563eb" : "#60a5fa") : "inherit",
        }}
      >
        {tcActive && tcLen > 0
          ? `${tcIdx}/${tcLen - 1}`
          : <>{METHODS[method.value].state.value?.idx ?? 0}/
        {METHODS[method.value].state.value?.stack?.length
          ? METHODS[method.value].state.value?.stack?.length! - 1
          : 0}</>}
      </div>
      <button
        type="button"
        title="Step forward in history or, if no history available, apply a new reduction in normal order (leftmost-outermost) if possible. Keyboard shortcut: right arrow key."
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          background: !tcActive && isDeltaFinalStep ? OPTIMAL_HIGHLIGHT_COLOR : "transparent"
        }}
        onClick={tcActive ? (() => { typeCheckStepIdx.value = Math.min(typeCheckSteps.peek().length - 1, typeCheckStepIdx.peek() + 1); }) : METHODS[method.value].state.value?.forward}
        disabled={tcActive ? tcIdx >= tcLen - 1 : !METHODS[method.value].state.value?.forward}
      >
        {tcActive
          ? <IconArrowRight />
          : ((METHODS[method.value].state.value?.idx! <
            METHODS[method.value].state.value?.stack.length! - 1) || METHODS[method.value].state.value?.forward === undefined
            ? <IconArrowRight />
            : <IconArrowRightToArc />)}
      </button>
      <button
        type="button"
        title="Go to the last step in the history. Keyboard shortcut: Shift + right arrow key."
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={tcActive ? (() => { typeCheckStepIdx.value = typeCheckSteps.peek().length - 1; }) : METHODS[method.value].state.value?.last}
        disabled={tcActive ? tcIdx >= tcLen - 1 : !METHODS[method.value].state.value?.last}
      >
        <IconArrowBarToRight />
      </button>
      <button
        type="button"
        title={`Toggle auto-centering (currently ${center.value ? "ON" : "OFF"
          })`}
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={() => {
          const newCenter = !center.peek();
          window.localStorage.setItem("center", newCenter ? "true" : "false");
          center.value = newCenter;
        }}
      >
        {center.value ? <IconFocusCentered /> : <IconMaximize />}
      </button>
      <button
        type="button"
        title="Download SVG of the current graph"
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={() => {
          // Store current theme and debug value
          const currTheme = theme.peek();
          const currDebug = debug.peek();
          // Switch to light theme and debug-mode-off for exporting
          theme.value = "light";
          debug.value = false;
          // Get svg element and serialize
          const svg = document.getElementById("root");
          const serializer = new XMLSerializer();
          let source = serializer.serializeToString(svg as any);
          // Revert to previous theme and debug mode
          theme.value = currTheme;
          debug.value = currDebug;
          // Compute viewBox
          const s = scene.peek()!;
          const width = s.getWidth();
          const height = s.getHeight();
          const viewBox =
            `${s.bounds.min.x} ${s.bounds.min.y} ${width} ${height}`;
          // Add XML and SVG boilerplate
          source =
            `<?xml version="1.0"?>\r\n<svg viewBox="${viewBox}" xmlns="http://www.w3.org/2000/svg" version="1.1">` +
            source +
            "</svg>";
          // Convert source to URI data scheme.
          const url = "data:image/svg+xml;charset=utf-8," +
            encodeURIComponent(source);
          // Download
          const downloadLink = document.createElement("a");
          downloadLink.href = url;
          downloadLink.download = "lambda.svg";
          downloadLink.click();
        }}
      >
        <IconDownload />
      </button>
      <button
        type="button"
        title={`Toggle visual debugging helpers (currently ${debug.value ? "ON" : "OFF"
          })`}
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={() => {
          const newDebug = !debug.peek();
          window.localStorage.setItem("debug", newDebug ? "true" : "false");
          debug.value = newDebug;
        }}
      >
        {debug.value ? <IconBug /> : <IconBugOff />}
      </button>
      <a
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        href="https://github.com/danaugrs/deltanets"
        target={"_blank"}
        rel="noopener noreferrer"
      >
        <GitHubIcon />
      </a>
      <button
        type="button"
        title={`Toggle theme (currently ${theme.value})`}
        class={squareButtonClass}
        style={{ borderColor: theme.value === "light" ? "#000D" : "#FFF6" }}
        onClick={() => {
          if (theme.value === "light") {
            theme.value = "dark";
            window.localStorage.setItem("theme", "dark");
          } else {
            theme.value = "light";
            window.localStorage.setItem("theme", "light");
          }
        }}
      >
        {theme.value === "light" ? <DarkThemeIcon /> : <LightThemeIcon />}
      </button>
    </div>
  );
}

const GitHubIcon = () => {
  return (
    <svg width="24" height="24" fill="currentColor" viewBox="3 3 18 18">
      <title>GitHub</title>
      <path d="M12 3C7.0275 3 3 7.12937 3 12.2276C3 16.3109 5.57625 19.7597 9.15374 20.9824C9.60374 21.0631 9.77249 20.7863 9.77249 20.5441C9.77249 20.3249 9.76125 19.5982 9.76125 18.8254C7.5 19.2522 6.915 18.2602 6.735 17.7412C6.63375 17.4759 6.19499 16.6569 5.8125 16.4378C5.4975 16.2647 5.0475 15.838 5.80124 15.8264C6.51 15.8149 7.01625 16.4954 7.18499 16.7723C7.99499 18.1679 9.28875 17.7758 9.80625 17.5335C9.885 16.9337 10.1212 16.53 10.38 16.2993C8.3775 16.0687 6.285 15.2728 6.285 11.7432C6.285 10.7397 6.63375 9.9092 7.20749 9.26326C7.1175 9.03257 6.8025 8.08674 7.2975 6.81794C7.2975 6.81794 8.05125 6.57571 9.77249 7.76377C10.4925 7.55615 11.2575 7.45234 12.0225 7.45234C12.7875 7.45234 13.5525 7.55615 14.2725 7.76377C15.9937 6.56418 16.7475 6.81794 16.7475 6.81794C17.2424 8.08674 16.9275 9.03257 16.8375 9.26326C17.4113 9.9092 17.76 10.7281 17.76 11.7432C17.76 15.2843 15.6563 16.0687 13.6537 16.2993C13.98 16.5877 14.2613 17.1414 14.2613 18.0065C14.2613 19.2407 14.25 20.2326 14.25 20.5441C14.25 20.7863 14.4188 21.0746 14.8688 20.9824C16.6554 20.364 18.2079 19.1866 19.3078 17.6162C20.4077 16.0457 20.9995 14.1611 21 12.2276C21 7.12937 16.9725 3 12 3Z">
      </path>
    </svg>
  );
};

const DarkThemeIcon = () => (
  <svg
    fill="none"
    viewBox="2 2 20 20"
    width="16"
    height="16"
    stroke="currentColor"
  >
    <path
      stroke-linecap="round"
      stroke-linejoin="round"
      stroke-width="2"
      fill="currentColor"
      d="M20.354 15.354A9 9 0 018.646 3.646 9.003 9.003 0 0012 21a9.003 9.003 0 008.354-5.646z"
    >
    </path>
  </svg>
);

const LightThemeIcon = () => (
  <svg
    fill="none"
    viewBox="3 3 18 18"
    width="16"
    height="16"
    stroke="currentColor"
  >
    <path
      stroke-linecap="round"
      stroke-linejoin="round"
      stroke-width="2"
      fill="currentColor"
      d="M12 3v1m0 16v1m9-9h-1M4 12H3m15.364 6.364l-.707-.707M6.343 6.343l-.707-.707m12.728 0l-.707.707M6.343 17.657l-.707.707M16 12a4 4 0 11-8 0 4 4 0 018 0z"
    >
    </path>
  </svg>
);
