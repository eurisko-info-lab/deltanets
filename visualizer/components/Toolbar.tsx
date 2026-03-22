import { batch } from "@preact/signals";
import {
  ast,
  center,
  codeEditorRef,
  currentLaneView,
  debug,
  enterTypeCheckMode,
  exitTypeCheckMode,
  inetGraphNames,
  inetMode,
  inetSelectedGraph,
  isFirstLoad,
  isLaneView,
  method,
  parseErrors,
  relativeLevel,
  scene,
  selectedSystemType,
  selectINetGraph,
  systemType,
  theme,
  typeCheckMode,
  typeCheckStepIdx,
  typeCheckSteps,
  typeResult,
  updateAst,
} from "../lib/appState.ts";
import { STORAGE_KEYS } from "../lib/config.ts";
import { OPTIMAL_HIGHLIGHT_COLOR } from "@deltanets/render";
import { type SystemType, typeToString } from "@deltanets/core";
import { hasTypeAnnotations } from "@deltanets/core";
import { DarkThemeIcon, GitHubIcon, LightThemeIcon } from "./Icons.tsx";
import { METHODS } from "@deltanets/methods";
import { typeReductionMode } from "@deltanets/methods";
import { LANE_VIEW_PREFIX, PROOF_TREE_PREFIX } from "@deltanets/lang";
import type { Example } from "../routes/index.tsx";

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
import IconPlayerPlay from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/player-play.tsx";
import IconPlayerStop from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/player-stop.tsx";
import IconVolume from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/volume.tsx";
import IconVolumeOff from "https://deno.land/x/tabler_icons_tsx@0.0.7/tsx/volume-off.tsx";
import { isPlaying, playLaneView, sonify, stop } from "../lib/audio.ts";

export default function Toolbar({ examples }: { examples: Example[] }) {
  const deltaNetsData = METHODS[method.value].state.value?.data;
  const isDeltaFinalStep = method.value === "deltanets" &&
    deltaNetsData?.isFinalStep && !deltaNetsData.appliedFinalStep;

  const tcActive = typeCheckMode.value;
  const tcIdx = tcActive ? typeCheckStepIdx.value : -1;
  const tcLen = typeCheckSteps.value.length;

  const squareButtonClass =
    `border-1 rounded p-2 text-xl min-h-[44px] min-w-[44px] bg-inherit flex flex-row justify-center items-center disabled:opacity-[0.4] disabled:cursor-not-allowed hover:bg-[${
      theme.value === "light" ? "white" : "#2A2A2A"
    }] disabled:bg-transparent`;

  return (
    <nav
      aria-label="Toolbar"
      role="toolbar"
      class="flex flex-row bg-inherit gap-[8px]"
      style={{
        overflowX: "scroll",
        scrollbarWidth: "none",
      }}
    >
      <select
        aria-label="Load example"
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
        class={`border-1 rounded px-1 text-xl min-h-[44px] bg-inherit w-[120px] bg-transparent hover:bg-[${
          theme.value === "light" ? "white" : "#2A2A2A"
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
          aria-label="Select graph"
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
              {name.startsWith(LANE_VIEW_PREFIX)
                ? `[lanes] ${name.slice(LANE_VIEW_PREFIX.length)}`
                : name.startsWith(PROOF_TREE_PREFIX)
                ? `[proof] ${name.slice(PROOF_TREE_PREFIX.length)}`
                : name}
            </option>
          ))}
        </select>
      )}
      {isLaneView.value && currentLaneView.value && (
        <button
          type="button"
          title={isPlaying.value ? "Stop playback" : "Play music"}
          class={squareButtonClass}
          style={{
            borderColor: isPlaying.value
              ? (theme.value === "light" ? "#dc2626" : "#f87171")
              : (theme.value === "light" ? "#000D" : "#FFF6"),
          }}
          onClick={() => {
            if (isPlaying.value) {
              stop();
            } else {
              playLaneView(currentLaneView.value!);
            }
          }}
        >
          {isPlaying.value ? <IconPlayerStop /> : <IconPlayerPlay />}
        </button>
      )}
      {!isLaneView.value && (
        <button
          type="button"
          title={sonify.value ? "Mute reduction sounds" : "Sonify reductions"}
          class={squareButtonClass}
          style={{
            borderColor: sonify.value
              ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
              : (theme.value === "light" ? "#000D" : "#FFF6"),
          }}
          onClick={() => {
            sonify.value = !sonify.value;
            window.localStorage.setItem(
              STORAGE_KEYS.sonify,
              String(sonify.value),
            );
          }}
        >
          {sonify.value ? <IconVolume /> : <IconVolumeOff />}
        </button>
      )}
      <select
        aria-label="Reduction method"
        onChange={(e) => {
          const newMethod = (e?.target as HTMLSelectElement).value;
          window.localStorage.setItem(STORAGE_KEYS.method, newMethod);
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
      {method.value === "deltanets" && (
        <select
          aria-label="Level mode"
          value={relativeLevel.value ? "relative" : "absolute"}
          onChange={(e) => {
            const newRelativeLevel =
              (e?.target as HTMLSelectElement).value === "relative";
            relativeLevel.value = newRelativeLevel;
          }}
          class="border-1 rounded px-1 text-xl min-h-[44px] bg-inherit"
          style={{
            borderColor: theme.value === "light" ? "#000D" : "#FFF6",
            background: theme.value === "light" ? "white" : "#1A1A1A",
          }}
        >
          <option value="absolute">Absolute levels (default)</option>
          <option value="relative">Relative levels</option>
        </select>
      )}
      {typeResult.value && (
        <div
          title={tcActive
            ? (typeCheckSteps.value[tcIdx]?.judgment ?? "Type check mode")
            : typeReductionMode.value
            ? "Type reduction mode — click to switch to expression reduction"
            : (typeResult.value.ok
              ? `Type: ${
                typeToString(typeResult.value.type)
              } — click to switch to type reduction`
              : `Type error: ${typeResult.value.error}`)}
          class="border-1 rounded px-2 text-sm min-h-[44px] bg-inherit flex flex-row items-center whitespace-nowrap select-none"
          style={{
            borderColor: (tcActive || typeReductionMode.value)
              ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
              : (theme.value === "light" ? "#000D" : "#FFF6"),
            color: (tcActive || typeReductionMode.value)
              ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
              : (typeResult.value.ok
                ? (!ast.value || hasTypeAnnotations(ast.value)
                  ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
                  : (theme.value === "light" ? "#666" : "#888"))
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
      {parseErrors.value.length > 0 && (
        <div
          class="border-1 rounded px-2 text-sm min-h-[44px] bg-inherit flex flex-row items-center whitespace-nowrap select-none"
          title={parseErrors.value.join("\n")}
          style={{
            borderColor: theme.value === "light" ? "#dc2626" : "#f87171",
            color: theme.value === "light" ? "#dc2626" : "#f87171",
            maxWidth: "360px",
            overflow: "hidden",
            textOverflow: "ellipsis",
          }}
        >
          {`✘ ${parseErrors.value[0]}`}
        </div>
      )}
      <select
        aria-label="System type"
        // This select is just an indicator in the lambda calculus method
        disabled={method.value === "lambdacalc"}
        onChange={(e) => {
          const newSystemType = (e?.target as HTMLSelectElement).value;
          selectedSystemType.value = newSystemType as SystemType;
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
        }}
      >
        <option value="linear" disabled={systemType.value !== "linear"}>
          Linear (L)
        </option>
        <option
          value="affine"
          disabled={systemType.value === "relevant" ||
            systemType.value === "full"}
        >
          Affine (A)
        </option>
        <option
          value="relevant"
          disabled={systemType.value === "affine" ||
            systemType.value === "full"}
        >
          Relevant (I)
        </option>
        <option value="full">Full (K)</option>
      </select>
      <button
        type="button"
        title="Return to the beginning. Keyboard shortcut: Shift + left arrow key."
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={tcActive
          ? (() => {
            typeCheckStepIdx.value = 0;
          })
          : METHODS[method.value].state.value?.reset}
        disabled={tcActive
          ? tcIdx <= 0
          : !METHODS[method.value].state.value?.reset}
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
        onClick={tcActive
          ? (() => {
            typeCheckStepIdx.value = Math.max(0, typeCheckStepIdx.peek() - 1);
          })
          : METHODS[method.value].state.value?.back}
        disabled={tcActive
          ? tcIdx <= 0
          : !METHODS[method.value].state.value?.back}
      >
        <IconArrowLeft />
      </button>
      <div
        class="border-0 rounded text-xl min-h-[44px] bg-inherit flex flex-row justify-center items-end font-mono p-1"
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          color: tcActive
            ? (theme.value === "light" ? "#2563eb" : "#60a5fa")
            : "inherit",
        }}
      >
        {tcActive && tcLen > 0 ? `${tcIdx}/${tcLen - 1}` : (
          <>
            {METHODS[method.value].state.value?.idx ?? 0}/
            {METHODS[method.value].state.value?.stack?.length
              ? METHODS[method.value].state.value?.stack?.length! - 1
              : 0}
          </>
        )}
      </div>
      <button
        type="button"
        title="Step forward in history or, if no history available, apply a new reduction in normal order (leftmost-outermost) if possible. Keyboard shortcut: right arrow key."
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
          background: !tcActive && isDeltaFinalStep
            ? OPTIMAL_HIGHLIGHT_COLOR
            : "transparent",
        }}
        onClick={tcActive
          ? (() => {
            typeCheckStepIdx.value = Math.min(
              typeCheckSteps.peek().length - 1,
              typeCheckStepIdx.peek() + 1,
            );
          })
          : METHODS[method.value].state.value?.forward}
        disabled={tcActive
          ? tcIdx >= tcLen - 1
          : !METHODS[method.value].state.value?.forward}
      >
        {tcActive
          ? <IconArrowRight />
          : ((METHODS[method.value].state.value?.idx! <
              METHODS[method.value].state.value?.stack.length! - 1) ||
              METHODS[method.value].state.value?.forward === undefined
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
        onClick={tcActive
          ? (() => {
            typeCheckStepIdx.value = typeCheckSteps.peek().length - 1;
          })
          : METHODS[method.value].state.value?.last}
        disabled={tcActive
          ? tcIdx >= tcLen - 1
          : !METHODS[method.value].state.value?.last}
      >
        <IconArrowBarToRight />
      </button>
      <button
        type="button"
        title={`Toggle auto-centering (currently ${
          center.value ? "ON" : "OFF"
        })`}
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={() => {
          const newCenter = !center.peek();
          window.localStorage.setItem(
            STORAGE_KEYS.center,
            newCenter ? "true" : "false",
          );
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
          if (!svg) return;
          const serializer = new XMLSerializer();
          let source = serializer.serializeToString(svg);
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
        title={`Toggle visual debugging helpers (currently ${
          debug.value ? "ON" : "OFF"
        })`}
        class={squareButtonClass}
        style={{
          borderColor: theme.value === "light" ? "#000D" : "#FFF6",
        }}
        onClick={() => {
          const newDebug = !debug.peek();
          window.localStorage.setItem(
            STORAGE_KEYS.debug,
            newDebug ? "true" : "false",
          );
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
        aria-label="GitHub repository"
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
            window.localStorage.setItem(STORAGE_KEYS.theme, "dark");
          } else {
            theme.value = "light";
            window.localStorage.setItem(STORAGE_KEYS.theme, "light");
          }
        }}
      >
        {theme.value === "light" ? <DarkThemeIcon /> : <LightThemeIcon />}
      </button>
    </nav>
  );
}
