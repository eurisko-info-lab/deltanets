import { batch, Signal, useSignal } from "@preact/signals";
import { useEffect } from "preact/hooks";
import { defaultStroke, Pos } from "@deltanets/render";
import { MAX_SCALE, MIN_SCALE } from "../lib/config.ts";

export function Graph(
  { theme, translate, scale, center }: {
    theme: "light" | "dark";
    translate: Signal<Pos>;
    scale: Signal<number>;
    center: Signal<boolean>;
  },
) {
  const state = useSignal<"none" | "pan">("none");
  const lastPos = useSignal<Pos>({ x: 0, y: 0 });

  // Set up event listeners
  useEffect(() => {
    const graph = document.getElementById("graph");
    if (!graph) return;

    // Press group
    const press = (e: MouseEvent | TouchEvent) => {
      state.value = "pan";
      if (e instanceof TouchEvent) {
        e.preventDefault();
        lastPos.value = { x: e.touches[0].clientX, y: e.touches[0].clientY };
      } else {
        lastPos.value = { x: e.clientX, y: e.clientY };
      }
    };
    graph.addEventListener("mousedown", press);
    graph.addEventListener("touchstart", press);

    // Release group
    const release = (_e: MouseEvent | TouchEvent) => {
      state.value = "none";
    };
    addEventListener("mouseup", release);
    addEventListener("touchend", release);

    // Move group
    const move = (e: MouseEvent | TouchEvent) => {
      if (state.value === "pan") {
        center.value = false;
        if (e instanceof MouseEvent) {
          translate.value = {
            x: translate.value.x + (e.clientX - lastPos.value.x) / scale.value,
            y: translate.value.y + (e.clientY - lastPos.value.y) / scale.value,
          };
        } else if (e instanceof TouchEvent) {
          e.preventDefault();
          translate.value = {
            x: translate.value.x +
              (e.touches[0].clientX - lastPos.value.x) / scale.value,
            y: translate.value.y +
              (e.touches[0].clientY - lastPos.value.y) / scale.value,
          };
        }
      }

      if (e instanceof MouseEvent) {
        lastPos.value = { x: e.clientX, y: e.clientY };
      } else if (e instanceof TouchEvent) {
        lastPos.value = { x: e.touches[0].clientX, y: e.touches[0].clientY };
      }
    };
    addEventListener("mousemove", move);
    addEventListener("touchmove", move, { passive: false });

    // Mouse wheel
    const wheel = (e: WheelEvent) => {
      const delta = -e.deltaY;
      let newScale = 1;
      if (delta > 0) {
        newScale = Math.min(scale.value * (1 + 0.001 * delta), MAX_SCALE);
      } else if (delta < 0) {
        newScale = Math.max(scale.value / (1 + 0.001 * -delta), MIN_SCALE);
      }

      const scaleDelta = 1 - newScale / scale.value;
      const rect = graph.getBoundingClientRect();
      const x = (e.clientX - rect.x) / newScale;
      const y = (e.clientY - rect.y) / newScale;

      batch(() => {
        center.value = false;
        scale.value = newScale;
        translate.value = {
          x: translate.value.x + x * scaleDelta,
          y: translate.value.y + y * scaleDelta,
        };
      });
    };
    graph.addEventListener("wheel", wheel);

    // Return function to remove event listeners
    return () => {
      graph.removeEventListener("mousedown", press);
      graph.removeEventListener("touchstart", press);
      removeEventListener("mouseup", release);
      removeEventListener("touchend", release);
      removeEventListener("mousemove", move);
      removeEventListener("touchmove", move);
      graph.removeEventListener("wheel", wheel);
    };
  }, []);

  return (
    <>
      <svg
        id="graph"
        role="img"
        aria-label="Interaction net graph visualization"
        class="rounded flex-1 w-full h-full bg-transparent border-1 select-none cursor-grab active:cursor-grabbing"
        style={{
          borderColor: theme === "light" ? "#000D" : "#FFF6",
          background: theme === "light" ? "white" : "#1A1A1A",
        }}
      >
        <defs>
          <marker
            id="arrowEnd"
            refX="6"
            refY="6"
            markerWidth="12"
            markerHeight="12"
            orient="auto"
          >
            <path d="M2,2 L10,6 L2,10" fill={defaultStroke(theme)} />
          </marker>
          <marker
            id="arrowStart"
            refX="6"
            refY="6"
            markerWidth="12"
            markerHeight="12"
            orient="auto"
          >
            <path d="M10,2 L2,6 L10,10" fill={defaultStroke(theme)} />
          </marker>
        </defs>
        <g id="zoom" transform={`scale(${scale.value})`}>
          <g
            id="pan"
            transform={`translate(${translate.value.x}, ${translate.value.y})`}
          >
            <g id="center">
              <pattern
                id="pattern-circles"
                x="0"
                y="0"
                width="25"
                height="25"
                patternUnits="userSpaceOnUse"
                patternContentUnits="userSpaceOnUse"
              >
                <circle
                  id="pattern-circle"
                  cx="8"
                  cy="8"
                  r="1"
                  fill={theme === "light" ? "#0004" : "#FFF3"}
                >
                </circle>
              </pattern>
              <rect
                id="background"
                x="-1000000"
                y="-1000000"
                width="2000000"
                height="2000000"
                fill="url(#pattern-circles)"
              />
              <g id="root" />
            </g>
          </g>
        </g>
      </svg>
    </>
  );
}
