// ═══════════════════════════════════════════════════════════════════
// INet View Language — Evaluator
// Walks the AST and produces: theme configs, agent styles, wire
// styles, level palettes, and layout parameters that can be consumed
// by the rendering pipeline (render.ts, methods/).
// ═══════════════════════════════════════════════════════════════════

import type * as AST from "./types.ts";

// ─── Output types ──────────────────────────────────────────────────

export type ThemeDef = {
  name: string;
  background: string;
  text: string;
  wire: string;
  optimal: string;
  suboptimal: string;
  extra: Record<string, string | number>;
};

export type ShapeDef =
  | { kind: "fan"; direction: "up" | "down" }
  | { kind: "replicator"; direction: "up" | "down" }
  | { kind: "eraser" }
  | { kind: "circle" }
  | { kind: "rect" }
  | { kind: "custom"; name: string };

export type AgentStyleDef = {
  agent: string;
  shape: ShapeDef;
  width?: number;
  height?: number;
  radius?: number;
  fill: string;             // color or special keyword like "level-color"
  stroke?: string;
  label?: string;           // "center", "above", "below"
  zIndex: number;
  showDeltas?: boolean;
  extra: Record<string, string | number>;
};

export type WireStyleDef = {
  name: string;
  width: number;
  curve: string;            // "bezier", "straight", "step"
  dash?: number[];
  extra: Record<string, string | number>;
};

export type PaletteDef = {
  colors: Map<number, string>;
};

export type LayoutDef = {
  spacing: number;
  depth: number;
  direction: string;
  extra: Record<string, string | number>;
};

export type ViewResult = {
  uses: string[];
  themes: Map<string, ThemeDef>;
  styles: Map<string, AgentStyleDef>;
  wireStyles: Map<string, WireStyleDef>;
  palette: PaletteDef;
  layout: LayoutDef;
  errors: string[];
};

// ─── Errors ────────────────────────────────────────────────────────

export class EvalError extends Error {
  constructor(msg: string) {
    super(`View eval error: ${msg}`);
  }
}

// ─── Main evaluator ────────────────────────────────────────────────

export function evaluate(program: AST.Program): ViewResult {
  const uses: string[] = [];
  const themes = new Map<string, ThemeDef>();
  const styles = new Map<string, AgentStyleDef>();
  const wireStyles = new Map<string, WireStyleDef>();
  let palette: PaletteDef = { colors: new Map() };
  let layout: LayoutDef = { spacing: 25, depth: 40, direction: "top-down", extra: {} };
  const errors: string[] = [];

  for (const stmt of program) {
    try {
      switch (stmt.kind) {
        case "use":
          uses.push(stmt.path);
          break;
        case "theme":
          themes.set(stmt.name, evalTheme(stmt));
          break;
        case "render":
          styles.set(stmt.agent, evalRender(stmt));
          break;
        case "wire-style":
          wireStyles.set(stmt.name, evalWireStyle(stmt));
          break;
        case "palette":
          palette = evalPalette(stmt);
          break;
        case "layout":
          layout = evalLayout(stmt);
          break;
      }
    } catch (e) {
      errors.push((e as Error).message);
    }
  }

  return { uses, themes, styles, wireStyles, palette, layout, errors };
}

// ─── Theme evaluation ──────────────────────────────────────────────

function evalTheme(decl: AST.ThemeDecl): ThemeDef {
  const props = propsToRecord(decl.properties);
  return {
    name: decl.name,
    background: getString(props, "background", "#1e1e1e"),
    text: getString(props, "text", "#ffffff"),
    wire: getString(props, "wire", "#aaaaaa"),
    optimal: getString(props, "optimal", "#4caf50"),
    suboptimal: getString(props, "suboptimal", "#ff9800"),
    extra: getExtraStrings(props, ["background", "text", "wire", "optimal", "suboptimal"]),
  };
}

// ─── Render (agent style) evaluation ───────────────────────────────

function evalRender(decl: AST.RenderDecl): AgentStyleDef {
  const props = propsToRecord(decl.properties);
  return {
    agent: decl.agent,
    shape: parseShape(props.shape),
    width: getNumber(props, "width"),
    height: getNumber(props, "height"),
    radius: getNumber(props, "radius"),
    fill: getString(props, "fill", "#888888"),
    stroke: getOptString(props, "stroke"),
    label: getOptString(props, "label"),
    zIndex: getNumber(props, "z") ?? getNumber(props, "z-index") ?? 0,
    showDeltas: getOptString(props, "show-deltas") === "true",
    extra: getExtraStrings(props, [
      "shape", "width", "height", "radius", "fill", "stroke",
      "label", "z", "z-index", "show-deltas",
    ]),
  };
}

function parseShape(value: AST.Value | undefined): ShapeDef {
  if (!value) return { kind: "circle" };

  if (value.kind === "ident") {
    const name = value.value;
    if (name === "eraser") return { kind: "eraser" };
    if (name === "circle") return { kind: "circle" };
    if (name === "rect")   return { kind: "rect" };
    return { kind: "custom", name };
  }

  if (value.kind === "call") {
    if (value.name === "fan") {
      const dir = value.args[0]?.kind === "ident" ? value.args[0].value : "down";
      return { kind: "fan", direction: dir as "up" | "down" };
    }
    if (value.name === "replicator") {
      const dir = value.args[0]?.kind === "ident" ? value.args[0].value : "down";
      return { kind: "replicator", direction: dir as "up" | "down" };
    }
    return { kind: "custom", name: value.name };
  }

  return { kind: "circle" };
}

// ─── Wire style evaluation ─────────────────────────────────────────

function evalWireStyle(decl: AST.WireStyleDecl): WireStyleDef {
  const props = propsToRecord(decl.properties);
  const dashVal = props.dash;
  let dash: number[] | undefined;
  if (dashVal?.kind === "array") {
    dash = dashVal.items
      .filter(v => v.kind === "number")
      .map(v => (v as AST.NumberValue).value);
  }
  return {
    name: decl.name,
    width: getNumber(props, "width") ?? 1.5,
    curve: getString(props, "curve", "bezier"),
    dash,
    extra: getExtraStrings(props, ["width", "curve", "dash"]),
  };
}

// ─── Palette evaluation ────────────────────────────────────────────

function evalPalette(decl: AST.PaletteDecl): PaletteDef {
  const colors = new Map<number, string>();
  for (const entry of decl.entries) {
    colors.set(entry.index, entry.color);
  }
  return { colors };
}

// ─── Layout evaluation ─────────────────────────────────────────────

function evalLayout(decl: AST.LayoutDecl): LayoutDef {
  const props = propsToRecord(decl.properties);
  return {
    spacing: getNumber(props, "spacing") ?? 25,
    depth: getNumber(props, "depth") ?? 40,
    direction: getString(props, "direction", "top-down"),
    extra: getExtraStrings(props, ["spacing", "depth", "direction"]),
  };
}

// ─── Helpers ───────────────────────────────────────────────────────

function propsToRecord(entries: AST.PropEntry[]): Record<string, AST.Value> {
  const rec: Record<string, AST.Value> = {};
  for (const e of entries) rec[e.key] = e.value;
  return rec;
}

function getString(props: Record<string, AST.Value>, key: string, fallback: string): string {
  const v = props[key];
  if (!v) return fallback;
  if (v.kind === "string" || v.kind === "ident" || v.kind === "color") return v.value;
  return fallback;
}

function getOptString(props: Record<string, AST.Value>, key: string): string | undefined {
  const v = props[key];
  if (!v) return undefined;
  if (v.kind === "string" || v.kind === "ident" || v.kind === "color") return v.value;
  return undefined;
}

function getNumber(props: Record<string, AST.Value>, key: string): number | undefined {
  const v = props[key];
  if (!v) return undefined;
  if (v.kind === "number") return v.value;
  return undefined;
}

function getExtraStrings(
  props: Record<string, AST.Value>,
  knownKeys: string[],
): Record<string, string | number> {
  const extra: Record<string, string | number> = {};
  for (const [k, v] of Object.entries(props)) {
    if (knownKeys.includes(k)) continue;
    if (v.kind === "string" || v.kind === "ident" || v.kind === "color") {
      extra[k] = v.value;
    } else if (v.kind === "number") {
      extra[k] = v.value;
    }
  }
  return extra;
}
