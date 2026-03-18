// ═══════════════════════════════════════════════════════════════════
// INet View Language — AST Types
// Describes visual presentation: themes, agent styles, palettes, layout.
// ═══════════════════════════════════════════════════════════════════

export type Program = Statement[];

export type Statement =
  | UseDecl
  | ThemeDecl
  | RenderDecl
  | WireStyleDecl
  | PaletteDecl
  | LayoutDecl;

// use "system-name.inet"
export type UseDecl = {
  kind: "use";
  path: string;
};

// theme name { prop: value, ... }
export type ThemeDecl = {
  kind: "theme";
  name: string;
  properties: PropEntry[];
};

// render agent-name { prop: value, ... }
export type RenderDecl = {
  kind: "render";
  agent: string;
  properties: PropEntry[];
};

// wire-style [name] { prop: value, ... }
export type WireStyleDecl = {
  kind: "wire-style";
  name: string;
  properties: PropEntry[];
};

// palette { index: color, ... }
export type PaletteDecl = {
  kind: "palette";
  entries: PaletteEntry[];
};

// layout { prop: value, ... }
export type LayoutDecl = {
  kind: "layout";
  properties: PropEntry[];
};

// Property entry: key: value
export type PropEntry = {
  key: string;
  value: Value;
};

// Palette entry: number: color
export type PaletteEntry = {
  index: number;
  color: string;
};

// Values
export type Value =
  | StringValue
  | NumberValue
  | ColorValue
  | IdentValue
  | ArrayValue
  | FuncCallValue;

export type StringValue = { kind: "string"; value: string };
export type NumberValue = { kind: "number"; value: number };
export type ColorValue = { kind: "color"; value: string };
export type IdentValue = { kind: "ident"; value: string };
export type ArrayValue = { kind: "array"; items: Value[] };
export type FuncCallValue = { kind: "call"; name: string; args: Value[] };
