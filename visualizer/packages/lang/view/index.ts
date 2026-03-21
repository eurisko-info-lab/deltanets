// ═══════════════════════════════════════════════════════════════════
// INet View Language — Public API
// compile(source) → { themes, styles, wireStyles, palette, layout, errors }
// ═══════════════════════════════════════════════════════════════════

import { LexError, tokenize } from "./lexer.ts";
import { parse, ParseError } from "./parser.ts";
import { EvalError, evaluate } from "./evaluator.ts";
import type { ViewResult } from "./evaluator.ts";

export { LexError, tokenize } from "./lexer.ts";
export { parse, ParseError } from "./parser.ts";
export { EvalError, evaluate } from "./evaluator.ts";
export type {
  AgentLevel,
  AgentRole,
  AgentStyleDef,
  LayoutDef,
  PaletteDef,
  ShapeDef,
  ThemeDef,
  ViewResult,
  WireStyleDef,
} from "./evaluator.ts";
export type * from "./types.ts";

export function compile(source: string): ViewResult {
  try {
    const tokens = tokenize(source);
    const ast = parse(tokens);
    return evaluate(ast);
  } catch (e) {
    if (
      e instanceof LexError || e instanceof ParseError || e instanceof EvalError
    ) {
      return {
        uses: [],
        themes: new Map(),
        styles: new Map(),
        wireStyles: new Map(),
        palette: { colors: new Map() },
        layout: { spacing: 25, depth: 40, direction: "top-down", extra: {} },
        errors: [e.message],
      };
    }
    return {
      uses: [],
      themes: new Map(),
      styles: new Map(),
      wireStyles: new Map(),
      palette: { colors: new Map() },
      layout: { spacing: 25, depth: 40, direction: "top-down", extra: {} },
      errors: [`Internal error: ${(e as Error).message}`],
    };
  }
}
