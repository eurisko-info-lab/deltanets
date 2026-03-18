// ═══════════════════════════════════════════════════════════════════
// INet View Language — Public API
// compile(source) → { themes, styles, wireStyles, palette, layout, errors }
// ═══════════════════════════════════════════════════════════════════

import { tokenize, LexError } from "./lexer.ts";
import { parse, ParseError } from "./parser.ts";
import { evaluate, EvalError } from "./evaluator.ts";
import type { ViewResult } from "./evaluator.ts";

export { tokenize, LexError } from "./lexer.ts";
export { parse, ParseError } from "./parser.ts";
export { evaluate, EvalError } from "./evaluator.ts";
export type {
  ViewResult, ThemeDef, ShapeDef, AgentStyleDef,
  WireStyleDef, PaletteDef, LayoutDef,
} from "./evaluator.ts";
export type * from "./types.ts";

export function compile(source: string): ViewResult {
  try {
    const tokens = tokenize(source);
    const ast = parse(tokens);
    return evaluate(ast);
  } catch (e) {
    if (e instanceof LexError || e instanceof ParseError || e instanceof EvalError) {
      return {
        uses: [], themes: new Map(), styles: new Map(), wireStyles: new Map(),
        palette: { colors: new Map() },
        layout: { spacing: 25, depth: 40, direction: "top-down", extra: {} },
        errors: [e.message],
      };
    }
    return {
      uses: [], themes: new Map(), styles: new Map(), wireStyles: new Map(),
      palette: { colors: new Map() },
      layout: { spacing: 25, depth: 40, direction: "top-down", extra: {} },
      errors: [`Internal error: ${(e as Error).message}`],
    };
  }
}
