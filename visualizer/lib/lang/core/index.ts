// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Public API
// compile(source) → { systems, graphs, definitions, errors }
// ═══════════════════════════════════════════════════════════════════

import { tokenize, LexError } from "./lexer.ts";
import { parse, ParseError } from "./parser.ts";
import { evaluate, EvalError } from "./evaluator.ts";
import type { CoreResult } from "./evaluator.ts";

export { tokenize, LexError } from "./lexer.ts";
export { parse, ParseError } from "./parser.ts";
export { evaluate, EvalError } from "./evaluator.ts";
export type { CoreResult, SystemDef, AgentDef, RuleDef, ModeDef, GraphDef } from "./evaluator.ts";
export type * from "./types.ts";

export function compile(source: string): CoreResult {
  try {
    const tokens = tokenize(source);
    const ast = parse(tokens);
    return evaluate(ast);
  } catch (e) {
    if (e instanceof LexError || e instanceof ParseError || e instanceof EvalError) {
      return { systems: new Map(), graphs: new Map(), definitions: new Map(), errors: [e.message] };
    }
    return { systems: new Map(), graphs: new Map(), definitions: new Map(), errors: [`Internal error: ${(e as Error).message}`] };
  }
}
