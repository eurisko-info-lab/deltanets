// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Public API
// compile(source) → { systems, graphs, definitions, errors }
// ═══════════════════════════════════════════════════════════════════

import { LexError, tokenize } from "./lexer.ts";
import { parse, ParseError } from "./parser.ts";
import { EvalError, evaluate } from "./evaluator.ts";
import type { CoreResult } from "./evaluator.ts";

export { LexError, tokenize } from "./lexer.ts";
export { parse, ParseError } from "./parser.ts";
export { EvalError, evaluate } from "./evaluator.ts";
export type {
  AgentDef,
  CoreResult,
  GraphDef,
  ModeDef,
  RuleDef,
  SystemDef,
} from "./evaluator.ts";
export type * from "./types.ts";

export function compile(source: string): CoreResult {
  try {
    const tokens = tokenize(source);
    const ast = parse(tokens);
    return evaluate(ast);
  } catch (e) {
    if (
      e instanceof LexError || e instanceof ParseError || e instanceof EvalError
    ) {
      return {
        systems: new Map(),
        graphs: new Map(),
        definitions: new Map(),
        errors: [e.message],
      };
    }
    return {
      systems: new Map(),
      graphs: new Map(),
      definitions: new Map(),
      errors: [`Internal error: ${(e as Error).message}`],
    };
  }
}
