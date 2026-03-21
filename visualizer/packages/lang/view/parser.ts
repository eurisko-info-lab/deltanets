// ═══════════════════════════════════════════════════════════════════
// INet View Language — Parser
// Recursive descent parser: tokens → AST.
//
// Grammar:
//   program      = statement*
//   statement    = useDecl | themeDecl | renderDecl | wireStyleDecl
//                | paletteDecl | layoutDecl
//   useDecl      = "use" STRING
//   themeDecl    = "theme" IDENT "{" propList "}"
//   renderDecl   = "render" IDENT "{" propList "}"
//   wireStyleDecl = "wire-style" [IDENT] "{" propList "}"
//   paletteDecl  = "palette" "{" paletteEntry* "}"
//   layoutDecl   = "layout" "{" propList "}"
//   propList     = (IDENT ":" value)*
//   paletteEntry = NUMBER ":" COLOR
//   value        = STRING | NUMBER | COLOR | funcCall | IDENT | array
//   funcCall     = IDENT "(" value ("," value)* ")"
//   array        = "[" value ("," value)* "]"
// ═══════════════════════════════════════════════════════════════════

import { TT } from "./lexer.ts";
import type { Token, TokenKind } from "./lexer.ts";
import type * as AST from "./types.ts";

export class ParseError extends Error {
  line: number;
  col: number;
  constructor(msg: string, line: number, col: number) {
    super(`Parse error at ${line}:${col}: ${msg}`);
    this.line = line;
    this.col = col;
  }
}

class Parser {
  pos = 0;
  constructor(private tokens: Token[]) {}

  peek(): Token { return this.tokens[this.pos]; }
  advance(): Token { return this.tokens[this.pos++]; }
  check(type: TokenKind): boolean { return this.peek().type === type; }

  eat(type: TokenKind): Token {
    const tok = this.peek();
    if (tok.type !== type) {
      throw new ParseError(
        `Expected ${type} but got '${tok.value || tok.type}'`,
        tok.line, tok.col,
      );
    }
    return this.advance();
  }

  // ─── Program ─────────────────────────────────────────────────────

  parseProgram(): AST.Program {
    const stmts: AST.Statement[] = [];
    while (!this.check(TT.EOF)) {
      stmts.push(this.parseStatement());
    }
    return stmts;
  }

  parseStatement(): AST.Statement {
    const tok = this.peek();
    switch (tok.type) {
      case TT.USE:        return this.parseUseDecl();
      case TT.THEME:      return this.parseThemeDecl();
      case TT.RENDER:     return this.parseRenderDecl();
      case TT.WIRE_STYLE: return this.parseWireStyleDecl();
      case TT.PALETTE:    return this.parsePaletteDecl();
      case TT.LAYOUT:     return this.parseLayoutDecl();
      default:
        throw new ParseError(`Unexpected '${tok.value || tok.type}'`, tok.line, tok.col);
    }
  }

  // ─── Use ─────────────────────────────────────────────────────────

  parseUseDecl(): AST.UseDecl {
    this.eat(TT.USE);
    const path = this.eat(TT.STRING).value;
    return { kind: "use", path };
  }

  // ─── Theme ───────────────────────────────────────────────────────

  parseThemeDecl(): AST.ThemeDecl {
    this.eat(TT.THEME);
    const name = this.eat(TT.IDENT).value;
    const properties = this.parsePropBlock();
    return { kind: "theme", name, properties };
  }

  // ─── Render ──────────────────────────────────────────────────────

  parseRenderDecl(): AST.RenderDecl {
    this.eat(TT.RENDER);
    const agent = this.eat(TT.IDENT).value;
    const properties = this.parsePropBlock();
    return { kind: "render", agent, properties };
  }

  // ─── Wire Style ──────────────────────────────────────────────────

  parseWireStyleDecl(): AST.WireStyleDecl {
    this.eat(TT.WIRE_STYLE);
    let name = "default";
    if (this.check(TT.IDENT)) {
      name = this.advance().value;
    }
    const properties = this.parsePropBlock();
    return { kind: "wire-style", name, properties };
  }

  // ─── Palette ─────────────────────────────────────────────────────

  parsePaletteDecl(): AST.PaletteDecl {
    this.eat(TT.PALETTE);
    this.eat(TT.LBRACE);
    const entries: AST.PaletteEntry[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const index = parseFloat(this.eat(TT.NUMBER).value);
      this.eat(TT.COLON);
      const color = this.eat(TT.COLOR).value;
      entries.push({ index, color });
    }
    this.eat(TT.RBRACE);
    return { kind: "palette", entries };
  }

  // ─── Layout ──────────────────────────────────────────────────────

  parseLayoutDecl(): AST.LayoutDecl {
    this.eat(TT.LAYOUT);
    const properties = this.parsePropBlock();
    return { kind: "layout", properties };
  }

  // ─── Property block { key: value, ... } ──────────────────────────

  parsePropBlock(): AST.PropEntry[] {
    this.eat(TT.LBRACE);
    const props: AST.PropEntry[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const key = this.eat(TT.IDENT).value;
      this.eat(TT.COLON);
      const value = this.parseValue();
      props.push({ key, value });
    }
    this.eat(TT.RBRACE);
    return props;
  }

  // ─── Values ──────────────────────────────────────────────────────

  parseValue(): AST.Value {
    const tok = this.peek();

    if (tok.type === TT.STRING) {
      this.advance();
      return { kind: "string", value: tok.value };
    }

    if (tok.type === TT.NUMBER) {
      this.advance();
      return { kind: "number", value: parseFloat(tok.value) };
    }

    if (tok.type === TT.COLOR) {
      this.advance();
      return { kind: "color", value: tok.value };
    }

    if (tok.type === TT.LBRACKET) {
      return this.parseArray();
    }

    if (tok.type === TT.IDENT) {
      // Look ahead for function call: ident(...)
      if (this.tokens[this.pos + 1]?.type === TT.LPAREN) {
        return this.parseFuncCall();
      }
      this.advance();
      return { kind: "ident", value: tok.value };
    }

    throw new ParseError(`Expected value, got '${tok.value || tok.type}'`, tok.line, tok.col);
  }

  parseArray(): AST.ArrayValue {
    this.eat(TT.LBRACKET);
    const items: AST.Value[] = [];
    if (!this.check(TT.RBRACKET)) {
      items.push(this.parseValue());
      while (this.check(TT.COMMA)) {
        this.advance();
        if (!this.check(TT.RBRACKET)) {
          items.push(this.parseValue());
        }
      }
    }
    this.eat(TT.RBRACKET);
    return { kind: "array", items };
  }

  parseFuncCall(): AST.FuncCallValue {
    const name = this.eat(TT.IDENT).value;
    this.eat(TT.LPAREN);
    const args: AST.Value[] = [];
    if (!this.check(TT.RPAREN)) {
      args.push(this.parseValue());
      while (this.check(TT.COMMA)) {
        this.advance();
        args.push(this.parseValue());
      }
    }
    this.eat(TT.RPAREN);
    return { kind: "call", name, args };
  }
}

export function parse(tokens: Token[]): AST.Program {
  return new Parser(tokens).parseProgram();
}
