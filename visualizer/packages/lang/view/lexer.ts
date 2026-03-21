// ═══════════════════════════════════════════════════════════════════
// INet View Language — Lexer
// Tokenizes .iview source files for visual configuration.
// ═══════════════════════════════════════════════════════════════════

export const TT = {
  // Keywords
  USE: "USE",
  THEME: "THEME",
  RENDER: "RENDER",
  WIRE_STYLE: "WIRE_STYLE",
  PALETTE: "PALETTE",
  LAYOUT: "LAYOUT",
  // Operators
  COLON: "COLON",
  LBRACE: "LBRACE",
  RBRACE: "RBRACE",
  LBRACKET: "LBRACKET",
  RBRACKET: "RBRACKET",
  LPAREN: "LPAREN",
  RPAREN: "RPAREN",
  COMMA: "COMMA",
  // Literals
  IDENT: "IDENT",
  STRING: "STRING",
  NUMBER: "NUMBER",
  COLOR: "COLOR",
  // End
  EOF: "EOF",
} as const;

export type TokenKind = typeof TT[keyof typeof TT];

export type Token = {
  type: TokenKind;
  value: string;
  line: number;
  col: number;
};

const KEYWORDS: Record<string, TokenKind> = {
  use: TT.USE,
  theme: TT.THEME,
  render: TT.RENDER,
  "wire-style": TT.WIRE_STYLE,
  palette: TT.PALETTE,
  layout: TT.LAYOUT,
};

export class LexError extends Error {
  line: number;
  col: number;
  constructor(msg: string, line: number, col: number) {
    super(`Lex error at ${line}:${col}: ${msg}`);
    this.line = line;
    this.col = col;
  }
}

export function tokenize(source: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;
  let line = 1;
  let col = 1;

  while (i < source.length) {
    // Newline
    if (source[i] === "\n") {
      line++;
      col = 1;
      i++;
      continue;
    }

    // Whitespace
    if (/\s/.test(source[i])) {
      i++;
      col++;
      continue;
    }

    // # can be a color literal (#rrggbb) or a line comment
    if (source[i] === "#") {
      // Color literal: # followed by hex digit
      if (i + 1 < source.length && /[0-9a-fA-F]/.test(source[i + 1])) {
        const startCol2 = col;
        let hex = "#";
        i++;
        col++;
        while (i < source.length && /[0-9a-fA-F]/.test(source[i])) {
          hex += source[i];
          i++;
          col++;
        }
        tokens.push({ type: TT.COLOR, value: hex, line, col: startCol2 });
        continue;
      }
      // Line comment: # to end of line
      while (i < source.length && source[i] !== "\n") i++;
      continue;
    }

    const startCol = col;

    // Single-character operators
    const singles: Record<string, TokenKind> = {
      ":": TT.COLON,
      "{": TT.LBRACE,
      "}": TT.RBRACE,
      "[": TT.LBRACKET,
      "]": TT.RBRACKET,
      "(": TT.LPAREN,
      ")": TT.RPAREN,
      ",": TT.COMMA,
    };
    if (singles[source[i]]) {
      tokens.push({
        type: singles[source[i]],
        value: source[i],
        line,
        col: startCol,
      });
      i++;
      col++;
      continue;
    }

    // String literal
    if (source[i] === '"') {
      let val = "";
      i++;
      col++;
      while (i < source.length && source[i] !== '"') {
        if (source[i] === "\\") {
          i++;
          col++;
          const c = source[i] ?? "";
          if (c === "n") val += "\n";
          else if (c === "t") val += "\t";
          else if (c === "\\") val += "\\";
          else if (c === '"') val += '"';
          else val += c;
        } else {
          if (source[i] === "\n") {
            line++;
            col = 0;
          }
          val += source[i];
        }
        i++;
        col++;
      }
      if (i >= source.length) {
        throw new LexError("Unterminated string", line, startCol);
      }
      i++;
      col++;
      tokens.push({ type: TT.STRING, value: val, line, col: startCol });
      continue;
    }

    // Number literal (supports negative and decimal)
    if (
      /[0-9]/.test(source[i]) ||
      (source[i] === "-" && i + 1 < source.length &&
        /[0-9]/.test(source[i + 1]))
    ) {
      let num = "";
      if (source[i] === "-") {
        num += "-";
        i++;
        col++;
      }
      while (i < source.length && /[0-9]/.test(source[i])) {
        num += source[i];
        i++;
        col++;
      }
      if (i < source.length && source[i] === ".") {
        num += ".";
        i++;
        col++;
        while (i < source.length && /[0-9]/.test(source[i])) {
          num += source[i];
          i++;
          col++;
        }
      }
      tokens.push({ type: TT.NUMBER, value: num, line, col: startCol });
      continue;
    }

    // Identifier / keyword (allows hyphens mid-word: wire-style, level-color)
    if (/[a-zA-Z_]/.test(source[i])) {
      let ident = "";
      while (i < source.length && /[a-zA-Z0-9_]/.test(source[i])) {
        ident += source[i];
        i++;
        col++;
        // Allow hyphen if followed by a letter
        if (
          i < source.length && source[i] === "-" &&
          i + 1 < source.length && /[a-zA-Z]/.test(source[i + 1])
        ) {
          ident += source[i];
          i++;
          col++;
        }
      }
      const kw = KEYWORDS[ident];
      tokens.push({ type: kw ?? TT.IDENT, value: ident, line, col: startCol });
      continue;
    }

    throw new LexError(`Unexpected character '${source[i]}'`, line, col);
  }

  tokens.push({ type: TT.EOF, value: "", line, col });
  return tokens;
}
