// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Lexer
// Tokenizes .inet source files for interaction net system definitions.
// ═══════════════════════════════════════════════════════════════════

export const TT = {
  // Keywords
  SYSTEM: "SYSTEM",
  AGENT: "AGENT",
  RULE: "RULE",
  MODE: "MODE",
  GRAPH: "GRAPH",
  DEF: "DEF",
  LET: "LET",
  WIRE: "WIRE",
  RELINK: "RELINK",
  ERASE: "ERASE",
  TERM: "TERM",
  ANNIHILATE: "ANNIHILATE",
  COMMUTE: "COMMUTE",
  AUX_FAN: "AUX_FAN",
  LEFT: "LEFT",
  RIGHT: "RIGHT",
  // Operators
  INTERACT: "INTERACT",   // <>
  ARROW: "ARROW",         // ->
  WIRE_OP: "WIRE_OP",     // --
  EQ: "EQ",               // =
  LPAREN: "LPAREN",
  RPAREN: "RPAREN",
  LBRACE: "LBRACE",
  RBRACE: "RBRACE",
  COMMA: "COMMA",
  DOT: "DOT",
  BACKSLASH: "BACKSLASH",
  MINUS: "MINUS",
  DOTDOT: "DOTDOT",       // ..
  // Literals
  IDENT: "IDENT",
  STRING: "STRING",
  NUMBER: "NUMBER",
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
  system: TT.SYSTEM,
  agent: TT.AGENT,
  rule: TT.RULE,
  mode: TT.MODE,
  graph: TT.GRAPH,
  def: TT.DEF,
  let: TT.LET,
  wire: TT.WIRE,
  relink: TT.RELINK,
  erase: TT.ERASE,
  term: TT.TERM,
  annihilate: TT.ANNIHILATE,
  commute: TT.COMMUTE,
  "aux-fan": TT.AUX_FAN,
  left: TT.LEFT,
  right: TT.RIGHT,
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

    // Line comments: # to end of line
    if (source[i] === "#") {
      while (i < source.length && source[i] !== "\n") i++;
      continue;
    }

    const startCol = col;

    // Two-character operators
    if (i + 1 < source.length) {
      const two = source[i] + source[i + 1];
      if (two === "<>") {
        tokens.push({ type: TT.INTERACT, value: "<>", line, col: startCol });
        i += 2; col += 2; continue;
      }
      if (two === "->") {
        tokens.push({ type: TT.ARROW, value: "->", line, col: startCol });
        i += 2; col += 2; continue;
      }
      if (two === "--") {
        tokens.push({ type: TT.WIRE_OP, value: "--", line, col: startCol });
        i += 2; col += 2; continue;
      }
      if (two === "..") {
        tokens.push({ type: TT.DOTDOT, value: "..", line, col: startCol });
        i += 2; col += 2; continue;
      }
    }

    // Single-character operators
    const singles: Record<string, TokenKind> = {
      "=": TT.EQ,
      "(": TT.LPAREN,
      ")": TT.RPAREN,
      "{": TT.LBRACE,
      "}": TT.RBRACE,
      ",": TT.COMMA,
      ".": TT.DOT,
      "\\": TT.BACKSLASH,
      "-": TT.MINUS,
    };
    if (singles[source[i]]) {
      tokens.push({ type: singles[source[i]], value: source[i], line, col: startCol });
      i++; col++; continue;
    }

    // String literal
    if (source[i] === '"') {
      let val = "";
      i++; col++;
      while (i < source.length && source[i] !== '"') {
        if (source[i] === "\\") {
          i++; col++;
          const c = source[i] ?? "";
          if (c === "n") val += "\n";
          else if (c === "t") val += "\t";
          else if (c === "\\") val += "\\";
          else if (c === '"') val += '"';
          else val += c;
        } else {
          if (source[i] === "\n") { line++; col = 0; }
          val += source[i];
        }
        i++; col++;
      }
      if (i >= source.length) throw new LexError("Unterminated string", line, startCol);
      i++; col++; // closing quote
      tokens.push({ type: TT.STRING, value: val, line, col: startCol });
      continue;
    }

    // Number literal
    if (/[0-9]/.test(source[i])) {
      let num = "";
      while (i < source.length && /[0-9]/.test(source[i])) {
        num += source[i]; i++; col++;
      }
      tokens.push({ type: TT.NUMBER, value: num, line, col: startCol });
      continue;
    }

    // Identifier / keyword (allows hyphens mid-word: rep-in, aux-fan)
    if (/[a-zA-Z_]/.test(source[i])) {
      let ident = "";
      while (i < source.length && /[a-zA-Z0-9_]/.test(source[i])) {
        ident += source[i]; i++; col++;
        // Allow hyphen only if followed by a letter (not -- or ->)
        if (i < source.length && source[i] === "-" &&
            i + 1 < source.length && /[a-zA-Z]/.test(source[i + 1])) {
          ident += source[i]; i++; col++;
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
