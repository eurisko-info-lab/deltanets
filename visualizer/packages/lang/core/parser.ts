// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Parser
// Recursive descent parser: tokens → AST.
//
// Grammar:
//   program      = statement*
//   statement    = systemDecl | extendDecl | composeDecl | agentDecl
//                | ruleDecl | modeDecl | graphDecl | defDecl
//   systemDecl   = "system" STRING "{" (agentDecl | ruleDecl | modeDecl)* "}"
//   extendDecl   = "system" STRING "extend" STRING "{" (agentDecl | ruleDecl | modeDecl)* "}"
//   composeDecl  = "system" STRING "=" "compose" STRING ("+" STRING)* "{" (agentDecl | ruleDecl | modeDecl)* "}"
//   agentDecl    = "agent" IDENT "(" portList ")"
//   portList     = portDef ("," portDef)*
//   portDef      = ".." IDENT | IDENT
//   ruleDecl     = "rule" IDENT "<>" IDENT "->" ruleAction
//   ruleAction   = "annihilate" | "erase" | "commute" | "aux-fan"
//                | "{" ruleStmt* "}"
//   ruleStmt     = letStmt | wireStmt | relinkStmt | eraseStmt
//   modeDecl     = "mode" IDENT "=" "{" ("-" IDENT ","?)* "}"
//   graphDecl    = "graph" IDENT "=" "term" lamExpr
//                | "graph" IDENT "{" (letStmt | wireStmt)* "}"
//   defDecl      = "def" IDENT "=" lamExpr
//   letStmt      = "let" IDENT "=" IDENT [STRING]
//   wireStmt     = "wire" portRef "--" portRef
//   relinkStmt   = "relink" portRef portRef
//   eraseStmt    = "erase" portRef
//   portRef      = IDENT "." IDENT | IDENT "." NUMBER
//                | "left" "." IDENT | "right" "." IDENT
//   lamExpr      = "\" IDENT (":" typeExpr)? "." lamExpr | appExpr
//   appExpr      = atomExpr+
//   atomExpr     = IDENT | "(" lamExpr ")"
//   typeExpr     = typeAtom ("->" typeExpr)?
//   typeAtom     = "?" | IDENT | "(" typeExpr ")"
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

  eatIdent(): string {
    return this.eat(TT.IDENT).value;
  }

  // Accept IDENT, or LEFT/RIGHT as identifier (used in port refs)
  eatName(): string {
    const tok = this.peek();
    if (tok.type === TT.IDENT || tok.type === TT.LEFT || tok.type === TT.RIGHT) {
      return this.advance().value;
    }
    throw new ParseError(`Expected name, got '${tok.value}'`, tok.line, tok.col);
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
      case TT.SYSTEM: return this.parseSystemOrExtendOrCompose();
      case TT.AGENT:  return this.parseAgentDecl();
      case TT.RULE:   return this.parseRuleDecl();
      case TT.MODE:   return this.parseModeDecl();
      case TT.GRAPH:  return this.parseGraphDecl();
      case TT.DEF:    return this.parseDefDecl();
      default:
        throw new ParseError(`Unexpected '${tok.value || tok.type}'`, tok.line, tok.col);
    }
  }

  // ─── System / Extend / Compose ───────────────────────────────────

  parseSystemOrExtendOrCompose(): AST.SystemDecl | AST.ExtendDecl | AST.ComposeDecl {
    this.eat(TT.SYSTEM);
    const name = this.eat(TT.STRING).value;

    // system "B" extend "A" { ... }
    if (this.check(TT.EXTEND)) {
      this.advance();
      const base = this.eat(TT.STRING).value;
      const body = this.parseSystemBody();
      return { kind: "extend", name, base, body };
    }

    // system "C" = compose "A" + "B" + ... { ... }
    if (this.check(TT.EQ)) {
      this.advance();
      this.eat(TT.COMPOSE);
      const components: string[] = [this.eat(TT.STRING).value];
      while (this.check(TT.PLUS)) {
        this.advance();
        components.push(this.eat(TT.STRING).value);
      }
      const body = this.parseSystemBody();
      return { kind: "compose", name, components, body };
    }

    // system "X" { ... }
    const body = this.parseSystemBody();
    return { kind: "system", name, body };
  }

  parseSystemBody(): (AST.AgentDecl | AST.RuleDecl | AST.ModeDecl)[] {
    this.eat(TT.LBRACE);
    const body: (AST.AgentDecl | AST.RuleDecl | AST.ModeDecl)[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const tok = this.peek();
      if (tok.type === TT.AGENT) body.push(this.parseAgentDecl());
      else if (tok.type === TT.RULE) body.push(this.parseRuleDecl());
      else if (tok.type === TT.MODE) body.push(this.parseModeDecl());
      else throw new ParseError(`Expected agent/rule/mode, got '${tok.value}'`, tok.line, tok.col);
    }
    this.eat(TT.RBRACE);
    return body;
  }

  // ─── Agent ───────────────────────────────────────────────────────

  parseAgentDecl(): AST.AgentDecl {
    this.eat(TT.AGENT);
    const name = this.eatIdent();
    this.eat(TT.LPAREN);
    const ports: AST.PortDef[] = [];
    if (!this.check(TT.RPAREN)) {
      ports.push(this.parsePortDef());
      while (this.check(TT.COMMA)) {
        this.advance();
        ports.push(this.parsePortDef());
      }
    }
    this.eat(TT.RPAREN);
    return { kind: "agent", name, ports };
  }

  parsePortDef(): AST.PortDef {
    if (this.check(TT.DOTDOT)) {
      this.advance();
      return { name: this.eatIdent(), variadic: true };
    }
    return { name: this.eatIdent(), variadic: false };
  }

  // ─── Rule ────────────────────────────────────────────────────────

  parseRuleDecl(): AST.RuleDecl {
    this.eat(TT.RULE);
    const agentA = this.eatIdent();
    this.eat(TT.INTERACT);
    const agentB = this.eatIdent();
    this.eat(TT.ARROW);
    const action = this.parseRuleAction();
    return { kind: "rule", agentA, agentB, action };
  }

  parseRuleAction(): AST.RuleAction {
    const tok = this.peek();
    if (tok.type === TT.ANNIHILATE) { this.advance(); return { kind: "builtin", name: "annihilate" }; }
    if (tok.type === TT.ERASE)     { this.advance(); return { kind: "builtin", name: "erase" }; }
    if (tok.type === TT.COMMUTE)   { this.advance(); return { kind: "builtin", name: "commute" }; }
    if (tok.type === TT.AUX_FAN)   { this.advance(); return { kind: "builtin", name: "aux-fan" }; }
    if (tok.type === TT.LBRACE)    { return { kind: "custom", body: this.parseCustomRuleBody() }; }
    throw new ParseError(
      `Expected rule action (annihilate/erase/commute/aux-fan/{...}), got '${tok.value}'`,
      tok.line, tok.col,
    );
  }

  parseCustomRuleBody(): AST.RuleStmt[] {
    this.eat(TT.LBRACE);
    const stmts: AST.RuleStmt[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      stmts.push(this.parseRuleStmt());
    }
    this.eat(TT.RBRACE);
    return stmts;
  }

  parseRuleStmt(): AST.RuleStmt {
    const tok = this.peek();
    if (tok.type === TT.LET)    return this.parseLetStmt();
    if (tok.type === TT.WIRE)   return this.parseWireStmt();
    if (tok.type === TT.RELINK) return this.parseRelinkStmt();
    if (tok.type === TT.ERASE)  return this.parseEraseStmt();
    throw new ParseError(`Expected let/wire/relink/erase, got '${tok.value}'`, tok.line, tok.col);
  }

  // ─── Graph body statements ───────────────────────────────────────

  parseLetStmt(): AST.LetStmt {
    this.eat(TT.LET);
    const varName = this.eatIdent();
    this.eat(TT.EQ);
    const agentType = this.eatIdent();
    let label: string | undefined;
    if (this.check(TT.STRING)) {
      label = this.advance().value;
    }
    return { kind: "let", varName, agentType, label };
  }

  parseWireStmt(): AST.WireStmt {
    this.eat(TT.WIRE);
    const portA = this.parsePortRef();
    this.eat(TT.WIRE_OP);
    const portB = this.parsePortRef();
    return { kind: "wire", portA, portB };
  }

  parseRelinkStmt(): AST.RelinkStmt {
    this.eat(TT.RELINK);
    const portA = this.parsePortRef();
    const portB = this.parsePortRef();
    return { kind: "relink", portA, portB };
  }

  parseEraseStmt(): AST.EraseStmt {
    this.eat(TT.ERASE);
    const port = this.parsePortRef();
    return { kind: "erase-stmt", port };
  }

  parsePortRef(): AST.PortRef {
    const node = this.eatName(); // allows "left" and "right"
    this.eat(TT.DOT);
    // Port can be IDENT or NUMBER
    const tok = this.peek();
    let port: string;
    if (tok.type === TT.NUMBER) {
      port = this.advance().value;
    } else {
      port = this.eatName();
    }
    return { node, port };
  }

  // ─── Mode ────────────────────────────────────────────────────────

  parseModeDecl(): AST.ModeDecl {
    this.eat(TT.MODE);
    const name = this.eatIdent();
    this.eat(TT.EQ);
    this.eat(TT.LBRACE);
    const exclude: string[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      this.eat(TT.MINUS);
      exclude.push(this.eatIdent());
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RBRACE);
    return { kind: "mode", name, exclude };
  }

  // ─── Graph ───────────────────────────────────────────────────────

  parseGraphDecl(): AST.GraphDecl {
    this.eat(TT.GRAPH);
    const name = this.eatIdent();

    // Explicit graph: graph name { ... }
    if (this.check(TT.LBRACE)) {
      this.eat(TT.LBRACE);
      const body: (AST.LetStmt | AST.WireStmt)[] = [];
      while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
        const tok = this.peek();
        if (tok.type === TT.LET) body.push(this.parseLetStmt());
        else if (tok.type === TT.WIRE) body.push(this.parseWireStmt());
        else throw new ParseError(`Expected let/wire, got '${tok.value}'`, tok.line, tok.col);
      }
      this.eat(TT.RBRACE);
      return { kind: "graph-explicit", name, body };
    }

    // Term graph: graph name = term <expr>
    this.eat(TT.EQ);
    this.eat(TT.TERM);
    const term = this.parseLamExpr();
    return { kind: "graph", name, term };
  }

  // ─── Def ─────────────────────────────────────────────────────────

  parseDefDecl(): AST.DefDecl {
    this.eat(TT.DEF);
    const name = this.eatIdent();
    this.eat(TT.EQ);
    const expr = this.parseLamExpr();
    return { kind: "def", name, expr };
  }

  // ─── Lambda expressions ──────────────────────────────────────────

  parseLamExpr(): AST.LamExpr {
    if (this.check(TT.BACKSLASH)) {
      this.advance();
      const param = this.eatIdent();
      let typeAnnotation: AST.TypeExpr | undefined;
      if (this.check(TT.COLON)) {
        this.advance();
        typeAnnotation = this.parseTypeExpr();
      }
      this.eat(TT.DOT);
      const body = this.parseLamExpr();
      return { kind: "lam", param, typeAnnotation, body };
    }
    return this.parseAppExpr();
  }

  parseAppExpr(): AST.LamExpr {
    let left = this.parseAtomExpr();
    while (this.isAtomStart()) {
      const right = this.parseAtomExpr();
      left = { kind: "app", func: left, arg: right };
    }
    return left;
  }

  isAtomStart(): boolean {
    const t = this.peek().type;
    return t === TT.IDENT || t === TT.LPAREN;
  }

  parseAtomExpr(): AST.LamExpr {
    if (this.check(TT.LPAREN)) {
      this.advance();
      const expr = this.parseLamExpr();
      this.eat(TT.RPAREN);
      return expr;
    }
    const name = this.eatIdent();
    return { kind: "var", name };
  }

  // ─── Type expressions ────────────────────────────────────────────

  parseTypeExpr(): AST.TypeExpr {
    const left = this.parseTypeAtom();
    if (this.check(TT.ARROW)) {
      this.advance();
      const right = this.parseTypeExpr();
      return { kind: "type-arrow", from: left, to: right };
    }
    return left;
  }

  parseTypeAtom(): AST.TypeExpr {
    if (this.check(TT.QUESTION)) {
      this.advance();
      return { kind: "type-hole" };
    }
    if (this.check(TT.LPAREN)) {
      this.advance();
      const ty = this.parseTypeExpr();
      this.eat(TT.RPAREN);
      return ty;
    }
    const name = this.eatIdent();
    return { kind: "type-base", name };
  }
}

export function parse(tokens: Token[]): AST.Program {
  return new Parser(tokens).parseProgram();
}
