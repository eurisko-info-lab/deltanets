// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Parser
// Recursive descent parser: tokens → AST.
//
// Grammar:
//   program      = statement*
//   statement    = systemDecl | extendDecl | composeDecl | agentDecl
//                | ruleDecl | modeDecl | graphDecl | defDecl | includeDecl
//                | lanesDecl | dataDecl
//   dataDecl     = "data" IDENT "{" ("|" IDENT ["(" field ("," field)* ")"])* "}"  (sugar)
//   lanesDecl    = "lanes" STRING "{" laneStmt* "}"
//   laneStmt     = laneDef | laneItem | laneMarker | laneLink
//   laneDef      = "lane" STRING ["{" (IDENT ":" (NUMBER | STRING) ","?)* "}"]
//   laneItem     = "at" NUMBER STRING "place" STRING ["duration" NUMBER]
//   laneMarker   = "bar" NUMBER [STRING]
//   laneLink     = "link" STRING "->" STRING [STRING]
//                | ruleDecl | modeDecl | graphDecl | defDecl | includeDecl
//   includeDecl  = "include" STRING
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
import type { BuiltinAction } from "./types.ts";

export class ParseError extends Error {
  line: number;
  col: number;
  constructor(msg: string, line: number, col: number) {
    super(`Parse error at ${line}:${col}: ${msg}`);
    this.line = line;
    this.col = col;
  }
}

type DeepPattern =
  | { kind: "var"; name: string }
  | { kind: "ctor"; name: string; args: DeepPattern[] };

function flattenDeepPatterns(
  args: DeepPattern[],
  body: AST.ProveExpr,
  counter: { value: number },
): { bindings: string[]; body: AST.ProveExpr } {
  const bindings: string[] = [];
  let wrappedBody = body;
  for (let i = args.length - 1; i >= 0; i--) {
    const arg = args[i];
    if (arg.kind === "var") {
      bindings.unshift(arg.name);
    } else {
      const freshVar = `_dp${counter.value++}`;
      bindings.unshift(freshVar);
      const inner = flattenDeepPatterns(arg.args, wrappedBody, counter);
      wrappedBody = {
        kind: "match",
        scrutinee: freshVar,
        cases: [{ pattern: arg.name, bindings: inner.bindings, body: inner.body }],
      };
    }
  }
  return { bindings, body: wrappedBody };
}

class Parser {
  pos = 0;
  private deepPatternCounter = { value: 0 };
  private notations = new Map<string, { func: string; precedence: number; assoc: "left" | "right" }>();
  constructor(private tokens: Token[]) {}

  peek(): Token {
    return this.tokens[this.pos];
  }
  advance(): Token {
    return this.tokens[this.pos++];
  }
  check(type: TokenKind): boolean {
    return this.peek().type === type;
  }

  eat(type: TokenKind): Token {
    const tok = this.peek();
    if (tok.type !== type) {
      throw new ParseError(
        `Expected ${type} but got '${tok.value || tok.type}'`,
        tok.line,
        tok.col,
      );
    }
    return this.advance();
  }

  eatIdent(): string {
    return this.eat(TT.IDENT).value;
  }

  /** Check if the next token is an IDENT with a specific value. */
  checkIdent(value: string): boolean {
    const tok = this.peek();
    return tok.type === TT.IDENT && tok.value === value;
  }

  /** Eat an IDENT with a specific value, or throw. */
  eatIdentValue(value: string): Token {
    const tok = this.peek();
    if (tok.type !== TT.IDENT || tok.value !== value) {
      throw new ParseError(
        `Expected '${value}' but got '${tok.value || tok.type}'`,
        tok.line,
        tok.col,
      );
    }
    return this.advance();
  }

  // Accept IDENT, or LEFT/RIGHT as identifier (used in port refs)
  eatName(): string {
    const tok = this.peek();
    if (
      tok.type === TT.IDENT || tok.type === TT.LEFT || tok.type === TT.RIGHT
    ) {
      return this.advance().value;
    }
    throw new ParseError(
      `Expected name, got '${tok.value}'`,
      tok.line,
      tok.col,
    );
  }

  /** Parse: item ("," item)* */
  parseCommaList<T>(parseItem: () => T): T[] {
    const items = [parseItem()];
    while (this.check(TT.COMMA)) { this.advance(); items.push(parseItem()); }
    return items;
  }

  // ─── Program ─────────────────────────────────────────────────────

  parseProgram(): AST.Program {
    const stmts: AST.Statement[] = [];
    while (!this.check(TT.EOF)) {
      const tok = this.peek();
      if (tok.type === TT.RULE) stmts.push(...this.parseRuleDecl());
      else stmts.push(this.parseStatement());
    }
    return stmts;
  }

  parseStatement(): AST.Statement {
    const tok = this.peek();
    switch (tok.type) {
      case TT.SYSTEM:
        return this.parseSystemOrExtendOrCompose();
      case TT.AGENT:
        return this.parseAgentDecl();
      case TT.RULE:
        return this.parseRuleDecl()[0]; // single-rule fallback
      case TT.MODE:
        return this.parseModeDecl();
      case TT.GRAPH:
        return this.parseGraphDecl();
      case TT.DEF:
        return this.parseDefDecl();
      case TT.INCLUDE:
        return this.parseIncludeDecl();
      case TT.LANES:
        return this.parseLanesDecl();
      case TT.PROVE:
        return this.parseProveDecl();
      case TT.DATA:
        return this.parseDataDecl();
      case TT.RECORD:
        return this.parseRecordDecl();
      case TT.CODATA:
        return this.parseCodataDecl();
      case TT.COMPUTE:
        return this.parseComputeDecl();
      case TT.TACTIC:
        return this.parseTacticDecl();
      case TT.MUTUAL:
        return this.parseMutualDecl();
      case TT.SECTION:
        return this.parseSectionDecl();
      case TT.NOTATION:
        return this.parseNotationDecl();
      case TT.COERCION:
        return this.parseCoercionDecl();
      default:
        throw new ParseError(
          `Unexpected '${tok.value || tok.type}'`,
          tok.line,
          tok.col,
        );
    }
  }

  // ─── Include ──────────────────────────────────────────────────────

  parseIncludeDecl(): AST.IncludeDecl {
    this.eat(TT.INCLUDE);
    const path = this.eat(TT.STRING).value;
    return { kind: "include", path };
  }

  // ─── Lanes ─────────────────────────────────────────────────────────

  parseLanesDecl(): AST.LanesDecl {
    this.eat(TT.LANES);
    const name = this.eat(TT.STRING).value;
    this.eat(TT.LBRACE);
    const body: AST.LaneStmt[] = [];
    while (!this.check(TT.RBRACE)) {
      const tok = this.peek();
      if (tok.type === TT.LANE) {
        body.push(this.parseLaneDef());
      } else if (tok.type === TT.IDENT && tok.value === "at") {
        body.push(this.parseLaneItem());
      } else if (tok.type === TT.IDENT && tok.value === "bar") {
        body.push(this.parseLaneMarker());
      } else if (tok.type === TT.IDENT && tok.value === "link") {
        body.push(this.parseLaneLink());
      } else {
        throw new ParseError(
          `Unexpected '${tok.value || tok.type}' in lanes block`,
          tok.line,
          tok.col,
        );
      }
    }
    this.eat(TT.RBRACE);
    return { kind: "lanes", name, body };
  }

  parseLaneDef(): AST.LaneDef {
    this.eat(TT.LANE);
    const name = this.eat(TT.STRING).value;
    const props: Record<string, string | number> = {};
    if (this.check(TT.LBRACE)) {
      this.advance();
      while (!this.check(TT.RBRACE)) {
        const key = this.eatIdent();
        this.eat(TT.COLON);
        const val = this.peek();
        if (val.type === TT.NUMBER) {
          props[key] = parseFloat(this.advance().value);
        } else if (val.type === TT.STRING) {
          props[key] = this.advance().value;
        } else {
          props[key] = this.eatIdent();
        }
        if (this.check(TT.COMMA)) this.advance();
      }
      this.eat(TT.RBRACE);
    }
    return { kind: "lane-def", name, props };
  }

  parseLaneItem(): AST.LaneItem {
    this.eatIdentValue("at");
    const position = parseFloat(this.eat(TT.NUMBER).value);
    const lane = this.eat(TT.STRING).value;
    this.eatIdentValue("place");
    const label = this.eat(TT.STRING).value;
    let duration = 0;
    if (this.checkIdent("duration")) {
      this.advance();
      duration = parseFloat(this.eat(TT.NUMBER).value);
    }
    return { kind: "lane-item", position, lane, label, duration };
  }

  parseLaneMarker(): AST.LaneMarker {
    this.eatIdentValue("bar");
    const position = parseFloat(this.eat(TT.NUMBER).value);
    let label: string | undefined;
    if (this.check(TT.STRING)) {
      label = this.advance().value;
    }
    return { kind: "lane-marker", position, label };
  }

  parseLaneLink(): AST.LaneLink {
    this.eatIdentValue("link");
    const from = this.eat(TT.STRING).value;
    this.eat(TT.ARROW);
    const to = this.eat(TT.STRING).value;
    let label: string | undefined;
    if (this.check(TT.STRING)) {
      label = this.advance().value;
    }
    return { kind: "lane-link", from, to, label };
  }

  // ─── System / Extend / Compose ───────────────────────────────────

  parseSystemOrExtendOrCompose():
    | AST.SystemDecl
    | AST.ExtendDecl
    | AST.ComposeDecl {
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

  parseSystemBody(): AST.SystemBody[] {
    this.eat(TT.LBRACE);
    const body: AST.SystemBody[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const tok = this.peek();
      if (tok.type === TT.AGENT) body.push(this.parseAgentDecl());
      else if (tok.type === TT.RULE) body.push(...this.parseRuleDecl());
      else if (tok.type === TT.MODE) body.push(this.parseModeDecl());
      else if (tok.type === TT.PROVE) body.push(this.parseProveDecl());
      else if (tok.type === TT.DATA) body.push(this.parseDataDecl());
      else if (tok.type === TT.RECORD) body.push(this.parseRecordDecl());
      else if (tok.type === TT.CODATA) body.push(this.parseCodataDecl());
      else if (tok.type === TT.COMPUTE) body.push(this.parseComputeDecl());
      else if (tok.type === TT.OPEN) body.push(this.parseOpenDecl());
      else if (tok.type === TT.EXPORT) body.push(this.parseExportDecl());
      else if (tok.type === TT.TACTIC) body.push(this.parseTacticDecl());
      else if (tok.type === TT.MUTUAL) body.push(this.parseMutualDecl());
      else if (tok.type === TT.SECTION) body.push(this.parseSectionDecl());
      else if (tok.type === TT.NOTATION) body.push(this.parseNotationDecl());
      else if (tok.type === TT.COERCION) body.push(this.parseCoercionDecl());
      else {throw new ParseError(
          `Expected agent/rule/mode/prove/data/record/codata/compute/open/export/tactic/mutual/section/notation/coercion, got '${tok.value}'`,
          tok.line,
          tok.col,
        );}
    }
    this.eat(TT.RBRACE);
    return body;
  }

  // ─── Agent ───────────────────────────────────────────────────────

  parseAgentDecl(): AST.AgentDecl {
    this.eat(TT.AGENT);
    const name = this.eatIdent();
    this.eat(TT.LPAREN);
    const ports = this.check(TT.RPAREN)
      ? [] : this.parseCommaList(() => this.parsePortDef());
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

  // rule agentA <> agentB -> action
  // rule [a, b, c] <> agentB -> action  (batch: expands to multiple rules)
  // Either side or both can use [brackets]
  parseRuleDecl(): AST.RuleDecl[] {
    this.eat(TT.RULE);
    const leftNames = this.parseAgentNameOrList();
    this.eat(TT.INTERACT);
    const rightNames = this.parseAgentNameOrList();
    this.eat(TT.ARROW);
    const action = this.parseRuleAction();
    const rules: AST.RuleDecl[] = [];
    for (const a of leftNames) {
      for (const b of rightNames) {
        rules.push({ kind: "rule", agentA: a, agentB: b, action });
      }
    }
    return rules;
  }

  /** Parse IDENT or "[" IDENT ("," IDENT)* "]" */
  private parseAgentNameOrList(): string[] {
    if (this.check(TT.LBRACKET)) {
      this.advance();
      const names = this.parseCommaList(() => this.eatIdent());
      this.eat(TT.RBRACKET);
      return names;
    }
    return [this.eatIdent()];
  }

  private static BUILTIN_RULES: Record<string, BuiltinAction["name"]> = {
    [TT.ANNIHILATE]: "annihilate", [TT.ERASE]: "erase",
    [TT.COMMUTE]: "commute", [TT.AUX_FAN]: "aux-fan",
  };

  parseRuleAction(): AST.RuleAction {
    const tok = this.peek();
    const builtin = Parser.BUILTIN_RULES[tok.type];
    if (builtin) { this.advance(); return { kind: "builtin", name: builtin }; }
    if (tok.type === TT.LBRACE) {
      return { kind: "custom", body: this.parseCustomRuleBody() };
    }
    throw new ParseError(
      `Expected rule action (annihilate/erase/commute/aux-fan/{...}), got '${tok.value}'`,
      tok.line,
      tok.col,
    );
  }

  parseCustomRuleBody(): AST.RuleStmt[] {
    this.eat(TT.LBRACE);
    const stmts: AST.RuleStmt[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const result = this.parseRuleStmt();
      if (Array.isArray(result)) stmts.push(...result);
      else stmts.push(result);
    }
    this.eat(TT.RBRACE);
    return stmts;
  }

  parseRuleStmt(): AST.RuleStmt | AST.RuleStmt[] {
    const tok = this.peek();
    if (tok.type === TT.LET) return this.parseLetStmt();
    if (tok.type === TT.WIRE) return this.parseWireStmts();
    if (tok.type === TT.RELINK) return this.parseRelinkStmt();
    if (tok.type === TT.ERASE) return this.parseEraseStmt();
    throw new ParseError(
      `Expected let/wire/relink/erase, got '${tok.value}'`,
      tok.line,
      tok.col,
    );
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

  // wire portRef -- portRef           (classic)
  // wire a ~ b                        (tilde: bare names default to .principal)
  // wire a ~ b, b.body ~ c, c -- d   (comma-separated chain)
  parseWireStmts(): AST.WireStmt[] {
    this.eat(TT.WIRE);
    const wires: AST.WireStmt[] = [];
    wires.push(this.parseOneWire());
    while (this.check(TT.COMMA)) {
      this.advance();
      wires.push(this.parseOneWire());
    }
    return wires;
  }

  private parseOneWire(): AST.WireStmt {
    const a = this.parsePortRefOrPrincipal();
    const portA = a.port !== null ? a as AST.PortRef : { node: a.node, port: "principal" };
    if (this.check(TT.TILDE)) {
      this.advance();
      const b = this.parsePortRefOrPrincipal();
      const portB = b.port !== null ? b as AST.PortRef : { node: b.node, port: "principal" };
      return { kind: "wire", portA, portB };
    }
    this.eat(TT.WIRE_OP);
    const portB = this.parsePortRef();
    return { kind: "wire", portA, portB };
  }

  /** Parse portRef, but allow bare IDENT (no .port) for tilde syntax. */
  private parsePortRefOrPrincipal(): { node: string; port: string | null } {
    const node = this.eatName();
    if (this.check(TT.DOT)) {
      this.advance();
      const tok = this.peek();
      let port: string;
      if (tok.type === TT.NUMBER) port = this.advance().value;
      else port = this.eatName();
      return { node, port };
    }
    return { node, port: null };
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

  // ─── Deep pattern parsing ─────────────────────────────────────────

  parseDeepPattern(): DeepPattern {
    const name = this.eatIdent();
    if (this.check(TT.LPAREN)) {
      this.advance();
      const args: DeepPattern[] = [];
      if (!this.check(TT.RPAREN))
        args.push(...this.parseCommaList(() => this.parseDeepPattern()));
      this.eat(TT.RPAREN);
      return { kind: "ctor", name, args };
    }
    return { kind: "var", name };
  }

  parseCaseArms(): AST.ProveCase[] {
    const cases: AST.ProveCase[] = [];
    while (this.check(TT.PIPE)) {
      this.advance();
      const pattern = this.eatIdent();
      let bindings: string[] = [];
      let deepArgs: DeepPattern[] | undefined;
      if (this.check(TT.LPAREN)) {
        this.advance();
        if (!this.check(TT.RPAREN))
          deepArgs = this.parseCommaList(() => this.parseDeepPattern());
        this.eat(TT.RPAREN);
      }
      this.eat(TT.ARROW);
      let body = this.parseProveExpr();
      if (deepArgs) {
        const flat = flattenDeepPatterns(deepArgs, body, this.deepPatternCounter);
        bindings = flat.bindings;
        body = flat.body;
      }
      cases.push({ pattern, bindings, body });
    }
    return cases;
  }

  // ─── Prove (tactic sugar) ────────────────────────────────────────

  parseProveDecl(): AST.ProveDecl {
    this.eat(TT.PROVE);
    const name = this.eatIdent();
    this.eat(TT.LPAREN);
    const params = this.parseCommaList(() => this.parseProveParam());
    this.eat(TT.RPAREN);
    // Optional return type: -> TypeExpr
    let returnType: AST.ProveExpr | undefined;
    if (this.check(TT.ARROW)) {
      this.advance();
      returnType = this.parseProveExpr();
    }
    this.eat(TT.LBRACE);
    const cases: AST.ProveCase[] = [];
    let induction: string | undefined;
    let measure: AST.ProveExpr | undefined;
    let wf: string | undefined;
    // Check for induction(var) sugar — auto-generates case arms
    if (!this.check(TT.PIPE) && !this.check(TT.RBRACE) &&
        this.check(TT.IDENT) && this.peek().value === "induction") {
      this.advance(); // eat 'induction'
      this.eat(TT.LPAREN);
      induction = this.eatIdent();
      this.eat(TT.RPAREN);
    } else if (!this.check(TT.PIPE) && !this.check(TT.RBRACE) &&
               this.check(TT.IDENT) && this.peek().value === "measure") {
      this.advance(); // eat 'measure'
      this.eat(TT.LPAREN);
      measure = this.parseProveExpr();
      this.eat(TT.RPAREN);
      cases.push(...this.parseCaseArms());
    } else if (!this.check(TT.PIPE) && !this.check(TT.RBRACE) &&
               this.check(TT.IDENT) && this.peek().value === "wf") {
      this.advance(); // eat 'wf'
      this.eat(TT.LPAREN);
      wf = this.eatIdent();
      this.eat(TT.RPAREN);
      cases.push(...this.parseCaseArms());
    } else {
      cases.push(...this.parseCaseArms());
    }
    this.eat(TT.RBRACE);
    return { kind: "prove", name, params, returnType, cases, induction, measure, wf };
  }

  parseProveParam(): AST.ProveParam {
    // Implicit param: {name} or {name : Type}
    if (this.check(TT.LBRACE)) {
      this.advance();
      const name = this.eatIdent();
      let type: AST.ProveExpr | undefined;
      if (this.check(TT.COLON)) {
        this.advance();
        type = this.parseProveExpr();
      }
      this.eat(TT.RBRACE);
      return { name, type, implicit: true };
    }
    const name = this.eatIdent();
    if (this.check(TT.COLON)) {
      this.advance();
      const type = this.parseProveExpr();
      return { name, type };
    }
    return { name };
  }

  // Map token types to notation symbol strings
  private tokenToNotationSymbol(): string | null {
    const tok = this.peek();
    switch (tok.type) {
      case TT.PLUS: return "+";
      case TT.MINUS: return "-";
      case TT.STAR: return "*";
      case TT.SLASH: return "/";
      default: return null;
    }
  }

  parseProveExpr(): AST.ProveExpr {
    return this.parseProveExprPrec(0);
  }

  private parseProveExprPrec(minPrec: number): AST.ProveExpr {
    let left = this.parsePrimaryProveExpr();
    // Infix notation loop (Pratt parsing)
    while (true) {
      const sym = this.tokenToNotationSymbol();
      if (!sym) break;
      const nota = this.notations.get(sym);
      if (!nota) break;
      if (nota.precedence < minPrec) break;
      this.advance(); // consume operator token
      const nextPrec = nota.assoc === "left" ? nota.precedence + 1 : nota.precedence;
      const right = this.parseProveExprPrec(nextPrec);
      left = { kind: "call", name: nota.func, args: [left, right] };
    }
    return left;
  }

  private parsePrimaryProveExpr(): AST.ProveExpr {
    if (this.check(TT.QUESTION)) {
      this.advance();
      return { kind: "hole" };
    }
    // let x = value in body
    if (this.check(TT.LET)) {
      this.advance();
      const name = this.eatIdent();
      this.eat(TT.EQ);
      const value = this.parseProveExpr();
      this.eat(TT.IN);
      const body = this.parseProveExpr();
      return { kind: "let", name, value, body };
    }
    // forall(x : A, B) — Pi type
    if (this.check(TT.IDENT) && this.peek().value === "forall") {
      this.advance();
      this.eat(TT.LPAREN);
      const param = this.eatIdent();
      this.eat(TT.COLON);
      const domain = this.parseProveExpr();
      this.eat(TT.COMMA);
      const codomain = this.parseProveExpr();
      this.eat(TT.RPAREN);
      return { kind: "pi", param, domain, codomain };
    }
    // exists(x : A, B) — Sigma type
    if (this.check(TT.IDENT) && this.peek().value === "exists") {
      this.advance();
      this.eat(TT.LPAREN);
      const param = this.eatIdent();
      this.eat(TT.COLON);
      const domain = this.parseProveExpr();
      this.eat(TT.COMMA);
      const codomain = this.parseProveExpr();
      this.eat(TT.RPAREN);
      return { kind: "sigma", param, domain, codomain };
    }
    // fun(x : A, body) — lambda
    if (this.check(TT.IDENT) && this.peek().value === "fun") {
      this.advance();
      this.eat(TT.LPAREN);
      const param = this.eatIdent();
      this.eat(TT.COLON);
      const paramType = this.parseProveExpr();
      this.eat(TT.COMMA);
      const body = this.parseProveExpr();
      this.eat(TT.RPAREN);
      return { kind: "lambda", param, paramType, body };
    }
    // \x:A.body — lambda (backslash syntax)
    if (this.check(TT.BACKSLASH)) {
      this.advance();
      const param = this.eatIdent();
      this.eat(TT.COLON);
      const paramType = this.parseProveExpr();
      this.eat(TT.DOT);
      const body = this.parseProveExpr();
      return { kind: "lambda", param, paramType, body };
    }
    const name = this.eatIdent();
    // match(scrutinee) { | Pat(bindings) -> body ... }
    if (name === "match") {
      this.eat(TT.LPAREN);
      const scrutinee = this.eatIdent();
      this.eat(TT.RPAREN);
      this.eat(TT.LBRACE);
      const cases = this.parseCaseArms();
      this.eat(TT.RBRACE);
      return { kind: "match", scrutinee, cases };
    }
    if (name === "with") {
      this.eat(TT.LPAREN);
      const scrutineeExpr = this.parseProveExpr();
      this.eat(TT.RPAREN);
      this.eat(TT.LBRACE);
      const withCases = this.parseCaseArms();
      this.eat(TT.RBRACE);
      const freshVar = `_with${this.deepPatternCounter.value++}`;
      return {
        kind: "let",
        name: freshVar,
        value: scrutineeExpr,
        body: { kind: "match", scrutinee: freshVar, cases: withCases },
      };
    }
    if (this.check(TT.LPAREN)) {
      this.advance();
      const args = this.check(TT.RPAREN)
        ? [] : this.parseCommaList(() => this.parseProveExpr());
      this.eat(TT.RPAREN);
      return { kind: "call", name, args };
    }
    return { kind: "ident", name };
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

  // ─── Data (sugar) ────────────────────────────────────────────────
  // data Name { | Con(field : Type, ...) | Con2 ... }
  // Syntactic sugar — desugars into constructor agents + duplicator.

  parseDataDecl(): AST.DataDecl {
    this.eat(TT.DATA);
    const name = this.eatIdent();
    const params: string[] = [];
    const indices: AST.DataIndex[] = [];
    if (this.check(TT.LPAREN)) {
      this.advance();
      if (!this.check(TT.RPAREN)) {
        // Parse params and indices: bare ident = param, ident : Type = index
        this.parseCommaList(() => {
          const paramName = this.eatIdent();
          if (this.check(TT.COLON)) {
            this.advance();
            const indexType = this.parseProveExpr();
            indices.push({ name: paramName, type: indexType });
          } else {
            params.push(paramName);
          }
          return paramName; // unused return for parseCommaList
        });
      }
      this.eat(TT.RPAREN);
    }
    this.eat(TT.LBRACE);
    const constructors: AST.DataConstructor[] = [];
    while (this.check(TT.PIPE)) {
      this.advance(); // eat |
      const consName = this.eatIdent();
      const fields: AST.DataField[] = [];
      if (this.check(TT.LPAREN)) {
        this.advance();
        if (!this.check(TT.RPAREN)) {
          fields.push(...this.parseCommaList(() => {
            const fieldName = this.eatIdent();
            this.eat(TT.COLON);
            const fieldType = this.parseProveExpr();
            return { name: fieldName, type: fieldType };
          }));
        }
        this.eat(TT.RPAREN);
      }
      // Optional return index annotation: | VNil : Vec(A, Zero)
      let returnIndices: AST.ProveExpr[] | undefined;
      if (this.check(TT.COLON)) {
        this.advance();
        const retType = this.parseProveExpr();
        // Extract index arguments from the return type call
        if (retType.kind === "call" && retType.name === name) {
          // Skip params, take only index positions
          returnIndices = retType.args.slice(params.length);
        }
      }
      constructors.push({ name: consName, fields, returnIndices });
    }
    this.eat(TT.RBRACE);
    return { kind: "data", name, params, indices, constructors };
  }

  // ─── Record (single-constructor data type with projections) ──────
  // record Name(params) { field : Type, ... }

  parseRecordDecl(): AST.RecordDecl {
    this.eat(TT.RECORD);
    const name = this.eatIdent();
    const params: string[] = [];
    if (this.check(TT.LPAREN)) {
      this.advance();
      if (!this.check(TT.RPAREN)) {
        this.parseCommaList(() => {
          const p = this.eatIdent();
          params.push(p);
          return p;
        });
      }
      this.eat(TT.RPAREN);
    }
    this.eat(TT.LBRACE);
    const fields: AST.DataField[] = [];
    if (!this.check(TT.RBRACE)) {
      fields.push(...this.parseCommaList(() => {
        const fieldName = this.eatIdent();
        this.eat(TT.COLON);
        const fieldType = this.parseProveExpr();
        return { name: fieldName, type: fieldType };
      }));
    }
    this.eat(TT.RBRACE);
    return { kind: "record", name, params, fields };
  }

  // ─── Codata (coinductive type) ───────────────────────────────────
  // codata Stream(A) { head : A, tail : Stream(A) }

  parseCodataDecl(): AST.CodataDecl {
    this.eat(TT.CODATA);
    const name = this.eatIdent();
    const params: string[] = [];
    if (this.check(TT.LPAREN)) {
      this.advance();
      if (!this.check(TT.RPAREN)) {
        this.parseCommaList(() => {
          const p = this.eatIdent();
          params.push(p);
          return p;
        });
      }
      this.eat(TT.RPAREN);
    }
    this.eat(TT.LBRACE);
    const fields: AST.DataField[] = [];
    if (!this.check(TT.RBRACE)) {
      fields.push(...this.parseCommaList(() => {
        const fieldName = this.eatIdent();
        this.eat(TT.COLON);
        const fieldType = this.parseProveExpr();
        return { name: fieldName, type: fieldType };
      }));
    }
    this.eat(TT.RBRACE);
    return { kind: "codata", name, params, fields };
  }

  // ─── Open (import from another system) ───────────────────────────
  // open "SystemName"
  // open "SystemName" use AgentA, AgentB

  parseOpenDecl(): AST.OpenDecl {
    this.eat(TT.OPEN);
    const system = this.eat(TT.STRING).value;
    let names: string[] | undefined;
    if (this.check(TT.USE)) {
      this.advance();
      names = this.parseCommaList(() => this.eatIdent());
    }
    return { kind: "open", system, names };
  }

  // ─── Export (visibility control) ─────────────────────────────────
  // export AgentA, AgentB

  parseExportDecl(): AST.ExportDecl {
    this.eat(TT.EXPORT);
    const names = this.parseCommaList(() => this.eatIdent());
    return { kind: "export", names };
  }

  // ─── Compute (type-level reduction rule) ─────────────────────────
  // compute funcName(pattern, ...) = result
  // Patterns: variable (ident) or constructor application (Ctor(v1, v2))

  parseComputeDecl(): AST.ComputeDecl {
    this.eat(TT.COMPUTE);
    const funcName = this.eatIdent();
    this.eat(TT.LPAREN);
    const args = this.parseCommaList(() => this.parseComputePattern());
    this.eat(TT.RPAREN);
    this.eat(TT.EQ);
    const result = this.parseProveExpr();
    return { kind: "compute", funcName, args, result };
  }

  parseComputePattern(): AST.ComputePattern {
    const name = this.eatIdent();
    if (this.check(TT.LPAREN)) {
      this.advance();
      const args = this.check(TT.RPAREN)
        ? [] : this.parseCommaList(() => this.eatIdent());
      this.eat(TT.RPAREN);
      return { kind: "ctor", name, args };
    }
    return { kind: "var", name };
  }

  // ─── Tactic (user-definable proof tactic) ────────────────────────
  // tactic name { agent..., rule... }
  // The tactic name is auto-declared as agent name(principal, result).

  parseTacticDecl(): AST.TacticDecl {
    this.eat(TT.TACTIC);
    const name = this.eatIdent();
    this.eat(TT.LBRACE);
    const body: (AST.AgentDecl | AST.RuleDecl)[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const tok = this.peek();
      if (tok.type === TT.AGENT) body.push(this.parseAgentDecl());
      else if (tok.type === TT.RULE) body.push(...this.parseRuleDecl());
      else {
        throw new ParseError(
          `Expected agent/rule in tactic body, got '${tok.value}'`,
          tok.line,
          tok.col,
        );
      }
    }
    this.eat(TT.RBRACE);
    return { kind: "tactic", name, body };
  }

  // ─── Mutual (mutual inductive types / mutual proves) ─────────────
  // mutual { data ... data ... prove ... prove ... }

  parseMutualDecl(): AST.MutualDecl {
    this.eat(TT.MUTUAL);
    this.eat(TT.LBRACE);
    const data: AST.DataDecl[] = [];
    const proves: AST.ProveDecl[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const tok = this.peek();
      if (tok.type === TT.DATA) data.push(this.parseDataDecl());
      else if (tok.type === TT.PROVE) proves.push(this.parseProveDecl());
      else {
        throw new ParseError(
          `Expected data/prove in mutual block, got '${tok.value}'`,
          tok.line,
          tok.col,
        );
      }
    }
    this.eat(TT.RBRACE);
    if (data.length + proves.length < 2) {
      throw new ParseError(
        `mutual block must contain at least 2 declarations`,
        this.peek().line,
        this.peek().col,
      );
    }
    return { kind: "mutual", data, proves };
  }

  // ─── Section ─────────────────────────────────────────────────────

  parseSectionDecl(): AST.SectionDecl {
    this.eat(TT.SECTION);
    const name = this.eatIdent();
    this.eat(TT.LBRACE);
    const variables: AST.SectionVariable[] = [];
    while (this.check(TT.VARIABLE)) {
      this.advance();
      this.eat(TT.LPAREN);
      const varName = this.eatIdent();
      this.eat(TT.COLON);
      const type = this.parseProveExpr();
      this.eat(TT.RPAREN);
      variables.push({ name: varName, type });
    }
    // Parse remaining declarations as system body items
    const body: AST.SystemBody[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const tok = this.peek();
      if (tok.type === TT.AGENT) body.push(this.parseAgentDecl());
      else if (tok.type === TT.RULE) body.push(...this.parseRuleDecl());
      else if (tok.type === TT.MODE) body.push(this.parseModeDecl());
      else if (tok.type === TT.PROVE) body.push(this.parseProveDecl());
      else if (tok.type === TT.DATA) body.push(this.parseDataDecl());
      else if (tok.type === TT.RECORD) body.push(this.parseRecordDecl());
      else if (tok.type === TT.CODATA) body.push(this.parseCodataDecl());
      else if (tok.type === TT.COMPUTE) body.push(this.parseComputeDecl());
      else if (tok.type === TT.OPEN) body.push(this.parseOpenDecl());
      else if (tok.type === TT.EXPORT) body.push(this.parseExportDecl());
      else if (tok.type === TT.TACTIC) body.push(this.parseTacticDecl());
      else if (tok.type === TT.MUTUAL) body.push(this.parseMutualDecl());
      else if (tok.type === TT.SECTION) body.push(this.parseSectionDecl());
      else if (tok.type === TT.NOTATION) body.push(this.parseNotationDecl());
      else if (tok.type === TT.COERCION) body.push(this.parseCoercionDecl());
      else {
        throw new ParseError(
          `Expected declaration in section body, got '${tok.value}'`,
          tok.line, tok.col,
        );
      }
    }
    this.eat(TT.RBRACE);
    return { kind: "section", name, variables, body };
  }

  // ─── Notation ────────────────────────────────────────────────────
  // notation "+" := add (prec 50, left)
  // Registers an infix operator and returns AST node.

  parseNotationDecl(): AST.NotationDecl {
    this.eat(TT.NOTATION);
    const symbol = this.eat(TT.STRING).value;
    this.eat(TT.EQ); // :=  (we parse = since := isn't a token; the : is part of string termination context)
    const func = this.eatIdent();
    // Parse optional (prec N, left|right)
    let precedence = 50;
    let assoc: "left" | "right" = "left";
    if (this.check(TT.LPAREN)) {
      this.advance();
      // expect: prec N
      this.eatIdentValue("prec");
      const precTok = this.eat(TT.NUMBER);
      precedence = parseInt(precTok.value, 10);
      if (this.check(TT.COMMA)) {
        this.advance();
        // left/right are keywords (TT.LEFT, TT.RIGHT), so accept both IDENT and keyword tokens
        const tok = this.peek();
        let assocStr: string;
        if (tok.type === TT.LEFT) { this.advance(); assocStr = "left"; }
        else if (tok.type === TT.RIGHT) { this.advance(); assocStr = "right"; }
        else { assocStr = this.eatIdent(); }
        if (assocStr === "left" || assocStr === "right") {
          assoc = assocStr;
        } else {
          throw new ParseError(
            `Expected 'left' or 'right', got '${assocStr}'`,
            this.peek().line, this.peek().col,
          );
        }
      }
      this.eat(TT.RPAREN);
    }
    // Register in parser's notation table for subsequent expressions
    this.notations.set(symbol, { func, precedence, assoc });
    return { kind: "notation", symbol, func, precedence, assoc };
  }

  // ─── Coercion ────────────────────────────────────────────────────
  // coercion name = From -> To via func

  parseCoercionDecl(): AST.CoercionDecl {
    this.eat(TT.COERCION);
    const name = this.eatIdent();
    this.eat(TT.EQ);
    const from = this.eatIdent();
    this.eat(TT.ARROW);
    const to = this.eatIdent();
    this.eatIdentValue("via");
    const func = this.eatIdent();
    return { kind: "coercion", name, from, to, func };
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
        else if (tok.type === TT.WIRE) body.push(...this.parseWireStmts());
        else {throw new ParseError(
            `Expected let/wire, got '${tok.value}'`,
            tok.line,
            tok.col,
          );}
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
