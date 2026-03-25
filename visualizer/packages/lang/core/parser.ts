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

type MixfixPart = { kind: "kw"; value: string } | { kind: "hole" };
type ParsedMixfix = { parts: MixfixPart[]; func: string; prec: number };

class Parser {
  pos = 0;
  private deepPatternCounter = { value: 0 };
  private notations = new Map<string, { func: string; precedence: number; assoc: "left" | "right" }>();
  // Mixfix: prefix patterns keyed by leading keyword, infix patterns keyed by keyword after first hole
  private prefixMixfix = new Map<string, ParsedMixfix[]>();
  private infixMixfix = new Map<string, ParsedMixfix[]>();
  private mixfixKeywords = new Set<string>();
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
      case TT.STRATEGY:
        return this.parseStrategyDecl();
      case TT.MUTUAL:
        return this.parseMutualDecl();
      case TT.SECTION:
        return this.parseSectionDecl();
      case TT.NOTATION:
        return this.parseNotationDecl();
      case TT.COERCION:
        return this.parseCoercionDecl();
      case TT.SETOID:
        return this.parseSetoidDecl();
      case TT.RING:
        return this.parseRingDecl();
      case TT.CLASS:
        return this.parseClassDecl();
      case TT.INSTANCE:
        return this.parseInstanceDecl();
      case TT.HINT:
        return this.parseHintDecl();
      case TT.CANONICAL:
        return this.parseCanonicalDecl();
      case TT.PROGRAM:
        return this.parseProgramDecl();
      case TT.THEOREM:
      case TT.LEMMA:
        return this.parseTheoremDecl();
      case TT.MODULE:
        return this.parseModuleDecl();
      default:
        // Contextual keywords (not reserved — can also be identifiers)
        if (tok.type === TT.IDENT && tok.value === "field") return this.parseFieldDecl();
        if (tok.type === TT.IDENT && tok.value === "scope") return this.parseScopeDecl();
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

    // Optional seal: system "X" : "Sig" ...
    let sig: string | undefined;
    if (this.check(TT.COLON)) {
      this.advance();
      sig = this.eat(TT.STRING).value;
    }

    // system "B" extend "A" { ... }  or  system "B" : "Sig" extend "A" { ... }
    if (this.check(TT.EXTEND)) {
      this.advance();
      const base = this.eat(TT.STRING).value;
      const body = this.parseSystemBody();
      return { kind: "extend", name, base, sig, body };
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

    // system "X" { ... }  or  system "X" : "Sig" { ... }
    const body = this.parseSystemBody();
    return { kind: "system", name, sig, body };
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
      else if (tok.type === TT.STRATEGY) body.push(this.parseStrategyDecl());
      else if (tok.type === TT.MUTUAL) body.push(this.parseMutualDecl());
      else if (tok.type === TT.SECTION) body.push(this.parseSectionDecl());
      else if (tok.type === TT.NOTATION) body.push(this.parseNotationDecl());
      else if (tok.type === TT.COERCION) body.push(this.parseCoercionDecl());
      else if (tok.type === TT.SETOID) body.push(this.parseSetoidDecl());
      else if (tok.type === TT.RING) body.push(this.parseRingDecl());
      else if (tok.type === TT.CLASS) body.push(this.parseClassDecl());
      else if (tok.type === TT.INSTANCE) body.push(this.parseInstanceDecl());
      else if (tok.type === TT.HINT) body.push(this.parseHintDecl());
      else if (tok.type === TT.CANONICAL) body.push(this.parseCanonicalDecl());
      else if (tok.type === TT.PROGRAM) body.push(this.parseProgramDecl());
      else if (tok.type === TT.THEOREM || tok.type === TT.LEMMA) body.push(this.parseTheoremDecl());
      else if (tok.type === TT.ALIAS) body.push(this.parseAliasDecl());
      else if (tok.type === TT.OPAQUE) body.push(this.parseOpaqueDecl());
      else if (tok.type === TT.TRANSPARENT) body.push(this.parseTransparentDecl());
      else if (tok.type === TT.ARGUMENTS) body.push(this.parseArgumentsDecl());
      else if (tok.type === TT.IDENT && tok.value === "field") body.push(this.parseFieldDecl());
      else if (tok.type === TT.IDENT && tok.value === "scope") body.push(this.parseScopeDecl());
      else if (tok.type === TT.AT) {
        // @[simp] prove/theorem/lemma ... — attribute syntax, auto-generates hint entries
        const attrs = this.parseAttributes();
        let prove: AST.ProveDecl;
        if (this.check(TT.THEOREM) || this.check(TT.LEMMA)) {
          prove = this.parseTheoremDecl();
        } else if (this.check(TT.PROVE)) {
          prove = this.parseProveDecl();
        } else {
          throw new ParseError(`Expected 'prove', 'theorem', or 'lemma' after attribute @[...]`, tok.line, tok.col);
        }
        prove.attributes = attrs;
        body.push(prove);
        // Auto-generate hint declarations for each attribute
        for (const attr of attrs) {
          body.push({ kind: "hint", db: attr, lemma: prove.name });
        }
      }
      else {throw new ParseError(
          `Expected agent/rule/mode/prove/theorem/lemma/data/record/codata/compute/open/export/tactic/mutual/section/notation/coercion/setoid/ring/field/class/instance/hint/canonical/program/alias/opaque/transparent/arguments/scope, got '${tok.value}'`,
          tok.line,
          tok.col,
        );}
    }
    this.eat(TT.RBRACE);
    return body;
  }

  // ─── Module (module type / functor / functor app) ──────────────

  parseModuleDecl(): AST.ModuleTypeDecl | AST.FunctorDecl | AST.FunctorAppDecl {
    this.eat(TT.MODULE);

    // module type "Name" { agent specs... }
    if (this.check(TT.IDENT) && this.peek().value === "type") {
      this.advance(); // consume 'type'
      const name = this.eat(TT.STRING).value;
      this.eat(TT.LBRACE);
      const specs: AST.AgentSpec[] = [];
      while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
        this.eat(TT.AGENT);
        const agentName = this.eatIdent();
        this.eat(TT.LPAREN);
        const ports = this.check(TT.RPAREN)
          ? [] : this.parseCommaList(() => this.eatIdent());
        this.eat(TT.RPAREN);
        specs.push({ name: agentName, ports });
      }
      this.eat(TT.RBRACE);
      return { kind: "module-type", name, specs };
    }

    const name = this.eat(TT.STRING).value;

    // module "X" := "F"("Arg1", ...)
    if (this.check(TT.WALRUS)) {
      this.advance();
      const functor = this.eat(TT.STRING).value;
      this.eat(TT.LPAREN);
      const args = this.parseCommaList(() => this.eat(TT.STRING).value);
      this.eat(TT.RPAREN);
      return { kind: "functor-app", name, functor, args };
    }

    // module "F" (M : "Sig", ...) [extend "Base"] { body }
    this.eat(TT.LPAREN);
    const params: { name: string; sig: string }[] = [];
    if (!this.check(TT.RPAREN)) {
      params.push(...this.parseCommaList(() => {
        const pname = this.eatIdent();
        this.eat(TT.COLON);
        const sig = this.eat(TT.STRING).value;
        return { name: pname, sig };
      }));
    }
    this.eat(TT.RPAREN);
    let base: string | undefined;
    if (this.check(TT.EXTEND)) {
      this.advance();
      base = this.eat(TT.STRING).value;
    }
    const body = this.parseSystemBody();
    return { kind: "functor", name, params, base, body };
  }

  // ─── Alias ─────────────────────────────────────────────────────

  parseAliasDecl(): AST.AliasDecl {
    this.eat(TT.ALIAS);
    const name = this.eatIdent();
    this.eat(TT.EQ);
    const target = this.eatIdent();
    return { kind: "alias", name, target };
  }

  // opaque name — mark compute rules for name as opaque (no unfolding)
  parseOpaqueDecl(): AST.OpaqueDecl {
    this.eat(TT.OPAQUE);
    const name = this.eatIdent();
    return { kind: "opaque", name };
  }

  // transparent name — mark compute rules for name as transparent (undo opaque)
  parseTransparentDecl(): AST.OpaqueDecl {
    this.eat(TT.TRANSPARENT);
    const name = this.eatIdent();
    return { kind: "opaque", name, transparent: true };
  }

  // arguments name(explicit, {implicit}, ...)
  parseArgumentsDecl(): AST.ArgumentsDecl {
    this.eat(TT.ARGUMENTS);
    const name = this.eatIdent();
    this.eat(TT.LPAREN);
    const params: { name: string; implicit: boolean }[] = [];
    while (!this.check(TT.RPAREN) && !this.check(TT.EOF)) {
      if (this.check(TT.LBRACE)) {
        this.advance();
        const pname = this.eatIdent();
        this.eat(TT.RBRACE);
        params.push({ name: pname, implicit: true });
      } else {
        const pname = this.eatIdent();
        params.push({ name: pname, implicit: false });
      }
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RPAREN);
    return { kind: "arguments", name, params };
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

  // ─── Program (prove + proof obligations) ─────────────────────────
  // program name(params) -> ReturnType {
  //   wf(R) | measure(expr)
  //   | Pat(bindings) -> body
  //   obligation name(params) -> Prop { cases }
  // }

  parseProgramDecl(): AST.ProgramDecl {
    this.eat(TT.PROGRAM);
    const name = this.eatIdent();
    this.eat(TT.LPAREN);
    const params = this.parseCommaList(() => this.parseProveParam());
    this.eat(TT.RPAREN);
    this.eat(TT.ARROW);
    const returnType = this.parseProveExpr();
    this.eat(TT.LBRACE);
    // Optional termination annotation: wf(R) or measure(expr)
    let wf: string | undefined;
    let measure: AST.ProveExpr | undefined;
    if (!this.check(TT.PIPE) && !this.check(TT.RBRACE) &&
        this.check(TT.IDENT) && this.peek().value === "wf") {
      this.advance();
      this.eat(TT.LPAREN);
      wf = this.eatIdent();
      this.eat(TT.RPAREN);
    } else if (!this.check(TT.PIPE) && !this.check(TT.RBRACE) &&
               this.check(TT.IDENT) && this.peek().value === "measure") {
      this.advance();
      this.eat(TT.LPAREN);
      measure = this.parseProveExpr();
      this.eat(TT.RPAREN);
    }
    const cases = this.parseCaseArms();
    // Parse obligation sub-proves
    const obligations: AST.ObligationDecl[] = [];
    while (this.check(TT.OBLIGATION)) {
      obligations.push(this.parseObligationDecl());
    }
    this.eat(TT.RBRACE);
    return { kind: "program", name, params, returnType, cases, wf, measure, obligations };
  }

  parseObligationDecl(): AST.ObligationDecl {
    this.eat(TT.OBLIGATION);
    const name = this.eatIdent();
    this.eat(TT.LPAREN);
    const params = this.parseCommaList(() => this.parseProveParam());
    this.eat(TT.RPAREN);
    this.eat(TT.ARROW);
    const returnType = this.parseProveExpr();
    this.eat(TT.LBRACE);
    const cases = this.parseCaseArms();
    this.eat(TT.RBRACE);
    return { kind: "obligation", name, params, returnType, cases };
  }

  // ─── Theorem / Lemma (Lean-like syntax) ──────────────────────────
  // theorem name (x y : A) {z : B} : ReturnType := body
  // theorem name (x y : A) : ReturnType := by | Case => body ...
  // lemma name (x : A) : P := by | Case => body ...

  parseTheoremDecl(): AST.ProveDecl {
    this.advance(); // eat 'theorem' or 'lemma'
    const name = this.eatIdent();

    // Parse Lean-style binder groups: (x y : A) {z : B} ...
    const params: AST.ProveParam[] = [];
    while (this.check(TT.LPAREN) || this.check(TT.LBRACE) || this.check(TT.LBRACKET)) {
      params.push(...this.parseLeanBinderGroup());
    }

    // Optional return type: `: ReturnType`
    let returnType: AST.ProveExpr | undefined;
    if (this.check(TT.COLON)) {
      this.advance();
      returnType = this.parseProveExpr();
    }

    // Body: `:= expr` or `:= by ...`
    this.eat(TT.WALRUS);

    let cases: AST.ProveCase[] = [];
    let induction: string | undefined;
    let measure: AST.ProveExpr | undefined;
    let wf: string | undefined;

    if (this.check(TT.BY)) {
      this.advance(); // eat 'by'
      // Check for induction/measure/wf annotations
      if (this.checkIdent("induction")) {
        this.advance();
        const varName = this.eatIdent();
        // `induction n with | cases...` — explicit case arms
        if (this.checkIdent("with")) {
          this.advance();
          cases = this.parseLeanCaseArms();
        } else {
          // `induction n` — auto-expand (existing behavior)
          induction = varName;
        }
      } else if (this.checkIdent("measure")) {
        this.advance();
        this.eat(TT.LPAREN);
        measure = this.parseProveExpr();
        this.eat(TT.RPAREN);
        cases = this.parseLeanCaseArms();
      } else if (this.checkIdent("wf")) {
        this.advance();
        this.eat(TT.LPAREN);
        wf = this.eatIdent();
        this.eat(TT.RPAREN);
        cases = this.parseLeanCaseArms();
      } else {
        // Plain `by` followed by case arms
        cases = this.parseLeanCaseArms();
      }
    } else {
      // Direct proof term: `:= expr`
      const body = this.parseProveExpr();
      cases = [{ pattern: "_", bindings: [], body }];
    }

    return { kind: "prove", name, params, returnType, cases, induction, measure, wf };
  }

  /** Parse a single Lean-style binder group: (x y : A), {x : A}, or [x : A] */
  private parseLeanBinderGroup(): AST.ProveParam[] {
    const implicit = this.check(TT.LBRACE) || this.check(TT.LBRACKET);
    const open = this.advance().type; // eat (, {, or [
    const close = open === TT.LBRACE ? TT.RBRACE
                : open === TT.LBRACKET ? TT.RBRACKET
                : TT.RPAREN;

    // Collect names until we see `:` or the closing bracket
    const names: string[] = [];
    while (this.check(TT.IDENT)) {
      // Peek ahead: if next is `:`, we have `name :` — stop collecting names
      const saved = this.pos;
      const nm = this.eatIdent();
      if (this.check(TT.COLON)) {
        names.push(nm);
        break;
      }
      // If next is closing bracket with no colon, these are untyped params
      if (this.check(close)) {
        names.push(nm);
        break;
      }
      names.push(nm);
    }

    let type: AST.ProveExpr | undefined;
    if (this.check(TT.COLON)) {
      this.advance();
      type = this.parseProveExpr();
    }
    this.eat(close);
    return names.map(n => ({ name: n, type, implicit }));
  }

  /** Parse Lean-style case arms: `| Pat args => body` or `| Pat(args) => body` */
  private parseLeanCaseArms(): AST.ProveCase[] {
    const cases: AST.ProveCase[] = [];
    while (this.check(TT.PIPE)) {
      this.advance();
      const pattern = this.eatIdent();
      let bindings: string[] = [];
      let deepArgs: DeepPattern[] | undefined;

      // Parenthesized bindings: | Succ(k) =>
      if (this.check(TT.LPAREN)) {
        this.advance();
        if (!this.check(TT.RPAREN))
          deepArgs = this.parseCommaList(() => this.parseDeepPattern());
        this.eat(TT.RPAREN);
      } else {
        // Space-separated bindings: | Succ k =>  (collect idents until => or ->)
        while (this.check(TT.IDENT) && !this.check(TT.FATARROW) && !this.check(TT.ARROW)) {
          bindings.push(this.eatIdent());
        }
      }

      // Accept => or -> as the arm separator
      if (this.check(TT.FATARROW)) {
        this.advance();
      } else {
        this.eat(TT.ARROW);
      }

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
      // Standard binary infix operators (+, -, *, /)
      const sym = this.tokenToNotationSymbol();
      if (sym) {
        const nota = this.notations.get(sym);
        if (nota && nota.precedence >= minPrec) {
          this.advance(); // consume operator token
          const nextPrec = nota.assoc === "left" ? nota.precedence + 1 : nota.precedence;
          const right = this.parseProveExprPrec(nextPrec);
          left = { kind: "call", name: nota.func, args: [left, right] };
          continue;
        }
      }
      // Infix mixfix: e.g. "_ :: _" or "_ ? _ : _"
      if (this.check(TT.IDENT) && this.infixMixfix.has(this.peek().value)) {
        const key = this.peek().value;
        const patterns = this.infixMixfix.get(key)!;
        let matched = false;
        for (const mx of patterns) {
          if (mx.prec < minPrec) continue;
          const result = this.tryMatchInfixMixfix(mx, left);
          if (result) { left = result; matched = true; break; }
        }
        if (matched) continue;
      }
      break;
    }
    return left;
  }

  /** Try to match a prefix mixfix pattern (starts with keyword). Returns null if no match. */
  private tryMatchMixfix(mx: ParsedMixfix): AST.ProveExpr | null {
    const save = this.pos;
    const args: AST.ProveExpr[] = [];
    for (const part of mx.parts) {
      if (part.kind === "kw") {
        if (this.check(TT.IDENT) && this.peek().value === part.value) {
          this.advance();
        } else {
          this.pos = save;
          return null;
        }
      } else {
        // hole: parse subexpression at prec 0 (delimited by next keyword or end)
        args.push(this.parseProveExprPrec(mx.prec + 1));
      }
    }
    return { kind: "call", name: mx.func, args };
  }

  /** Try to match an infix mixfix pattern (starts with _ hole). left is the already-parsed first arg. */
  private tryMatchInfixMixfix(mx: ParsedMixfix, left: AST.ProveExpr): AST.ProveExpr | null {
    const save = this.pos;
    const args: AST.ProveExpr[] = [left]; // first hole is already parsed
    // Skip first part (it's a hole, already consumed as `left`)
    for (let i = 1; i < mx.parts.length; i++) {
      const part = mx.parts[i];
      if (part.kind === "kw") {
        if (this.check(TT.IDENT) && this.peek().value === part.value) {
          this.advance();
        } else {
          this.pos = save;
          return null;
        }
      } else {
        args.push(this.parseProveExprPrec(mx.prec + 1));
      }
    }
    return { kind: "call", name: mx.func, args };
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
    // fun(x : A, body) — lambda (old syntax)
    // fun (x : A) => body — lambda (Lean syntax, typed)
    // fun x => body — lambda (Lean syntax, type inferred)
    if (this.check(TT.IDENT) && this.peek().value === "fun") {
      this.advance();
      if (this.check(TT.LPAREN)) {
        this.advance(); // eat (
        const param = this.eatIdent();
        if (this.check(TT.COLON)) {
          this.advance(); // eat :
          const paramType = this.parseProveExpr();
          if (this.check(TT.COMMA)) {
            // Old syntax: fun(x : A, body)
            this.advance(); // eat ,
            const body = this.parseProveExpr();
            this.eat(TT.RPAREN);
            return { kind: "lambda", param, paramType, body };
          } else {
            // Lean syntax: fun (x : A) => body
            this.eat(TT.RPAREN);
            if (this.check(TT.FATARROW)) this.advance();
            else this.eat(TT.ARROW); // also accept ->
            const body = this.parseProveExpr();
            return { kind: "lambda", param, paramType, body };
          }
        } else {
          // Lean syntax: fun (x) => body (type inferred)
          this.eat(TT.RPAREN);
          if (this.check(TT.FATARROW)) this.advance();
          else this.eat(TT.ARROW);
          const body = this.parseProveExpr();
          return { kind: "lambda", param, paramType: { kind: "hole" }, body };
        }
      } else {
        // Lean syntax: fun x => body
        const param = this.eatIdent();
        if (this.check(TT.FATARROW)) this.advance();
        else this.eat(TT.ARROW);
        const body = this.parseProveExpr();
        return { kind: "lambda", param, paramType: { kind: "hole" }, body };
      }
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
    // ring keyword used as tactic in prove body
    if (this.check(TT.RING)) {
      this.advance();
      return { kind: "ident", name: "ring" };
    }
    // Prefix mixfix: check if current ident starts a registered pattern
    if (this.check(TT.IDENT) && this.prefixMixfix.has(this.peek().value)) {
      const key = this.peek().value;
      const patterns = this.prefixMixfix.get(key)!;
      // Try longest pattern first (most specific match)
      for (const mx of patterns) {
        const result = this.tryMatchMixfix(mx);
        if (result) return result;
      }
    }
    // Stop at mixfix keywords — don't consume them as regular identifiers
    if (this.check(TT.IDENT) && this.mixfixKeywords.has(this.peek().value)) {
      throw new ParseError(
        `Unexpected mixfix keyword '${this.peek().value}'`,
        this.peek().line, this.peek().col,
      );
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
    // Optional sort annotation: data X : Prop { ... } or data X : Set { ... } or data X : SProp { ... }
    let sort: "Prop" | "Set" | "SProp" | undefined;
    if (this.check(TT.COLON)) {
      this.advance();
      const sortName = this.eatIdent();
      if (sortName === "Prop" || sortName === "Set" || sortName === "SProp") {
        sort = sortName;
      } else {
        throw new Error(`Expected 'Prop', 'Set', or 'SProp' after ':' in data declaration, got '${sortName}'`);
      }
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
    return { kind: "data", name, params, indices, constructors, sort };
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

  // ─── Strategy (proof primitive composition) ──────────────────────
  // strategy name = first(conv, ctx_search, rewrite)
  // Primitives: conv, ctx_search, rewrite, ground
  // Combinators: first(a, b, ...), cong(Ctor, s), cong(s), search(n)

  parseStrategyDecl(): AST.StrategyDecl {
    this.eat(TT.STRATEGY);
    const name = this.eatIdent();
    this.eat(TT.EQ);
    const body = this.parseStrategyExpr();
    return { kind: "strategy", name, body };
  }

  parseStrategyExpr(): AST.StrategyExpr {
    const tok = this.peek();
    if (tok.type === TT.NUMBER) {
      // Bare number — shouldn't appear at top level, but handle gracefully
      throw new ParseError(
        `Expected strategy expression, got number '${tok.value}'`,
        tok.line, tok.col,
      );
    }
    const name = this.eatIdent();
    // Check for combinator call: name(...)
    if (this.check(TT.LPAREN)) {
      this.advance(); // eat (
      if (name === "first") {
        const alts: AST.StrategyExpr[] = [];
        if (!this.check(TT.RPAREN)) {
          alts.push(this.parseStrategyExpr());
          while (this.check(TT.COMMA)) {
            this.advance();
            alts.push(this.parseStrategyExpr());
          }
        }
        this.eat(TT.RPAREN);
        return { kind: "first", alts };
      }
      if (name === "cong") {
        const first = this.parseStrategyExpr();
        if (this.check(TT.COMMA)) {
          // cong(Ctor, inner) — first arg is constructor name
          this.advance();
          const inner = this.parseStrategyExpr();
          this.eat(TT.RPAREN);
          if (first.kind !== "ident") {
            throw new ParseError(
              `Expected constructor name as first argument to cong`,
              tok.line, tok.col,
            );
          }
          return { kind: "cong", ctor: first.name, inner };
        }
        this.eat(TT.RPAREN);
        // cong(inner) — any constructor
        return { kind: "cong", inner: first };
      }
      if (name === "search") {
        const depthTok = this.eat(TT.NUMBER);
        this.eat(TT.RPAREN);
        return { kind: "search", depth: parseInt(depthTok.value, 10) };
      }
      if (name === "eauto") {
        const depthTok = this.eat(TT.NUMBER);
        this.eat(TT.RPAREN);
        return { kind: "eauto", depth: parseInt(depthTok.value, 10) };
      }
      // Generic named strategy with args — treat as first() for extensibility
      // (future: could be strategy application)
      throw new ParseError(
        `Unknown strategy combinator '${name}'`,
        tok.line, tok.col,
      );
    }
    // Simple identifier — primitive or strategy reference
    return { kind: "ident", name };
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
      else if (tok.type === TT.STRATEGY) body.push(this.parseStrategyDecl());
      else if (tok.type === TT.MUTUAL) body.push(this.parseMutualDecl());
      else if (tok.type === TT.SECTION) body.push(this.parseSectionDecl());
      else if (tok.type === TT.NOTATION) body.push(this.parseNotationDecl());
      else if (tok.type === TT.COERCION) body.push(this.parseCoercionDecl());
      else if (tok.type === TT.SETOID) body.push(this.parseSetoidDecl());
      else if (tok.type === TT.RING) body.push(this.parseRingDecl());
      else if (tok.type === TT.IDENT && tok.value === "field") body.push(this.parseFieldDecl());
      else if (tok.type === TT.IDENT && tok.value === "scope") body.push(this.parseScopeDecl());
      else if (tok.type === TT.CLASS) body.push(this.parseClassDecl());
      else if (tok.type === TT.INSTANCE) body.push(this.parseInstanceDecl());
      else if (tok.type === TT.HINT) body.push(this.parseHintDecl());
      else if (tok.type === TT.CANONICAL) body.push(this.parseCanonicalDecl());
      else if (tok.type === TT.PROGRAM) body.push(this.parseProgramDecl());
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
    // Detect mixfix patterns (contain "_" holes)
    const parts = symbol.split(/\s+/).filter(s => s.length > 0);
    const hasHoles = parts.includes("_");
    if (hasHoles) {
      const parsed: MixfixPart[] = parts.map(p => p === "_" ? { kind: "hole" as const } : { kind: "kw" as const, value: p });
      const mx: ParsedMixfix = { parts: parsed, func, prec: precedence };
      if (parsed[0].kind === "kw") {
        // Prefix mixfix: e.g. "if _ then _ else _"
        const key = parsed[0].value;
        if (!this.prefixMixfix.has(key)) this.prefixMixfix.set(key, []);
        this.prefixMixfix.get(key)!.push(mx);
      } else if (parsed.length >= 2 && parsed[1].kind === "kw") {
        // Infix mixfix: e.g. "_ :: _" or "_ ? _ : _"
        const key = parsed[1].value;
        if (!this.infixMixfix.has(key)) this.infixMixfix.set(key, []);
        this.infixMixfix.get(key)!.push(mx);
      }
      // Register all keyword parts so they stop expression parsing
      for (const p of parsed) {
        if (p.kind === "kw") this.mixfixKeywords.add(p.value);
      }
    } else {
      this.notations.set(symbol, { func, precedence, assoc });
    }
    return { kind: "notation", symbol, func, precedence, assoc };
  }

  // ─── Setoid ──────────────────────────────────────────────────────
  // setoid R on T { refl = r, sym = s, trans = t }

  parseSetoidDecl(): AST.SetoidDecl {
    this.eat(TT.SETOID);
    const name = this.eatIdent();
    this.eatIdentValue("on");
    const type = this.eatIdent();
    this.eat(TT.LBRACE);
    let refl: string | null = null;
    let sym: string | null = null;
    let trans: string | null = null;
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const key = this.eatIdent();
      this.eat(TT.EQ);
      const val = this.eatIdent();
      if (key === "refl") refl = val;
      else if (key === "sym") sym = val;
      else if (key === "trans") trans = val;
      else throw new ParseError(`Unknown setoid field '${key}', expected refl/sym/trans`, this.prev().line, this.prev().col);
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RBRACE);
    if (!refl || !sym || !trans) {
      throw new ParseError("setoid must declare refl, sym, and trans", this.prev().line, this.prev().col);
    }
    return { kind: "setoid", name, type, refl, sym, trans };
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

  // ─── Ring ────────────────────────────────────────────────────────
  // ring T { zero = Z, add = f, mul = g }

  parseRingDecl(): AST.RingDecl {
    this.eat(TT.RING);
    const type = this.eatIdent();
    this.eat(TT.LBRACE);
    let zero: string | null = null;
    let one: string | null = null;
    let add: string | null = null;
    let mul: string | null = null;
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const key = this.eatIdent();
      this.eat(TT.EQ);
      const val = this.eatIdent();
      if (key === "zero") zero = val;
      else if (key === "one") one = val;
      else if (key === "add") add = val;
      else if (key === "mul") mul = val;
      else throw new ParseError(`Unknown ring field '${key}', expected zero/one/add/mul`, this.prev().line, this.prev().col);
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RBRACE);
    if (!zero || !add || !mul) {
      throw new ParseError("ring must declare zero, add, and mul", this.prev().line, this.prev().col);
    }
    return { kind: "ring", type, zero, add, mul, ...(one ? { one } : {}) };
  }

  // ─── Field ───────────────────────────────────────────────────────
  // field T { zero = Z, one = O, add = f, mul = g, neg = h, inv = i }

  parseFieldDecl(): AST.FieldDecl {
    this.eatIdentValue("field");
    const type = this.eatIdent();
    this.eat(TT.LBRACE);
    let zero: string | null = null;
    let one: string | null = null;
    let add: string | null = null;
    let mul: string | null = null;
    let neg: string | null = null;
    let inv: string | null = null;
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const key = this.eatIdent();
      this.eat(TT.EQ);
      const val = this.eatIdent();
      if (key === "zero") zero = val;
      else if (key === "one") one = val;
      else if (key === "add") add = val;
      else if (key === "mul") mul = val;
      else if (key === "neg") neg = val;
      else if (key === "inv") inv = val;
      else throw new ParseError(`Unknown field field '${key}', expected zero/one/add/mul/neg/inv`, this.prev().line, this.prev().col);
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RBRACE);
    if (!zero || !one || !add || !mul || !neg || !inv) {
      throw new ParseError("field must declare zero, one, add, mul, neg, and inv", this.prev().line, this.prev().col);
    }
    return { kind: "field", type, zero, one, add, mul, neg, inv };
  }

  // ─── Scope (notation scoping) ────────────────────────────────────
  // scope "name" { ... }

  parseScopeDecl(): AST.ScopeDecl {
    this.eatIdentValue("scope");
    const name = this.eat(TT.STRING).value;
    // Save parser notation state
    const savedNotations = new Map(this.notations);
    const savedPrefixMixfix = new Map(this.prefixMixfix);
    const savedInfixMixfix = new Map(this.infixMixfix);
    const savedMixfixKeywords = new Set(this.mixfixKeywords);
    const body = this.parseSystemBody();
    // Restore parser notation state — scope notations don't leak
    this.notations = savedNotations;
    this.prefixMixfix = savedPrefixMixfix;
    this.infixMixfix = savedInfixMixfix;
    this.mixfixKeywords = savedMixfixKeywords;
    return { kind: "scope", name, body };
  }

  // ─── Class (typeclass declaration) ───────────────────────────────
  // class Show(A) { show : A -> String }

  parseClassDecl(): AST.ClassDecl {
    this.eat(TT.CLASS);
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
    const methods: AST.DataField[] = [];
    if (!this.check(TT.RBRACE)) {
      methods.push(...this.parseCommaList(() => {
        const fieldName = this.eatIdent();
        this.eat(TT.COLON);
        const fieldType = this.parseProveExpr();
        return { name: fieldName, type: fieldType };
      }));
    }
    this.eat(TT.RBRACE);
    return { kind: "class", name, params, methods };
  }

  // ─── Instance (typeclass implementation) ─────────────────────────
  // instance Show(Nat) { show = showNat }

  parseInstanceDecl(): AST.InstanceDecl {
    this.eat(TT.INSTANCE);
    const className = this.eatIdent();
    const args: string[] = [];
    if (this.check(TT.LPAREN)) {
      this.advance();
      if (!this.check(TT.RPAREN)) {
        this.parseCommaList(() => {
          const a = this.eatIdent();
          args.push(a);
          return a;
        });
      }
      this.eat(TT.RPAREN);
    }
    this.eat(TT.LBRACE);
    const methods: { name: string; value: string }[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const key = this.eatIdent();
      this.eat(TT.EQ);
      const val = this.eatIdent();
      methods.push({ name: key, value: val });
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RBRACE);
    return { kind: "instance", className, args, methods };
  }

  // canonical Name : StructName { field = value, ... }
  parseCanonicalDecl(): AST.CanonicalDecl {
    this.eat(TT.CANONICAL);
    const name = this.eatIdent();
    this.eat(TT.COLON);
    const structName = this.eatIdent();
    this.eat(TT.LBRACE);
    const fields: { name: string; value: string }[] = [];
    while (!this.check(TT.RBRACE) && !this.check(TT.EOF)) {
      const key = this.eatIdent();
      this.eat(TT.EQ);
      const val = this.eatIdent();
      fields.push({ name: key, value: val });
      if (this.check(TT.COMMA)) this.advance();
    }
    this.eat(TT.RBRACE);
    return { kind: "canonical", name, structName, fields };
  }

  // hint auto : lemmaName
  parseHintDecl(): AST.HintDecl {
    this.eat(TT.HINT);
    const db = this.eatIdent();
    this.eat(TT.COLON);
    const lemma = this.eatIdent();
    return { kind: "hint", db, lemma };
  }

  // @[simp] or @[simp, auto] — comma-separated attribute names in brackets
  parseAttributes(): string[] {
    this.eat(TT.AT);
    this.eat(TT.LBRACKET);
    const attrs: string[] = [this.eatIdent()];
    while (this.check(TT.COMMA)) {
      this.advance();
      attrs.push(this.eatIdent());
    }
    this.eat(TT.RBRACKET);
    return attrs;
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
