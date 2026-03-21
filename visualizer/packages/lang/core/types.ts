// ═══════════════════════════════════════════════════════════════════
// INet Core Language — AST Types
// Describes interaction net systems: agents, rules, modes, graphs.
// ═══════════════════════════════════════════════════════════════════

export type Program = Statement[];

export type Statement =
  | SystemDecl
  | ExtendDecl
  | ComposeDecl
  | AgentDecl
  | RuleDecl
  | ModeDecl
  | GraphDecl
  | DefDecl
  | IncludeDecl
  | LanesDecl;

// system "name" { agent..., rule..., mode... }
export type SystemDecl = {
  kind: "system";
  name: string;
  body: (AgentDecl | RuleDecl | ModeDecl)[];
};

// system "B" extend "A" { agent..., rule..., mode... }
export type ExtendDecl = {
  kind: "extend";
  name: string; // new system name
  base: string; // system to extend
  body: (AgentDecl | RuleDecl | ModeDecl)[];
};

// system "C" = compose "A" + "B" { rule... }
// The pushout: union agents from A and B, union rules, add cross-rules
export type ComposeDecl = {
  kind: "compose";
  name: string; // new system name
  components: string[]; // systems to compose (≥2)
  body: (AgentDecl | RuleDecl | ModeDecl)[]; // cross-interaction rules
};

// agent name(port, port, ..variadicPort)
export type AgentDecl = {
  kind: "agent";
  name: string;
  ports: PortDef[];
};

export type PortDef = {
  name: string;
  variadic: boolean;
};

// rule agentA <> agentB -> action
export type RuleDecl = {
  kind: "rule";
  agentA: string;
  agentB: string;
  action: RuleAction;
};

export type RuleAction =
  | BuiltinAction
  | CustomAction;

export type BuiltinAction = {
  kind: "builtin";
  name: "annihilate" | "erase" | "commute" | "aux-fan";
};

export type CustomAction = {
  kind: "custom";
  body: RuleStmt[];
};

export type RuleStmt = LetStmt | WireStmt | RelinkStmt | EraseStmt;

// let name = AgentType ["label"]
export type LetStmt = {
  kind: "let";
  varName: string;
  agentType: string;
  label?: string;
};

// wire portRef -- portRef
export type WireStmt = {
  kind: "wire";
  portA: PortRef;
  portB: PortRef;
};

// relink portRef portRef
export type RelinkStmt = {
  kind: "relink";
  portA: PortRef;
  portB: PortRef;
};

// erase portRef
export type EraseStmt = {
  kind: "erase-stmt";
  port: PortRef;
};

export type PortRef = {
  node: string; // variable name, or "left"/"right" in rule bodies
  port: string; // named port or numeric index
};

// mode name = { -agent1, -agent2 }
export type ModeDecl = {
  kind: "mode";
  name: string;
  exclude: string[];
};

// graph name = term <lambda-expr>
// graph name { let..., wire... }
export type GraphDecl =
  | GraphFromTerm
  | GraphExplicit;

export type GraphFromTerm = {
  kind: "graph";
  name: string;
  term: LamExpr;
};

export type GraphExplicit = {
  kind: "graph-explicit";
  name: string;
  body: (LetStmt | WireStmt)[];
};

// def name = <lambda-expr>
export type DefDecl = {
  kind: "def";
  name: string;
  expr: LamExpr;
};

// include "path"
export type IncludeDecl = {
  kind: "include";
  path: string;
};

// ─── Lane declarations ─────────────────────────────────────────────

// lanes "name" { lane... at... bar... link... }
export type LanesDecl = {
  kind: "lanes";
  name: string;
  body: LaneStmt[];
};

export type LaneStmt =
  | LaneDef
  | LaneItem
  | LaneMarker
  | LaneLink;

// lane "name" { key: value, ... }
export type LaneDef = {
  kind: "lane-def";
  name: string;
  props: Record<string, string | number>;
};

// at <pos> "lane" place "label" [duration <n>]
export type LaneItem = {
  kind: "lane-item";
  position: number;
  lane: string;
  label: string;
  duration: number; // 0 = point event
};

// bar <pos> ["label"]
export type LaneMarker = {
  kind: "lane-marker";
  position: number;
  label?: string;
};

// link "from" -> "to" ["label"]
export type LaneLink = {
  kind: "lane-link";
  from: string;
  to: string;
  label?: string;
};

// Lambda calculus expressions
export type LamExpr =
  | LamAbs
  | LamApp
  | LamVar;

export type LamAbs = {
  kind: "lam";
  param: string;
  typeAnnotation?: TypeExpr;
  body: LamExpr;
};

export type LamApp = {
  kind: "app";
  func: LamExpr;
  arg: LamExpr;
};

export type LamVar = {
  kind: "var";
  name: string;
};

// Type expressions for annotations
export type TypeExpr =
  | TypeBase
  | TypeArrow
  | TypeHole;

export type TypeBase = {
  kind: "type-base";
  name: string;
};

export type TypeArrow = {
  kind: "type-arrow";
  from: TypeExpr;
  to: TypeExpr;
};

export type TypeHole = {
  kind: "type-hole";
};
