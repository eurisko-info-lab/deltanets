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
  | LanesDecl
  | ProveDecl
  | DataDecl
  | ComputeDecl;

// system "name" { agent..., rule..., mode... }
export type SystemDecl = {
  kind: "system";
  name: string;
  body: SystemBody[];
};

// system "B" extend "A" { agent..., rule..., mode... }
export type ExtendDecl = {
  kind: "extend";
  name: string; // new system name
  base: string; // system to extend
  body: SystemBody[];
};

// system "C" = compose "A" + "B" { rule... }
// The pushout: union agents from A and B, union rules, add cross-rules
export type ComposeDecl = {
  kind: "compose";
  name: string; // new system name
  components: string[]; // systems to compose (≥2)
  body: SystemBody[]; // cross-interaction rules
};

// Items allowed inside a system body
export type SystemBody = AgentDecl | RuleDecl | ModeDecl | ProveDecl | DataDecl | ComputeDecl;

// prove name(param [: Type], ...) [-> Proposition] { | Constructor -> expr ... }
// Desugars into an AgentDecl + RuleDecl[] during evaluation.
// Optional type annotations enable dependent type checking.
export type ProveDecl = {
  kind: "prove";
  name: string;
  params: ProveParam[]; // first = principal (induction var), rest = aux ports
  returnType?: ProveExpr; // optional: the proposition being proved
  cases: ProveCase[];
  induction?: string; // if set, auto-expand cases for this variable's type
};

export type ProveParam = {
  name: string;
  type?: ProveExpr; // optional type annotation (e.g., Nat)
};

export type ProveCase = {
  pattern: string; // constructor name (Zero, Succ, ...)
  bindings: string[]; // bound variables from the constructor (e.g., k in Succ(k))
  body: ProveExpr;
};

export type ProveExpr =
  | { kind: "ident"; name: string } // variable reference or nullary agent
  | { kind: "call"; name: string; args: ProveExpr[] } // agent application
  | { kind: "hole" } // unfilled goal placeholder (?)
  | { kind: "match"; scrutinee: string; cases: ProveCase[] }; // nested case analysis

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

// ─── Data declaration (syntactic sugar) ────────────────────────────
// Desugars into constructor AgentDecl[] + duplicator AgentDecl + RuleDecl[].
//
//   data Nat {
//     | Zero
//     | Succ(pred : Nat)
//   }

export type DataDecl = {
  kind: "data";
  name: string;
  params: string[];  // type parameters (e.g., ["A"] for List(A))
  constructors: DataConstructor[];
};

export type DataConstructor = {
  name: string;
  fields: DataField[];
};

export type DataField = {
  name: string;
  type: ProveExpr;
};

// ─── Compute declaration (type-level reduction rules) ──────────────
// Declares a computational equation for the type checker's normalizer.
//
//   compute add(Zero, y) = y
//   compute add(Succ(k), y) = Succ(add(k, y))

export type ComputeDecl = {
  kind: "compute";
  funcName: string;
  args: ComputePattern[];
  result: ProveExpr;
};

export type ComputePattern =
  | { kind: "var"; name: string }
  | { kind: "ctor"; name: string; args: string[] };

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
