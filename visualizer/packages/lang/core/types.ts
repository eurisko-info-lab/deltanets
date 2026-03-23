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
  | RecordDecl
  | CodataDecl
  | ComputeDecl
  | TacticDecl
  | MutualDecl
  | SectionDecl
  | NotationDecl
  | CoercionDecl
  | SetoidDecl;

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
export type SystemBody = AgentDecl | RuleDecl | ModeDecl | ProveDecl | DataDecl | RecordDecl | CodataDecl | ComputeDecl | OpenDecl | ExportDecl | TacticDecl | MutualDecl | SectionDecl | NotationDecl | CoercionDecl | SetoidDecl;

// open "SystemName" — import all agents/rules from another system
// open "SystemName" use AgentA, AgentB — selective import
export type OpenDecl = {
  kind: "open";
  system: string;
  names?: string[]; // undefined = import all, string[] = selective
};

// export AgentA, AgentB — restrict visible agents for extend/open consumers
export type ExportDecl = {
  kind: "export";
  names: string[];
};

// section "name" { variable(A : Type) ... declarations ... }
// Variables are auto-abstracted as implicit params on enclosed proves.
export type SectionDecl = {
  kind: "section";
  name: string;
  variables: SectionVariable[];
  body: SystemBody[];
};

export type SectionVariable = {
  name: string;
  type: ProveExpr;
};

// notation "x + y" := add(x, y) (prec 50, left)
// Desugars infix operator into function call at parse time.
export type NotationDecl = {
  kind: "notation";
  symbol: string; // operator character, e.g. "+"
  func: string; // expansion function name, e.g. "add"
  precedence: number;
  assoc: "left" | "right";
};

// coercion name = From -> To via func
// Registers an implicit type conversion for the type checker.
export type CoercionDecl = {
  kind: "coercion";
  name: string;
  from: string;
  to: string;
  func: string;
};

// setoid R on T { refl = r, sym = s, trans = t }
// Registers a binary relation as an equivalence relation (setoid).
export type SetoidDecl = {
  kind: "setoid";
  name: string;  // relation name (binary agent already declared)
  type: string;  // domain type name
  refl: string;  // reflexivity proof name
  sym: string;   // symmetry proof name
  trans: string;  // transitivity proof name
};

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
  measure?: ProveExpr; // {measure expr} — well-founded recursion via measure function
  wf?: string; // {wf R} — well-founded recursion via named relation (trusted)
};

export type ProveParam = {
  name: string;
  type?: ProveExpr; // optional type annotation (e.g., Nat)
  implicit?: boolean; // true if wrapped in {braces} — inferred, not an agent port
};

/** The first explicit (non-implicit) parameter — the induction variable. */
export function inductionParam(params: ProveParam[]): ProveParam | undefined {
  return params.find((p) => !p.implicit);
}

/** All explicit (non-implicit) parameters after the induction variable. */
export function auxParams(params: ProveParam[]): ProveParam[] {
  const idx = params.findIndex((p) => !p.implicit);
  return idx < 0 ? [] : params.slice(idx + 1).filter((p) => !p.implicit);
}

export type ProveCase = {
  pattern: string; // constructor name (Zero, Succ, ...)
  bindings: string[]; // bound variables from the constructor (e.g., k in Succ(k))
  body: ProveExpr;
};

export type ProveExpr =
  | { kind: "ident"; name: string } // variable reference or nullary agent
  | { kind: "call"; name: string; args: ProveExpr[] } // agent application
  | { kind: "hole" } // unfilled goal placeholder (?)
  | { kind: "match"; scrutinee: string; cases: ProveCase[] } // nested case analysis
  | { kind: "let"; name: string; value: ProveExpr; body: ProveExpr } // let x = e in body
  | { kind: "pi"; param: string; domain: ProveExpr; codomain: ProveExpr } // forall(x : A, B)
  | { kind: "sigma"; param: string; domain: ProveExpr; codomain: ProveExpr } // exists(x : A, B)
  | { kind: "lambda"; param: string; paramType: ProveExpr; body: ProveExpr } // fun(x : A, body)
  | { kind: "metavar"; id: number }; // unification variable ?id

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

export type MetaAction = {
  kind: "meta";
  handler: import("@deltanets/core").MetaHandler;
};

export type RuleAction =
  | BuiltinAction
  | CustomAction
  | MetaAction;

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
  indices: DataIndex[];  // value indices (e.g., [{ name: "n", type: Nat }] for Vec(A, n : Nat))
  constructors: DataConstructor[];
};

export type DataIndex = {
  name: string;
  type: ProveExpr;
};

export type DataConstructor = {
  name: string;
  fields: DataField[];
  returnIndices?: ProveExpr[];  // specific index values for this constructor (e.g., [Zero] for VNil)
};

export type DataField = {
  name: string;
  type: ProveExpr;
};

// ─── Record declaration (single-constructor data type with projections) ──
// Sugar for a data type with one constructor + projection functions.
//
//   record Pair(A, B) { fst : A, snd : B }
// Desugars to:
//   data Pair(A, B) { | mkPair(fst : A, snd : B) }
//   compute fst(mkPair(x, y)) = x
//   compute snd(mkPair(x, y)) = y

// ─── Mutual declaration (mutual inductive types / mutual proofs) ──
// Groups multiple data or prove declarations for mutual references.
//
//   mutual {
//     data Even { | EZero | ESucc(pred : Odd) }
//     data Odd { | OSucc(pred : Even) }
//   }

export type MutualDecl = {
  kind: "mutual";
  data: DataDecl[];
  proves: ProveDecl[];
};

export type RecordDecl = {
  kind: "record";
  name: string;
  params: string[];
  fields: DataField[];
};

// ─── Coinductive data declaration ──────────────────────────────────
// Dual of data: defined by observations (destructors) rather than
// constructors. Allows self-reference in field types (guarded corecursion).
//
//   codata Stream(A) { head : A, tail : Stream(A) }
// Desugars to:
//   agent guard_stream(principal, head, tail)  — the "constructor" (guard)
//   agent head(principal, result)               — observation agent
//   agent tail(principal, result)               — observation agent
//   rule head <> guard_stream → relink result to head field
//   rule tail <> guard_stream → relink result to tail field
//   compute head(guard_stream(h, t)) = h
//   compute tail(guard_stream(h, t)) = t

export type CodataDecl = {
  kind: "codata";
  name: string;
  params: string[];
  fields: DataField[];
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

// ─── Tactic declaration (user-definable proof tactics) ─────────────
// Defines a named tactic with its own agents and interaction rules.
//
//   tactic my_simp {
//     rule my_simp <> TmApp -> { ... }
//   }
//
// The tactic name is auto-declared as an agent with (principal, result) ports.

export type TacticDecl = {
  kind: "tactic";
  name: string;
  body: (AgentDecl | RuleDecl)[];
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
