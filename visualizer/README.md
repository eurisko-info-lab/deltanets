# Delta-Nets Visualizer

A dependent type theory prover built on interaction nets, with an interactive
web visualizer. ~21k LoC TypeScript, 1086 tests, ~92% Rocq surface parity.

Built with [Deno](https://deno.com/), [Fresh](https://fresh.deno.dev/),
Preact, and D3.js.

## Quick Start

```
deno task start     # Development server with hot reload
deno task test      # Run all 1086 tests
deno task build     # Production build
```

| Command                | Purpose                                     |
| ---------------------- | ------------------------------------------- |
| `deno task start`      | Development server with hot reload           |
| `deno task build`      | Production build                             |
| `deno task preview`    | Preview production build                     |
| `deno task check`      | Run formatter, linter, and type checker      |
| `deno task test`       | Run all tests                                |
| `deno task test:core`  | Core package tests only                      |
| `deno task test:lang`  | Lang package tests only                      |

## Architecture

Deno workspace with five packages:

```
packages/
  core/           @deltanets/core — interaction net types, graph ops, reductions
    types.ts        Node, Graph, Redex, InteractionSystem, TreeSystem
    graph.ts        link(), reciprocal() graph primitives
    reductions.ts   Universal reductions: annihilate, erase, commute
    ast.ts          AST types, parser invocation, expression classification
    util.ts         Exhaustive match(), branded Mut<T> type
    typechecker.ts  Simply-typed lambda calculus type checker
    systems/
      lambdacalc.ts   Tree-based λ-calculus system
      deltanets/      Δ-net interaction system (build, readback, redexes, custom rules)
  lang/           @deltanets/lang — .inet and .iview language compilers
    core/           .inet compiler (lexer → parser → evaluator → type checker)
      types.ts          AST: DataDecl, ComputeDecl, ProveDecl, ProveExpr, …
      lexer.ts          Tokenizer with DATA, COMPUTE, PROVE keywords
      parser.ts         Recursive descent parser for all .inet declarations
      evaluator.ts      Top-level evaluation: include resolution, system building
      eval-system.ts    System evaluation: desugar data/prove, build compute rules
      typecheck-prove.ts  Dependent type checker for prove blocks + proof trees
      normalize.ts      Types, substitution, equality, normalization engine
      termination.ts    Termination/productivity/exhaustiveness checking
      desugar.ts        Data/record/codata desugaring, evalAgent
      extract.ts        Code extraction to TypeScript/JS
    view/           .iview compiler (lexer → parser → evaluator)
    bridge.ts       Connects .inet compilation to the visualizer
  render/         @deltanets/render — SVG rendering primitives and agents
    core.ts         Node2D scene tree, bounds, SVG helpers
    primitives.ts   Drawing primitives (circles, triangles, etc.)
    proof-tree.ts   Natural-deduction proof tree renderer
    lanes.ts        Lane view renderer (swimlanes, staves, timelines)
    music.ts        Music notation renderer (noteheads, clefs, staves)
    agents/         Per-agent SVG renderers (enclosure, replicator, wire, etc.)
  methods/        @deltanets/methods — reduction method registry + render pipelines
    lambdacalc.ts   Tree-stepping method with render
    deltanets/      Graph-stepping method with render pipeline
  tests/          @deltanets/tests — 69 test files, 1086 tests
    helpers.ts      System fixtures, compile/reduce helpers
    *_test.ts       Per-feature tests (nat, bool, list, eq, dep_types, …)

islands/            Main app shell (App.tsx) + SVG canvas (Graph.tsx)
components/         Toolbar controls: examples, method, stepping, playback, settings
hooks/              Extracted effects: editor init, scene rendering, layout
lib/
  appState.ts       Central reactive state (Preact signals)
  audio.ts          Web Audio playback engine with note highlighting
  config.ts         Shared constants and storage keys
  examples.ts       Example file loader
```

**Data flow:** Source text → `updateAst()` → AST / Graph / Lane View →
method `init()` → method `render()` → `Node2D` scene tree → D3 SVG.

## Type Theory Features

The `.inet` language implements a dependent type theory with ~92% Rocq
surface feature coverage:

- **CIC core:** Pi, Sigma, Let, Lambda, Match — full dependent types
- **Inductive types:** parameterized, indexed, mutual, with auto-generated eliminators
- **Coinductive types:** `codata` with guard agents and productivity checking
- **Record types:** primitive projections with definitional eta
- **Universe hierarchy:** `Type(0) : Type(1) : …`, impredicative Prop + SProp, cumulative
- **Pattern matching:** nested deep patterns, with-clauses, overlap detection
- **Termination:** structural recursion, `{measure}`, `{wf}`
- **Implicit arguments:** `{x : A}` with unification-based inference
- **Unification:** first-order + Miller's pattern fragment (higher-order)
- **Module system:** system/extend/compose/open/export + functors
- **Sections & variables:** auto-abstraction over section variables
- **Notations:** full mixfix with underscores
- **Coercions, canonical structures, typeclasses**
- **Tactics:** assumption, simp, decide, omega, auto, calc, conv, rewrite, ring
- **Tactic combinators:** first/then/try/repeat/all — user-defined tactics via `tactic` blocks
- **Strategy declarations:** compile to real INet agents (Ok/Fail/Gate protocol)
- **Quotation & reflection:** quote/unquote + term-encoding agents
- **Setoid rewriting, hint databases, definitional equality**
- **Program/Equations:** dependent matching with obligations
- **Interactive proof mode:** step-through with hole suggestions
- **Bytecode VM:** fast normalization with caching
- **Code extraction:** to TypeScript/JS
- **Standard library:** Nat, Bool, Eq, Option, List, Sigma

## Reduction Methods

- **Lambda Calculus (tree):** β-reduction with substitution, step-through.
- **Delta-Nets (graph):** Compiles λ-terms to interaction nets, reduces via
  annihilation, erasure, and commutation. Supports all four substructural
  systems: Linear (L), Affine (A), Relevant (I), and Full (K).

## The .inet Language

Define custom interaction net systems with agents, rules, modes, definitions,
and graphs:

```inet
system "Example" {
  agent abs(principal, body, bind)
  agent app(func, result, arg)
  agent era(principal)

  rule abs <> app -> annihilate
  rule abs <> era -> erase

  mode linear = { -era }
}

def I = \x.x
graph identity = term I
```

### Data Types

```inet
data Nat {
  | Zero
  | Succ(pred : Nat)
}

data List {
  | Nil
  | Cons(head : Nat, tail : List)
}
```

### Compute Rules

```inet
compute add(Zero, y) = y
compute add(Succ(k), y) = Succ(add(k, y))
```

### Proofs

```inet
prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
  | Zero -> refl
  | Succ(k) -> cong_succ(plus_zero_right(k))
}

prove plus_comm(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
  | Zero -> sym(plus_zero_right(m))
  | Succ(k) -> trans(cong_succ(plus_comm(k, m)), sym(plus_succ_right(m, k)))
}
```

Proof constructs: `refl`, `sym`, `trans`, `cong_X`, `subst`, `pair`/`fst`/`snd`,
`exact`, `apply`, `rewrite`, `assumption`, and recursive inductive-hypothesis calls.

### Visual Presentation (.iview)

```
theme dark {
  background: #1e1e1e
  text: #e0e0e0
}

render abs {
  shape: fan(down)
  fill: level-color
}
```

## Lane Views

The `lanes` block defines swim-lane diagrams, timelines, or music staves.
Lanes with a `clef` property render as music notation with noteheads, stems,
flags, accidentals, and ledger lines. A play button appears for audio playback
via Web Audio API with real-time note highlighting.

## Keyboard Shortcuts

| Key        | Action                                   |
| ---------- | ---------------------------------------- |
| `→`        | Step forward (reduce or advance history) |
| `←`        | Step backward in history                 |
| `Shift+→`  | Jump to last step                        |
| `Shift+←`  | Jump to first step                       |
| `\`        | Insert λ symbol in the editor            |

## Lambda Parser

The λ-calculi parser in [`packages/core/parser.gen.ts`](packages/core/parser.gen.ts)
was generated using [tsPEG](https://www.npmjs.com/package/tspeg) (3.3.1) from
[`packages/core/lambda.grammar`](packages/core/lambda.grammar).

```
npm install -g tspeg
tspeg packages/core/lambda.grammar packages/core/parser.gen.ts
```
