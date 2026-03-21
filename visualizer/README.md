# Delta-Nets and λ-Calculi Interactive Visualizer

An interactive web visualizer for Δ-nets (interaction nets) and λ-calculus
expressions. Built with [Fresh](https://fresh.deno.dev/) (Deno), Preact, and
D3.js.

## Usage

Start the development server:

```
deno task start
```

This watches the project directory and restarts on changes. Other tasks:

| Command               | Purpose                                 |
| --------------------- | --------------------------------------- |
| `deno task start`     | Development server with hot reload      |
| `deno task build`     | Production build                        |
| `deno task preview`   | Preview production build                |
| `deno task check`     | Run formatter, linter, and type checker |
| `deno task test`      | Run all tests                           |
| `deno task test:core` | Run core package tests only             |
| `deno task test:lang` | Run lang package tests only             |

## Keyboard Shortcuts

| Key       | Action                                   |
| --------- | ---------------------------------------- |
| `→`       | Step forward (reduce or advance history) |
| `←`       | Step backward in history                 |
| `Shift+→` | Jump to last step                        |
| `Shift+←` | Jump to first step                       |
| `\`       | Insert λ symbol in the editor            |

## Architecture

The project is organized as a Deno workspace with four packages:

```
packages/
  core/                  ← @deltanets/core: interaction net types, graph ops, reductions
    types.ts             ← Node, Graph, Redex, InteractionSystem, TreeSystem
    graph.ts             ← link(), reciprocal() graph primitives
    reductions.ts        ← Universal reductions: annihilate, erase, commute
    ast.ts               ← AST types, parser invocation, expression classification
    typechecker.ts       ← Simply-typed lambda calculus type checker
    systems/
      lambdacalc.ts      ← Tree-based λ-calculus system
      deltanets/         ← Δ-net interaction system (build, readback, redexes)
  lang/                  ← @deltanets/lang: .inet and .iview language compilers
    core/                ← .inet compiler (lexer → parser → evaluator)
    view/                ← .iview compiler (lexer → parser → evaluator)
    bridge.ts            ← Connects .inet compilation to the visualizer
    examples/            ← Example .inet and .iview files
  render/                ← @deltanets/render: SVG rendering primitives and agents
    core.ts              ← Node2D scene tree, bounds, SVG helpers
    primitives.ts        ← Drawing primitives (circles, triangles, etc.)
    agents/              ← Per-agent SVG renderers (enclosure, replicator, wire, etc.)
    lanes.ts             ← Lane view renderer (swimlanes, staves, timelines)
    music.ts             ← Music notation renderer (noteheads, clefs, staves)
  methods/               ← @deltanets/methods: reduction method registry
    index.ts             ← Method registry (lambdacalc, deltanets)
    lambdacalc.ts        ← Tree-stepping method with render
    deltanets/           ← Graph-stepping method with render pipeline

islands/App.tsx          ← Main app shell, composes editor + graph + toolbar
islands/Graph.tsx        ← SVG canvas with pan/zoom/drag (D3)
components/Toolbar.tsx   ← Controls: examples, method, stepping, playback, settings
hooks/                   ← Extracted effects: editor init, scene rendering, layout
lib/
  appState.ts            ← Central reactive state (Preact signals)
  audio.ts               ← Web Audio playback engine with note highlighting
  config.ts              ← Shared constants and storage keys
```

**Data flow:** Source text → `updateAst()` → AST / Graph / Lane View →
method `init()` → method `render()` → `Node2D` scene tree → D3 SVG.

For lane views (music, swimlanes): Source text → `applyLaneView()` →
`renderLaneView()` → `Node2D` scene tree → D3 SVG. Playback:
`playLaneView()` → Web Audio scheduling + RAF highlight loop.

## Reduction Methods

- **Lambda Calculus (tree):** Operates directly on the AST using β-reduction
  with substitution. Supports stepping through reductions.
- **Delta-Nets (graph):** Compiles λ-terms to interaction nets, then reduces via
  annihilation, erasure, and commutation rules. Supports all four substructural
  systems: Linear (L), Affine (A), Relevant (I), and Full (K).

## Lane Views

The `lanes` block defines swim-lane diagrams, timelines, or music staves:

```
lanes "Ode to Joy" {
  lane "Treble" { clef: "treble", lines: 5 }

  at 0 "Treble" place "E4" duration 1
  at 1 "Treble" place "E4" duration 1
  at 2 "Treble" place "F4" duration 1
  at 3 "Treble" place "G4" duration 1

  bar 0
  bar 4
}
```

Lanes with a `clef` property (treble, bass, alto) render as music staves with
noteheads, stems, flags, accidentals, and ledger lines. A play button appears
in the toolbar for music views — clicking it plays the notes via Web Audio API
with real-time note highlighting.

## The .inet Language

The `.inet` format defines custom interaction net systems with agents, rules,
modes, and graphs:

```
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

The `.iview` format defines visual presentation (themes, agent styles, wire
styles, palettes):

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

See `packages/lang/examples/` for complete examples.

## Tests

```
deno task test        # All tests
deno task test:core   # Core package (reductions, readback, build, redexes, typechecker)
deno task test:lang   # Lang package (compiler, examples, lanes, music)
```

## About the λ-calculi parser

The λ-calculi parser in [`lib/parser.gen.ts`](lib/parser.gen.ts) was generated
using [tsPEG](https://www.npmjs.com/package/tspeg) (3.3.1) based on the grammar
in [`lib/lambda.grammar`](lib/lambda.grammar).

```
npm install -g tspeg
tspeg lib/lambda.grammar lib/parser.gen.ts
```
