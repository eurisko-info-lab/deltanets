# Delta-Nets and λ-Calculi Interactive Visualizer

An interactive web visualizer for Δ-nets (interaction nets) and λ-calculus expressions. Built with [Fresh](https://fresh.deno.dev/) (Deno), Preact, and D3.js.

## Usage

Start the development server:

```
deno task start
```

This watches the project directory and restarts on changes. Other tasks:

| Command | Purpose |
|---------|---------|
| `deno task start` | Development server with hot reload |
| `deno task build` | Production build |
| `deno task preview` | Preview production build |
| `deno task check` | Run formatter, linter, and type checker |

## Keyboard Shortcuts

| Key | Action |
|-----|--------|
| `→` | Step forward (reduce or advance history) |
| `←` | Step backward in history |
| `Shift+→` | Jump to last step |
| `Shift+←` | Jump to first step |
| `\` | Insert λ symbol in the editor |

## Architecture

```
islands/App.tsx          ← Main app shell, composes editor + graph + toolbar
islands/Graph.tsx        ← SVG canvas with pan/zoom/drag (D3)
components/Toolbar.tsx   ← Controls: examples, method, stepping, settings
hooks/                   ← Extracted effects: editor init, scene rendering, layout
lib/
  appState.ts            ← Central reactive state (Preact signals)
  ast.ts                 ← AST types, parser invocation, utilities
  examples.ts            ← Built-in example expressions
  core/
    types.ts             ← Interaction net types (Node, Graph, Redex, etc.)
    graph.ts             ← link(), reciprocal() graph primitives
    reductions.ts        ← Universal reductions: annihilate, erase, commute
    typechecker.ts       ← Bidirectional type checker
    systems/
      lambdacalc.ts      ← Tree-based λ-calculus system
      deltanets/         ← Δ-net interaction system (build, readback, redexes)
  methods/
    index.ts             ← Method registry (lambdacalc, deltanets)
    lambdacalc.ts        ← Tree-stepping method with render
    deltanets/           ← Graph-stepping method with render pipeline
  render/
    core.ts              ← Node2D scene tree, bounds, SVG helpers
    primitives.ts        ← Drawing primitives (circles, triangles, etc.)
    agents/              ← Per-agent SVG renderers (enclosure, replicator, wire, etc.)
  lang/
    core/                ← .inet language compiler (lexer → parser → evaluator)
    view/                ← .iview styling language compiler
    bridge.ts            ← Connects .inet compilation to the visualizer
```

**Data flow:** Source text → `updateAst()` → AST / Graph → method `init()` → method `render()` → `Node2D` scene tree → D3 SVG.

## Reduction Methods

- **Lambda Calculus (tree):** Operates directly on the AST using β-reduction with substitution. Supports stepping through reductions.
- **Delta-Nets (graph):** Compiles λ-terms to interaction nets, then reduces via annihilation, erasure, and commutation rules. Supports all four substructural systems: Linear (L), Affine (A), Relevant (I), and Full (K).

## The .inet Language

The `.inet` format allows defining custom interaction net systems with agents, rules, and graphs directly. Files can include `.iview` styling declarations. See `lib/lang/examples/` for examples.

## Tests

```
deno run test_readback.ts    # Readback: λ-term → graph → λ-term roundtrip
deno run test_reductions.ts  # Core reduction primitives (annihilate, erase, commute)
deno run lib/lang/test.ts    # .inet / .iview language compiler
```

## About the λ-calculi parser

The λ-calculi parser in [`lib/parser.gen.ts`](lib/parser.gen.ts) was generated using [tsPEG](https://www.npmjs.com/package/tspeg) (3.3.1) based on the grammar in [`lib/lambda.grammar`](lib/lambda.grammar).

```
npm install -g tspeg
tspeg lib/lambda.grammar lib/parser.gen.ts
```
