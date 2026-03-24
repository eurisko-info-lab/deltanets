# Delta-Nets → Rocq: Gap Analysis & Roadmap

**Generated**: 2026-03-23, post-Phase 12  
**Updated**: 2026-03-24, post-Phase 39  
**Current state**: ~12k LoC TypeScript (46 files) · 830 tests · strategy-based tactic protocol  
**Overall Rocq parity**: ~85% surface, ~70% depth

---

## Completed Phases (1–39)

| Phase | Feature | Commit |
|-------|---------|--------|
| 1 | Parameterized data types | `3db5cbd` |
| 2 | General match expressions | `19eba10` |
| 3 | Dependent pattern matching | `d8d9eb0` |
| 4 | Indexed data types | `d55df8e` |
| 5 | Auto-generated eliminators | `72e8138` |
| 6 | Implicit arguments | `5bf695f` |
| 7 | Termination checking | `789c7de` |
| 8 | Tactic combinators (calc/conv) | `bf2ba2f` |
| 9 | Simp tactic | `efb60b0` |
| 10 | Record types | `143ef3c` |
| 11 | Module system (open/export) | `cdbd191` |
| 12 | Decision procedures (decide/omega/auto) | `2550a48` |
| 13 | Let-bindings in proofs | `65a30fb` |
| 14 | Pi & Sigma types | `ab77d12` |
| 15 | Unification engine | `a7b33a5` |
| 16 | Universe polymorphism | `fbbbad7` |
| 17 | Quotation & reflection | `97d6aaf` |
| 18 | Meta-agents | `c3cc341` |
| 19 | Tactic-as-rules | `917d6c6` |
| 19a | Unified tactic pipeline | `25db1ab` |
| 20 | Tactic meta-agent primitives (CtxSearch, EqCheck) | `9e80c07` |
| 21 | Mutual inductive types | `c837d65` |
| 22 | Coinductive types (codata) | `8613b05` |
| 23 | Well-founded recursion | `01b317d` |
| 24 | Nested pattern matching | `03b74be` |
| 25 | Sections & variables | `af14873` |
| 26 | Notations | `54087c1` |
| 27 | Coercions | `7d5b267` |
| 28 | Setoid rewriting | `f4c8b8d` |
| 29 | Ring / field solvers | `4028a04` |
| 30 | Typeclasses | `8dd682a` |
| 31 | Hint databases | `b08e65f` |
| 32 | Definitional equality | `6d1389c` |
| 33 | Prop / Set / Type sorting | `7e06227` |
| 34 | Tactic combinator language | `fbbfe88` |
| 35 | Rewriting with lemma databases | `7f5eda8` |
| 36 | Canonical structures | `c7def90` |
| 37 | Program / Equations | `1d4fdfb` |
| 38 | Strategy declarations | `c68a172` |
| 39 | Meta-INet strategy protocol | `3b60d93` |

---

## What's Implemented (Rocq Feature Map)

| Rocq Feature | INet Equivalent | Depth |
|---|---|---|
| CIC type theory | Pi, Sigma, Let, Lambda, Metavar, Match exprs | Good — full dependent types, no extraction kernel |
| Inductive types | `data` with params + indices, eliminators | Good — auto-eliminators, dependent matching |
| Mutual inductives | `mutual { data ... data ... }` + joint positivity | Good |
| Coinductive types | `codata` + guard agents + productivity checking | Good — observation-based |
| Record types | `record` → single-constructor data + projections | Good |
| Universe hierarchy | `Type(0) : Type(1) : ...`, Prop, Set, cumulative | Good — impredicative Prop, no SProp |
| Pattern matching | Nested deep patterns, with-clauses, overlap detection | Good |
| Termination | Structural recursion + `{measure}` + `{wf}` | Good — `wf` is trusted |
| Implicit args | `{x : A}` in prove params, unification-based inference | Good — with canonical structure resolution |
| Unification | First-order unification with metavars | Basic — no higher-order unification |
| Sections/Variables | `section S { variable(A : Type) ... }` with auto-abstraction | Good |
| Notations | `notation "+" := add (prec 50, left)` | Basic — infix only, no mixfix |
| Coercions | `coercion name = From -> To via func` | Good |
| Tactics | assumption, simp, decide, omega, auto, calc, conv, rewrite, ring | Good breadth |
| Tactic combinators | `first(t1, t2)`, `then(t1, t2)`, `try(t)`, `repeat(t)`, `all(t)` | Good |
| User-defined tactics | `tactic name { agents... rules... }` with meta-agent primitives | Good — CtxSearch, Normalize, EqCheck |
| Strategy protocol | `strategy name = first(conv, rewrite)` — compiles to real INet agents | Good — Ok/Fail/Gate wiring |
| Setoid rewriting | `setoid R on T { refl, sym, trans }` + rewrite tactic | Good |
| Ring solver | `ring T { zero, add, mul }` + polynomial normalization | Basic — semiring, no field |
| Quotation/Reflection | quote/unquote + term-encoding agents | Good |
| Module system | system/extend/compose/open/export | Good — but no functors |
| Typeclasses | `class C(A) { method : Type }` + `instance` | Good — method dispatch via compute rules |
| Hint databases | `@[simp]`, `@[auto]`, `hint db lemma` | Good |
| Definitional equality | `conv` checks conversion, `Eq` requires proof | Good |
| Prop/Set sorting | Impredicative Prop, large Set, cumulative Type(n) | Good — singleton elimination |
| Canonical structures | `canonical name : S := { proj := val }` | Good — unification hints |
| Program/Equations | `program` with obligations, dependent matching | Good |
| Proof trees | Natural-deduction derivation trees with hole suggestions | Good — unique to INet |

---

## Architectural Decisions

### Meta-INet (decided Phase 17–18, solidified Phase 38–39)

INet reduction is Turing-complete and already the execution backbone.
Quotation & reflection represent proof goals/terms as INet agents.
Strategy declarations compile to real INet agent graphs (Ok/Fail/Gate
protocol), eliminating the TS-interpreter fallback for non-recursive
strategies. The trusted kernel = the INet reduction engine (~200 LoC).

### Tactic Architecture (decided Phase 19a, extended Phase 34–39)

**Built-in tactics (assumption/simp/decide/omega/auto) stay in TypeScript.**
They are proof *finders*, not proof *checkers* — `buildProofTree` + the type
checker independently validate any proof term they produce. A buggy tactic
can't break soundness.

**User-defined tactics run as INet reductions** via `tactic name { agents... rules... }`.
Meta-agent primitives (Normalize, CtxSearch, EqCheck) give user tactics the
same power as built-in ones. Strategy combinators (first/then/all) compose
primitives declaratively without needing to write INet agents by hand.

### Code Organization (Phase 39 refactor)

The two largest files were decomposed:
- **normalize.ts** (434 lines) — types, substitution, equality, normalization engine
- **termination.ts** (239 lines) — termination/productivity/exhaustiveness checking
- **desugar.ts** (499 lines) — data/record/codata desugaring, evalAgent
- **typecheck-prove.ts** (2,113 lines) — type checker, proof search, unification
- **eval-system.ts** (1,146 lines) — system evaluation, processProve pipeline

---

## What's Missing: Reassessing Distance to Rocq

### The Honest Picture

At Phase 39, the **surface feature set** is ~85% of Rocq — nearly every
major declaration form exists (data, record, codata, class, instance,
canonical, section, notation, coercion, setoid, ring, program). What's
missing is not breadth but **depth and practicality**:

1. **No extraction.** Verified code stays inside the prover. Rocq's
   raison d'être is extracting OCaml/Haskell — without it, proofs are
   academic exercises.

2. **First-order unification only.** `?f x = S x` fails. Rocq's
   pattern-fragment unification handles this. Many dependent types need it.

3. **No interactive mode.** Every proof is batch-verified. Rocq users
   develop proofs incrementally, inspecting intermediate goals. This is
   a workflow gap, not a feature gap — but it determines usability.

4. **Performance.** INet graph reduction is orders of magnitude slower
   than Rocq's VM/native compute. Large computations timeout.

5. **No standard library.** No Nat lemmas, List lemmas, etc. Every
   project re-derives `plus_comm` from scratch.

6. **Omega is shallow.** Rocq's omega solves Presburger arithmetic;
   ours does simple congruence matching.

### What More TypeScript Won't Fix

The remaining gaps fall into two categories:

**Category A — More TS code would help:** module functors, mixfix
notations, higher-order unification, SProp, primitive projections.
These are well-understood algorithms; implementing them is straightforward.

**Category B — Wrong abstraction level:** extraction, standard library,
interactive mode, performance. These need a different kind of work:
extraction needs a compilation target; the standard library needs the
*language itself* to be pleasant to write in at scale; interactive mode
needs an editor protocol; performance needs a bytecode compiler.

Category B reveals that the **real bottleneck is no longer TypeScript
implementation LoC — it's that the language lacks a proper term language
for writing programs and proofs in**.

---

## The Custom Language Question

### Problem: JavaScript/TypeScript is wrong for extending the prover

The INet `.inet` syntax defines interaction net *systems* — agents, rules,
graphs. But the proof language (`prove`, `compute`, `data`, etc.) lives in
a custom syntax embedded inside system declarations. This creates friction:

1. **Proofs are second-class.** A `prove` block is a case-expression with
   pattern-matching. There's no way to write `let lemma = ... in ...` at
   the top level, define named proof terms, or compose proofs outside of
   case arms.

2. **No real term language.** `ProveExpr` has 9 AST nodes (ident, call,
   hole, match, let, pi, sigma, lambda, metavar). That's enough for
   type annotations but not for writing programs. There are no
   if/then/else, no where-clauses, no do-notation, no list comprehensions.

3. **The standard library can't be written in INet.** To build Nat
   lemmas you'd write `.inet` files with `prove` blocks — but the syntax
   is too spartan for scale. Compare:

   ```
   # INet today
   prove plus_comm(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
     | Zero -> plus_zero_right(m)
     | Succ(k) -> cong_succ(plus_comm(k, m))
   }
   ```

   vs. what a term language could look like:

   ```
   theorem plus_comm (n m : Nat) : n + m = m + n := by
     induction n with
     | zero => exact plus_zero_right m
     | succ k ih => exact congruence (S ·) ih
   ```

### What would a custom language look like?

Not a general-purpose language. A **proof term language** layered on top
of the existing INet reduction engine:

- **Surface syntax** close to Lean 4 / Rocq — `theorem`, `def`,
  `induction`, `by`, `exact`, `apply`, `simp`, `ring`
- **Elaboration** to the existing `ProveExpr` AST + `data`/`record`/etc.
- **The INet core stays unchanged** — agents, rules, reduction
- **Proof terms desugar to INet compute rules** — what `prove` already does

This is essentially **replacing the parser front-end** (~1,600 lines in
`parser.ts` + `lexer.ts`) without touching the backend (`eval-system.ts`,
`typecheck-prove.ts`, `normalize.ts`).

### Cost/benefit analysis

| Approach | Effort | Payoff |
|----------|--------|--------|
| Keep extending .inet | Zero | Proofs stay awkward, no stdlib feasible |
| Lean-like front-end syntax | ~1,500 LoC new parser | Pleasant proofs, stdlib possible |
| Full TS→INet compiler | ~3,000 LoC | Write proofs in TS (weird but possible) |
| Separate .proof files | ~800 LoC | Quick win but split ecosystem |

**Recommendation:** A Lean-like surface syntax is the sweet spot. The
existing `ProveExpr` AST is already CIC-shaped; it just needs a better
way to write terms. The INet substrate (agents, rules, graphs) stays as
the compilation target and execution engine. Think of it as:

```
.inet files  → INet systems (agents, rules, graphs)
.proof files → Elaborated proof terms → ProveExpr → compute rules → INet agents
```

The `.proof` language would be a thin veneer:
- `theorem`/`def`/`lemma` instead of `prove`
- `by` introduces tactic mode
- `fun x => ...` instead of `fun(x : A, body)`
- Implicit args via `{}`/`[]` matching Lean conventions
- `where` clauses for local definitions

This could unblock Phases 40 (standard library) and 41 (extraction) which
are currently stalled on ergonomics.

---

## Roadmap (Phases 40–50)

### Tier A — Ergonomics & Ecosystem (→ ~90%)

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **40** | **Proof term language** | Lean-like surface syntax for proofs/programs. New parser producing existing AST. Unlocks stdlib. | ~1,500 |
| **41** | **Standard library** | Nat, Bool, List, Option, Sigma, Fin, Vec — core lemmas in the new syntax. Validates end-to-end. | ~800 |
| **42** | **Module functors** | `Module Type`, `Module ... : SIG`, parameterized modules. | ~400 |
| **43** | **Mixfix notations** | `notation "if _ then _ else _" := ...` | ~250 |

### Tier B — Depth & Power (→ ~95%)

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **44** | **Higher-order unification** | Pattern-fragment unification. Handles `?f x = S x`. Required for serious dependent types. | ~500 |
| **45** | **Code extraction** | Generate TypeScript/JS from verified programs. Erase Prop. Requires stdlib. | ~500 |
| **46** | **SProp** | Strict propositions — definitional proof irrelevance. | ~300 |
| **47** | **Primitive projections** | Records with definitional eta. `mk(fst(p), snd(p)) ≡ p`. | ~250 |

### Tier C — Performance & Scale (→ ~98%)

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **48** | **Interactive proof mode** | LSP-style step-through. Show goals, apply tactics incrementally. | ~800 |
| **49** | **Bytecode / VM compute** | Compile INet terms for fast reduction. 10-100x speedup. | ~600 |
| **50** | **Guard condition for cofixpoints** | Robust nested corecursive productivity checking. | ~300 |

---

## Estimated Totals

| Tier | Phases | Est. LoC | Cumulative Rocq % |
|------|--------|----------|-------------------|
| Done (1–39) | 41 | ~12,100 | ~85% |
| Tier A: Ergonomics | 40–43 | ~2,950 | ~90% |
| Tier B: Depth & power | 44–47 | ~1,550 | ~95% |
| Tier C: Performance | 48–50 | ~1,700 | ~98% |

**Total remaining: ~6,200 LoC across 11 phases**

### Key Milestone: Phase 40 is the inflection point

The proof term language is the gating factor. Without it:
- Standard library is infeasible (Phase 41)
- Extraction has nothing to extract (Phase 45)
- Interactive mode has no ergonomic front-end (Phase 48)

With it, INet becomes a practical proof assistant rather than a
proof-of-concept theorem prover.

The remaining ~2% is Rocq's 30+ years of standard library, extraction
maturity, and ecosystem (CoqIDE, SerAPI, coq-lsp, opam packages,
ssreflect, MathComp, Iris) — not necessary to replicate.

---

## Critical Path

```
Phase 30 (typeclasses) ──→ Phase 31 (instance search) ──→ Phase 35 (simp lemma DB)
Phase 33 (Prop/Set/Type) ──→ Phase 41 (extraction)
Phase 32 (def/prop eq) ──→ Phase 42 (HO unification) ──→ Phase 43 (SProp)
Phase 34 (tactic combinators) — independent
Phase 38 (module functors) — independent
Phase 40 (stdlib) — depends on Phases 30–33
```

Phases 30–33 unlock everything. Typeclasses + Prop sorting is the
foundation that the rest builds on. Recommended order:

1. **30–31 first** (typeclasses + instance search) — highest user-facing impact
2. **33 next** (Prop/Set) — required for extraction and proof irrelevance
3. **34** (tactic combinators) — makes everything after it cheaper to build
4. **40** in parallel with Tier B — a growing stdlib validates every new feature
