# Delta-Nets → Rocq: Gap Analysis & Roadmap

**Generated**: 2026-03-23, post-Phase 12  
**Updated**: 2026-03-23, post-Phase 29  
**Current state**: ~32.5k LoC TypeScript · 741 tests · 5 built-in tactics · user-defined tactics  
**Overall Rocq parity**: ~75% surface, ~60% depth

---

## Completed Phases (1–29)

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

---

## What's Implemented (Rocq Feature Map)

| Rocq Feature | INet Equivalent | Depth |
|---|---|---|
| CIC type theory | Pi, Sigma, Let, Lambda, Metavar, Match exprs | Shallow — AST-level, no full CIC kernel |
| Inductive types | `data` with params + indices, eliminators | Good — auto-eliminators, dependent matching |
| Mutual inductives | `mutual { data ... data ... }` + joint positivity | Good |
| Coinductive types | `codata` + guard agents + productivity checking | Good — observation-based |
| Record types | `record` → single-constructor data + projections | Good |
| Universe hierarchy | `Type(0) : Type(1) : ...`, cumulative subtyping | Basic — no SProp, no poly quantifiers |
| Pattern matching | Nested deep patterns, with-clauses, overlap detection | Good |
| Termination | Structural recursion + `{measure}` + `{wf}` | Good — `wf` is trusted |
| Implicit args | `{x : A}` in prove params, unification-based inference | Basic — no canonical structures |
| Unification | First-order unification with metavars | Basic — no higher-order unification |
| Sections/Variables | `section S { variable(A : Type) ... }` with auto-abstraction | Good |
| Notations | `notation "+" := add (prec 50, left)` | Basic — infix only, no mixfix |
| Coercions | `coercion name = From -> To via func` | Good |
| Tactics | assumption, simp, decide, omega, auto, calc, conv, rewrite, ring | Good breadth |
| User-defined tactics | `tactic name { agents... rules... }` with meta-agent primitives | Good — CtxSearch, Normalize, EqCheck |
| Setoid rewriting | `setoid R on T { refl, sym, trans }` + rewrite tactic | Basic |
| Ring solver | `ring T { zero, add, mul }` + polynomial normalization | Basic — semiring, no field |
| Quotation/Reflection | quote/unquote + term-encoding agents | Good |
| Module system | system/extend/compose/open/export | Good — but no functors |

---

## Architectural Decisions

### Meta-INet (decided Phase 17–18)

INet reduction is Turing-complete and already the execution backbone.
Quotation & reflection represent proof goals/terms as INet agents.
Tactic resolution = INet reduction. The trusted kernel = the INet reduction
engine (~200 LoC).

### Tactic Architecture (decided Phase 19a)

**Built-in tactics (assumption/simp/decide/omega/auto) stay in TypeScript.**
They are proof *finders*, not proof *checkers* — `buildProofTree` + the type
checker independently validate any proof term they produce. A buggy tactic
can't break soundness.

**User-defined tactics run as INet reductions** via `tactic name { agents... rules... }`.
Meta-agent primitives (Normalize, CtxSearch, EqCheck) give user tactics
the same power as built-in ones.

---

## Roadmap (Phases 30–46)

### Tier A — Foundational Holes (→ ~85%)

Features Rocq users reach for in every non-trivial development.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **30** | **Typeclasses** | Rocq's primary abstraction mechanism. `class Monoid(A) { ... }` with `instance` declarations. Enables `Functor`, `DecidableEq`, etc. | ~500 |
| **31** | **Instance search / hint databases** | Engine behind typeclasses. Extensible hint sets for `auto` and `simp`. Currently `auto` has no user-extensible hint DB. | ~400 |
| **32** | **Definitional / propositional equality separation** | Enforce the boundary: `conv` checks definitional equality (conversion), `Eq` requires proof. Currently all equality is propositional `Eq(a, b)`. | ~300 |
| **33** | **Prop / Set / Type sorting** | `Prop` is proof-irrelevant (enables extraction). Currently everything lives in `Type(n)`. Adding `Prop` unlocks erasure and singleton elimination. | ~350 |

### Tier B — Proof Ergonomics (→ ~90%)

Features that make complex proofs feasible rather than theoretically possible.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **34** | **Tactic combinator language** | `try`, `repeat`, `first`, `all:`, `;` — compose tactics declaratively instead of writing INet agents. Ltac-lite. | ~450 |
| **35** | **Rewriting with lemma databases** | `simp` rewrites with registered lemmas. `@[simp]` attributes on proves. Currently `simp` only uses compute rules. | ~350 |
| **36** | **Canonical structures** | Unification hints that trigger during type inference. Alternative to typeclasses (used heavily in MathComp). | ~300 |
| **37** | **Program / Equations** | Dependent pattern matching with proof obligations. Complex recursive definitions where `{measure}` isn't enough. | ~400 |

### Tier C — Scale & Ecosystem (→ ~95%)

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **38** | **Module functors** | `Module Type`, `Module ... : SIG`, parameterized modules. Abstraction over module signatures beyond system/extend/compose. | ~400 |
| **39** | **Mixfix notations** | `notation "if _ then _ else _" := ...`. Currently limited to binary infix operators. | ~250 |
| **40** | **Standard library** | Core lemmas for Nat, Bool, List, Option, Sigma, Fin, Vec. Validates that the system works end-to-end. | ~800 |
| **41** | **Code extraction** | Generate TypeScript/JS from verified programs. Erase propositions (requires Phase 33 Prop/Set). | ~500 |

### Tier D — Advanced Theory (→ ~98%)

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **42** | **Higher-order unification** | Pattern-fragment unification for metavariables in dependent contexts. Currently first-order only — fails on `?f x = S x`. | ~500 |
| **43** | **SProp (strict propositions)** | Definitional proof irrelevance. `(p : 0 = 0) = (q : 0 = 0)` definitionally. | ~300 |
| **44** | **Primitive projections** | Records with definitional eta-expansion. `mkPair(fst(p), snd(p)) ≡ p` definitionally. | ~250 |
| **45** | **Guard condition for cofixpoints** | Robust nested corecursive productivity checking (Rocq's guard condition is subtle). | ~300 |
| **46** | **Native/VM compute** | Compilation of INet terms to optimized native reduction. Currently all computation is unoptimized INet reduction. | ~600 |

---

## Estimated Totals

| Tier | Phases | Est. LoC | Cumulative Rocq % |
|------|--------|----------|-------------------|
| Done (1–29) | 31 | ~12,000 | ~75% |
| Tier A: Foundations | 30–33 | ~1,550 | ~85% |
| Tier B: Proof ergonomics | 34–37 | ~1,500 | ~90% |
| Tier C: Scale & ecosystem | 38–41 | ~1,950 | ~95% |
| Tier D: Advanced theory | 42–46 | ~1,950 | ~98% |

**Total remaining: ~6,950 LoC across 17 phases**

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
