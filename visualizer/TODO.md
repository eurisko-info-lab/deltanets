# Delta-Nets → Rocq: Gap Analysis & Roadmap

**Generated**: 2026-03-23, post-Phase 12  
**Updated**: 2026-03-23, post-Phase 19  
**Current state**: ~20k LoC TypeScript · 614 tests · 5 built-in tactics · user-defined tactics  
**Overall Rocq parity**: ~65% surface, ~45% depth

---

## Completed Phases (1–19)

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

---

## Remaining Gaps

| # | Gap | Impact | Current state |
|---|-----|--------|--------------|
| 1 | No tactic meta-agent primitives | User tactics can't normalize, search context, or check types | Only syntactic Tm* rewriting |
| 2 | No coinductive types | No streams, bisimulation, productivity | Not in AST |
| 3 | No mutual/nested recursion | Can't define Even/Odd mutually | Sequential prove blocks only |
| 4 | No sections/variables | Must repeat params everywhere | No auto-abstraction |
| 5 | No notations/coercions | Syntax is fixed | No user extensibility |

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
Currently limited to syntactic Tm* rewriting (no normalization, no context access).

**Next step: meta-agent primitives** — expose Normalize, CtxSearch, EqCheck
as MetaHandlers inside `runUserTactic`, giving user tactics the same
power as built-in ones. Built-in tactics can optionally be ported to INet
later once the primitives are proven.

---

## Roadmap (Phases 20–28)

### Tier 3a — Tactic Meta-Agents

Expose kernel operations to the INet tactic engine.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **20** | **Tactic meta-agent primitives** | Normalize (reduce Tm* via compute rules), CtxSearch (inject proof context, search bindings matching goal), EqCheck (structural equality with α-renaming) as MetaHandlers in `runUserTactic`; pass ProveCtx into tactic graph | ~350 |

### Tier 3b — Expressiveness

Richer data types and recursion patterns.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **21** | **Mutual inductive types** | `mutual { data Even ... data Odd ... }` with joint positivity | ~300 |
| **22** | **Coinductive types** | `codata Stream(A) { head, tail }` + productivity checking | ~400 |
| **23** | **Well-founded recursion** | `Function` with `{measure f}` or `{wf R}` | ~350 |
| **24** | **Nested pattern matching** | Deep patterns, with-clauses, overlapping checks | ~250 |

### Tier 4 — Scale & Usability

Module system, syntax, and ergonomics.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **25** | **Sections & variables** | `section S { variable (A : Type) }` with auto-abstraction | ~200 |
| **26** | **Notations** | `notation "x + y" := add(x, y)` with precedence | ~300 |
| **27** | **Coercions** | Implicit type conversions registered per pair | ~200 |

### Tier 5 — Automation Libraries (INet-native)

Written as INet rule sets using meta-agent primitives from Phase 20.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **28** | **Setoid rewriting** | Rewrite under arbitrary equivalence relations (INet rules) | ~300 |
| **29** | **Ring / field solvers** | Commutative ring normalization (INet rules) | ~350 |

---

## Estimated Totals

| Tier | Phases | Est. LoC | Cumulative Rocq % |
|------|--------|----------|-------------------|
| Done (1–19a) | 20 | ~8,400 | ~65% |
| Tier 3a: Meta-agents | 20 | ~350 | ~70% |
| Tier 3b: Expressiveness | 21–24 | ~1,300 | ~80% |
| Tier 4: Usability | 25–27 | ~700 | ~85% |
| Tier 5: Automation libs | 28–29 | ~650 | ~90% |

**Total remaining: ~3,000 LoC across 10 phases**

The remaining ~15% is Rocq's 30+ years of standard library, extraction
machinery, and ecosystem (CoqIDE, SerAPI, coq-lsp, opam packages) —
not necessary to replicate.

---

## Critical Path

```
Phase 13 (let) ──→ Phase 14 (Pi/Sigma) ──→ Phase 15 (unification) ──┐
                                                                      ├→ Phase 17 (quotation) → 18 → 19
                                            Phase 16 (universes) ─────┘
                                                                      ├→ Phase 20–23 (data types)
                                                                      └→ Phase 24–28 (usability + libs)
```

Phases 13–15 unlock everything. Phase 17 (quotation) is the architectural
pivot that makes Tiers 4–5 dramatically cheaper.
