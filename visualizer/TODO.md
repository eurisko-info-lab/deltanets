# Delta-Nets → Rocq: Gap Analysis & Roadmap

**Generated**: 2026-03-23, post-Phase 12  
**Current state**: 15,546 LoC TypeScript · 340 tests · 17 tactics  
**Overall Rocq parity**: ~25% surface, ~15% depth

---

## Completed Phases (1–12)

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

---

## Top 10 Remaining Gaps

| # | Gap | Impact | Current state |
|---|-----|--------|--------------|
| 1 | No trusted kernel / proof terms | Can't verify proofs independently | Tactics rewrite AST directly |
| 2 | No unification | Implicit args never solved, no type inference | `exprEqual` is syntactic only |
| 3 | No Pi/Sigma type formers | Types limited to constructor applications | No `∀(x:A), B x` |
| 4 | No coinductive types | No streams, bisimulation, productivity | Not in AST |
| 5 | No mutual/nested recursion | Can't define Even/Odd mutually | Sequential prove blocks only |
| 6 | No let-bindings in proofs | Every proof is a single expression | Only pattern bindings |
| 7 | No universe polymorphism | Only concrete Type₀, Type₁ | No universe variables |
| 8 | No sections/variables | Must repeat params everywhere | No auto-abstraction |
| 9 | No notations/coercions | Syntax is fixed | No user extensibility |
| 10 | No tactic language | Tactics hardcoded in TypeScript | No user-defined tactics |

---

## Architectural Decision: Meta-INet

**Insight**: INet reduction is Turing-complete and already the execution backbone.
Most proof automation (tactics, proof search, rewriting) can be implemented as
INet rule sets rather than hardcoded TypeScript resolvers.

**Mechanism**: Quotation & reflection — represent proof goals and proof terms
as INet agents. Tactic resolution = INet reduction. The trusted kernel = the
INet reduction engine (~200 LoC), already implemented.

**Benefits**:
- Trusted kernel for free (INet reducer is tiny and already exists)
- User-extensible tactics (just write new agents + rules)
- Proof certificates are nets (verifiable by reduction)
- Automation phases become library code, not core changes

**Still needs TypeScript**: Pi/Sigma types, universe hierarchy, unification —
these define what "well-typed" means and can't self-host until the system
can prove its own soundness.

---

## Roadmap (Phases 13–28)

### Tier 1 — Type-Theory Foundations

These define the core type theory. Must be in TypeScript (the "kernel").

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **13** | **Let-bindings in proofs** | `let x = expr in body` inside prove blocks | ~150 |
| **14** | **Pi & Sigma types** | `∀(x:A), B x` and `Σ(x:A), B x` as first-class ProveExpr formers | ~400 |
| **15** | **Unification engine** | Metavariables, occurs check, flex-rigid, implicit argument solving | ~600 |
| **16** | **Universe polymorphism** | Universe variables, cumulativity, constraint solving | ~400 |

*Cumulative Rocq %: ~50%*

### Tier 2 — Quotation & Meta-INet

The pivot: make the INet engine the metalanguage for proof automation.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **17** | **Quotation & reflection** | `quote`/`unquote` primitives; represent ProveExpr as INet agents; proof goals as nets | ~500 |
| **18** | **Meta-agents** | Built-in agents that inspect/construct/transform quoted terms (match-goal, apply-rule, normalize-term) | ~400 |
| **19** | **Tactic-as-rules** | Rewrite simp/decide/omega/auto as INet rule sets; user-definable tactics via `tactic name { agents... rules... }` | ~350 |

*Cumulative Rocq %: ~65%*

### Tier 3 — Expressiveness

Richer data types and recursion patterns.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **20** | **Mutual inductive types** | `mutual { data Even ... data Odd ... }` with joint positivity | ~300 |
| **21** | **Coinductive types** | `codata Stream(A) { head, tail }` + productivity checking | ~400 |
| **22** | **Well-founded recursion** | `Function` with `{measure f}` or `{wf R}` | ~350 |
| **23** | **Nested pattern matching** | Deep patterns, with-clauses, overlapping checks | ~250 |

*Cumulative Rocq %: ~75%*

### Tier 4 — Scale & Usability

Module system, syntax, and ergonomics.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **24** | **Sections & variables** | `section S { variable (A : Type) }` with auto-abstraction | ~200 |
| **25** | **Notations** | `notation "x + y" := add(x, y)` with precedence | ~300 |
| **26** | **Coercions** | Implicit type conversions registered per pair | ~200 |

*Cumulative Rocq %: ~80%*

### Tier 5 — Automation Libraries (INet-native)

Written as INet rule sets using the meta-INet framework from Tier 2.

| Phase | Feature | Description | Est. LoC |
|-------|---------|-------------|----------|
| **27** | **Setoid rewriting** | Rewrite under arbitrary equivalence relations (INet rules) | ~300 |
| **28** | **Ring / field solvers** | Commutative ring normalization (INet rules) | ~350 |

*Cumulative Rocq %: ~85%*

---

## Estimated Totals

| Tier | Phases | Est. LoC | Cumulative Rocq % |
|------|--------|----------|-------------------|
| Current (1–12) | 12 | 4,737 | ~25% |
| Tier 1: Foundations | 13–16 | ~1,550 | ~50% |
| Tier 2: Meta-INet | 17–19 | ~1,250 | ~65% |
| Tier 3: Expressiveness | 20–23 | ~1,300 | ~75% |
| Tier 4: Usability | 24–26 | ~700 | ~80% |
| Tier 5: Automation libs | 27–28 | ~650 | ~85% |

**Total remaining: ~6,450 LoC across 16 phases**

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
