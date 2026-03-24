// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Built-in Prelude
// The trusted kernel shared by all interaction net systems.
// This is the canonical source for `include "prelude"`.
// ═══════════════════════════════════════════════════════════════════

export const PRELUDE_SOURCE = `\
system "Prelude" {

  # ─── Structural ─────────────────────────────────────────────
  agent root(principal)
  agent var(principal)

  # ─── Quotation: Term Reification ────────────────────────────
  agent TmVar(principal)
  agent TmApp(principal, args)
  agent TmPi(principal, domain, codomain)
  agent TmSigma(principal, domain, codomain)
  agent TmLam(principal, paramType, body)
  agent TmNil(principal)
  agent TmCons(principal, head, tail)
  agent QGoal(principal, prop, ctx)
  agent CtxNil(principal)
  agent CtxCons(principal, name_term, type_term, tail)

  rule TmVar   <> TmVar   -> annihilate
  rule TmApp   <> TmApp   -> annihilate
  rule TmPi    <> TmPi    -> annihilate
  rule TmSigma <> TmSigma -> annihilate
  rule TmLam   <> TmLam   -> annihilate
  rule TmNil   <> TmNil   -> annihilate
  rule TmCons  <> TmCons  -> annihilate
  rule QGoal   <> QGoal   -> annihilate
  rule CtxNil  <> CtxNil  -> annihilate
  rule CtxCons <> CtxCons -> annihilate

  # ─── Meta-Agents ────────────────────────────────────────────
  agent MatchGoal(principal, on_var, on_app, on_pi, on_sigma, on_lam, on_other)
  agent ApplyRule(principal, result)
  agent NormalizeTerm(principal, result)
  agent CtxSearch(principal, result)
  agent EqCheck(principal, second, on_eq, on_neq)

  # ─── Strategy Protocol ──────────────────────────────────────
  agent Ok(principal, result)
  agent Fail(principal)
  agent Gate(principal, on_ok, on_fail)
  agent DupTerm(principal, copy1, copy2)
  agent StratConv(principal, output)
  agent StratCtxLookup(principal, output)
  agent StratRewrite(principal, output)
  agent StratGround(principal, output)
  agent StratSearch(principal, output, depth)
  agent StratCong(principal, output, inner)

  # Handler rules (trusted kernel)
  open "Meta"

  # ─── Default Strategies ─────────────────────────────────────
  strategy assumption = ctx_search
  strategy simp        = first(conv, ctx_search, rewrite)
  strategy decide      = ground
  strategy omega       = first(conv, cong(Succ, omega), rewrite, cong(Succ, rewrite))
  strategy auto        = search(3)
}
`;
