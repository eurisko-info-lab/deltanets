// ═══════════════════════════════════════════════════════════════════
// INet Standard Library
// Core data types and lemmas, available via `include "stdlib"`.
// Each module builds on the Prelude and previous modules.
// ═══════════════════════════════════════════════════════════════════

// ─── Nat ───────────────────────────────────────────────────────────

export const STDLIB_NAT = `\
system "Stdlib.Nat" extend "Prelude" {
  data Nat { | Zero | Succ(pred : Nat) }

  agent add(principal, result, accum)
  rule add <> Zero -> { relink left.result left.accum }
  rule add <> Succ -> {
    let s = Succ
    let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}
`;

// ─── Bool ──────────────────────────────────────────────────────────

export const STDLIB_BOOL = `\
system "Stdlib.Bool" extend "Prelude" {
  data Bool { | True | False }

  agent not(principal, result)
  rule not <> True  -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True   relink left.result t.principal }
  compute not(True) = False
  compute not(False) = True

  agent and(principal, result, second)
  rule and <> True  -> { relink left.result left.second }
  rule and <> False -> { erase left.second  let f = False  relink left.result f.principal }
  compute and(True, b)  = b
  compute and(False, b) = False

  agent or(principal, result, second)
  rule or <> True  -> { erase left.second  let t = True  relink left.result t.principal }
  rule or <> False -> { relink left.result left.second }
  compute or(True, b)  = True
  compute or(False, b) = b
}
`;

// ─── Eq ────────────────────────────────────────────────────────────

export const STDLIB_EQ = `\
system "Stdlib.Eq" extend "Prelude" {
  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent cong(principal, result, func)
  agent trans(principal, result, second)

  rule subst <> refl  -> { relink left.result left.value }
  rule sym   <> refl  -> { let r = refl  relink left.result r.principal }
  rule cong  <> refl  -> { let r = refl  relink left.result r.principal  erase left.func }
  rule trans <> refl  -> { relink left.result left.second }
}
`;

// ─── Option ────────────────────────────────────────────────────────

export const STDLIB_OPTION = `\
system "Stdlib.Option" extend "Prelude" {
  data Option(A) { | None | Some(value : A) }
}
`;

// ─── List ──────────────────────────────────────────────────────────

export const STDLIB_LIST = `\
system "Stdlib.List" extend "Prelude" {
  data List(A) { | Nil | Cons(head : A, tail : List(A)) }

  agent append(principal, result, second)
  rule append <> Nil -> { relink left.result left.second }
  rule append <> Cons -> {
    let c = Cons
    let a = append
    relink left.result c.principal
    relink right.head c.head
    wire c.tail -- a.result
    relink left.second a.second
    relink right.tail a.principal
  }
  compute append(Nil, ys)      = ys
  compute append(Cons(x, xs), ys) = Cons(x, append(xs, ys))

  agent length(principal, result)
  rule length <> Nil -> { let z = Zero  relink left.result z.principal }
  rule length <> Cons -> {
    let s = Succ
    let l = length
    relink left.result s.principal
    wire s.pred -- l.result
    erase right.head
    relink right.tail l.principal
  }
  compute length(Nil)         = Zero
  compute length(Cons(x, xs)) = Succ(length(xs))
}
`;

// ─── Sigma (dependent pairs) ──────────────────────────────────────

export const STDLIB_SIGMA = `\
system "Stdlib.Sigma" extend "Prelude" {
  data Sigma(A, B) { | Pair(fst : A, snd : B) }
}
`;

// ─── Z (integers) ─────────────────────────────────────────────────

export const STDLIB_Z = `\
system "Stdlib.Z" extend "Prelude" {
  data Nat { | Zero | Succ(pred : Nat) }

  agent add(principal, result, accum)
  rule add <> Zero -> { relink left.result left.accum }
  rule add <> Succ -> {
    let s = Succ
    let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  # Z = Pos(n) for n >= 0, NegSucc(n) for -(n+1)
  data Z { | Pos(n : Nat) | NegSucc(n : Nat) }

  # Negation: dispatches via helper agents
  agent neg_z(principal, result)
  rule neg_z <> Pos -> {
    let d = neg_z_pos
    relink left.result d.result
    relink right.n d.principal
  }
  rule neg_z <> NegSucc -> {
    let p = Pos
    let s = Succ
    relink left.result p.principal
    wire p.n -- s.principal
    relink right.n s.pred
  }
  agent neg_z_pos(principal, result)
  rule neg_z_pos <> Zero -> {
    let p = Pos
    let z = Zero
    relink left.result p.principal
    wire p.n -- z.principal
  }
  rule neg_z_pos <> Succ -> {
    let n = NegSucc
    relink left.result n.principal
    relink right.pred n.n
  }

  # Flat compute rules for the normalizer
  compute neg_z(Pos(n)) = neg_z_pos(n)
  compute neg_z(NegSucc(n)) = Pos(Succ(n))
  compute neg_z_pos(Zero) = Pos(Zero)
  compute neg_z_pos(Succ(n)) = NegSucc(n)

  # Successor on Z
  agent succ_z(principal, result)
  rule succ_z <> Pos -> {
    let p = Pos
    let s = Succ
    relink left.result p.principal
    wire p.n -- s.principal
    relink right.n s.pred
  }
  rule succ_z <> NegSucc -> {
    let d = succ_z_neg
    relink left.result d.result
    relink right.n d.principal
  }
  agent succ_z_neg(principal, result)
  rule succ_z_neg <> Zero -> {
    let p = Pos
    let z = Zero
    relink left.result p.principal
    wire p.n -- z.principal
  }
  rule succ_z_neg <> Succ -> {
    let n = NegSucc
    relink left.result n.principal
    relink right.pred n.n
  }

  compute succ_z(Pos(n)) = Pos(Succ(n))
  compute succ_z(NegSucc(n)) = succ_z_neg(n)
  compute succ_z_neg(Zero) = Pos(Zero)
  compute succ_z_neg(Succ(n)) = NegSucc(n)
}
`;

// ─── Stream (coinductive) ─────────────────────────────────────────

export const STDLIB_STREAM = `\
system "Stdlib.Stream" extend "Prelude" {
  data Nat { | Zero | Succ(pred : Nat) }

  agent add(principal, result, accum)
  rule add <> Zero -> { relink left.result left.accum }
  rule add <> Succ -> {
    let s = Succ
    let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  codata Stream(A) { head : A, tail : Stream(A) }

  agent refl(principal)
  rule sym   <> refl -> { let r = refl  relink left.result r.principal }
  rule trans <> refl -> { relink left.result left.second }

  agent cong_succ(principal, result)
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }

  # repeat(n) produces the constant stream n, n, n, ...
  prove repeat(n : Nat) -> Stream(Nat) {
    | Zero -> guard_stream(Zero, repeat(Zero))
    | Succ(k) -> guard_stream(Succ(k), repeat(Succ(k)))
  }

  # head of a constant stream
  prove head_repeat(n : Nat) -> Eq(head(guard_stream(n, guard_stream(n, repeat(n)))), n) {
    | Zero -> conv
    | Succ(k) -> conv
  }
}
`;

// ─── Core: combined standard library ──────────────────────────────
// `include "stdlib"` gives you everything.

export const STDLIB_SOURCE = `\
include "prelude"

${STDLIB_NAT}
${STDLIB_BOOL}
${STDLIB_EQ}
${STDLIB_OPTION}
${STDLIB_SIGMA}

# Combined system with all stdlib types and lemmas
system "Stdlib" extend "Prelude" {
  data Nat { | Zero | Succ(pred : Nat) }

  agent add(principal, result, accum)
  rule add <> Zero -> { relink left.result left.accum }
  rule add <> Succ -> {
    let s = Succ
    let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  data Bool { | True | False }

  agent not(principal, result)
  rule not <> True  -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True   relink left.result t.principal }
  compute not(True) = False
  compute not(False) = True

  agent and(principal, result, second)
  rule and <> True  -> { relink left.result left.second }
  rule and <> False -> { erase left.second  let f = False  relink left.result f.principal }
  compute and(True, b)  = b
  compute and(False, b) = False

  agent or(principal, result, second)
  rule or <> True  -> { erase left.second  let t = True  relink left.result t.principal }
  rule or <> False -> { relink left.result left.second }
  compute or(True, b)  = True
  compute or(False, b) = b

  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent cong(principal, result, func)
  agent trans(principal, result, second)
  agent cong_succ(principal, result)
  agent cong_cons(principal, result, head)

  rule subst     <> refl -> { relink left.result left.value }
  rule sym       <> refl -> { let r = refl  relink left.result r.principal }
  rule cong      <> refl -> { let r = refl  relink left.result r.principal  erase left.func }
  rule trans     <> refl -> { relink left.result left.second }
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }
  rule cong_cons <> refl -> { let r = refl  relink left.result r.principal  erase left.head }

  data Option(A) { | None | Some(value : A) }
  data List(A)   { | Nil  | Cons(head : A, tail : List(A)) }
  data Sigma(A, B) { | Pair(fst : A, snd : B) }

  agent append(principal, result, second)
  rule append <> Nil -> { relink left.result left.second }
  rule append <> Cons -> {
    let c = Cons
    let a = append
    relink left.result c.principal
    relink right.head c.head
    wire c.tail -- a.result
    relink left.second a.second
    relink right.tail a.principal
  }
  compute append(Nil, ys)         = ys
  compute append(Cons(x, xs), ys) = Cons(x, append(xs, ys))

  agent length(principal, result)
  rule length <> Nil -> { let z = Zero  relink left.result z.principal }
  rule length <> Cons -> {
    let s = Succ
    let l = length
    relink left.result s.principal
    wire s.pred -- l.result
    erase right.head
    relink right.tail l.principal
  }
  compute length(Nil)          = Zero
  compute length(Cons(x, xs))  = Succ(length(xs))

  # ─── Core Lemmas (Nat) ──────────────────────────────────────
  theorem plus_zero_right (n : Nat) : Eq(add(n, Zero), n) := by
    | Zero => refl
    | Succ(k) => cong_succ(plus_zero_right(k))

  theorem plus_succ_right (n m : Nat) : Eq(add(n, Succ(m)), Succ(add(n, m))) := by
    | Zero => refl
    | Succ(k) => cong_succ(plus_succ_right(k, m))

  theorem plus_zero_left (n : Nat) : Eq(add(Zero, n), n) := refl

  # ─── Core Lemmas (Bool) ─────────────────────────────────────
  theorem not_not (b : Bool) : Eq(not(not(b)), b) := by
    | True => refl
    | False => refl

  theorem and_true_right (b : Bool) : Eq(and(b, True), b) := by
    | True => refl
    | False => refl

  theorem or_false_right (b : Bool) : Eq(or(b, False), b) := by
    | True => refl
    | False => refl

  # ─── Core Lemmas (List) ─────────────────────────────────────
  theorem append_nil_right (xs : List) : Eq(append(xs, Nil), xs) := by
    | Nil => refl
    | Cons(h, t) => cong_cons(append_nil_right(t), h)
}
`;
