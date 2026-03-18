const examples = [
  {
    name: "Starter",
    code: `# Reduce the net by clicking on highlighted node pairs (green = optimal), using the arrow keys on your keyboard, or clicking the buttons in the toolbar.

# Use backslash ("\\") to insert a "λ".
# Give a name to a lambda term with "=".
# For example:

I = λx.x # The identity function
T = λx.λy.x # Boolean True
F = λx.λy.y # Boolean False
And = λp.λq.p q p # Logical AND
Or = λp.λq.p p q # Logical OR
Not = λp.p F T # Logical NOT

# The last expression (below) is then represented as a graph/net on the right-hand-side of the screen.
And T F`,
  },
  {
    name: "Lamping A",
    code: `# Lamping A
(λx.(λy.((λf.((λh.(h (λp.(h (λq.p))))) (λl.(((f (λn.(l n))) x) y)))) (λg.(λu.(λv.((g u) (g v))))))))`,
  },
  {
    name: "Lamping B",
    code: `# Lamping B
(λx.(λy.((λf.((λh.(h (λp.(h (λq.q))))) (λl.(((f (λn.(l n))) x) y)))) (λg.(λu.(λv.((g u) (g v))))))))`,
  },
  {
    name: "List Head",
    code: `# List Head
Cons = λa.λb.λf.f a b
Head = λx.x λa.λb.a
Tail = λx.x λa.λb.b

Head (Cons one (Cons two three))`,
  },
  {
    name: "Ω (Non-Normalizing)",
    code: `# Ω (Non-Normalizing)
(λa.a a) (λb.b b)`,
  },
  {
    name: "Y (Non-Normalizing)",
    code: `# Y (Non-Normalizing)
λf.(λx.f (x x)) (λx.f (x x))`,
  },
  {
    name: "Two Squared Twice",
    code: `# Two Squared Twice
(λa.a (a a)) λf.λx.f (f x)`,
  },
  {
    name: "Erasure vs Sharing",
    code: `# Erasure vs Sharing
(λk.u) (λf.(λx.f (x x)) (λx.f (x x)))`,
  },
  {
    name: "Replicator Decay",
    code: `# Replicator Decay
λp.p ((λk.u) (λf.p p))
`
  },
  {
    name: "Graph Coloring",
    code: `# Graph Coloring

T = λx.λy.x # Boolean True
F = λx.λy.y # Boolean False
Or = λp.λq.p p q # Logical OR
Not = λp.p F T # Logical NOT

# Colors
C1 = λc1.λc2.c1
C2 = λc1.λc2.c2

# ColorEq returns T if two colors are equal, and F otherwise
ColorEq = λa.λb.a (b T F) (b F T)

# Colorable returns T if a function f returns T for any of the two colors, and F otherwise
Colorable = λf.Or (f C1) (f C2)

# A 2-colorable graph with 2 nodes
# 1---2
GraphColorable = Colorable λn1.Colorable λn2.Not (ColorEq n1 n2)

# A non-2-colorable graph with 3 nodes
# 1---2
#  \\ /
#   3
GraphNotColorable = Colorable λn1.Colorable λn2.Colorable λn3.Not (Or (ColorEq n1 n2) (Or (ColorEq n2 n3) (ColorEq n1 n3)))

GraphColorable # Results in T
# GraphNotColorable # Results in F
`,
  },
  {
    name: "STLC: Identity",
    code: `# Simply-Typed Lambda Calculus: Identity
# Type annotations are optional. Use ":" after the parameter name.
# Use "->" or "→" for arrow types.

# The polymorphic identity on Nat
λx:Nat.x`,
  },
  {
    name: "STLC: Church Booleans",
    code: `# Simply-Typed Lambda Calculus: Church Booleans
# Here we encode booleans as Nat -> Nat -> Nat

T = λx:Nat.λy:Nat.x
F = λx:Nat.λy:Nat.y

T`,
  },
  {
    name: "STLC: Composition",
    code: `# Simply-Typed Lambda Calculus: Composition
# compose : (B -> C) -> (A -> B) -> A -> C

λf:B -> C.λg:A -> B.λx:A.f (g x)`,
  },
  {
    name: "INet: Δ-Nets",
    code: `# Δ-Nets system definition (.inet format)
# This defines the complete delta-nets interaction system
# with agents, rules, modes, definitions, and example graphs.
# Use the graph selector dropdown to switch between graphs.

system "delta-nets" {
  agent abs(principal, body, bind, type)
  agent app(func, result, arg)
  agent rep-in(principal, ..aux)
  agent rep-out(principal, ..aux)
  agent era(principal)
  agent var(principal)
  agent root(principal)

  rule abs <> app -> annihilate
  rule abs <> era -> erase
  rule app <> era -> erase
  rule rep-in <> era -> erase
  rule rep-out <> era -> erase
  rule rep-in <> rep-out -> annihilate
  rule rep-in <> rep-in -> commute
  rule app <> rep-out -> aux-fan

  mode linear   = { -era, -rep-in, -rep-out }
  mode affine   = { -rep-in, -rep-out }
  mode relevant = { -era }
  mode full     = {}
}

def I = \\x.x
def T = \\x.\\y.x
def F = \\x.\\y.y
def And = \\p.\\q.p q p
def Or = \\p.\\q.p p q
def Not = \\p.p F T
def Church2 = \\f.\\x.f (f x)

graph identity = term I
graph church-two = term Church2
graph and-true-false = term And T F
graph two-squared-twice = term (\\a.a (a a)) (\\f.\\x.f (f x))`,
  },
  {
    name: "INet: Lambda Calculus",
    code: `# Lambda Calculus system definition (.inet format)
# Standard lambda calculus with combinators and Church encodings.

system "lambda-calculus" {
  agent abs(principal, body, bind)
  agent app(func, result, arg)
  agent var(principal)
  agent root(principal)

  rule abs <> app -> annihilate
}

def S = \\f.\\g.\\x.f x (g x)
def K = \\x.\\y.x
def I = \\x.x

def True  = \\x.\\y.x
def False = \\x.\\y.y

def Zero = \\f.\\x.x
def One  = \\f.\\x.f x
def Two  = \\f.\\x.f (f x)
def Three = \\f.\\x.f (f (f x))
def Succ = \\n.\\f.\\x.f (n f x)
def Plus = \\m.\\n.\\f.\\x.m f (n f x)
def Mult = \\m.\\n.\\f.m (n f)

graph succ-two = term Succ Two
graph two-plus-three = term Plus Two Three
graph two-times-three = term Mult Two Three
graph ski-identity = term S K K`,
  },
  {
    name: "INet: Δ-Nets (Composed)",
    code: `# Δ-Nets as a Pushout Composition
# The delta-nets system decomposes into three components:
#   Lambda      — core beta-reduction (abs, app, var, root)
#   Erasable    — garbage collection (era)
#   Replicable  — sharing / duplication (rep-in, rep-out)
#
# Composition via categorical pushout:
#   Δ-Nets = Lambda + Erasable + Replicable

system "Lambda" {
  agent abs(principal, body, bind, type)
  agent app(func, result, arg)
  agent var(principal)
  agent root(principal)
  rule abs <> app -> annihilate
  mode linear = {}
}

system "Erasable" extend "Lambda" {
  agent era(principal)
  rule abs <> era -> erase
  rule app <> era -> erase
  mode affine = {}
}

system "Replicable" extend "Lambda" {
  agent rep-in(principal, ..aux)
  agent rep-out(principal, ..aux)
  rule rep-in <> rep-out -> annihilate
  rule rep-in <> rep-in -> commute
  rule app <> rep-out -> aux-fan
  mode relevant = {}
}

system "Δ-Nets" = compose "Erasable" + "Replicable" {
  rule rep-in <> era -> erase
  rule rep-out <> era -> erase
  mode full = {}
}

def I = \\x.x
def T = \\x.\\y.x
def F = \\x.\\y.y
def And = \\p.\\q.p q p
def Church2 = \\f.\\x.f (f x)

graph identity = term I
graph church-two = term Church2
graph and-true-false = term And T F
graph two-squared-twice = term (\\a.a (a a)) (\\f.\\x.f (f x))`,
  },
  {
    name: "INet: Typing (STLC)",
    code: `# Simply-Typed Lambda Calculus — Typing Examples
# Type annotations: \\x:T.body   Types: base (A, Nat), arrow (A -> B), hole (?)

system "STLC" {
  agent abs(principal, body, bind, type)
  agent app(func, result, arg)
  agent var(principal)
  agent root(principal)
  agent type-base(principal)
  agent type-arrow(principal, domain, codomain)
  agent type-hole(principal)
  rule abs <> app -> annihilate
}

# Identity: Bool → Bool
def id-bool = \\x:Bool.x

# Constant: A → B → A
def const = \\x:A.\\y:B.x

# Apply: (A → B) → A → B
def apply = \\f:A -> B.\\x:A.f x

# Flip: (A → B → C) → B → A → C
def flip = \\f:A -> B -> C.\\y:B.\\x:A.f x y

# Church booleans
def true  = \\x:A.\\y:B.x
def false = \\x:A.\\y:B.y

# Church numerals: (Nat → Nat) → Nat → Nat
def zero  = \\f:Nat -> Nat.\\x:Nat.x
def two   = \\f:Nat -> Nat.\\x:Nat.f (f x)
def succ  = \\n:?.\\f:Nat -> Nat.\\x:Nat.f (n f x)

graph typed-identity = term id-bool
graph typed-const = term const
graph typed-apply = term apply
graph typed-church-two = term two
graph typed-succ-two = term succ two
graph typed-flip = term flip`,
  },
  {
    name: "INet: Lambda Cube",
    code: `# The Lambda Cube — typed systems via pushout composition
# Three axes beyond λ→: polymorphism, dependent types, type operators.
# Each axis extends λ→; cube corners are pushout compositions.

system "λ→" {
  agent abs(principal, body, bind, type)
  agent app(func, result, arg)
  agent var(principal)
  agent root(principal)
  agent type-base(principal)
  agent type-arrow(principal, domain, codomain)
  agent type-hole(principal)
  rule abs <> app -> annihilate
}

# Axis 1: Polymorphism (System F) — terms abstract over types
system "Poly" extend "λ→" {
  agent tyabs(principal, body, bind)
  agent tyapp(principal, result, arg)
  agent forall(principal, body, bind)
  rule tyabs <> tyapp -> annihilate
}

# Axis 2: Dependent types (λP) — types depend on terms
system "Dependent" extend "λ→" {
  agent pi(principal, domain, codomain)
  agent sigma(principal, fst-type, snd-type)
  agent pair(principal, fst, snd)
  agent fst(principal, result)
  agent snd(principal, result)
  rule fst <> pair -> annihilate
  rule snd <> pair -> annihilate
}

# Axis 3: Type operators (λω̲) — types depend on types
system "TyOp" extend "λ→" {
  agent type-abs(principal, body, bind)
  agent type-app(principal, result, arg)
  agent kind-star(principal)
  agent kind-arrow(principal, domain, codomain)
  rule type-abs <> type-app -> annihilate
}

system "λP2" = compose "Poly" + "Dependent" {
  rule tyabs <> fst -> erase
  rule tyabs <> snd -> erase
}

system "λPω" = compose "Dependent" + "TyOp" {
  rule type-abs <> fst -> erase
  rule type-abs <> snd -> erase
}

system "λω" = compose "Poly" + "TyOp" {
  rule tyapp <> type-abs -> annihilate
}

system "λC" = compose "Poly" + "Dependent" + "TyOp" {
  rule tyabs <> fst -> erase
  rule tyabs <> snd -> erase
  rule type-abs <> fst -> erase
  rule type-abs <> snd -> erase
  rule tyapp <> type-abs -> annihilate
}

# ─── λ→ (STLC) ───────────────────────────────────────────────────

def I = \\x:A.x
def K = \\x:A.\\y:B.x
def S = \\f:A -> B -> C.\\g:A -> B.\\x:A.f x (g x)

graph stlc-identity = term I
graph stlc-const = term K
graph stlc-s-combinator = term S
graph stlc-apply-id = term (\\f:A -> B.\\x:A.f x) (\\y:A.y)

# ─── Axis 1: Polymorphism ────────────────────────────────────────

# Λα. λx:α. x  (polymorphic identity)
graph poly-identity {
  let r   = root
  let ta  = tyabs "Λα"
  let a   = abs "λx"
  wire r.principal  -- ta.principal
  wire ta.body      -- a.principal
  wire a.bind       -- a.body
  wire ta.bind      -- a.type
}

# (Λα. λx. x) [Bool]  — active pair: tyabs <> tyapp
graph poly-beta {
  let r    = root
  let ta   = tyabs "Λα"
  let tp   = tyapp
  let a    = abs "λx"
  let arg  = type-base "Bool"
  wire ta.principal -- tp.principal
  wire tp.result    -- r.principal
  wire ta.body      -- a.principal
  wire a.bind       -- a.body
  wire tp.arg       -- arg.principal
  wire ta.bind      -- a.type
}

# ∀α. α→α  (universal type)
graph poly-forall-type {
  let r   = root
  let fa  = forall "∀α"
  let arr = type-arrow "α→α"
  wire r.principal  -- fa.principal
  wire fa.body      -- arr.principal
  wire fa.bind      -- arr.domain
}

# ─── Axis 2: Dependent Types ────────────────────────────────────

# Π(A:*). A→A
graph dep-pi-type {
  let r   = root
  let p   = pi "Π(A:*)"
  let tb  = type-base "A"
  let arr = type-arrow "A→A"
  wire r.principal  -- p.principal
  wire p.domain     -- tb.principal
  wire p.codomain   -- arr.principal
}

# (a, b) : Σ(x:A).B
graph dep-sigma-pair {
  let r   = root
  let sg  = sigma "Σ"
  let p   = pair "(a,b)"
  let a   = var "a"
  let b   = var "b"
  let ta  = type-base "A"
  let tb  = type-base "B"
  wire r.principal   -- p.principal
  wire p.fst         -- a.principal
  wire p.snd         -- b.principal
  wire sg.fst-type   -- ta.principal
  wire sg.snd-type   -- tb.principal
}

# fst (a, b) → a  — active pair: fst <> pair
graph dep-fst-elim {
  let r   = root
  let f   = fst
  let p   = pair "(a,b)"
  let a   = var "a"
  let b   = var "b"
  wire f.principal -- p.principal
  wire f.result    -- r.principal
  wire p.fst       -- a.principal
  wire p.snd       -- b.principal
}

# snd (a, b) → b  — active pair: snd <> pair
graph dep-snd-elim {
  let r   = root
  let s   = snd
  let p   = pair "(a,b)"
  let a   = var "a"
  let b   = var "b"
  wire s.principal -- p.principal
  wire s.result    -- r.principal
  wire p.fst       -- a.principal
  wire p.snd       -- b.principal
}

# ─── Axis 3: Type Operators ─────────────────────────────────────

# (λα:*. α→Nat) Bool  — active pair: type-abs <> type-app
graph tyop-beta {
  let r    = root
  let ta   = type-abs "λα"
  let tp   = type-app
  let arr  = type-arrow "α→Nat"
  let nat  = type-base "Nat"
  let arg  = type-base "Bool"
  wire ta.principal  -- tp.principal
  wire tp.result     -- r.principal
  wire ta.body       -- arr.principal
  wire ta.bind       -- arr.domain
  wire arr.codomain  -- nat.principal
  wire tp.arg        -- arg.principal
}

# ★ → ★  (kind of unary type operators)
graph tyop-kind {
  let r   = root
  let ka  = kind-arrow "★→★"
  let k1  = kind-star "★"
  let k2  = kind-star "★"
  wire r.principal   -- ka.principal
  wire ka.domain     -- k1.principal
  wire ka.codomain   -- k2.principal
}

# ─── Cross-Axis: λω (tyapp <> type-abs) ─────────────────────────

graph fw-cross-annihilate {
  let r    = root
  let tp   = tyapp
  let ta   = type-abs "λα"
  let arr  = type-arrow "α→Nat"
  let nat  = type-base "Nat"
  let arg  = type-base "Bool"
  wire tp.principal  -- ta.principal
  wire tp.result     -- r.principal
  wire ta.body       -- arr.principal
  wire ta.bind       -- arr.domain
  wire arr.codomain  -- nat.principal
  wire tp.arg        -- arg.principal
}

# ─── λC: full corner ────────────────────────────────────────────

graph coc-poly-dep-tyop {
  let r    = root
  let ta   = tyabs "Λα"
  let a    = abs "λx"
  let p    = pi "Π"
  let ka   = kind-arrow "★→★"
  let k1   = kind-star "★"
  let k2   = kind-star "★"
  wire r.principal   -- ta.principal
  wire ta.body       -- a.principal
  wire a.bind        -- a.body
  wire ta.bind       -- p.principal
  wire p.domain      -- ka.principal
  wire ka.domain     -- k1.principal
  wire ka.codomain   -- k2.principal
}

# ─── Untyped baselines ──────────────────────────────────────────

def Omega = (\\x.x x) (\\x.x x)
def Y = \\f.(\\x.f (x x)) (\\x.f (x x))

graph omega = term Omega
graph y-combinator = term Y`,
  },
];

export default examples;
