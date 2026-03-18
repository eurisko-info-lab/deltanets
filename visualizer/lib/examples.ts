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
];

export default examples;
