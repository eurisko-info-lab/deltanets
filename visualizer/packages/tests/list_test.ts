// End-to-end tests for the ListProofs system.
// Verifies list operations (length, append) and proof-by-induction
// over lists, producing refl for append_nil_right on every input.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NAT_SYSTEM, EQ_AGENTS, collectRules, collectAgentPorts, reduceAll, readRootType, countNodes } from "./helpers.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const LIST_SOURCE = NAT_SYSTEM + `
system "List" extend "Nat" {
  agent Nil(principal)
  agent Cons(principal, head, tail)
  agent length(principal, result)
  agent append(principal, result, ys)

  rule length <> Nil -> { let z = Zero  relink left.result z.principal }
  rule length <> Cons -> {
    let s = Succ
    let l = length
    relink left.result s.principal
    wire s.pred -- l.result
    relink right.tail l.principal
    erase right.head
  }
  rule append <> Nil -> { relink left.result left.ys }
  rule append <> Cons -> {
    let c = Cons
    let a = append
    relink left.result c.principal
    relink right.head c.head
    wire c.tail -- a.result
    relink right.tail a.principal
    relink left.ys a.ys
  }
}

system "Eq" extend "List" {
${EQ_AGENTS}
}

system "ListProofs" extend "Eq" {
  agent cong_cons(principal, result, head)
  rule cong_cons <> refl -> {
    let r = refl
    relink left.result r.principal
    erase left.head
  }

  agent append_nil_right(principal, result)
  rule append_nil_right <> Nil -> {
    let r = refl
    relink left.result r.principal
  }
  rule append_nil_right <> Cons -> {
    let anr = append_nil_right
    let cc  = cong_cons
    relink left.result cc.result
    wire cc.principal -- anr.result
    relink right.tail anr.principal
    relink right.head cc.head
  }
}
`;

function compileList(graphSource: string) {
  const source = LIST_SOURCE + "\n" + graphSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

// ─── Tests ─────────────────────────────────────────────────────────

Deno.test("list: system compiles with all agents and rules", () => {
  const result = compileCore(LIST_SOURCE);
  assertEquals(result.errors.length, 0);
  const lp = result.systems.get("ListProofs")!;
  // Nat(2) + List(4) + Eq(4) + ListProofs(3) = 13 rules
  assertEquals(lp.rules.length, 13);
  assertEquals(lp.agents.has("Nil"), true);
  assertEquals(lp.agents.has("Cons"), true);
  assertEquals(lp.agents.has("length"), true);
  assertEquals(lp.agents.has("append"), true);
  assertEquals(lp.agents.has("cong_cons"), true);
  assertEquals(lp.agents.has("append_nil_right"), true);
});

// ─── Computation tests ─────────────────────────────────────────────

Deno.test("list: length(Nil) = Zero", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let len = length
      let n   = Nil
      wire r.principal   -- len.result
      wire len.principal -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "Zero");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("list: length([0]) = Succ(Zero)", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let len = length
      let c   = Cons
      let z   = Zero
      let n   = Nil
      wire r.principal   -- len.result
      wire len.principal -- c.principal
      wire c.head        -- z.principal
      wire c.tail        -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 3);   // len<>Cons, erase Zero, len<>Nil
  assertEquals(readRootType(g.graph), "Succ");
  assertEquals(countNodes(g.graph), 2);  // Succ → Zero
});

Deno.test("list: length([0, 0]) = 2", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let len = length
      let c1  = Cons
      let z1  = Zero
      let c2  = Cons
      let z2  = Zero
      let n   = Nil
      wire r.principal   -- len.result
      wire len.principal -- c1.principal
      wire c1.head       -- z1.principal
      wire c1.tail       -- c2.principal
      wire c2.head       -- z2.principal
      wire c2.tail       -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 5);   // 2*(len<>Cons + erase) + len<>Nil
  assertEquals(readRootType(g.graph), "Succ");
  assertEquals(countNodes(g.graph), 3);  // Succ → Succ → Zero
});

Deno.test("list: append(Nil, [0]) = [0]", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let app = append
      let n   = Nil
      let c   = Cons
      let z   = Zero
      let n2  = Nil
      wire r.principal   -- app.result
      wire app.principal -- n.principal
      wire app.ys        -- c.principal
      wire c.head        -- z.principal
      wire c.tail        -- n2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "Cons");
  assertEquals(countNodes(g.graph), 3);  // Cons(Zero, Nil)
});

Deno.test("list: append([0], [0]) = [0, 0]", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let app = append
      let c1  = Cons
      let z1  = Zero
      let n1  = Nil
      let c2  = Cons
      let z2  = Zero
      let n2  = Nil
      wire r.principal   -- app.result
      wire app.principal -- c1.principal
      wire c1.head       -- z1.principal
      wire c1.tail       -- n1.principal
      wire app.ys        -- c2.principal
      wire c2.head       -- z2.principal
      wire c2.tail       -- n2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);   // app<>Cons, app<>Nil
  assertEquals(readRootType(g.graph), "Cons");
  assertEquals(countNodes(g.graph), 5);  // Cons(Zero, Cons(Zero, Nil))
});

// ─── append_nil_right proof tests ──────────────────────────────────

Deno.test("list: append_nil_right(Nil) → refl in 1 step", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let anr = append_nil_right
      let n   = Nil
      wire r.principal   -- anr.result
      wire anr.principal -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("list: append_nil_right([0]) → refl in 4 steps", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let anr = append_nil_right
      let c   = Cons
      let z   = Zero
      let n   = Nil
      wire r.principal   -- anr.result
      wire anr.principal -- c.principal
      wire c.head        -- z.principal
      wire c.tail        -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 4);   // anr<>Cons, anr<>Nil, cc<>refl, erase Zero
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("list: append_nil_right([0, 0]) → refl in 7 steps", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let anr = append_nil_right
      let c1  = Cons
      let z1  = Zero
      let c2  = Cons
      let z2  = Zero
      let n   = Nil
      wire r.principal   -- anr.result
      wire anr.principal -- c1.principal
      wire c1.head       -- z1.principal
      wire c1.tail       -- c2.principal
      wire c2.head       -- z2.principal
      wire c2.tail       -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 7);   // 3*2 + 1 = 7
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("list: append_nil_right([0, 0, 0]) → refl in 10 steps", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let anr = append_nil_right
      let c1  = Cons
      let z1  = Zero
      let c2  = Cons
      let z2  = Zero
      let c3  = Cons
      let z3  = Zero
      let n   = Nil
      wire r.principal   -- anr.result
      wire anr.principal -- c1.principal
      wire c1.head       -- z1.principal
      wire c1.tail       -- c2.principal
      wire c2.head       -- z2.principal
      wire c2.tail       -- c3.principal
      wire c3.head       -- z3.principal
      wire c3.tail       -- n.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 10);   // 3*3 + 1 = 10
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

// ─── Verification test ─────────────────────────────────────────────

Deno.test("list: verify append_nil_right(Nil) via subst → Nil", () => {
  const core = compileList(`
    graph test {
      let r   = root
      let sub = subst
      let anr = append_nil_right
      let n1  = Nil
      let app = append
      let n2  = Nil
      let n3  = Nil
      wire r.principal   -- sub.result
      wire sub.principal -- anr.result
      wire sub.value     -- app.result
      wire anr.principal -- n1.principal
      wire app.principal -- n2.principal
      wire app.ys        -- n3.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  // anr→refl(1), subst→pass(1), app→Nil(1) or some interleaving = 3-4 steps
  assertEquals(readRootType(g.graph), "Nil");
  assertEquals(countNodes(g.graph), 1);
});
