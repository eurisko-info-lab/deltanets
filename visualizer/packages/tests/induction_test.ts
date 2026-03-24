// End-to-end tests for the Induction system.
// Verifies that proof-by-induction over Nat reduces correctly,
// producing refl for every concrete input.
// Tests both plus_zero_right (n + 0 = n) and plus_succ_right (n + S(m) = S(n + m)).

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM, collectRules, collectAgentPorts, reduceAll, readRootType, countNodes } from "./helpers.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const INDUCTION_SOURCE = NATEQ_SYSTEM + `
system "Induction" extend "NatEq" {
  agent plus_zero_right(principal, result)

  rule plus_zero_right <> Zero -> {
    let r = refl
    relink left.result r.principal
  }
  rule plus_zero_right <> Succ -> {
    let pzr = plus_zero_right
    let cs  = cong_succ
    relink left.result cs.result
    wire cs.principal -- pzr.result
    relink right.pred pzr.principal
  }

  agent plus_succ_right(principal, result, m)

  rule plus_succ_right <> Zero -> {
    let r = refl
    relink left.result r.principal
    erase left.m
  }
  rule plus_succ_right <> Succ -> {
    let psr = plus_succ_right
    let cs  = cong_succ
    relink left.result cs.result
    wire cs.principal -- psr.result
    relink right.pred psr.principal
    relink left.m psr.m
  }

  agent dup_nat(principal, copy1, copy2)

  rule dup_nat <> Zero -> {
    let z1 = Zero
    let z2 = Zero
    relink left.copy1 z1.principal
    relink left.copy2 z2.principal
  }
  rule dup_nat <> Succ -> {
    let d  = dup_nat
    let s1 = Succ
    let s2 = Succ
    relink left.copy1 s1.principal
    relink left.copy2 s2.principal
    relink right.pred d.principal
    wire d.copy1 -- s1.pred
    wire d.copy2 -- s2.pred
  }

  agent plus_comm(principal, result, m)

  rule plus_comm <> Zero -> {
    let pzr = plus_zero_right
    relink left.result pzr.result
    relink left.m pzr.principal
  }
  rule plus_comm <> Succ -> {
    let dm  = dup_nat
    let dk  = dup_nat
    let t   = trans
    let cs  = cong_succ
    let pc  = plus_comm
    let sy  = sym
    let psr = plus_succ_right
    relink left.m dm.principal
    relink right.pred dk.principal
    relink left.result t.result
    wire t.principal -- cs.result
    wire cs.principal -- pc.result
    wire dk.copy1 -- pc.principal
    wire dm.copy1 -- pc.m
    wire t.second -- sy.result
    wire sy.principal -- psr.result
    wire dm.copy2 -- psr.principal
    wire dk.copy2 -- psr.m
  }
}
`;

function compileInduction(graphSource: string) {
  const source = INDUCTION_SOURCE + "\n" + graphSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

// ─── Tests ─────────────────────────────────────────────────────────

Deno.test("induction: system compiles with all agents and rules", () => {
  const result = compileCore(INDUCTION_SOURCE);
  assertEquals(result.errors.length, 0);
  const ind = result.systems.get("Induction")!;
  // 29 Prelude + 2 Nat + 4 Eq + 1 NatEq + 2 pzr + 2 psr + 2 dup + 2 pc = 44
  assertEquals(ind.rules.length, 44);
  assertEquals(ind.agents.has("plus_zero_right"), true);
  assertEquals(ind.agents.has("plus_succ_right"), true);
  assertEquals(ind.agents.has("dup_nat"), true);
  assertEquals(ind.agents.has("plus_comm"), true);
  assertEquals(ind.agents.has("cong_succ"), true);
  assertEquals(ind.agents.has("refl"), true);
  assertEquals(ind.agents.has("add"), true);
});

Deno.test("induction: plus_zero_right(Zero) → refl in 1 step", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- z.principal
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

Deno.test("induction: plus_zero_right(1) → refl in 3 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s   = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s.principal
      wire s.pred        -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 3);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_zero_right(2) → refl in 5 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 5);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_zero_right(3) → refl in 7 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let s3  = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- s3.principal
      wire s3.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 7);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: step count follows 2n+1 formula (n=5)", () => {
  // Build Succ(Succ(Succ(Succ(Succ(Zero))))) = 5
  const core = compileInduction(`
    graph test {
      let r   = root
      let pzr = plus_zero_right
      let s1  = Succ
      let s2  = Succ
      let s3  = Succ
      let s4  = Succ
      let s5  = Succ
      let z   = Zero
      wire r.principal   -- pzr.result
      wire pzr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- s3.principal
      wire s3.pred       -- s4.principal
      wire s4.pred       -- s5.principal
      wire s5.pred       -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 11); // 2*5 + 1
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: verify-two-plus-zero via subst+add", () => {
  // subst(refl, add(Succ(Succ(Zero)), Zero)) should reduce to Succ(Succ(Zero))
  const core = compileInduction(`
    graph test {
      let r   = root
      let sub = subst
      let rf  = refl
      let a   = add
      let s1  = Succ
      let s2  = Succ
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- sub.result
      wire sub.principal -- rf.principal
      wire sub.value     -- a.result
      wire a.principal   -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z1.principal
      wire a.accum       -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  // add(Succ(Succ(Zero)), Zero) → Succ(Succ(Zero))
  // subst(refl, Succ(Succ(Zero))) → Succ(Succ(Zero))
  assertEquals(readRootType(g.graph), "Succ");
  // Succ(Succ(Zero)) = 3 nodes
  assertEquals(countNodes(g.graph), 3);
});

Deno.test("induction: NatEq regression — cong_succ(refl) still works", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let cs  = cong_succ
      let rf  = refl
      wire r.principal  -- cs.result
      wire cs.principal -- rf.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
});

// ─── plus_succ_right tests ─────────────────────────────────────────

Deno.test("induction: plus_succ_right(0, 0) → refl in 2 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- z1.principal
      wire psr.m         -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_succ_right(1, 0) → refl in 4 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let s   = Succ
      let z1  = Zero
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- s.principal
      wire s.pred        -- z1.principal
      wire psr.m         -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 4);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_succ_right(0, 2) → refl in 4 steps", () => {
  // m=2 means 3 erase steps: era<>Succ, era<>Succ, era<>Zero
  // Total: 1 base + 3 erase = 4 steps
  const core = compileInduction(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let z1  = Zero
      let s1  = Succ
      let s2  = Succ
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- z1.principal
      wire psr.m         -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 4);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_succ_right(2, 1) → refl in 7 steps", () => {
  // 2n + m + 2 = 4 + 1 + 2 = 7
  const core = compileInduction(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let s1  = Succ
      let s2  = Succ
      let z1  = Zero
      let sm  = Succ
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z1.principal
      wire psr.m         -- sm.principal
      wire sm.pred       -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 7);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_succ_right formula 2n+m+2 (n=3, m=2) → 10 steps", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let psr = plus_succ_right
      let s1  = Succ
      let s2  = Succ
      let s3  = Succ
      let z1  = Zero
      let m1  = Succ
      let m2  = Succ
      let z2  = Zero
      wire r.principal   -- psr.result
      wire psr.principal -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- s3.principal
      wire s3.pred       -- z1.principal
      wire psr.m         -- m1.principal
      wire m1.pred       -- m2.principal
      wire m2.pred       -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  const steps = reduceAll(g.graph, rules, ports);
  assertEquals(steps, 10); // 2*3 + 2 + 2
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: verify add(2, S(1)) → 4 via subst", () => {
  // add(Succ(Succ(Zero)), Succ(Succ(Zero))) → Succ⁴(Zero) = 4
  const core = compileInduction(`
    graph test {
      let r   = root
      let sub = subst
      let rf  = refl
      let a   = add
      let s1  = Succ
      let s2  = Succ
      let z1  = Zero
      let sm  = Succ
      let s3  = Succ
      let z2  = Zero
      wire r.principal   -- sub.result
      wire sub.principal -- rf.principal
      wire sub.value     -- a.result
      wire a.principal   -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z1.principal
      wire a.accum       -- sm.principal
      wire sm.pred       -- s3.principal
      wire s3.pred       -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  // add(2, 2) = 4 = Succ(Succ(Succ(Succ(Zero))))
  assertEquals(readRootType(g.graph), "Succ");
  assertEquals(countNodes(g.graph), 5); // 4 Succs + 1 Zero
});

// ─── dup_nat tests ─────────────────────────────────────────────────

Deno.test("induction: dup_nat(0) produces two Zeros", () => {
  // Connect copy1 to root via add(copy1, copy2) = add(0,0) = 0
  const core = compileInduction(`
    graph test {
      let r = root
      let d = dup_nat
      let a = add
      let z = Zero
      wire r.principal -- a.result
      wire a.principal -- d.copy1
      wire a.accum     -- d.copy2
      wire d.principal -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "Zero");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: dup_nat(2) + add gives 4", () => {
  // dup_nat(2) → (2, 2); add(2, 2) = 4
  const core = compileInduction(`
    graph test {
      let r  = root
      let d  = dup_nat
      let a  = add
      let s1 = Succ
      let s2 = Succ
      let z  = Zero
      wire r.principal -- a.result
      wire a.principal -- d.copy1
      wire a.accum     -- d.copy2
      wire d.principal -- s1.principal
      wire s1.pred     -- s2.principal
      wire s2.pred     -- z.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "Succ");
  assertEquals(countNodes(g.graph), 5); // 4 Succs + 1 Zero = Succ^4(Zero)
});

// ─── plus_comm tests ───────────────────────────────────────────────

Deno.test("induction: plus_comm(0, 0) → refl", () => {
  const core = compileInduction(`
    graph test {
      let r  = root
      let pc = plus_comm
      let z1 = Zero
      let z2 = Zero
      wire r.principal  -- pc.result
      wire pc.principal -- z1.principal
      wire pc.m         -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_comm(0, 1) → refl", () => {
  const core = compileInduction(`
    graph test {
      let r  = root
      let pc = plus_comm
      let z  = Zero
      let s  = Succ
      let zm = Zero
      wire r.principal  -- pc.result
      wire pc.principal -- z.principal
      wire pc.m         -- s.principal
      wire s.pred       -- zm.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_comm(1, 0) → refl", () => {
  const core = compileInduction(`
    graph test {
      let r  = root
      let pc = plus_comm
      let s  = Succ
      let z1 = Zero
      let z2 = Zero
      wire r.principal  -- pc.result
      wire pc.principal -- s.principal
      wire s.pred       -- z1.principal
      wire pc.m         -- z2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_comm(1, 1) → refl", () => {
  const core = compileInduction(`
    graph test {
      let r  = root
      let pc = plus_comm
      let sn = Succ
      let zn = Zero
      let sm = Succ
      let zm = Zero
      wire r.principal  -- pc.result
      wire pc.principal -- sn.principal
      wire sn.pred      -- zn.principal
      wire pc.m         -- sm.principal
      wire sm.pred      -- zm.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_comm(2, 1) → refl", () => {
  const core = compileInduction(`
    graph test {
      let r  = root
      let pc = plus_comm
      let s1 = Succ
      let s2 = Succ
      let zn = Zero
      let sm = Succ
      let zm = Zero
      wire r.principal  -- pc.result
      wire pc.principal -- s1.principal
      wire s1.pred      -- s2.principal
      wire s2.pred      -- zn.principal
      wire pc.m         -- sm.principal
      wire sm.pred      -- zm.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: plus_comm(2, 3) → refl", () => {
  const core = compileInduction(`
    graph test {
      let r  = root
      let pc = plus_comm
      let s1 = Succ
      let s2 = Succ
      let zn = Zero
      let m1 = Succ
      let m2 = Succ
      let m3 = Succ
      let zm = Zero
      wire r.principal  -- pc.result
      wire pc.principal -- s1.principal
      wire s1.pred      -- s2.principal
      wire s2.pred      -- zn.principal
      wire pc.m         -- m1.principal
      wire m1.pred      -- m2.principal
      wire m2.pred      -- m3.principal
      wire m3.pred      -- zm.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports);
  assertEquals(readRootType(g.graph), "refl");
  assertEquals(countNodes(g.graph), 1);
});

Deno.test("induction: verify plus_comm(2,1) via subst+add → 3", () => {
  const core = compileInduction(`
    graph test {
      let r   = root
      let sub = subst
      let pc  = plus_comm
      let a   = add
      let s1  = Succ
      let s2  = Succ
      let z1  = Zero
      let sm  = Succ
      let z2  = Zero
      let a1  = Succ
      let a2  = Succ
      let z3  = Zero
      let a3  = Succ
      let z4  = Zero
      wire r.principal   -- sub.result
      wire sub.principal -- pc.result
      wire sub.value     -- a.result
      wire pc.principal  -- s1.principal
      wire s1.pred       -- s2.principal
      wire s2.pred       -- z1.principal
      wire pc.m          -- sm.principal
      wire sm.pred       -- z2.principal
      wire a.principal   -- a1.principal
      wire a1.pred       -- a2.principal
      wire a2.pred       -- z3.principal
      wire a.accum       -- a3.principal
      wire a3.pred       -- z4.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const rules = collectRules(core);
  const ports = collectAgentPorts(core);
  reduceAll(g.graph, rules, ports, 500);
  // add(2, 1) = 3 = Succ(Succ(Succ(Zero)))
  assertEquals(readRootType(g.graph), "Succ");
  assertEquals(countNodes(g.graph), 4); // 3 Succs + 1 Zero
});
