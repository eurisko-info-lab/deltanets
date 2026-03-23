// Tests for record types: single-constructor data with named projections.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NAT_SYSTEM, compileAndAssert, collectRules, collectAgentPorts, reduceAll, readRootType } from "./helpers.ts";

const BASE = NAT_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic record declaration ──────────────────────────────────────

Deno.test("record: basic Pair compiles with constructor and projections", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      record Pair(A, B) { fst : A, snd : B }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("mkPair"), true, "should have mkPair agent");
  assertEquals(sys.agents.has("fst"), true, "should have fst projection");
  assertEquals(sys.agents.has("snd"), true, "should have snd projection");
});

Deno.test("record: generates dup agent", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      record Point { x : Nat, y : Nat }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("dup_point"), true, "should have dup_point");
});

// ─── Projection rules ──────────────────────────────────────────────

Deno.test("record: fst projection reduces", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      record Pair(A, B) { fst : A, snd : B }
    }

    graph test {
      let r = root
      let f = fst
      let p = mkPair
      let a = Zero
      let b = Succ
      let c = Zero
      wire r.principal -- f.result
      wire f.principal -- p.principal
      wire p.fst -- a.principal
      wire p.snd -- b.principal
      wire b.pred -- c.principal
    }
  `);
  const g = result.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(result), collectAgentPorts(result));
  assertEquals(steps >= 1, true, "should reduce");
  assertEquals(readRootType(g.graph), "Zero");
});

Deno.test("record: snd projection reduces", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      record Pair(A, B) { fst : A, snd : B }
    }

    graph test {
      let r = root
      let f = snd
      let p = mkPair
      let a = Zero
      let b = Succ
      let c = Zero
      wire r.principal -- f.result
      wire f.principal -- p.principal
      wire p.fst -- a.principal
      wire p.snd -- b.principal
      wire b.pred -- c.principal
    }
  `);
  const g = result.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(result), collectAgentPorts(result));
  assertEquals(steps >= 1, true, "should reduce");
  assertEquals(readRootType(g.graph), "Succ");
});

// ─── Compute rules for type checker ────────────────────────────────

Deno.test("record: projection compute rules available to normalizer", () => {
  const result = compile(`
    system "T" extend "Nat" {
      record Pair(A, B) { fst : A, snd : B }

      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove pair_fst(n : Nat) -> Eq(fst(mkPair(n, Zero)), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
