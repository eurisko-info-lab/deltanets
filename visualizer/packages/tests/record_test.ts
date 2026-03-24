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

// ─── Primitive projections: eta-reduction ──────────────────────────
// mkR(f1(p), f2(p), ..., fn(p)) ≡ p

Deno.test("record: eta-reduction in normalize — mkPair(fst(p), snd(p)) = p", async () => {
  const { normalize, withNormTable } = await import("../lang/core/normalize.ts");
  const recordDefs = new Map<string, { ctor: string; fields: string[] }>([
    ["mkPair", { ctor: "mkPair", fields: ["fst", "snd"] }],
  ]);
  const result = withNormTable([], () => {
    return normalize({
      kind: "call", name: "mkPair", args: [
        { kind: "call", name: "fst", args: [{ kind: "ident", name: "p" }] },
        { kind: "call", name: "snd", args: [{ kind: "ident", name: "p" }] },
      ],
    });
  }, undefined, recordDefs);
  assertEquals(result.kind, "ident");
  assertEquals((result as any).name, "p");
});

Deno.test("record: eta-reduction does NOT fire with mismatched base", async () => {
  const { normalize, withNormTable } = await import("../lang/core/normalize.ts");
  const recordDefs = new Map<string, { ctor: string; fields: string[] }>([
    ["mkPair", { ctor: "mkPair", fields: ["fst", "snd"] }],
  ]);
  const result = withNormTable([], () => {
    return normalize({
      kind: "call", name: "mkPair", args: [
        { kind: "call", name: "fst", args: [{ kind: "ident", name: "p" }] },
        { kind: "call", name: "snd", args: [{ kind: "ident", name: "q" }] },
      ],
    });
  }, undefined, recordDefs);
  assertEquals(result.kind, "call");
  assertEquals((result as any).name, "mkPair");
});

Deno.test("record: eta-reduction does NOT fire with wrong projection order", async () => {
  const { normalize, withNormTable } = await import("../lang/core/normalize.ts");
  const recordDefs = new Map<string, { ctor: string; fields: string[] }>([
    ["mkPair", { ctor: "mkPair", fields: ["fst", "snd"] }],
  ]);
  const result = withNormTable([], () => {
    return normalize({
      kind: "call", name: "mkPair", args: [
        { kind: "call", name: "snd", args: [{ kind: "ident", name: "p" }] },
        { kind: "call", name: "fst", args: [{ kind: "ident", name: "p" }] },
      ],
    });
  }, undefined, recordDefs);
  assertEquals(result.kind, "call");
  assertEquals((result as any).name, "mkPair");
});

Deno.test("record: eta in prove — mkPair(fst(p), snd(p)) ≡ p", () => {
  const result = compile(`
    system "T" extend "Nat" {
      record Pair(A, B) { fst : A, snd : B }

      prove eta_pair(p : Pair(Nat, Nat)) -> Eq(mkPair(fst(p), snd(p)), p) {
        | mkPair(a, b) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("record: eta 3-field record — mk(f1(p), f2(p), f3(p)) ≡ p", () => {
  const result = compile(`
    system "T" extend "Nat" {
      record Triple(A, B, C) { first : A, second : B, third : C }

      prove eta_triple(p : Triple(Nat, Nat, Nat)) -> Eq(mkTriple(first(p), second(p), third(p)), p) {
        | mkTriple(a, b, c) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("record: eta for Point — mkPoint(x(p), y(p)) ≡ p", () => {
  const result = compile(`
    system "T" extend "Nat" {
      record Point { x : Nat, y : Nat }

      prove eta_point(p : Point) -> Eq(mkPoint(x(p), y(p)), p) {
        | mkPoint(a, b) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("record: beta-eta round-trip", () => {
  const result = compile(`
    system "T" extend "Nat" {
      record Pair(A, B) { fst : A, snd : B }

      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove beta_fst(n : Nat, m : Nat) -> Eq(fst(mkPair(n, m)), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }

      prove eta_pair(p : Pair(Nat, Nat)) -> Eq(mkPair(fst(p), snd(p)), p) {
        | mkPair(a, b) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
