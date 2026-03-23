// Tests for the `data` declaration — syntactic sugar that desugars into
// constructor agents + duplicator agent + duplicator rules.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { getRedexes } from "@deltanets/core";
import { compileAndAssert, collectRules, collectAgentPorts, reduceAll, readNat, readRootType } from "./helpers.ts";

// ─── Minimal data Nat using sugar ──────────────────────────────────

const DATA_NAT = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

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
}
`;

// ─── Basic desugaring checks ───────────────────────────────────────

Deno.test("data: Nat desugars constructor agents", () => {
  const core = compileAndAssert(DATA_NAT);
  const nat = core.systems.get("Nat")!;
  assertEquals(nat.agents.has("Zero"), true, "Zero agent exists");
  assertEquals(nat.agents.has("Succ"), true, "Succ agent exists");
  // Check port structure
  assertEquals(nat.agents.get("Zero")!.ports.length, 1);  // just principal
  assertEquals(nat.agents.get("Succ")!.ports.length, 2);  // principal + pred
  assertEquals(nat.agents.get("Succ")!.ports[1].name, "pred");
});

Deno.test("data: Nat desugars dup_nat agent", () => {
  const core = compileAndAssert(DATA_NAT);
  const nat = core.systems.get("Nat")!;
  assertEquals(nat.agents.has("dup_nat"), true, "dup_nat agent exists");
  const dup = nat.agents.get("dup_nat")!;
  assertEquals(dup.ports.length, 3);
  assertEquals(dup.ports[0].name, "principal");
  assertEquals(dup.ports[1].name, "copy1");
  assertEquals(dup.ports[2].name, "copy2");
});

Deno.test("data: Nat desugars dup rules for each constructor", () => {
  const core = compileAndAssert(DATA_NAT);
  const nat = core.systems.get("Nat")!;
  const dupRules = nat.rules.filter(
    (r) => r.agentA === "dup_nat" || r.agentB === "dup_nat",
  );
  assertEquals(dupRules.length, 2, "one dup rule per constructor");
  const targets = new Set(dupRules.map((r) => r.agentB));
  assertEquals(targets.has("Zero"), true);
  assertEquals(targets.has("Succ"), true);
});

Deno.test("data: registers constructorsByType", () => {
  const core = compileAndAssert(DATA_NAT);
  const nat = core.systems.get("Nat")!;
  const ctors = nat.constructorsByType.get("Nat");
  assertEquals(ctors !== undefined, true);
  assertEquals(ctors!.has("Zero"), true);
  assertEquals(ctors!.has("Succ"), true);
});

// ─── Arithmetic still works with data sugar ────────────────────────

function compileAndGetGraph(graphSource: string) {
  const source = DATA_NAT + "\n" + graphSource;
  const core = compileAndAssert(source);
  const rules = collectRules(core);
  const agentPorts = collectAgentPorts(core);
  const graphs = core.graphs;
  const [, gdef] = [...graphs.entries()].at(-1)!;
  if (gdef.kind !== "explicit") throw new Error("expected explicit graph");
  return { graph: gdef.graph, rules, agentPorts };
}

Deno.test("data: 0 + 0 = 0", () => {
  const { graph, rules, agentPorts } = compileAndGetGraph(`
    graph test {
      let r  = root
      let a  = add
      let z1 = Zero
      let z2 = Zero
      wire r.principal -- a.result
      wire a.principal -- z1.principal
      wire a.accum    -- z2.principal
    }
  `);
  reduceAll(graph, rules, agentPorts);
  assertEquals(readNat(graph), 0);
});

Deno.test("data: 2 + 1 = 3", () => {
  const { graph, rules, agentPorts } = compileAndGetGraph(`
    graph test {
      let r  = root
      let a  = add
      let s1 = Succ
      let s2 = Succ
      let z1 = Zero
      let s3 = Succ
      let z2 = Zero
      wire r.principal -- a.result
      wire a.principal -- s1.principal
      wire s1.pred    -- s2.principal
      wire s2.pred    -- z1.principal
      wire a.accum    -- s3.principal
      wire s3.pred    -- z2.principal
    }
  `);
  reduceAll(graph, rules, agentPorts);
  assertEquals(readNat(graph), 3);
});

// ─── Duplicator actually works ─────────────────────────────────────

Deno.test("data: dup_nat duplicates Zero", () => {
  const { graph, rules, agentPorts } = compileAndGetGraph(`
    graph test {
      let r  = root
      let d  = dup_nat
      let z  = Zero
      let e  = era
      wire r.principal -- d.copy1
      wire d.principal -- z.principal
      wire d.copy2     -- e.principal
    }
  `);
  reduceAll(graph, rules, agentPorts);
  assertEquals(readRootType(graph), "Zero");
});

Deno.test("data: dup_nat duplicates Succ(Zero)", () => {
  const { graph, rules, agentPorts } = compileAndGetGraph(`
    graph test {
      let r  = root
      let d  = dup_nat
      let s  = Succ
      let z  = Zero
      let e  = era
      wire r.principal -- d.copy1
      wire d.principal -- s.principal
      wire s.pred      -- z.principal
      wire d.copy2     -- e.principal
    }
  `);
  reduceAll(graph, rules, agentPorts);
  assertEquals(readNat(graph), 1);
});

// ─── Data Bool ─────────────────────────────────────────────────────

const DATA_BOOL = `
include "prelude"

system "Bool" extend "Prelude" {
  data Bool {
    | True
    | False
  }

  agent not(principal, result)
  rule not <> True -> {
    let f = False
    relink left.result f.principal
  }
  rule not <> False -> {
    let t = True
    relink left.result t.principal
  }
}
`;

Deno.test("data: Bool desugars agents and dup", () => {
  const core = compileAndAssert(DATA_BOOL);
  const sys = core.systems.get("Bool")!;
  assertEquals(sys.agents.has("True"), true);
  assertEquals(sys.agents.has("False"), true);
  assertEquals(sys.agents.has("dup_bool"), true);
  assertEquals(sys.agents.get("True")!.ports.length, 1);
  assertEquals(sys.agents.get("False")!.ports.length, 1);
});

// ─── Data with multiple fields (List) ──────────────────────────────

const DATA_LIST = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }
}

system "List" extend "Nat" {
  data List {
    | Nil
    | Cons(head : Nat, tail : List)
  }
}
`;

Deno.test("data: List desugars Nil and Cons agents", () => {
  const core = compileAndAssert(DATA_LIST);
  const sys = core.systems.get("List")!;
  assertEquals(sys.agents.has("Nil"), true);
  assertEquals(sys.agents.has("Cons"), true);
  assertEquals(sys.agents.get("Nil")!.ports.length, 1);     // just principal
  assertEquals(sys.agents.get("Cons")!.ports.length, 3);     // principal + head + tail
  assertEquals(sys.agents.get("Cons")!.ports[1].name, "head");
  assertEquals(sys.agents.get("Cons")!.ports[2].name, "tail");
});

Deno.test("data: List desugars dup_list with rules", () => {
  const core = compileAndAssert(DATA_LIST);
  const sys = core.systems.get("List")!;
  assertEquals(sys.agents.has("dup_list"), true);
  const dupRules = sys.rules.filter(
    (r) => r.agentA === "dup_list" || r.agentB === "dup_list",
  );
  assertEquals(dupRules.length, 2, "dup_list rules for Nil and Cons");
});

// ─── Data sugar + prove integration ────────────────────────────────

const DATA_PROVE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

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

system "Eq" extend "Nat" {
  agent refl(principal)
  agent sym(principal, result)
  agent trans(principal, result, second)
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule trans <> refl -> { relink left.result left.second }
}

system "NatEq" extend "Eq" {
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> {
    let r = refl
    relink left.result r.principal
  }
}

system "Proofs" extend "NatEq" {
  prove plus_zero_right(n : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> refl
    | Succ(k) -> cong_succ(plus_zero_right(k))
  }
}
`;

Deno.test("data: prove works with data-declared constructors", () => {
  const core = compileAndAssert(DATA_PROVE);
  const sys = core.systems.get("Proofs")!;
  assertEquals(sys.agents.has("plus_zero_right"), true, "prove agent generated");
  const pzrRules = sys.rules.filter(
    (r) => r.agentA === "plus_zero_right" || r.agentB === "plus_zero_right",
  );
  assertEquals(pzrRules.length >= 2, true, "prove rules generated for Zero and Succ");
});

// ─── Parameterized data types ──────────────────────────────────────

const DATA_PARAM_LIST = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }
}

system "List" extend "Nat" {
  data List(A) {
    | Nil
    | Cons(head : A, tail : List(A))
  }
}
`;

Deno.test("data: parameterized List(A) desugars agents", () => {
  const core = compileAndAssert(DATA_PARAM_LIST);
  const sys = core.systems.get("List")!;
  assertEquals(sys.agents.has("Nil"), true);
  assertEquals(sys.agents.has("Cons"), true);
  assertEquals(sys.agents.get("Nil")!.ports.length, 1);
  assertEquals(sys.agents.get("Cons")!.ports.length, 3);
});

Deno.test("data: parameterized List(A) desugars dup_list", () => {
  const core = compileAndAssert(DATA_PARAM_LIST);
  const sys = core.systems.get("List")!;
  assertEquals(sys.agents.has("dup_list"), true);
  const dupRules = sys.rules.filter(
    (r) => r.agentA === "dup_list" || r.agentB === "dup_list",
  );
  assertEquals(dupRules.length, 2);
});

Deno.test("data: parameterized List(A) stores params in constructorTyping", () => {
  const core = compileAndAssert(DATA_PARAM_LIST);
  const sys = core.systems.get("List")!;
  const nilInfo = sys.constructorTyping.get("Nil")!;
  assertEquals(nilInfo.typeName, "List");
  assertEquals(nilInfo.params, ["A"]);
  assertEquals(nilInfo.fields.length, 0);

  const consInfo = sys.constructorTyping.get("Cons")!;
  assertEquals(consInfo.typeName, "List");
  assertEquals(consInfo.params, ["A"]);
  assertEquals(consInfo.fields.length, 2);
  assertEquals(consInfo.fields[0].name, "head");
  assertEquals(consInfo.fields[0].type, { kind: "ident", name: "A" });
  assertEquals(consInfo.fields[1].name, "tail");
  assertEquals(consInfo.fields[1].type, { kind: "call", name: "List", args: [{ kind: "ident", name: "A" }] });
});

Deno.test("data: non-parameterized data has empty params", () => {
  const core = compileAndAssert(DATA_NAT);
  const sys = core.systems.get("Nat")!;
  const succInfo = sys.constructorTyping.get("Succ")!;
  assertEquals(succInfo.params, []);
  assertEquals(succInfo.indices, []);
  assertEquals(succInfo.fields[0].type, { kind: "ident", name: "Nat" });
});

// ─── Indexed data types ────────────────────────────────────────────

const DATA_VEC = `
include "prelude"

system "Vec" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

  data Vec(A, n : Nat) {
    | VNil : Vec(A, Zero)
    | VCons(head : A, tail : Vec(A, k)) : Vec(A, Succ(k))
  }
}
`;

Deno.test("data: indexed Vec(A, n : Nat) parses indices", () => {
  const core = compileAndAssert(DATA_VEC);
  const sys = core.systems.get("Vec")!;
  const vnilInfo = sys.constructorTyping.get("VNil")!;
  assertEquals(vnilInfo.typeName, "Vec");
  assertEquals(vnilInfo.params, ["A"]);
  assertEquals(vnilInfo.indices.length, 1);
  assertEquals(vnilInfo.indices[0].name, "n");
  assertEquals(vnilInfo.indices[0].type, { kind: "ident", name: "Nat" });
  assertEquals(vnilInfo.returnIndices!, [{ kind: "ident", name: "Zero" }]);
});

Deno.test("data: indexed VCons has Succ(k) return index", () => {
  const core = compileAndAssert(DATA_VEC);
  const sys = core.systems.get("Vec")!;
  const vconsInfo = sys.constructorTyping.get("VCons")!;
  assertEquals(vconsInfo.typeName, "Vec");
  assertEquals(vconsInfo.params, ["A"]);
  assertEquals(vconsInfo.indices.length, 1);
  assertEquals(vconsInfo.returnIndices!, [
    { kind: "call", name: "Succ", args: [{ kind: "ident", name: "k" }] },
  ]);
});

Deno.test("data: non-indexed data has empty indices", () => {
  const core = compileAndAssert(DATA_NAT);
  const sys = core.systems.get("Nat")!;
  const zeroInfo = sys.constructorTyping.get("Zero")!;
  assertEquals(zeroInfo.indices, []);
  assertEquals(zeroInfo.returnIndices, undefined);
});
