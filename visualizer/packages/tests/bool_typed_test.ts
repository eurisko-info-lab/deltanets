// End-to-end tests for typed Bool prove blocks.
// Verifies that Bool proofs generated via `prove` syntax with dependent
// type checking compile, type-check, and reduce identically to hand-written versions.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { collectRules, collectAgentPorts, reduceAll, readRootType } from "./helpers.ts";

// ─── Helpers ───────────────────────────────────────────────────────

const BASE_SYSTEM = `
include "prelude"

system "Bool" extend "Prelude" {
  agent True(principal)
  agent False(principal)
  agent not(principal, result)
  agent and(principal, result, b)
  agent or(principal, result, b)

  rule not <> True -> { let f = False  relink left.result f.principal }
  rule not <> False -> { let t = True  relink left.result t.principal }
  rule and <> True -> { relink left.result left.b }
  rule and <> False -> { let f = False  relink left.result f.principal  erase left.b }
  rule or <> True -> { let t = True  relink left.result t.principal  erase left.b }
  rule or <> False -> { relink left.result left.b }

  compute not(True) = False
  compute not(False) = True
  compute and(True, y) = y
  compute and(False, y) = False
  compute or(True, y) = True
  compute or(False, y) = y
}

system "Eq" extend "Bool" {
  agent refl(principal)
  agent subst(principal, result, value)
  agent sym(principal, result)
  agent trans(principal, result, second)

  rule subst <> refl -> { relink left.result left.value }
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule trans <> refl -> { relink left.result left.second }
}
`;

function compile(extraSource: string) {
  const source = BASE_SYSTEM + "\n" + extraSource;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `compile errors: ${result.errors}`);
  return result;
}

// ─── Typed Bool Prove System ───────────────────────────────────────

const TYPED_BOOL = `
system "TypedBool" extend "Eq" {
  agent dup_bool(principal, copy1, copy2)
  rule dup_bool <> True -> {
    let t1 = True  let t2 = True
    relink left.copy1 t1.principal
    relink left.copy2 t2.principal
  }
  rule dup_bool <> False -> {
    let f1 = False  let f2 = False
    relink left.copy1 f1.principal
    relink left.copy2 f2.principal
  }

  prove not_not(b : Bool) -> Eq(not(not(b)), b) {
    | True -> refl
    | False -> refl
  }

  prove and_comm_t(b : Bool) -> Eq(and(True, b), and(b, True)) {
    | True -> refl
    | False -> refl
  }
  prove and_comm_f(b : Bool) -> Eq(and(False, b), and(b, False)) {
    | True -> refl
    | False -> refl
  }
  prove and_comm(a : Bool, b : Bool) -> Eq(and(a, b), and(b, a)) {
    | True -> and_comm_t(b)
    | False -> and_comm_f(b)
  }

  prove demorgan(a : Bool, b : Bool) -> Eq(not(and(a, b)), or(not(a), not(b))) {
    | True -> refl
    | False -> refl
  }
}
`;

// ─── Compilation Tests ─────────────────────────────────────────────

Deno.test("bool-typed: all typed prove agents compile", () => {
  const result = compile(TYPED_BOOL);
  const sys = result.systems.get("TypedBool")!;
  assertEquals(sys.agents.has("not_not"), true);
  assertEquals(sys.agents.has("and_comm"), true);
  assertEquals(sys.agents.has("and_comm_t"), true);
  assertEquals(sys.agents.has("and_comm_f"), true);
  assertEquals(sys.agents.has("demorgan"), true);
});

Deno.test("bool-typed: not_not has correct ports", () => {
  const result = compile(TYPED_BOOL);
  const nn = result.systems.get("TypedBool")!.agents.get("not_not")!;
  assertEquals(nn.ports.map((p: { name: string }) => p.name), ["principal", "result"]);
});

Deno.test("bool-typed: and_comm has correct ports (principal + b)", () => {
  const result = compile(TYPED_BOOL);
  const ac = result.systems.get("TypedBool")!.agents.get("and_comm")!;
  assertEquals(ac.ports.map((p: { name: string }) => p.name), ["principal", "result", "b"]);
});

// ─── not_not Reduction Tests ───────────────────────────────────────
// Should be identical to hand-written: 1 step → refl

Deno.test("bool-typed: not_not(True) → refl in 1 step", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let nn = not_not  let t = True
      wire r.principal -- nn.result
      wire nn.principal -- t.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("bool-typed: not_not(False) → refl in 1 step", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let nn = not_not  let f = False
      wire r.principal -- nn.result
      wire nn.principal -- f.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 1);
  assertEquals(readRootType(g.graph), "refl");
});

// ─── and_comm Reduction Tests ──────────────────────────────────────
// Uses cross-lemma calls: and_comm → and_comm_t/f → refl (2 steps)

Deno.test("bool-typed: and_comm(True, True) → refl in 2 steps", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let ac = and_comm  let t1 = True  let t2 = True
      wire r.principal -- ac.result
      wire ac.principal -- t1.principal
      wire ac.b -- t2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("bool-typed: and_comm(True, False) → refl in 2 steps", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let ac = and_comm  let t = True  let f = False
      wire r.principal -- ac.result
      wire ac.principal -- t.principal
      wire ac.b -- f.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("bool-typed: and_comm(False, True) → refl in 2 steps", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let ac = and_comm  let f = False  let t = True
      wire r.principal -- ac.result
      wire ac.principal -- f.principal
      wire ac.b -- t.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("bool-typed: and_comm(False, False) → refl in 2 steps", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let ac = and_comm  let f1 = False  let f2 = False
      wire r.principal -- ac.result
      wire ac.principal -- f1.principal
      wire ac.b -- f2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

// ─── demorgan Reduction Tests ──────────────────────────────────────
// b is auto-erased; 2 steps: demorgan <> True/False → refl, erase <> b

Deno.test("bool-typed: demorgan(True, True) → refl in 2 steps", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let dm = demorgan  let t1 = True  let t2 = True
      wire r.principal -- dm.result
      wire dm.principal -- t1.principal
      wire dm.b -- t2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

Deno.test("bool-typed: demorgan(False, False) → refl in 2 steps", () => {
  const core = compile(TYPED_BOOL + `
    graph test {
      let r  = root  let dm = demorgan  let f1 = False  let f2 = False
      wire r.principal -- dm.result
      wire dm.principal -- f1.principal
      wire dm.b -- f2.principal
    }
  `);
  const g = core.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(core), collectAgentPorts(core));
  assertEquals(steps, 2);
  assertEquals(readRootType(g.graph), "refl");
});

// ─── Type Error Detection ──────────────────────────────────────────

Deno.test("bool-typed: wrong not_not proposition is caught", () => {
  const source = BASE_SYSTEM + `
    system "Wrong" extend "Eq" {
      agent dup_bool(principal, copy1, copy2)
      rule dup_bool <> True -> {
        let t1 = True  let t2 = True
        relink left.copy1 t1.principal  relink left.copy2 t2.principal
      }
      rule dup_bool <> False -> {
        let f1 = False  let f2 = False
        relink left.copy1 f1.principal  relink left.copy2 f2.principal
      }
      prove bad_not_not(b : Bool) -> Eq(not(not(b)), not(b)) {
        | True -> refl
        | False -> refl
      }
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length > 0, true, "expected type errors for wrong Bool proposition");
});

Deno.test("bool-typed: wrong and_comm proof (missing helper) is caught", () => {
  const source = BASE_SYSTEM + `
    system "Wrong2" extend "Eq" {
      agent dup_bool(principal, copy1, copy2)
      rule dup_bool <> True -> {
        let t1 = True  let t2 = True
        relink left.copy1 t1.principal  relink left.copy2 t2.principal
      }
      rule dup_bool <> False -> {
        let f1 = False  let f2 = False
        relink left.copy1 f1.principal  relink left.copy2 f2.principal
      }
      prove bad_and_comm(a : Bool, b : Bool) -> Eq(and(a, b), and(b, a)) {
        | True -> refl
        | False -> refl
      }
    }
  `;
  const result = compileCore(source);
  // True case: Eq(and(True, b), and(b, True)) → Eq(b, and(b, True))
  // sides differ (b vs and(b, True)) → refl fails
  assertEquals(result.errors.length > 0, true, "expected type errors for incomplete and_comm");
});
