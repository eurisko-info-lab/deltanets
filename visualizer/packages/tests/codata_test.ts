// Tests for coinductive types (codata): guard agents, observation agents,
// interaction rules, compute rules, and productivity checking.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NAT_SYSTEM, NATEQ_SYSTEM, compileAndAssert, collectRules, collectAgentPorts, reduceAll, readRootType } from "./helpers.ts";

const BASE = NAT_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic codata declaration ──────────────────────────────────────

Deno.test("codata: basic Stream compiles with guard and observations", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("guard_stream"), true, "should have guard_stream agent");
  assertEquals(sys.agents.has("head"), true, "should have head observation");
  assertEquals(sys.agents.has("tail"), true, "should have tail observation");
});

Deno.test("codata: generates dup agent", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("dup_stream"), true, "should have dup_stream");
});

Deno.test("codata: guard agent has correct ports", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }
  `);
  const sys = result.systems.get("T")!;
  const guard = sys.agents.get("guard_stream")!;
  const portNames = guard.ports.map((p) => p.name);
  assertEquals(portNames.includes("principal"), true, "should have principal port");
  assertEquals(portNames.includes("head"), true, "should have head port");
  assertEquals(portNames.includes("tail"), true, "should have tail port");
});

Deno.test("codata: observation agents have correct ports", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }
  `);
  const sys = result.systems.get("T")!;
  const headAgent = sys.agents.get("head")!;
  const headPorts = headAgent.ports.map((p) => p.name);
  assertEquals(headPorts.includes("principal"), true, "head: should have principal");
  assertEquals(headPorts.includes("result"), true, "head: should have result");

  const tailAgent = sys.agents.get("tail")!;
  const tailPorts = tailAgent.ports.map((p) => p.name);
  assertEquals(tailPorts.includes("principal"), true, "tail: should have principal");
  assertEquals(tailPorts.includes("result"), true, "tail: should have result");
});

// ─── Observation rules (interaction net reduction) ─────────────────

Deno.test("codata: head observation reduces", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }

    graph test {
      let r = root
      let h = head
      let g = guard_stream
      let a = Zero
      let b = Succ
      let c = Zero
      wire r.principal -- h.result
      wire h.principal -- g.principal
      wire g.head -- a.principal
      wire g.tail -- b.principal
      wire b.pred -- c.principal
    }
  `);
  const g = result.graphs.get("test")!;
  if (g.kind !== "explicit") throw new Error("expected explicit graph");
  const steps = reduceAll(g.graph, collectRules(result), collectAgentPorts(result));
  assertEquals(steps >= 1, true, "should reduce");
  assertEquals(readRootType(g.graph), "Zero");
});

Deno.test("codata: tail observation reduces", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }

    graph test {
      let r = root
      let t = tail
      let g = guard_stream
      let a = Zero
      let b = Succ
      let c = Zero
      wire r.principal -- t.result
      wire t.principal -- g.principal
      wire g.head -- a.principal
      wire g.tail -- b.principal
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

Deno.test("codata: observation compute rules available to normalizer", () => {
  const result = compile(`
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove head_of_guard(n : Nat) -> Eq(head(guard_stream(n, Zero)), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("codata: tail compute rule normalizes", () => {
  const result = compile(`
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove tail_of_guard(n : Nat, m : Nat) -> Eq(tail(guard_stream(n, m)), m) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Multi-field codata ────────────────────────────────────────────

Deno.test("codata: three-field codata compiles", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Triple(A, B, C) { first : A, second : B, third : C }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.agents.has("guard_triple"), true, "guard_triple");
  assertEquals(sys.agents.has("first"), true, "first observation");
  assertEquals(sys.agents.has("second"), true, "second observation");
  assertEquals(sys.agents.has("third"), true, "third observation");
});

// ─── Codata in system extend ───────────────────────────────────────

Deno.test("codata: extends another system", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }

    system "T2" extend "T" {
      codata CoList(A) { isNil : Nat, hd : A, tl : CoList(A) }
    }
  `);
  const sys = result.systems.get("T2")!;
  assertEquals(sys.agents.has("guard_stream"), true, "inherited guard_stream");
  assertEquals(sys.agents.has("guard_colist"), true, "new guard_colist");
});

// ─── Productivity checking ─────────────────────────────────────────

Deno.test("codata: productive corecursion accepted", () => {
  const result = compile(`
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove repeat(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, repeat(Zero))
        | Succ(k) -> guard_stream(Zero, repeat(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("codata: unproductive corecursion rejected", () => {
  const result = compile(`
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove bad(n : Nat) -> Stream(Nat) {
        | Zero -> bad(Zero)
        | Succ(k) -> bad(k)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject unproductive corecursion");
  assertEquals(
    result.errors.some((e) => e.includes("not productive")),
    true,
    `expected productivity error, got: ${result.errors}`,
  );
});

// ─── Constructor typing registration ───────────────────────────────

Deno.test("codata: guard registered in constructorTyping", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.constructorTyping.has("guard_stream"), true, "guard_stream in typing");
  const info = sys.constructorTyping.get("guard_stream")!;
  assertEquals(info.typeName, "Stream");
  assertEquals(info.params, ["A"]);
});

Deno.test("codata: guard registered in constructorsByType", () => {
  const result = compileAndAssert(BASE + `
    system "T" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }
    }
  `);
  const sys = result.systems.get("T")!;
  assertEquals(sys.constructorsByType.has("Stream"), true, "Stream in constructorsByType");
  assertEquals(sys.constructorsByType.get("Stream")!.has("guard_stream"), true, "guard_stream is constructor");
});
