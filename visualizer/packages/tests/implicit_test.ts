// Tests for implicit arguments in prove blocks.
// Verifies that {name} and {name : Type} syntax parses correctly,
// implicit params are excluded from agent ports, and proofs still compile.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore, core } from "@deltanets/lang";
import { compileAndAssert, NATEQ_SYSTEM } from "./helpers.ts";

const { tokenize, parse } = core;

// ─── Parsing Tests ─────────────────────────────────────────────────

Deno.test("implicit: {A} parsed as implicit param without type", () => {
  const source = `
    system "T" {
      prove foo({A}, n) {
        | Zero -> refl
      }
    }
  `;
  const ast = parse(tokenize(source));
  const sys = ast.find((s) => s.kind === "system")! as { kind: "system"; body: { kind: string; params?: { name: string; implicit?: boolean }[] }[] };
  const prove = sys.body.find((d) => d.kind === "prove")!;
  assertEquals(prove.params![0].name, "A");
  assertEquals(prove.params![0].implicit, true);
  assertEquals(prove.params![1].name, "n");
  assertEquals(prove.params![1].implicit, undefined);
});

Deno.test("implicit: {A : Type} parsed as implicit param with type", () => {
  const source = `
    system "T" {
      prove foo({A : Type}, n : Nat) -> Eq(n, n) {
        | Zero -> refl
      }
    }
  `;
  const ast = parse(tokenize(source));
  const sys = ast.find((s) => s.kind === "system")! as { kind: "system"; body: { kind: string; params?: { name: string; implicit?: boolean; type?: { kind: string; name?: string } }[] }[] };
  const prove = sys.body.find((d) => d.kind === "prove")!;
  assertEquals(prove.params![0].name, "A");
  assertEquals(prove.params![0].implicit, true);
  assertEquals(prove.params![0].type?.kind, "ident");
  assertEquals(prove.params![0].type?.name, "Type");
  assertEquals(prove.params![1].name, "n");
  assertEquals(prove.params![1].implicit, undefined);
  assertEquals(prove.params![1].type?.kind, "ident");
});

// ─── Desugaring Tests ──────────────────────────────────────────────

const BASE = NATEQ_SYSTEM;

Deno.test("implicit: implicit params excluded from agent ports", () => {
  const result = compileAndAssert(BASE + `
    system "Impl" extend "NatEq" {
      prove pzr({A : Type}, n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  const sys = result.systems.get("Impl")!;
  const agent = sys.agents.get("pzr")!;
  // Should only have: principal, result (no port for A)
  assertEquals(agent.ports.length, 2);
  assertEquals(agent.ports[0].name, "principal");
  assertEquals(agent.ports[1].name, "result");
});

Deno.test("implicit: explicit aux params still become ports", () => {
  const result = compileAndAssert(BASE + `
    system "Impl2" extend "NatEq" {
      prove psr({A : Type}, n : Nat, m : Nat) -> Eq(add(n, Succ(m)), Succ(add(n, m))) {
        | Zero -> refl
        | Succ(k) -> cong_succ(psr(k, m))
      }
    }
  `);
  const sys = result.systems.get("Impl2")!;
  const agent = sys.agents.get("psr")!;
  // Should have: principal, result, m (no port for A)
  assertEquals(agent.ports.length, 3);
  assertEquals(agent.ports[0].name, "principal");
  assertEquals(agent.ports[1].name, "result");
  assertEquals(agent.ports[2].name, "m");
});

Deno.test("implicit: prove without implicit args still works", () => {
  const result = compileAndAssert(BASE + `
    system "NoImpl" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }
    }
  `);
  const sys = result.systems.get("NoImpl")!;
  const agent = sys.agents.get("pzr")!;
  assertEquals(agent.ports.length, 2);
});
