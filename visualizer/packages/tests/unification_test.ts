// Tests for the unification engine and implicit argument solving (Phase 15).
// Verifies metavar creation, occurs check, unification, zonking,
// and implicit parameter inference in prove/lemma calls.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import {
  freshMeta,
  unify,
  type UnifCtx,
  zonk,
} from "../lang/core/typecheck-prove.ts";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Unit tests for the unification engine ─────────────────────────

Deno.test("unify: identical idents", () => {
  const ctx: UnifCtx = new Map();
  const a = { kind: "ident" as const, name: "Nat" };
  const b = { kind: "ident" as const, name: "Nat" };
  assertEquals(unify(a, b, ctx), true);
});

Deno.test("unify: different idents fail", () => {
  const ctx: UnifCtx = new Map();
  const a = { kind: "ident" as const, name: "Nat" };
  const b = { kind: "ident" as const, name: "Bool" };
  assertEquals(unify(a, b, ctx), false);
});

Deno.test("unify: metavar solves to ident", () => {
  const ctx: UnifCtx = new Map();
  const m = freshMeta();
  const nat = { kind: "ident" as const, name: "Nat" };
  assertEquals(unify(m, nat, ctx), true);
  assertEquals(m.kind, "metavar");
  if (m.kind === "metavar") {
    assertEquals(ctx.get(m.id)?.kind, "ident");
  }
});

Deno.test("unify: metavar solves to call", () => {
  const ctx: UnifCtx = new Map();
  const m = freshMeta();
  const eq = { kind: "call" as const, name: "Eq", args: [
    { kind: "ident" as const, name: "a" },
    { kind: "ident" as const, name: "b" },
  ]};
  assertEquals(unify(m, eq, ctx), true);
  if (m.kind === "metavar") {
    const sol = ctx.get(m.id)!;
    assertEquals(sol.kind, "call");
    if (sol.kind === "call") {
      assertEquals(sol.name, "Eq");
      assertEquals(sol.args.length, 2);
    }
  }
});

Deno.test("unify: occurs check prevents cyclic solution", () => {
  const ctx: UnifCtx = new Map();
  const m = freshMeta();
  if (m.kind !== "metavar") throw new Error("expected metavar");
  const cyclic = { kind: "call" as const, name: "Succ", args: [m] };
  assertEquals(unify(m, cyclic, ctx), false);
});

Deno.test("unify: call args pairwise", () => {
  const ctx: UnifCtx = new Map();
  const m1 = freshMeta();
  const m2 = freshMeta();
  const a = { kind: "call" as const, name: "Eq", args: [m1, m2] };
  const b = { kind: "call" as const, name: "Eq", args: [
    { kind: "ident" as const, name: "x" },
    { kind: "ident" as const, name: "y" },
  ]};
  assertEquals(unify(a, b, ctx), true);
  if (m1.kind === "metavar" && m2.kind === "metavar") {
    const s1 = ctx.get(m1.id)!;
    const s2 = ctx.get(m2.id)!;
    assertEquals(s1.kind === "ident" && s1.name, "x");
    assertEquals(s2.kind === "ident" && s2.name, "y");
  }
});

Deno.test("unify: call name mismatch fails", () => {
  const ctx: UnifCtx = new Map();
  const a = { kind: "call" as const, name: "Eq", args: [{ kind: "ident" as const, name: "x" }] };
  const b = { kind: "call" as const, name: "Neq", args: [{ kind: "ident" as const, name: "x" }] };
  assertEquals(unify(a, b, ctx), false);
});

Deno.test("zonk: resolves metavar chain", () => {
  const ctx: UnifCtx = new Map();
  const m1 = freshMeta();
  const m2 = freshMeta();
  if (m1.kind !== "metavar" || m2.kind !== "metavar") throw new Error("expected metavar");
  ctx.set(m1.id, m2);
  ctx.set(m2.id, { kind: "ident", name: "Nat" });
  const result = zonk(m1, ctx);
  assertEquals(result.kind, "ident");
  if (result.kind === "ident") assertEquals(result.name, "Nat");
});

Deno.test("zonk: unsolved metavar passes through", () => {
  const ctx: UnifCtx = new Map();
  const m = freshMeta();
  const result = zonk(m, ctx);
  assertEquals(result.kind, "metavar");
});

// ─── Integration: implicit arg inference in prove calls ────────────

Deno.test("implicit: cross-lemma implicit param inferred from explicit arg type", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove pzr(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr(k))
      }

      prove uses_pzr({A : Nat}, m : Nat) -> Eq(add(m, Zero), m) {
        | Zero -> refl
        | Succ(k) -> cong_succ(uses_pzr(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("implicit: recursive call with implicit param", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove pzr2({A : Nat}, n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pzr2(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("implicit: multiple implicit params", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove multi_impl({A : Nat}, {B : Nat}, n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(multi_impl(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("implicit: implicit param used in return type", () => {
  // The implicit param A is used in the return type.
  // When calling reflA(k), A should be inferred from k's type context.
  const result = compile(`
    system "T" extend "NatEq" {
      prove reflA({A : Nat}, n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
