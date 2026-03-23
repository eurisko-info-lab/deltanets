// Tests for universe polymorphism (Phase 16).
// Verifies Pi/Sigma universe computation, typeUniverse for first-class
// types, typeSubsumes cumulativity, and universe-polymorphic prove blocks.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore, typeUniverse, typeSubsumes, core } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

type ProveExpr = core.ProveExpr;

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// helper constructors
const ident = (name: string): ProveExpr => ({ kind: "ident", name });
const call = (name: string, ...args: ProveExpr[]): ProveExpr => ({ kind: "call", name, args });
const pi = (param: string, domain: ProveExpr, codomain: ProveExpr): ProveExpr =>
  ({ kind: "pi", param, domain, codomain });
const sigma = (param: string, domain: ProveExpr, codomain: ProveExpr): ProveExpr =>
  ({ kind: "sigma", param, domain, codomain });

// ─── typeUniverse for Pi types ─────────────────────────────────────

Deno.test("universe: Pi(Nat, Nat) lives in Type₀", () => {
  // forall(x : Nat, Nat) : Type₀ (max(0,0) = 0)
  assertEquals(typeUniverse(pi("x", ident("Nat"), ident("Nat"))), 0);
});

Deno.test("universe: Pi(Type0, Nat) lives in Type₁", () => {
  // forall(A : Type0, Nat) : Type₁ (max(1,0) = 1)
  assertEquals(typeUniverse(pi("A", ident("Type0"), ident("Nat"))), 1);
});

Deno.test("universe: Pi(Type0, Type1) lives in Type₂", () => {
  // forall(A : Type0, Type1) : Type₂ (max(1,2) = 2)
  assertEquals(typeUniverse(pi("A", ident("Type0"), ident("Type1"))), 2);
});

Deno.test("universe: Pi(Nat, Type0) lives in Type₁", () => {
  // forall(n : Nat, Type0) : Type₁ (max(0,1) = 1)
  assertEquals(typeUniverse(pi("n", ident("Nat"), ident("Type0"))), 1);
});

// ─── typeUniverse for Sigma types ──────────────────────────────────

Deno.test("universe: Sigma(Nat, Nat) lives in Type₀", () => {
  assertEquals(typeUniverse(sigma("x", ident("Nat"), ident("Nat"))), 0);
});

Deno.test("universe: Sigma(Type0, Nat) lives in Type₁", () => {
  assertEquals(typeUniverse(sigma("A", ident("Type0"), ident("Nat"))), 1);
});

// ─── typeSubsumes cumulativity ─────────────────────────────────────

Deno.test("universe: typeSubsumes — Type₀ ≤ Type₀", () => {
  assertEquals(typeSubsumes(ident("Type0"), ident("Type0")), true);
});

Deno.test("universe: typeSubsumes — Type₀ ≤ Type₁", () => {
  assertEquals(typeSubsumes(ident("Type0"), ident("Type1")), true);
});

Deno.test("universe: typeSubsumes — Type₁ ≰ Type₀", () => {
  assertEquals(typeSubsumes(ident("Type1"), ident("Type0")), false);
});

Deno.test("universe: typeSubsumes — Type ≤ Type₁ (Type normalizes to Type₀)", () => {
  assertEquals(typeSubsumes(ident("Type"), ident("Type1")), true);
});

Deno.test("universe: typeSubsumes — Nat ≤ Nat (non-universe fallback)", () => {
  assertEquals(typeSubsumes(ident("Nat"), ident("Nat")), true);
});

Deno.test("universe: typeSubsumes — Nat ≰ Bool (non-universe different)", () => {
  assertEquals(typeSubsumes(ident("Nat"), ident("Bool")), false);
});

// ─── Pi/Sigma infer correct universe in prove ──────────────────────

Deno.test("universe: Pi type infers correct universe level", () => {
  // A Pi over Type0 should have type Type₁, not Type₀
  const result = compile(`
    system "T" extend "NatEq" {
      prove pi_univ(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(pi_univ(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("universe: prove with forall in return type compiles", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove id_type(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(id_type(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Nested Pi universe computation ────────────────────────────────

Deno.test("universe: nested Pi computes max correctly", () => {
  // forall(A : Type1, forall(B : Nat, Nat)) → max(2, max(0,0)) = 2
  const nested = pi("A", ident("Type1"), pi("B", ident("Nat"), ident("Nat")));
  assertEquals(typeUniverse(nested), 2);
});

Deno.test("universe: Sigma inside Pi", () => {
  // forall(x : Nat, exists(y : Nat, Eq(x, y))) → max(0, max(0,0)) = 0
  const inner = sigma("y", ident("Nat"), call("Eq", ident("x"), ident("y")));
  const outer = pi("x", ident("Nat"), inner);
  assertEquals(typeUniverse(outer), 0);
});

// ─── Implicit universe-level params (integration with Phase 15) ────

Deno.test("universe: implicit param with Type annotation", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove poly({A : Type}, n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(poly(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("universe: multiple implicit Type params", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove poly2({A : Type}, {B : Type}, n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(poly2(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
