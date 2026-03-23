// Tests for Phase 27: Coercions — coercion name = From -> To via func
// Implicit type conversions registered per pair for the type checker.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";

// Base system with data types (using data declarations for type inference)
const BASE = `
include "prelude"

system "Base" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

  agent add(principal, result, accum)
  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))

  agent refl(principal)
  agent cong_succ(principal, result)
  rule cong_succ <> refl -> {
    let r = refl
    relink left.result r.principal
  }
}
`;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic coercion ────────────────────────────────────────────────

Deno.test("coercion: parses coercion declaration", () => {
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      coercion nat_to_bool = Nat -> Bool via natToBool
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("coercion: implicit conversion in prove return type", () => {
  // prove returns Bool but body produces Nat — coercion should accept
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      coercion nat_to_bool = Nat -> Bool via natToBool

      prove test(n : Nat) -> Bool {
        | Zero -> Zero
        | Succ(k) -> Succ(k)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("coercion: type mismatch without coercion", () => {
  // Without coercion, returning Nat when Bool is expected should error
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      prove test(n : Nat) -> Bool {
        | Zero -> Zero
        | Succ(k) -> Succ(k)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, `expected type error but got none`);
});

Deno.test("coercion: correct type needs no coercion", () => {
  // Returning Bool when Bool is expected — no coercion needed
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      prove test(n : Nat) -> Bool {
        | Zero -> True
        | Succ(k) -> False
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("coercion: coercion in one direction only", () => {
  // coercion Nat -> Bool exists but not Bool -> Nat
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      coercion nat_to_bool = Nat -> Bool via natToBool

      prove test(n : Nat) -> Nat {
        | Zero -> True
        | Succ(k) -> False
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, `expected type error for reverse direction`);
});

// ─── Multiple coercions ────────────────────────────────────────────

Deno.test("coercion: multiple coercions in same system", () => {
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      data Bit {
        | One
        | ZeroBit
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      agent boolToBit(principal, result)
      compute boolToBit(True) = One
      compute boolToBit(False) = ZeroBit

      coercion nat_to_bool = Nat -> Bool via natToBool
      coercion bool_to_bit = Bool -> Bit via boolToBit

      prove testNatBool(n : Nat) -> Bool {
        | Zero -> Zero
        | Succ(k) -> Succ(k)
      }

      prove testBoolBit(n : Nat) -> Bit {
        | Zero -> True
        | Succ(k) -> False
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Coercion in section ──────────────────────────────────────────

Deno.test("coercion: coercion inside section", () => {
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      section S {
        coercion nat_to_bool = Nat -> Bool via natToBool

        prove test(n : Nat) -> Bool {
          | Zero -> Zero
          | Succ(k) -> Succ(k)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Coercion with Eq-type proves ──────────────────────────────────

Deno.test("coercion: Eq-type proves unaffected by coercion declarations", () => {
  // Regular Eq proofs should still work fine even with coercions declared
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      coercion nat_to_bool = Nat -> Bool via natToBool

      prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(addZero(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("coercion: coercion does not help Eq-type mismatches", () => {
  // Coercion is for top-level types, not for Eq sides
  const result = compile(`
    system "T" extend "Base" {
      data Bool {
        | True
        | False
      }

      agent natToBool(principal, result)
      compute natToBool(Zero) = False
      compute natToBool(Succ(k)) = True

      coercion nat_to_bool = Nat -> Bool via natToBool

      prove wrong(n : Nat) -> Eq(add(n, Zero), add(Zero, n)) {
        | Zero -> refl
        | Succ(k) -> refl
      }
    }
  `);
  // This should still give type errors — coercion doesn't fix Eq side mismatches
  assertEquals(result.errors.length > 0, true, `expected Eq mismatch error`);
});

// ─── Edge cases ────────────────────────────────────────────────────

Deno.test("coercion: same-type coercion (identity)", () => {
  const result = compile(`
    system "T" extend "Base" {
      agent natId(principal, result)
      compute natId(Zero) = Zero
      compute natId(Succ(k)) = Succ(natId(k))

      coercion nat_id = Nat -> Nat via natId

      prove test(n : Nat) -> Nat {
        | Zero -> Zero
        | Succ(k) -> Succ(k)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
