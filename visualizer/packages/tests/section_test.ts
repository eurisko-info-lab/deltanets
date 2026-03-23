// Tests for Phase 25: Sections & variables — section S { variable(A : Type) }
// with auto-abstraction into implicit params on prove/data declarations.

import { assertEquals, assertNotEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic section with variable ───────────────────────────────────

Deno.test("section: variable auto-abstracted as implicit param on prove", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Arith {
        variable(n : Nat)

        prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
          | Zero -> refl
          | Succ(k) -> cong_succ(addZero(k))
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: multiple variables", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Multi {
        variable(a : Nat)
        variable(b : Nat)

        prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
          | Zero -> refl
          | Succ(k) -> cong_succ(addZero(k))
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: data inside section gets type parameter", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Parametric {
        variable(A : Type)

        data MyList {
          | MyNil
          | MyCons(head : A, tail : MyList)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: nested sections accumulate variables", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Outer {
        variable(n : Nat)
        section Inner {
          variable(m : Nat)

          prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
            | Zero -> refl
            | Succ(k) -> cong_succ(addZero(k))
          }
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: prove without section variables works unchanged", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Empty {
        prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
          | Zero -> refl
          | Succ(k) -> cong_succ(addZero(k))
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: items after section are not affected", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Scoped {
        variable(x : Nat)
        agent Dummy(principal)
      }

      prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(addZero(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: multiple proves inside section", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Lemmas {
        variable(n : Nat)

        prove addZero(n : Nat) -> Eq(add(n, Zero), n) {
          | Zero -> refl
          | Succ(k) -> cong_succ(addZero(k))
        }

        prove reflN(n : Nat) -> Eq(n, n) {
          | Zero -> refl
          | Succ(k) -> cong_succ(reflN(k))
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: compute rules pass through unchanged", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section WithCompute {
        variable(n : Nat)
        compute add(Zero, y) = y
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: agent declarations pass through unchanged", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section WithAgent {
        variable(n : Nat)
        agent MyAgent(principal, x)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("section: parse error on missing variable type", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      section Bad {
        variable(x)
      }
    }
  `);
  assertNotEquals(result.errors.length, 0, "should fail: variable needs type annotation");
});
