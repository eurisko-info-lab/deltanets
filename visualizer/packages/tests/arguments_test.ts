// Tests for the Arguments declaration.
// `arguments f (x, {y})` changes which parameters are implicit/explicit.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Arguments declaration parses ──────────────────────────────────

Deno.test("arguments: parses without error", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove id_nat(n : Nat) -> Eq(n, n) {
        | Zero -> refl
        | Succ(k) -> cong_succ(id_nat(k))
      }

      arguments id_nat ({n})
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("arguments: multiple params parses", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      prove sum_eq(n : Nat, m : Nat) -> Eq(add(n, m), add(n, m)) {
        | Zero -> refl
        | Succ(k) -> cong_succ(sum_eq(k, m))
      }

      arguments sum_eq ({n}, m)
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
