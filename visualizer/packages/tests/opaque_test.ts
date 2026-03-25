// Tests for Opaque/Transparent declarations.
// `opaque f` prevents the normalizer from unfolding compute rules for `f`.
// `transparent f` re-enables unfolding.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Basic opaque blocks unfolding ─────────────────────────────────

Deno.test("opaque: blocks normalization of compute rule", () => {
  // Without opaque, add(Zero, n) = n is trivially conv.
  // With opaque add, the normalizer can't unfold add, so conv fails.
  const result = compile(`
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      opaque add

      prove blocked(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "opaque should block conv");
});

Deno.test("opaque: non-opaque still works", () => {
  // Same proof without opaque should succeed
  const result = compile(`
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      prove works(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Transparent re-enables unfolding ──────────────────────────────

Deno.test("opaque: transparent re-enables after opaque", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      opaque add
      transparent add

      prove unblocked(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Opaque only affects named function ────────────────────────────

Deno.test("opaque: only affects the named function", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      compute add(Zero, y) = y
      compute add(Succ(k), y) = Succ(add(k, y))

      agent mul(principal, result, accum)
      rule mul <> Zero -> { let z = Zero  relink left.result z.principal  erase left.accum }
      rule mul <> Succ -> {
        let a = add
        let m = mul
        relink left.result a.result
        wire a.principal -- m.result
        relink left.accum m.accum
        relink right.pred m.principal
        wire a.accum -- left.accum
      }
      compute mul(Zero, y) = Zero
      compute mul(Succ(k), y) = add(mul(k, y), y)

      opaque mul

      # add is still transparent
      prove add_still_works(n : Nat) -> Eq(add(Zero, n), n) {
        | Zero -> conv
        | Succ(k) -> conv
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});
