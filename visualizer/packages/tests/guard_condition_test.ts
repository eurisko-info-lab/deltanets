// Phase 50: Guard condition for cofixpoints — robust nested corecursive
// productivity checking tests.

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NAT_SYSTEM } from "./helpers.ts";

const BASE = NAT_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ═══════════════════════════════════════════════════════════════════
// Guard propagation through match
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: match inside guard arg — recursive call in match case is productive", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove choose(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, choose(Zero))
        | Succ(k) -> guard_stream(
            Zero,
            match(k) {
              | Zero -> choose(Zero)
              | Succ(j) -> choose(j)
            }
          )
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("guard: match NOT inside guard — recursive call in match case is unproductive", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove bad_match(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, bad_match(Zero))
        | Succ(k) -> match(k) {
            | Zero -> bad_match(Zero)
            | Succ(j) -> bad_match(j)
          }
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject unguarded match");
  assertEquals(
    result.errors.some(e => e.includes("not productive")),
    true,
    `expected productivity error, got: ${result.errors}`,
  );
});

Deno.test("guard: nested match inside guard", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove nested_match(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, nested_match(Zero))
        | Succ(k) -> guard_stream(
            Zero,
            match(k) {
              | Zero -> match(k) {
                  | Zero -> nested_match(Zero)
                  | Succ(j) -> nested_match(j)
                }
              | Succ(j) -> nested_match(j)
            }
          )
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ═══════════════════════════════════════════════════════════════════
// Guard propagation through let bindings
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: let binding inside guard arg", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove let_in_guard(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, let_in_guard(Zero))
        | Succ(k) -> guard_stream(
            Zero,
            let x = let_in_guard(k) in x
          )
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("guard: let-transparency — rec call in value, used in guarded position", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove let_trans(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, let_trans(Zero))
        | Succ(k) -> let x = let_trans(k) in guard_stream(Zero, x)
      }
    }
  `);
  assertEquals(result.errors.length, 0, `expected let-transparency, got: ${result.errors}`);
});

Deno.test("guard: let value used in unguarded position — rejected", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove bad_let(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, bad_let(Zero))
        | Succ(k) -> let x = bad_let(k) in x
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject unguarded let");
  assertEquals(
    result.errors.some(e => e.includes("not productive")),
    true,
    `expected productivity error, got: ${result.errors}`,
  );
});

// ═══════════════════════════════════════════════════════════════════
// Constructor transparency
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: nested guard constructors accepted", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove double_guard(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, double_guard(Zero))
        | Succ(k) -> guard_stream(
            Zero,
            guard_stream(Zero, double_guard(k))
          )
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("guard: data constructor inside guard is transparent", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove ctor_guard(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, ctor_guard(Zero))
        | Succ(k) -> guard_stream(Succ(Zero), ctor_guard(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ═══════════════════════════════════════════════════════════════════
// Observation blocking
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: observation wrapping recursive call blocks guard", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove obs_bad(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, obs_bad(Zero))
        | Succ(k) -> guard_stream(Zero, tail(obs_bad(k)))
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "observation should block guard");
  assertEquals(
    result.errors.some(e => e.includes("observation")),
    true,
    `expected observation-aware error, got: ${result.errors}`,
  );
});

Deno.test("guard: head observation wrapping recursive call blocks guard", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove obs_bad2(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, obs_bad2(Zero))
        | Succ(k) -> guard_stream(Zero, head(obs_bad2(k)))
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "observation should block guard");
});

// ═══════════════════════════════════════════════════════════════════
// Multi-field codata
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: multi-field codata with recursive call in correct field", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata CoList(A) { isNil : Nat, hd : A, tl : CoList(A) }

      prove repeat_list(n : Nat) -> CoList(Nat) {
        | Zero -> guard_colist(Zero, Zero, repeat_list(Zero))
        | Succ(k) -> guard_colist(Zero, Zero, repeat_list(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("guard: multi-field codata — unguarded rejected", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata CoList(A) { isNil : Nat, hd : A, tl : CoList(A) }

      prove bad_list(n : Nat) -> CoList(Nat) {
        | Zero -> bad_list(Zero)
        | Succ(k) -> bad_list(k)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject unguarded");
});

// ═══════════════════════════════════════════════════════════════════
// Complex nested patterns
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: match + let + nested guard accepted", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove complex(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, complex(Zero))
        | Succ(k) -> guard_stream(
            Zero,
            match(k) {
              | Zero -> let y = complex(Zero) in y
              | Succ(j) -> guard_stream(j, complex(j))
            }
          )
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("guard: partially guarded — one case guarded, one not", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove partial(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, partial(Zero))
        | Succ(k) -> partial(k)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "Succ case is unguarded");
  assertEquals(
    result.errors.some(e => e.includes("not productive") && e.includes("Succ")),
    true,
    `expected Succ-case error, got: ${result.errors}`,
  );
});

// ═══════════════════════════════════════════════════════════════════
// Error message quality
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: error mentions guard constructor name", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove err_msg(n : Nat) -> Stream(Nat) {
        | Zero -> err_msg(Zero)
        | Succ(k) -> err_msg(k)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should have errors");
  assertEquals(
    result.errors.some(e => e.includes("guard_stream")),
    true,
    `error should mention guard_stream, got: ${result.errors}`,
  );
});

Deno.test("guard: observation error is specific", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove obs_err(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, obs_err(Zero))
        | Succ(k) -> guard_stream(Zero, tail(obs_err(k)))
      }
    }
  `);
  const obsErrors = result.errors.filter(e => e.includes("observation") && e.includes("tail"));
  assertEquals(obsErrors.length > 0, true, `expected observation-specific error for tail, got: ${result.errors}`);
});

// ═══════════════════════════════════════════════════════════════════
// Regression tests
// ═══════════════════════════════════════════════════════════════════

Deno.test("guard: basic repeat still accepted (regression)", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove repeat(n : Nat) -> Stream(Nat) {
        | Zero -> guard_stream(Zero, repeat(Zero))
        | Succ(k) -> guard_stream(Zero, repeat(k))
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("guard: basic bad still rejected (regression)", () => {
  const result = compile(`
    system "G" extend "Nat" {
      codata Stream(A) { head : A, tail : Stream(A) }

      prove bad(n : Nat) -> Stream(Nat) {
        | Zero -> bad(Zero)
        | Succ(k) -> bad(k)
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject");
  assertEquals(
    result.errors.some(e => e.includes("not productive")),
    true,
    `expected productivity error, got: ${result.errors}`,
  );
});
