// Tests for Phase 21: Mutual inductive types
// - mutual { data ... data ... } syntax
// - Joint positivity checking
// - Cross-type eliminator generation (mutual compute rules)
// - mutual { prove ... prove ... } with mutual termination checking

import { assertEquals } from "$std/assert/mod.ts";
import { compileCore } from "@deltanets/lang";
import { NATEQ_SYSTEM } from "./helpers.ts";

const BASE = NATEQ_SYSTEM;

function compile(extra: string) {
  return compileCore(BASE + "\n" + extra);
}

// ─── Parsing ───────────────────────────────────────────────────────

Deno.test("mutual: parse Even/Odd data types", () => {
  const result = compile(`
    system "EO" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("mutual: requires at least 2 declarations", () => {
  const result = compile(`
    system "Bad" extend "NatEq" {
      mutual {
        data Lonely {
          | Mk
        }
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject single-decl mutual block");
});

// ─── Constructor agents ────────────────────────────────────────────

Deno.test("mutual: generates constructor agents for all types", () => {
  const result = compile(`
    system "EO" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("EO")!;
  assertEquals(sys.agents.has("EZero"), true, "EZero agent");
  assertEquals(sys.agents.has("ESucc"), true, "ESucc agent");
  assertEquals(sys.agents.has("OSucc"), true, "OSucc agent");
});

Deno.test("mutual: generates dup agents for each type", () => {
  const result = compile(`
    system "EO" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("EO")!;
  assertEquals(sys.agents.has("dup_even"), true, "dup_even agent");
  assertEquals(sys.agents.has("dup_odd"), true, "dup_odd agent");
});

Deno.test("mutual: registers constructorsByType for both types", () => {
  const result = compile(`
    system "EO" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("EO")!;
  const evenCtors = sys.constructorsByType.get("Even");
  assertEquals(evenCtors !== undefined, true);
  assertEquals(evenCtors!.has("EZero"), true);
  assertEquals(evenCtors!.has("ESucc"), true);
  const oddCtors = sys.constructorsByType.get("Odd");
  assertEquals(oddCtors !== undefined, true);
  assertEquals(oddCtors!.has("OSucc"), true);
});

// ─── Cross-type eliminator compute rules ───────────────────────────

Deno.test("mutual: generates cross-type eliminator compute rules", () => {
  const result = compile(`
    system "EO" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("EO")!;
  const evenRec = sys.computeRules.filter((r) => r.funcName === "Even_rec");
  const oddRec = sys.computeRules.filter((r) => r.funcName === "Odd_rec");
  assertEquals(evenRec.length, 2, "Even_rec has 2 rules (EZero, ESucc)");
  assertEquals(oddRec.length, 1, "Odd_rec has 1 rule (OSucc)");
});

// ─── Joint positivity checking ─────────────────────────────────────

Deno.test("mutual: rejects negative occurrence of mutual type", () => {
  const result = compile(`
    system "Bad" extend "NatEq" {
      mutual {
        data Pos {
          | PZero
          | PSucc(pred : Neg)
        }
        data Neg {
          | NMk(bad : forall(x : Pos, Nat))
        }
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject negative position");
  assertEquals(
    result.errors[0].includes("negative position"),
    true,
    `error message: ${result.errors[0]}`,
  );
});

Deno.test("mutual: accepts strictly positive occurrences", () => {
  const result = compile(`
    system "Good" extend "NatEq" {
      mutual {
        data Tree {
          | Leaf
          | Node(child : Forest)
        }
        data Forest {
          | Nil
          | Cons(head : Tree, tail : Forest)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

// ─── Mutual prove blocks ──────────────────────────────────────────

Deno.test("mutual: mutual prove blocks with cross-calls accepted", () => {
  const result = compile(`
    system "EO" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }

      mutual {
        prove even_trivial(n : Even) -> Eq(Zero, Zero) {
          | EZero -> refl
          | ESucc(p) -> odd_trivial(p)
        }
        prove odd_trivial(n : Odd) -> Eq(Zero, Zero) {
          | OSucc(p) -> even_trivial(p)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("mutual: mutual prove blocks reject non-decreasing cross-call", () => {
  const result = compile(`
    system "Bad" extend "NatEq" {
      mutual {
        data Even {
          | EZero
          | ESucc(pred : Odd)
        }
        data Odd {
          | OSucc(pred : Even)
        }
      }

      mutual {
        prove even_bad(n : Even) -> Eq(n, n) {
          | EZero -> refl
          | ESucc(p) -> odd_bad(n)
        }
        prove odd_bad(n : Odd) -> Eq(n, n) {
          | OSucc(p) -> even_bad(n)
        }
      }
    }
  `);
  assertEquals(result.errors.length > 0, true, "should reject non-decreasing mutual call");
  assertEquals(
    result.errors[0].includes("not structurally decreasing"),
    true,
    `error message: ${result.errors[0]}`,
  );
});

// ─── Mutual proves: self-recursion still checked ───────────────────

Deno.test("mutual: self-recursion within mutual block still checked", () => {
  const result = compile(`
    system "T" extend "NatEq" {
      mutual {
        prove f(n : Nat) -> Eq(n, n) {
          | Zero -> refl
          | Succ(k) -> g(k)
        }
        prove g(n : Nat) -> Eq(n, n) {
          | Zero -> refl
          | Succ(k) -> g(n)
        }
      }
    }
  `);
  // g(n) calls g(n) — self-recursion with non-decreasing arg
  assertEquals(result.errors.length > 0, true, "should reject non-decreasing self-call");
});

// ─── Mutual data with params ───────────────────────────────────────

Deno.test("mutual: parameterized mutual data types", () => {
  const result = compile(`
    system "PM" extend "NatEq" {
      mutual {
        data Tree {
          | Leaf
          | Node(val : Nat, children : Forest)
        }
        data Forest {
          | FNil
          | FCons(head : Tree, tail : Forest)
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("PM")!;
  assertEquals(sys.agents.has("Leaf"), true);
  assertEquals(sys.agents.has("Node"), true);
  assertEquals(sys.agents.has("FNil"), true);
  assertEquals(sys.agents.has("FCons"), true);
});

// ─── Three-way mutual types ───────────────────────────────────────

Deno.test("mutual: three-way mutual data types", () => {
  const result = compile(`
    system "Tri" extend "NatEq" {
      mutual {
        data A {
          | MkA(next : B)
          | AEnd
        }
        data B {
          | MkB(next : C)
          | BEnd
        }
        data C {
          | MkC(next : A)
          | CEnd
        }
      }
    }
  `);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("Tri")!;
  assertEquals(sys.agents.has("MkA"), true);
  assertEquals(sys.agents.has("MkB"), true);
  assertEquals(sys.agents.has("MkC"), true);
  // All three recursors should be generated
  const aRec = sys.computeRules.filter((r) => r.funcName === "A_rec");
  const bRec = sys.computeRules.filter((r) => r.funcName === "B_rec");
  const cRec = sys.computeRules.filter((r) => r.funcName === "C_rec");
  assertEquals(aRec.length, 2, "A_rec has 2 rules");
  assertEquals(bRec.length, 2, "B_rec has 2 rules");
  assertEquals(cRec.length, 2, "C_rec has 2 rules");
});
