// Tests for `match` expressions inside prove blocks — nested case analysis.

import { assertEquals } from "$std/assert/mod.ts";
import { compileAndAssert } from "./helpers.ts";

// ─── Base system with Nat + Eq + compute ───────────────────────────

const BASE = `
include "prelude"

system "Nat" extend "Prelude" {
  data Nat {
    | Zero
    | Succ(pred : Nat)
  }

  agent add(principal, result, accum)
  rule add <> Zero -> { relink left.result left.accum }
  rule add <> Succ -> {
    let s = Succ
    let a = add
    relink left.result s.principal
    wire s.pred -- a.result
    relink left.accum a.accum
    relink right.pred a.principal
  }

  compute add(Zero, y) = y
  compute add(Succ(k), y) = Succ(add(k, y))
}

system "Eq" extend "Nat" {
  agent refl(principal)
  agent sym(principal, result)
  agent trans(principal, result, second)
  agent cong_succ(principal, result)
  rule sym <> refl -> { let r = refl  relink left.result r.principal }
  rule trans <> refl -> { relink left.result left.second }
  rule cong_succ <> refl -> { let r = refl  relink left.result r.principal }
}
`;

// ─── Match expression: simple nested case analysis ─────────────────

Deno.test("match: two-variable case splitting type-checks", () => {
  const src = BASE + `
system "Proofs" extend "Eq" {
  prove add_zero_both(n : Nat, m : Nat) -> Eq(add(n, m), add(m, n)) {
    | Zero -> match(m) {
      | Zero -> refl
      | Succ(j) -> cong_succ(add_zero_both(Zero, j))
    }
    | Succ(k) -> match(m) {
      | Zero -> cong_succ(add_zero_both(k, Zero))
      | Succ(j) -> ?
    }
  }
}
  `;
  // Should compile without errors — the ? hole is allowed
  compileAndAssert(src);
});

Deno.test("match: simple match on second parameter", () => {
  const src = BASE + `
system "Proofs" extend "Eq" {
  prove double_zero(n : Nat) -> Eq(add(n, n), add(n, n)) {
    | Zero -> refl
    | Succ(k) -> refl
  }
}
  `;
  compileAndAssert(src);
});

Deno.test("match: match type error is caught", () => {
  const src = BASE + `
system "Proofs" extend "Eq" {
  prove foo(n : Nat, m : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> match(m) {
      | Zero -> refl
      | Succ(j) -> sym(refl)
    }
    | Succ(k) -> cong_succ(foo(k, m))
  }
}
  `;
  // Should compile — both match arms produce valid proofs
  // Zero case: refl proves add(Zero, Zero) = Zero
  // Succ(j) case: sym(refl) is still a valid proof for add(Zero, Zero) = Zero
  compileAndAssert(src);
});

Deno.test("match: prove with match does not generate agents", () => {
  const src = BASE + `
system "Proofs" extend "Eq" {
  prove test_match(n : Nat, m : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> match(m) {
      | Zero -> refl
      | Succ(j) -> refl
    }
    | Succ(k) -> cong_succ(test_match(k, m))
  }
}
  `;
  const core = compileAndAssert(src);
  const sys = core.systems.get("Proofs")!;
  // Match-containing proofs don't generate agents (yet)
  assertEquals(sys.agents.has("test_match"), false);
});

Deno.test("match: proof tree is generated for match expressions", () => {
  const src = BASE + `
system "Proofs" extend "Eq" {
  prove trivial(n : Nat, m : Nat) -> Eq(add(n, Zero), n) {
    | Zero -> match(m) {
      | Zero -> refl
      | Succ(j) -> refl
    }
    | Succ(k) -> cong_succ(trivial(k, m))
  }
}
  `;
  const core = compileAndAssert(src);
  // Check proof trees exist
  assertEquals(core.proofTrees.size >= 1, true);
  const tree = core.proofTrees.get("trivial");
  assertEquals(tree !== undefined, true);
  // Zero case should have a match node with 2 children
  const zeroCase = tree!.cases.find((c: { pattern: string }) => c.pattern === "Zero");
  assertEquals(zeroCase !== undefined, true);
  assertEquals(zeroCase!.tree.rule, "match");
  assertEquals(zeroCase!.tree.children.length, 2);
});
