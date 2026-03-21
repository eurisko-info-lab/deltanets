// Tests for the core and view language compilers.

import { assert, assertEquals } from "$std/assert/mod.ts";
import { compileCore, compileView } from "./index.ts";

// ─── Core Language ─────────────────────────────────────────────────

const coreSource = `
system "Test" {
  agent abs(principal, body, bind)
  agent app(func, result, arg)
  agent era(principal)

  rule abs <> app -> annihilate
  rule abs <> era -> erase

  mode linear = { -era }
}

def I = \\x.x
def K = \\x.\\y.x
def Church2 = \\f.\\x.f (f x)

graph identity = term I
graph k-true = term K
graph church-two = term Church2
graph apply-id = term (\\x.x) (\\y.y)

graph manual {
  let r = root
  let a = abs "λx"
  wire r.principal -- a.principal
}
`;

Deno.test("core: compiles without errors", () => {
  const result = compileCore(coreSource);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("core: parses system with agents, rules and modes", () => {
  const result = compileCore(coreSource);
  const sys = result.systems.get("Test");
  assert(sys !== undefined, "Test system exists");
  assertEquals([...sys.agents.keys()].sort(), ["abs", "app", "era"]);
  assertEquals(sys.rules.length, 2);
  assertEquals([...sys.modes.keys()], ["linear"]);
});

Deno.test("core: parses definitions", () => {
  const result = compileCore(coreSource);
  assertEquals([...result.definitions.keys()].sort(), ["Church2", "I", "K"]);
});

Deno.test("core: parses graphs", () => {
  const result = compileCore(coreSource);
  const graphNames = [...result.graphs.keys()].sort();
  assertEquals(graphNames, [
    "apply-id",
    "church-two",
    "identity",
    "k-true",
    "manual",
  ]);
});

// ─── Composition (Pushout) ─────────────────────────────────────────

const composeSource = `
system "Lambda" {
  agent abs(principal, body, bind)
  agent app(func, result, arg)
  agent var(principal)
  agent root(principal)
  rule abs <> app -> annihilate
  mode linear = {}
}

system "Erasable" extend "Lambda" {
  agent era(principal)
  rule abs <> era -> erase
  rule app <> era -> erase
  mode affine = {}
}

system "Replicable" extend "Lambda" {
  agent rep-in(principal, ..aux)
  agent rep-out(principal, ..aux)
  rule rep-in <> rep-out -> annihilate
  rule rep-in <> rep-in -> commute
  rule app <> rep-out -> aux-fan
  mode relevant = {}
}

system "Δ-Nets" = compose "Erasable" + "Replicable" {
  rule rep-in <> era -> erase
  rule rep-out <> era -> erase
  mode full = {}
}
`;

Deno.test("compose: Δ-Nets has all agents", () => {
  const result = compileCore(composeSource);
  assertEquals(result.errors.length, 0);
  const dnets = result.systems.get("Δ-Nets");
  assert(dnets !== undefined);
  const expected = ["abs", "app", "era", "rep-in", "rep-out", "root", "var"];
  assertEquals([...dnets.agents.keys()].sort(), expected);
});

Deno.test("compose: Δ-Nets has cross-rules", () => {
  const result = compileCore(composeSource);
  const dnets = result.systems.get("Δ-Nets")!;
  const crossRules = dnets.rules.filter(
    (r) =>
      (r.agentA === "rep-in" || r.agentA === "rep-out") && r.agentB === "era",
  );
  assertEquals(crossRules.length, 2);
});

Deno.test("compose: Erasable extends Lambda", () => {
  const result = compileCore(composeSource);
  const erasable = result.systems.get("Erasable")!;
  assert(erasable.agents.has("abs"), "Erasable inherits abs");
  assert(erasable.agents.has("era"), "Erasable defines era");
});

// ─── View Language ─────────────────────────────────────────────────

const viewSource = `
use "test.inet"

theme dark {
  background: #1e1e1e
  text: #e0e0e0
  wire: #aaaaaa
  optimal: #4caf50
  suboptimal: #ff9800
}

render abs {
  shape: fan(down)
  width: 30
  fill: level-color
  z: 2
}

render era {
  shape: eraser
  radius: 8
  fill: #888888
}

wire-style {
  width: 1.5
  curve: bezier
}

palette {
  0: #4285f4
  1: #34a853
}

layout {
  spacing: 25
  depth: 40
  direction: top-down
}
`;

Deno.test("view: compiles without errors", () => {
  const result = compileView(viewSource);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("view: parses themes", () => {
  const result = compileView(viewSource);
  assert(result.themes.has("dark"));
  assertEquals(result.themes.get("dark")!.background, "#1e1e1e");
});

Deno.test("view: parses render styles", () => {
  const result = compileView(viewSource);
  assert(result.styles.has("abs"));
  assert(result.styles.has("era"));
});

Deno.test("view: parses palette", () => {
  const result = compileView(viewSource);
  assertEquals(result.palette.colors.size, 2);
});

// ─── Error paths: Core ─────────────────────────────────────────────

Deno.test("core error: invalid agent declaration", () => {
  const result = compileCore(`system "Bad" { agent 123 }`);
  assert(result.errors.length > 0, "should report errors");
});

Deno.test("core error: empty source compiles with no systems", () => {
  const result = compileCore("");
  assertEquals(result.systems.size, 0);
});

Deno.test("core error: undefined rule agent compiles", () => {
  const result = compileCore(`
    system "X" {
      agent a(principal)
      rule a <> b -> annihilate
    }
  `);
  // The compiler currently accepts undeclared agents in rules
  assertEquals(result.systems.size, 1);
});

// ─── Error paths: View ─────────────────────────────────────────────

Deno.test("view error: malformed render block", () => {
  const result = compileView(`render { }`);
  assert(result.errors.length > 0, "should report errors");
});

Deno.test("view error: empty source compiles with no styles", () => {
  const result = compileView("");
  assertEquals(result.styles.size, 0);
});
