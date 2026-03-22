// Tests for the core and view language compilers.

import { assert, assertEquals } from "$std/assert/mod.ts";
import { compileCore, compileView, core } from "@deltanets/lang";

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
  assertEquals(erasable.agents.get("abs")!.ports.length, 3, "abs has 3 ports");
  assertEquals(erasable.agents.get("era")!.ports.length, 1, "era has 1 port");
  assertEquals(erasable.rules.length, 3, "annihilate + 2 erase rules");
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

// ─── Include & Prelude ─────────────────────────────────────────────

Deno.test("include: prelude provides root and var agents", () => {
  const source = `
    include "prelude"
    system "Test" extend "Prelude" {
      agent abs(principal, body, bind)
      agent app(func, result, arg)
      rule abs <> app -> annihilate
    }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("Test")!;
  assert(sys.agents.has("root"), "inherits root from Prelude");
  assert(sys.agents.has("var"), "inherits var from Prelude");
  assert(sys.agents.has("abs"), "defines own abs");
});

Deno.test("include: unresolvable path reports error", () => {
  const source = `include "nonexistent"`;
  const result = compileCore(source);
  assert(result.errors.length > 0, "should report unresolvable include");
  assert(result.errors[0].includes("nonexistent"));
});

Deno.test("include: custom resolver", () => {
  const source = `
    include "custom"
    system "A" extend "Base" {
      agent foo(principal)
    }
  `;
  const resolver = (path: string) =>
    path === "custom" ? `system "Base" { agent bar(principal) }` : null;
  const result = compileCore(source, resolver);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("A")!;
  assert(sys.agents.has("bar"), "inherits bar from included Base");
  assert(sys.agents.has("foo"), "defines own foo");
});

Deno.test("include: circular includes are skipped", () => {
  const resolver = (path: string) =>
    path === "a" ? `include "a"\nsystem "S" { agent x(principal) }` : null;
  const result = compileCore(`include "a"`, resolver);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  assert(result.systems.has("S"));
});

// ─── Lane Views ────────────────────────────────────────────────────

const laneSource = `
lanes "Test Lanes" {
  lane "Track A" { lines: 3 }
  lane "Track B"

  at 0 "Track A" place "Item1"
  at 1 "Track B" place "Item2" duration 2
  at 3 "Track A" place "Item3"

  bar 0 "Start"
  bar 4

  link "Item1" -> "Item2" "depends"
  link "Item2" -> "Item3"
}
`;

Deno.test("lanes: compiles without errors", () => {
  const result = compileCore(laneSource);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("lanes: produces lane view definition", () => {
  const result = compileCore(laneSource);
  assert(result.laneViews.has("Test Lanes"), "lane view exists");
  const view = result.laneViews.get("Test Lanes")!;
  assertEquals(view.name, "Test Lanes");
});

Deno.test("lanes: parses lane definitions", () => {
  const result = compileCore(laneSource);
  const view = result.laneViews.get("Test Lanes")!;
  assertEquals(view.lanes.length, 2);
  assertEquals(view.lanes[0].name, "Track A");
  assertEquals(view.lanes[0].props.lines, 3);
  assertEquals(view.lanes[1].name, "Track B");
});

Deno.test("lanes: parses items with position and duration", () => {
  const result = compileCore(laneSource);
  const view = result.laneViews.get("Test Lanes")!;
  assertEquals(view.items.length, 3);
  assertEquals(view.items[0], {
    position: 0,
    lane: "Track A",
    label: "Item1",
    duration: 0,
  });
  assertEquals(view.items[1], {
    position: 1,
    lane: "Track B",
    label: "Item2",
    duration: 2,
  });
});

Deno.test("lanes: parses markers", () => {
  const result = compileCore(laneSource);
  const view = result.laneViews.get("Test Lanes")!;
  assertEquals(view.markers.length, 2);
  assertEquals(view.markers[0], { position: 0, label: "Start" });
  assertEquals(view.markers[1], { position: 4, label: undefined });
});

Deno.test("lanes: parses links", () => {
  const result = compileCore(laneSource);
  const view = result.laneViews.get("Test Lanes")!;
  assertEquals(view.links.length, 2);
  assertEquals(view.links[0], {
    from: "Item1",
    to: "Item2",
    label: "depends",
  });
  assertEquals(view.links[1], { from: "Item2", to: "Item3", label: undefined });
});

Deno.test("lanes: multiple lane views", () => {
  const source = `
    lanes "View A" { lane "X" }
    lanes "View B" { lane "Y" }
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  assertEquals(result.laneViews.size, 2);
  assert(result.laneViews.has("View A"));
  assert(result.laneViews.has("View B"));
});

// ─── Music Lanes ───────────────────────────────────────────────────

const musicSource = `
lanes "Melody" {
  lane "Treble" { clef: "treble", lines: 5 }

  at 0 "Treble" place "E4" duration 1
  at 1 "Treble" place "F4" duration 1
  at 2 "Treble" place "G4" duration 2

  bar 0
  bar 4
}
`;

Deno.test("music lanes: compiles without errors", () => {
  const result = compileCore(musicSource);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
});

Deno.test("music lanes: has clef property", () => {
  const result = compileCore(musicSource);
  const view = result.laneViews.get("Melody")!;
  assertEquals(view.lanes[0].props.clef, "treble");
  assertEquals(view.lanes[0].props.lines, 5);
});

Deno.test("music lanes: pitch labels preserved", () => {
  const result = compileCore(musicSource);
  const view = result.laneViews.get("Melody")!;
  assertEquals(view.items[0].label, "E4");
  assertEquals(view.items[1].label, "F4");
  assertEquals(view.items[2].label, "G4");
});

Deno.test("music lanes: durations preserved", () => {
  const result = compileCore(musicSource);
  const view = result.laneViews.get("Melody")!;
  assertEquals(view.items[0].duration, 1);
  assertEquals(view.items[2].duration, 2);
});

Deno.test("music lanes: piano with two staves", () => {
  const source = `
lanes "Piano" {
  lane "Right" { clef: "treble", lines: 5 }
  lane "Left"  { clef: "bass",   lines: 5 }

  at 0 "Right" place "C5" duration 2
  at 0 "Left"  place "C3" duration 4

  bar 0
  bar 4
}
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const view = result.laneViews.get("Piano")!;
  assertEquals(view.lanes.length, 2);
  assertEquals(view.lanes[0].props.clef, "treble");
  assertEquals(view.lanes[1].props.clef, "bass");
  assertEquals(view.items.length, 2);
});

Deno.test("music lanes: accidentals in labels", () => {
  const source = `
lanes "Chromatic" {
  lane "Staff" { clef: "treble", lines: 5 }
  at 0 "Staff" place "C#4" duration 1
  at 1 "Staff" place "Eb4" duration 1
  at 2 "Staff" place "Bb4" duration 1
}
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const view = result.laneViews.get("Chromatic")!;
  assertEquals(view.items[0].label, "C#4");
  assertEquals(view.items[1].label, "Eb4");
  assertEquals(view.items[2].label, "Bb4");
});

// ─── Syntax Extensions ────────────────────────────────────────────

Deno.test("syntax: batch rules expand to cross product", () => {
  const source = `
system "T" {
  agent a(principal)
  agent b(principal, body, bind)
  agent c(principal)
  agent d(principal)
  rule [a, b] <> [c, d] -> erase
}
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.rules.length, 4);
  const pairs = sys.rules.map((r) => `${r.agentA}<>${r.agentB}`).sort();
  assertEquals(pairs, ["a<>c", "a<>d", "b<>c", "b<>d"]);
});

Deno.test("syntax: batch rule one-sided bracket", () => {
  const source = `
system "T" {
  agent x(principal)
  agent y(principal)
  agent z(principal)
  rule [x, y] <> z -> erase
}
  `;
  const result = compileCore(source);
  assertEquals(result.errors.length, 0, `errors: ${result.errors}`);
  const sys = result.systems.get("T")!;
  assertEquals(sys.rules.length, 2);
  const pairs = sys.rules.map((r) => `${r.agentA}<>${r.agentB}`).sort();
  assertEquals(pairs, ["x<>z", "y<>z"]);
});

Deno.test("syntax: tilde shorthand wires principals", () => {
  const source = `
graph test {
  let r = root
  let a = abs "λx"
  wire r ~ a
}
  `;
  const ast = core.parse(core.tokenize(source));
  const graph = ast.find((s): s is core.GraphExplicit => s.kind === "graph-explicit" && s.name === "test")!;
  const wires = graph.body.filter((s): s is core.WireStmt => s.kind === "wire");
  assertEquals(wires.length, 1);
  assertEquals(wires[0].portA.port, "principal");
  assertEquals(wires[0].portB.port, "principal");
});

Deno.test("syntax: tilde with explicit port on one side", () => {
  const source = `
graph test {
  let r = root
  let a = abs "λx"
  wire a.body ~ r
}
  `;
  const ast = core.parse(core.tokenize(source));
  const graph = ast.find((s): s is core.GraphExplicit => s.kind === "graph-explicit" && s.name === "test")!;
  const wires = graph.body.filter((s): s is core.WireStmt => s.kind === "wire");
  assertEquals(wires.length, 1);
  assertEquals(wires[0].portA.port, "body");
  assertEquals(wires[0].portB.port, "principal");
});

Deno.test("syntax: wire chain with commas", () => {
  const source = `
graph test {
  let r = root
  let a = abs "λx"
  wire r ~ a, a.bind -- a.body
}
  `;
  const ast = core.parse(core.tokenize(source));
  const graph = ast.find((s): s is core.GraphExplicit => s.kind === "graph-explicit" && s.name === "test")!;
  const wires = graph.body.filter((s): s is core.WireStmt => s.kind === "wire");
  assertEquals(wires.length, 2);
  assertEquals(wires[0].portA.port, "principal");
  assertEquals(wires[0].portB.port, "principal");
  assertEquals(wires[1].portA.port, "bind");
  assertEquals(wires[1].portB.port, "body");
});
