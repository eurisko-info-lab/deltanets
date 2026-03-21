// Quick smoke test for both languages.
// Run: deno run lib/lang/test.ts

import { compileCore, compileView } from "./index.ts";

// ─── Test Core Language ────────────────────────────────────────────

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

console.log("═══ Core Language ═══");
const coreResult = compileCore(coreSource);

if (coreResult.errors.length > 0) {
  console.error("Errors:", coreResult.errors);
} else {
  console.log("Systems:", [...coreResult.systems.keys()]);
  for (const [name, sys] of coreResult.systems) {
    console.log(`  ${name}:`);
    console.log(`    Agents: ${[...sys.agents.keys()].join(", ")}`);
    console.log(`    Rules: ${sys.rules.length}`);
    console.log(`    Modes: ${[...sys.modes.keys()].join(", ")}`);
  }
  console.log("Definitions:", [...coreResult.definitions.keys()]);
  console.log("Graphs:", [...coreResult.graphs.keys()]);
  for (const [name, g] of coreResult.graphs) {
    console.log(`  ${name}: ${g.kind}`);
    if (g.kind === "from-term") {
      console.log(`    AST root type: ${g.astNode.type}`);
    } else {
      console.log(`    Nodes: ${g.graph.length}`);
    }
  }
}

// ─── Test View Language ────────────────────────────────────────────

// ─── Test Composition (Pushout) ────────────────────────────────────

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

console.log("\n═══ Composition (Pushout) ═══");
const compResult = compileCore(composeSource);

if (compResult.errors.length > 0) {
  console.error("Errors:", compResult.errors);
  Deno.exit(1);
} else {
  const dnets = compResult.systems.get("Δ-Nets");
  if (!dnets) { console.error("Missing Δ-Nets system!"); Deno.exit(1); }

  const agentNames = [...dnets.agents.keys()].sort();
  console.log("Agents:", agentNames.join(", "));
  console.log("Rules:", dnets.rules.length);
  console.log("Modes:", [...dnets.modes.keys()].join(", "));

  // Verify the composed system has all expected agents
  const expected = ["abs", "app", "era", "rep-in", "rep-out", "root", "var"];
  const missing = expected.filter((a) => !dnets.agents.has(a));
  if (missing.length > 0) { console.error("Missing agents:", missing); Deno.exit(1); }

  // Verify it has the expected cross-rules (era<>rep-in, era<>rep-out)
  const crossRules = dnets.rules.filter(
    (r) => (r.agentA === "rep-in" || r.agentA === "rep-out") && r.agentB === "era",
  );
  if (crossRules.length !== 2) {
    console.error("Expected 2 cross-rules, got", crossRules.length);
    Deno.exit(1);
  }

  // Verify Lambda system standalone
  const lambda = compResult.systems.get("Lambda");
  if (!lambda) { console.error("Missing Lambda system!"); Deno.exit(1); }
  console.log("Lambda agents:", [...lambda.agents.keys()].join(", "));
  console.log("Lambda rules:", lambda.rules.length);

  // Verify Erasable extends Lambda
  const erasable = compResult.systems.get("Erasable");
  if (!erasable) { console.error("Missing Erasable system!"); Deno.exit(1); }
  if (!erasable.agents.has("abs")) {
    console.error("Erasable should inherit abs from Lambda"); Deno.exit(1);
  }
  console.log("Erasable agents:", [...erasable.agents.keys()].sort().join(", "));

  console.log("✓ Composition test passed.");
}

// ─── Test View Language ────────────────────────────────────────────

const viewSource = `
use "test.inet"

theme dark {
  background: #1e1e1e
  text: #e0e0e0
  wire: #aaaaaa
  optimal: #4caf50
  suboptimal: #ff9800
}

theme light {
  background: #f5f5f5
  text: #333333
  wire: #666666
  optimal: #2e7d32
  suboptimal: #e65100
}

render abs {
  shape: fan(down)
  width: 30
  fill: level-color
  z: 2
}

render app {
  shape: fan(up)
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

wire-style dashed {
  width: 1
  curve: bezier
  dash: [4, 4]
}

palette {
  0: #4285f4
  1: #34a853
  2: #ea4335
  3: #fbbc04
  4: #9c27b0
}

layout {
  spacing: 25
  depth: 40
  direction: top-down
}
`;

console.log("\n═══ View Language ═══");
const viewResult = compileView(viewSource);

if (viewResult.errors.length > 0) {
  console.error("Errors:", viewResult.errors);
} else {
  console.log("Uses:", viewResult.uses);
  console.log("Themes:", [...viewResult.themes.keys()]);
  for (const [name, theme] of viewResult.themes) {
    console.log(`  ${name}: bg=${theme.background} wire=${theme.wire}`);
  }
  console.log("Styles:", [...viewResult.styles.keys()]);
  for (const [name, style] of viewResult.styles) {
    console.log(`  ${name}: ${style.shape.kind} fill=${style.fill} z=${style.zIndex}`);
  }
  console.log("Wire styles:", [...viewResult.wireStyles.keys()]);
  console.log("Palette entries:", viewResult.palette.colors.size);
  console.log("Layout:", viewResult.layout);
}

console.log("\n✓ All tests passed.");
