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
