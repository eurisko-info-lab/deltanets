// Example manifest: each entry maps a display name to a file in static/examples/.
// The code is loaded from data files at module initialization time.

const exampleFiles = [
  { name: "Starter", file: "starter.lam" },
  { name: "Lamping A", file: "lamping-a.lam" },
  { name: "Lamping B", file: "lamping-b.lam" },
  { name: "List Head", file: "list-head.lam" },
  { name: "Ω (Non-Normalizing)", file: "omega.lam" },
  { name: "Y (Non-Normalizing)", file: "y-combinator.lam" },
  { name: "Two Squared Twice", file: "two-squared-twice.lam" },
  { name: "Erasure vs Sharing", file: "erasure-vs-sharing.lam" },
  { name: "Replicator Decay", file: "replicator-decay.lam" },
  { name: "Graph Coloring", file: "graph-coloring.lam" },
  { name: "STLC: Identity", file: "stlc-identity.lam" },
  { name: "STLC: Church Booleans", file: "stlc-church-booleans.lam" },
  { name: "STLC: Composition", file: "stlc-composition.lam" },
  { name: "INet: Δ-Nets", file: "inet-deltanets.inet" },
  { name: "INet: Lambda Calculus", file: "inet-lambda-calculus.inet" },
  { name: "INet: Δ-Nets (Composed)", file: "inet-deltanets-composed.inet" },
  { name: "INet: Typing (STLC)", file: "inet-typing-stlc.inet" },
  { name: "INet: Lambda Cube", file: "inet-lambda-cube.inet" },
];

const examplesDir = new URL("../static/examples/", import.meta.url).pathname;

const examples: { name: string; code: string }[] = exampleFiles.map(
  ({ name, file }) => ({
    name,
    code: Deno.readTextFileSync(`${examplesDir}${file}`),
  }),
);

export default examples;
