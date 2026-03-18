// Core interaction net library.
// Exports universal types, primitives, and the Δ-Nets system implementation.

export type { Graph, Node, NodePort, Redex, InteractionSystem } from "./types.ts";
export { link, reciprocal } from "./graph.ts";
export { reduceAnnihilate, reduceErase, reduceCommute } from "./reductions.ts";
export { deltanets } from "./systems/deltanets.ts";

