// Core interaction net library.
// Exports universal types, primitives, and system implementations.

export type { Graph, Node, NodePort, Redex, InteractionSystem, TreeSystem } from "./types.ts";
export { link, reciprocal } from "./graph.ts";
export { reduceAnnihilate, reduceErase, reduceCommute } from "./reductions.ts";
export { deltanets } from "./systems/deltanets.ts";
export { lambdacalc } from "./systems/lambdacalc.ts";

