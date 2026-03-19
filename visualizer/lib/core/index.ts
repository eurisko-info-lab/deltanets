// Core interaction net library.
// Exports universal types, primitives, and system implementations.

export { Ports } from "./types.ts";
export type { Graph, Node, NodePort, Redex, InteractionSystem, TreeSystem } from "./types.ts";
export { link, reciprocal } from "./graph.ts";
export { reduceAnnihilate, reduceErase, reduceCommute } from "./reductions.ts";
export { deltanets } from "./systems/deltanets/index.ts";
export { lambdacalc } from "./systems/lambdacalc.ts";
export { typeCheck, hasTypeAnnotations, generateTypeCheckSteps, tagAstWithTypeCheckIndices } from "./typechecker.ts";
export type { TypeResult, TypeEnv, TypeCheckStep } from "./typechecker.ts";

