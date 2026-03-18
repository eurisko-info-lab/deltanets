// Core business logic for interaction nets and lambda calculus reduction.
// This module is free of UI dependencies (no Preact, no d3, no rendering).

export type {
  Graph,
  Node,
  NodePort,
  NodeType,
  RepStatus,
} from "./graph.ts";

export {
  link,
  reciprocal,
  parseRepLabel,
  formatRepLabel,
  isParentPort,
  isConnectedToAllErasers,
  isConnectedToSomeErasers,
  countAuxErasers,
} from "./graph.ts";

export {
  reduceAnnihilate,
  reduceErase,
  reduceCommute,
  reduceAuxFan,
} from "./reductions.ts";

export type {
  Redex,
  DeltaData,
} from "./deltanets.ts";

export {
  getRedex,
  buildGraph,
  getRedexes,
  findReachableNodes,
  cleanupGraph,
  levelColor,
} from "./deltanets.ts";
