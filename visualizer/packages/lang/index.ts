// ═══════════════════════════════════════════════════════════════════
// INet Languages — Top-level re-exports
// Two languages for expressing interaction nets:
//   core  — mechanics: agents, rules, modes, graphs, lambda terms
//   view  — presentation: themes, agent styles, wire styles, palettes
// ═══════════════════════════════════════════════════════════════════

import { compile as compileCore } from "./core/index.ts";
import { compile as compileView } from "./view/index.ts";

export { compileCore, compileView };
export { exportProofJSON, exportProofText, exportProofTerm } from "./core/proof-export.ts";
export { extractSystem, renderTypeScript, renderJavaScript } from "./core/extract.ts";
export type { ExtractionResult, ExtractedType, ExtractedFunction } from "./core/extract.ts";
export type { ProofNode, ProofTree } from "./core/typecheck-prove.ts";
export * as core from "./core/index.ts";
export * as view from "./view/index.ts";
