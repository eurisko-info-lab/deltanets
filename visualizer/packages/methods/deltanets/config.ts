import { signal } from "@preact/signals";
import type { AgentPortDefs, InteractionRule } from "@deltanets/core";
import type { AgentRole, AgentStyleDef } from "@deltanets/lang";

// Agent visual styles from .iview files
export const agentStyles = signal<Map<string, AgentStyleDef>>(new Map());

// Style-aware isExprAgent: checks style level, falls back to hardcoded set.
// Unknown/custom agent types default to expression-level so their redexes
// are not filtered out in the normal (non-type) reduction mode.
const FALLBACK_EXPR_TYPES = new Set(["abs", "app", "var", "era", "root"]);
const NON_EXPR_TYPES = new Set([
  "type-base", "type-arrow", "type-hole", "kind-star", "kind-arrow",
  "pi", "sigma", "forall",
]);
export function isExprAgentFromStyles(type: string): boolean {
  const style = agentStyles.peek().get(type);
  if (style?.level) return style.level === "expr";
  if (FALLBACK_EXPR_TYPES.has(type) || type.startsWith("rep")) return true;
  if (NON_EXPR_TYPES.has(type)) return false;
  // Unknown/custom agent types are expression-level by default
  return true;
}

// Infer agent role from type name (fallback when no style is loaded)
function inferRole(type: string): AgentRole | undefined {
  if (
    type === "var" || type === "era" || type === "type-base" ||
    type === "kind-star" || type === "type-hole"
  ) return "leaf";
  if (
    type === "abs" || type === "tyabs" || type === "type-abs" ||
    type === "forall"
  ) return "binder";
  if (type === "app" || type === "tyapp" || type === "type-app") {
    return "applicator";
  }
  if (
    type === "type-arrow" || type === "pi" || type === "sigma" ||
    type === "kind-arrow" || type === "pair"
  ) return "type-constructor";
  if (type === "fst" || type === "snd") return "destructor";
  if (type.startsWith("rep")) return "replicator";
  return undefined;
}

// Get the role for an agent, from style or fallback
export function getRole(type: string): AgentRole | undefined {
  const style = agentStyles.peek().get(type);
  return style?.role ?? inferRole(type);
}

// Type reduction mode: when true, only type-level redexes are active
export const typeReductionMode = signal(false);

// Method-specific data
export type Data = {
  appliedFinalStep: boolean;
  isFinalStep: boolean;
  rules?: InteractionRule[];
  agentPorts?: AgentPortDefs;
};
