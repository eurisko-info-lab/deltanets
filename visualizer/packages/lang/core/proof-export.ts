// ═══════════════════════════════════════════════════════════════════
// Proof term export — serializable proof certificates
//
// Converts ProofTree structures into portable formats:
//   exportProofJSON  — structured JSON for machine verification
//   exportProofText  — human-readable tree notation
//   exportProofTerm  — compact proof term notation (Agda-like)
// ═══════════════════════════════════════════════════════════════════

import type { ProofNode, ProofTree } from "./typecheck-prove.ts";

// ─── JSON export ───────────────────────────────────────────────────
// Outputs a clean JSON representation suitable for storage,
// transfer, or independent verification tools.

export function exportProofJSON(tree: ProofTree): string {
  return JSON.stringify(tree, null, 2);
}

// ─── Text export ───────────────────────────────────────────────────
// Produces a human-readable proof certificate with tree structure.
//
// Example output:
//   theorem plus_zero_right : Eq(add(n, Zero), n)
//   case Zero:
//     refl : Eq(Zero, Zero)
//   case Succ(k):
//     cong_succ : Eq(Succ(add(k, Zero)), Succ(k))
//       └─ IH plus_zero_right(k) : Eq(add(k, Zero), k)

export function exportProofText(tree: ProofTree): string {
  const lines: string[] = [];
  const status = tree.hasHoles ? " [INCOMPLETE]" : " [VERIFIED]";
  lines.push(`theorem ${tree.name} : ${tree.proposition}${status}`);

  for (const c of tree.cases) {
    const pat = c.bindings.length > 0
      ? `${c.pattern}(${c.bindings.join(", ")})`
      : c.pattern;
    lines.push(`case ${pat}:`);
    renderNodeText(c.tree, lines, "  ");
  }

  return lines.join("\n");
}

function renderNodeText(
  node: ProofNode,
  lines: string[],
  indent: string,
): void {
  const marker = node.isGoal ? "? " : "";
  lines.push(`${indent}${marker}${node.rule} ${node.term} : ${node.conclusion}`);
  if (node.suggestions && node.suggestions.length > 0) {
    for (const s of node.suggestions) {
      lines.push(`${indent}  → ${s}`);
    }
  }
  for (let i = 0; i < node.children.length; i++) {
    const isLast = i === node.children.length - 1;
    const branch = isLast ? "└─ " : "├─ ";
    const cont = isLast ? "   " : "│  ";
    const child = node.children[i];
    const childMarker = child.isGoal ? "? " : "";
    lines.push(
      `${indent}${branch}${childMarker}${child.rule} ${child.term} : ${child.conclusion}`,
    );
    if (child.suggestions && child.suggestions.length > 0) {
      for (const s of child.suggestions) {
        lines.push(`${indent}${cont}  → ${s}`);
      }
    }
    for (let j = 0; j < child.children.length; j++) {
      renderNodeText(child.children[j], lines, indent + cont);
    }
  }
}

// ─── Proof term export ─────────────────────────────────────────────
// Compact notation showing just the proof terms per case,
// similar to Agda/Lean pattern-matching definitions.
//
// Example output:
//   plus_zero_right : (n : Nat) → Eq(add(n, Zero), n)
//   plus_zero_right Zero       = refl
//   plus_zero_right (Succ k)   = cong_succ(plus_zero_right(k))

export function exportProofTerm(tree: ProofTree): string {
  const lines: string[] = [];
  lines.push(`${tree.name} : ${tree.proposition}`);

  for (const c of tree.cases) {
    const pat = c.bindings.length > 0
      ? `(${c.pattern} ${c.bindings.join(" ")})`
      : c.pattern;
    const term = nodeToTerm(c.tree);
    lines.push(`${tree.name} ${pat} = ${term}`);
  }

  return lines.join("\n");
}

function nodeToTerm(node: ProofNode): string {
  if (node.isGoal) return "?";
  return node.term;
}
