// ═══════════════════════════════════════════════════════════════════
// Gentzen-style proof derivation tree renderer
// Renders ProofTree data as an SVG Node2D scene.
// ═══════════════════════════════════════════════════════════════════

import * as d3 from "d3";
import {
  DEFAULT_LINE_WIDTH,
  defaultStroke,
  Node2D,
  type Pos,
  type SVG,
} from "./core.ts";

// ─── Types ─────────────────────────────────────────────────────────

/** A node in a natural-deduction proof derivation tree. */
export type ProofNode = {
  rule: string;
  term: string;
  conclusion: string;
  children: ProofNode[];
  isGoal?: boolean;
  suggestions?: string[];
};

/** Proof derivation tree for one prove block. */
export type ProofTree = {
  name: string;
  proposition: string;
  cases: { pattern: string; bindings: string[]; tree: ProofNode }[];
  hasHoles: boolean;
};

// ─── Layout constants ──────────────────────────────────────────────

const FONT_SIZE = 14;
const RULE_FONT_SIZE = 12;
const TITLE_FONT_SIZE = 16;
const LINE_PAD = 6;       // horizontal padding beyond text on inference line
const CHILD_GAP = 24;     // gap between sibling premises
const LEVEL_GAP = 8;      // vertical gap between conclusion and inference line
const CASE_GAP = 60;      // gap between case blocks
const TITLE_GAP = 30;     // gap below title

// Approximate character width for layout (monospace-ish)
const CHAR_W = FONT_SIZE * 0.58;
const RULE_CHAR_W = RULE_FONT_SIZE * 0.55;

const GOAL_COLOR = "#e8a838"; // amber for open goals
const SUGGEST_COLOR = "#4caf50"; // green for suggestions
const SUGGEST_FONT_SIZE = 12;

// ─── SVG text primitive ───────────────────────────────────────────

class ProofText extends Node2D {
  value: string;
  fontSize: number;
  color?: string;
  bold: boolean;
  italic: boolean;

  constructor(value: string, fontSize = FONT_SIZE, opts: { color?: string; bold?: boolean; italic?: boolean } = {}) {
    super();
    this.value = value;
    this.fontSize = fontSize;
    this.color = opts.color;
    this.bold = opts.bold ?? false;
    this.italic = opts.italic ?? false;
  }

  override renderSelf(pos: Pos, theme: "light" | "dark"): SVG | null {
    const svg = d3.create("svg:text")
      .text(this.value)
      .attr("x", pos.x)
      .attr("y", pos.y)
      .attr("text-anchor", "middle")
      .attr("dominant-baseline", "middle")
      .attr("fill", this.color ?? defaultStroke(theme))
      .style("font-size", `${this.fontSize}px`)
      .attr("font-family", "monospace")
      .attr("pointer-events", "none");
    if (this.bold) svg.style("font-weight", "bold");
    if (this.italic) svg.style("font-style", "italic");
    return svg;
  }
}

// Horizontal inference line
class InferenceLine extends Node2D {
  width: number;
  color?: string;

  constructor(width: number, color?: string) {
    super();
    this.width = width;
    this.color = color;
  }

  override renderSelf(pos: Pos, theme: "light" | "dark"): SVG | null {
    return d3.create("svg:line")
      .attr("x1", pos.x - this.width / 2)
      .attr("y1", pos.y)
      .attr("x2", pos.x + this.width / 2)
      .attr("y2", pos.y)
      .attr("stroke", this.color ?? defaultStroke(theme))
      .attr("stroke-width", DEFAULT_LINE_WIDTH);
  }
}

// Rounded rectangle highlight for goal nodes
class GoalHighlight extends Node2D {
  w: number;
  h: number;

  constructor(w: number, h: number) {
    super();
    this.w = w;
    this.h = h;
  }

  override renderSelf(pos: Pos, _theme: "light" | "dark"): SVG | null {
    return d3.create("svg:rect")
      .attr("x", pos.x - this.w / 2 - 6)
      .attr("y", pos.y - this.h / 2 - 4)
      .attr("width", this.w + 12)
      .attr("height", this.h + 8)
      .attr("rx", 4)
      .attr("ry", 4)
      .attr("fill", GOAL_COLOR)
      .attr("fill-opacity", 0.15)
      .attr("stroke", GOAL_COLOR)
      .attr("stroke-width", 1.5)
      .attr("stroke-dasharray", "4,3");
  }
}

// ─── Layout engine ─────────────────────────────────────────────────

type LayoutNode = {
  width: number;
  height: number;
  render: (parent: Node2D, cx: number, bottomY: number) => void;
};

function textWidth(text: string, charW: number): number {
  return text.length * charW;
}

/** Lay out a single ProofNode as a Gentzen tree (bottom-up). */
function layoutNode(node: ProofNode): LayoutNode {
  const conclusionW = textWidth(node.conclusion, CHAR_W);
  const ruleW = textWidth(node.rule, RULE_CHAR_W);

  // Goal leaf (? hole) — render with highlight and suggestions
  if (node.isGoal) {
    const lineW = conclusionW + 2 * LINE_PAD;
    const totalW = lineW + ruleW + LINE_PAD;
    const suggestions = node.suggestions ?? [];
    const suggestH = suggestions.length > 0
      ? LEVEL_GAP + suggestions.length * (SUGGEST_FONT_SIZE + 3)
      : 0;
    const totalH = FONT_SIZE + LEVEL_GAP + DEFAULT_LINE_WIDTH + suggestH;
    return {
      width: totalW,
      height: totalH,
      render(parent, cx, bottomY) {
        // Suggestions below the conclusion
        let sy = bottomY;
        if (suggestions.length > 0) {
          for (let i = suggestions.length - 1; i >= 0; i--) {
            const label = i === 0 ? `→ ${suggestions[i]}` : `  ${suggestions[i]}`;
            const st = new ProofText(label, SUGGEST_FONT_SIZE, { color: SUGGEST_COLOR, italic: true });
            st.pos = { x: cx, y: sy };
            parent.add(st, false);
            sy -= SUGGEST_FONT_SIZE + 3;
          }
          sy -= LEVEL_GAP / 2;
        }
        // Highlight box behind the conclusion
        const concY = sy;
        const bg = new GoalHighlight(conclusionW, FONT_SIZE);
        bg.pos = { x: cx, y: concY };
        parent.add(bg, false);
        // Conclusion text in goal color
        const concText = new ProofText(node.conclusion, FONT_SIZE, { color: GOAL_COLOR, bold: true });
        concText.pos = { x: cx, y: concY };
        parent.add(concText, false);
        // Inference line in goal color
        const lineY = concY - FONT_SIZE / 2 - LEVEL_GAP;
        const line = new InferenceLine(lineW, GOAL_COLOR);
        line.pos = { x: cx, y: lineY };
        parent.add(line, false);
        // Rule label
        const ruleLabel = new ProofText("?", RULE_FONT_SIZE, { italic: true, color: GOAL_COLOR });
        ruleLabel.pos = { x: cx + lineW / 2 + LINE_PAD + ruleW / 2, y: lineY };
        parent.add(ruleLabel, false);
      },
    };
  }

  if (node.children.length === 0) {
    // Leaf (axiom or call)
    const lineW = conclusionW + 2 * LINE_PAD;
    const totalW = lineW + ruleW + LINE_PAD;
    const totalH = FONT_SIZE + LEVEL_GAP + DEFAULT_LINE_WIDTH;
    return {
      width: totalW,
      height: totalH,
      render(parent, cx, bottomY) {
        // Conclusion text (below line)
        const concText = new ProofText(node.conclusion);
        concText.pos = { x: cx, y: bottomY };
        parent.add(concText, false);
        // Inference line
        const lineY = bottomY - FONT_SIZE / 2 - LEVEL_GAP;
        const line = new InferenceLine(lineW);
        line.pos = { x: cx, y: lineY };
        parent.add(line, false);
        // Rule label (right of line)
        const ruleLabel = new ProofText(node.rule, RULE_FONT_SIZE, { italic: true, color: "#888" });
        ruleLabel.pos = { x: cx + lineW / 2 + LINE_PAD + ruleW / 2, y: lineY };
        parent.add(ruleLabel, false);
      },
    };
  }

  // Lay out children
  const childLayouts = node.children.map(layoutNode);
  const premisesW = childLayouts.reduce((s, c) => s + c.width, 0) +
    (childLayouts.length - 1) * CHILD_GAP;
  const premisesH = Math.max(...childLayouts.map((c) => c.height));

  const lineW = Math.max(conclusionW, premisesW) + 2 * LINE_PAD;
  const totalW = lineW + ruleW + LINE_PAD;
  const totalH = FONT_SIZE + LEVEL_GAP + DEFAULT_LINE_WIDTH + LEVEL_GAP + premisesH;

  return {
    width: totalW,
    height: totalH,
    render(parent, cx, bottomY) {
      // Conclusion text
      const concText = new ProofText(node.conclusion);
      concText.pos = { x: cx, y: bottomY };
      parent.add(concText, false);
      // Inference line
      const lineY = bottomY - FONT_SIZE / 2 - LEVEL_GAP;
      const line = new InferenceLine(lineW);
      line.pos = { x: cx, y: lineY };
      parent.add(line, false);
      // Rule label
      const ruleLabel = new ProofText(node.rule, RULE_FONT_SIZE, { italic: true, color: "#888" });
      ruleLabel.pos = { x: cx + lineW / 2 + LINE_PAD + ruleW / 2, y: lineY };
      parent.add(ruleLabel, false);
      // Premises (above line)
      const premisesTop = lineY - LEVEL_GAP;
      let childX = cx - premisesW / 2;
      for (const cl of childLayouts) {
        const childCx = childX + cl.width / 2;
        cl.render(parent, childCx, premisesTop);
        childX += cl.width + CHILD_GAP;
      }
    },
  };
}

// ─── Public API ────────────────────────────────────────────────────

/** Render a ProofTree as a Node2D scene (Gentzen-style derivation tree). */
export function renderProofTree(tree: ProofTree): Node2D {
  const root = new Node2D();
  let y = 0;

  // Title
  const titleStr = tree.hasHoles
    ? `${tree.name} : ${tree.proposition}  [incomplete]`
    : `${tree.name} : ${tree.proposition}`;
  const title = new ProofText(
    titleStr,
    TITLE_FONT_SIZE,
    { bold: true },
  );
  title.pos = { x: 0, y };
  root.add(title, false);
  y += TITLE_GAP;

  // Render each case
  let maxRight = 0;
  let maxLeft = 0;

  for (const c of tree.cases) {
    // Case header
    const patternLabel = c.bindings.length > 0
      ? `${c.pattern}(${c.bindings.join(", ")})`
      : c.pattern;
    const header = new ProofText(`| ${patternLabel}`, FONT_SIZE, { bold: true });
    header.pos = { x: 0, y };
    root.add(header, false);
    y += FONT_SIZE + LEVEL_GAP;

    // Layout and render the tree
    const layout = layoutNode(c.tree);
    const cx = 0;
    const bottomY = y + layout.height;
    layout.render(root, cx, bottomY);
    y = bottomY + CASE_GAP;

    maxRight = Math.max(maxRight, layout.width / 2);
    maxLeft = Math.max(maxLeft, layout.width / 2);
  }

  // Set bounds
  root.bounds = {
    min: { x: -maxLeft - 20, y: -20 },
    max: { x: maxRight + 20, y: y + 20 },
  };

  return root;
}
