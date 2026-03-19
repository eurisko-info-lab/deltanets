// Compound/variable-size agents: Enclosure, Replicator, Twine + palette.

import * as d3 from "d3";
import {
  Node2D, D, SHAPE_LINE_WIDTH, DEFAULT_LINE_WIDTH,
  OPTIMAL_HIGHLIGHT_COLOR,
  defaultFill,
  type Pos, type SVG, type Bounds,
} from "../core.ts";
import { Text, Rect, Path, Label } from "../primitives.ts";
import { Fan } from "./simple.ts";
import { Wire } from "./wire.ts";

// A function enclosure, used by the Naive method.
export class Enclosure extends Node2D {
  vars: Label[];

  constructor(bounds: Bounds, vars: Label[]) {
    super();
    this.bounds = bounds;
    this.vars = vars;
    this.skipDebugBounds = true;
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
    debug = false,
  ): SVG | null {
    const newChildren: Node2D[] = [];
    if (this.vars.length > 0) {
      const globalPos = this.globalPosition();
      // Get the right-most variable
      const maxX = this.vars.reduce((acc, v) => {
        const varGlobalPos = v.globalPosition();
        const relativePos = {
          x: varGlobalPos.x - globalPos.x,
          y: varGlobalPos.y - globalPos.y,
        };
        return relativePos.x > acc ? relativePos.x : acc;
      }, -Infinity);
      // Draw left-side enclosure
      const leftSide = new Path();
      leftSide.path.moveTo(0, 0);
      leftSide.path.arcTo(
        this.bounds.min.x,
        0,
        this.bounds.min.x,
        this.bounds.max.y,
        Wire.CORNER_RADIUS,
      );
      leftSide.path.arcTo(
        this.bounds.min.x,
        this.bounds.max.y,
        0,
        this.bounds.max.y,
        Wire.CORNER_RADIUS,
      );
      leftSide.path.lineTo(maxX - Wire.CORNER_RADIUS, this.bounds.max.y);
      newChildren.push(leftSide);
      // Draw right-side enclosure
      const rightSide = new Path();
      rightSide.attrs = { "stroke-dasharray": "4,6" };
      rightSide.path.moveTo(0, 0);
      rightSide.path.arcTo(
        this.bounds.max.x,
        0,
        this.bounds.max.x,
        this.bounds.max.y,
        Wire.CORNER_RADIUS,
      );
      rightSide.path.arcTo(
        this.bounds.max.x,
        this.bounds.max.y,
        this.bounds.min.x,
        this.bounds.max.y,
        Wire.CORNER_RADIUS,
      );
      rightSide.path.lineTo(maxX, this.bounds.max.y);
      newChildren.push(rightSide);

      // Draw vertical lines under each bound variable
      this.vars.forEach((v) => {
        const varGlobalPos = v.globalPosition();
        const relativePos = {
          x: varGlobalPos.x - globalPos.x,
          y: varGlobalPos.y - globalPos.y,
        };
        const varPath = new Path();
        varPath.path.moveTo(relativePos.x, relativePos.y);
        varPath.path.arcTo(
          relativePos.x,
          this.bounds.max.y,
          this.bounds.min.x,
          this.bounds.max.y,
          Wire.CORNER_RADIUS,
        );
        newChildren.push(varPath);
      });
    } // No variables - draw full dashed enclosure
    else {
      const rect = new Rect(
        this.getWidth(),
        this.getHeight(),
        Wire.CORNER_RADIUS,
        Wire.CORNER_RADIUS,
      );
      rect.attrs = { fill: "none", "stroke-dasharray": "4,6" };
      rect.pos.x = this.bounds.min.x;
      rect.pos.y = this.bounds.min.y;
      newChildren.push(rect);
    }
    this.children = newChildren;
  }
}

// A replicator is a triangle-shaped interaction net agent with one principal port and any number of auxiliary ports.
// Each auxiliary port has a integer associated with it, called a "level delta".
export class Replicator extends Node2D {
  public static readonly AUX_WIDTH = 2 * D; // The width of each auxiliary port
  public static readonly HEIGHT = Fan.HEIGHT + this.AUX_WIDTH;

  type: "up" | "down";
  text: Text;
  levelDeltaTexts: Text[];
  path: Path;
  levelDeltas: number[];

  constructor(
    type: "up" | "down",
    label: string = "",
    levelDeltas: number[],
    height = Replicator.HEIGHT,
  ) {
    super();
    this.type = type;
    this.text = new Text(label);
    this.levelDeltaTexts = [];
    this.path = new Path();
    this.levelDeltas = levelDeltas;

    const xd = (Replicator.AUX_WIDTH * levelDeltas.length) / 2;

    this.path.attrs["stroke-width"] = SHAPE_LINE_WIDTH;
    const path = this.path.path;
    if (type === "up") {
      this.text.pos.y = 0.65 * (height - Replicator.AUX_WIDTH);
      path.moveTo(0, 0);
      path.lineTo(xd, height - Replicator.AUX_WIDTH);
      path.lineTo(-xd, height - Replicator.AUX_WIDTH);
      path.lineTo(0, 0);
      path.moveTo(-xd, height - Replicator.AUX_WIDTH);
      path.lineTo(-xd, height);
      path.lineTo(xd, height);
      path.lineTo(xd, height - Replicator.AUX_WIDTH);
      for (let i = 0; i < levelDeltas.length; i++) {
        path.moveTo(
          -xd + i * Replicator.AUX_WIDTH,
          height - Replicator.AUX_WIDTH,
        );
        path.lineTo(-xd + i * Replicator.AUX_WIDTH, height);
        const levelDeltaText = new Text(
          levelDeltas[levelDeltas.length - 1 - i].toString(),
        );
        levelDeltaText.styles["font-size"] = "16px";
        this.levelDeltaTexts.push(levelDeltaText);
        levelDeltaText.pos.x = -xd + i * Replicator.AUX_WIDTH +
          0.5 * Replicator.AUX_WIDTH;
        levelDeltaText.pos.y = height - 0.45 * Replicator.AUX_WIDTH;
        this.add(levelDeltaText);
      }
      path.closePath();
    } else {
      this.text.pos.y = Replicator.AUX_WIDTH +
        0.4 * (height - Replicator.AUX_WIDTH);
      path.moveTo(-xd, Replicator.AUX_WIDTH);
      path.lineTo(xd, Replicator.AUX_WIDTH);
      path.lineTo(0, height);
      path.lineTo(-xd, Replicator.AUX_WIDTH);
      path.moveTo(-xd, Replicator.AUX_WIDTH);
      path.lineTo(-xd, 0);
      path.lineTo(xd, 0);
      path.lineTo(xd, Replicator.AUX_WIDTH);
      for (let i = 0; i < levelDeltas.length; i++) {
        path.moveTo(-xd + i * Replicator.AUX_WIDTH, Replicator.AUX_WIDTH);
        path.lineTo(-xd + i * Replicator.AUX_WIDTH, 0);
        const levelDeltaText = new Text(levelDeltas[i].toString());
        levelDeltaText.styles["font-size"] = "16px";
        this.levelDeltaTexts.push(levelDeltaText);
        levelDeltaText.pos.x = -xd + i * Replicator.AUX_WIDTH +
          0.5 * Replicator.AUX_WIDTH;
        levelDeltaText.pos.y = 0.55 * Replicator.AUX_WIDTH;
        this.add(levelDeltaText);
      }

      path.closePath();
    }
    this.add(this.path);
    this.add(this.text);
    this.bounds = {
      min: { x: -(levelDeltas.length / 2) * Replicator.AUX_WIDTH - D, y: -D },
      max: {
        x: (levelDeltas.length / 2) * Replicator.AUX_WIDTH + D,
        y: height + D,
      },
    };
  }

  portDelta(i: number): number {
    return (i + 0.5 - this.levelDeltas.length / 2) * Replicator.AUX_WIDTH;
  }
}

// A twine is a sequence of boxes, each with an integer and a pointer (and arrow point out of the box to another twine).
// The integer represents the level of the pointed-to twine. As such, a twine's level is stored in all of the twines which point to it.
export class Twine extends Node2D {
  public static readonly SIZE = 2 * D; // The size of each box
  public static readonly PADDING = D / 3; // The padding around the twine

  type: "horizontal" | "vertical" = "horizontal";
  levels: (string | null)[]; // null means no pointer (i.e. an eraser)
  labelLeft?: string;
  labelRight?: string;
  labelLeftText?: Text;
  labelRightText?: Text;
  path: Path;
  innerRect: Rect;
  outerRect: Rect;
  highlightRect: Rect;
  color?: string;

  // Optional click handler
  onClick?: () => void;

  constructor(
    levels: (string | null)[],
    labelLeft?: string,
    labelRight?: string,
    type: "horizontal" | "vertical" = "horizontal",
    color?: string,
    deltas?: number[],
  ) {
    super();
    this.type = type;
    this.levels = levels;
    this.labelLeft = labelLeft;
    this.labelRight = labelRight;
    this.color = color;
    this.path = new Path();
    this.path.attrs["stroke-width"] = DEFAULT_LINE_WIDTH;
    this.path.attrs["pointer-events"] = "none";
    const path = this.path.path;

    const xd = (Twine.SIZE * levels.length) / 2;

    // Create LHS label if one was provided
    if (labelLeft) {
      this.labelLeftText = new Text(labelLeft);
      this.labelLeftText.styles["font-size"] = "16px";
      this.labelLeftText.styles["text-anchor"] = "end";
      this.labelLeftText.styles["opacity"] = 0.6;
      this.labelLeftText.pos.x = -8;
      this.labelLeftText.pos.y = -0.5 * Twine.SIZE;
      this.add(this.labelLeftText);
    }

    // Create RHS label if one was provided
    if (labelRight) {
      this.labelRightText = new Text(labelRight);
      this.labelRightText.styles["font-size"] = "16px";
      this.labelRightText.styles["text-anchor"] = "start";
      this.labelRightText.styles["opacity"] = 0.6;
      this.labelRightText.pos.x = 8;
      this.labelRightText.pos.y = -0.5 * Twine.SIZE;
      this.add(this.labelRightText);
    }

    const longOuterSide = Twine.SIZE * levels.length + 2 * Twine.PADDING;
    const shortOuterSide = Twine.SIZE + 2 * Twine.PADDING;

    // Create highlight rectangle (outer than outer)
    const highlightAddition = Twine.SIZE;
    this.highlightRect = new Rect(
      (type === "horizontal" ? longOuterSide : shortOuterSide) +
        highlightAddition,
      (type === "horizontal" ? shortOuterSide : longOuterSide) +
        highlightAddition,
      6,
      6,
      { display: "none" },
    );
    this.highlightRect.pos.x =
      (type === "horizontal"
        ? -Twine.PADDING - xd
        : -0.5 * (Twine.SIZE + levels.length * Twine.PADDING)) -
      highlightAddition / 2;
    this.highlightRect.pos.y = -highlightAddition / 2;
    this.add(this.highlightRect);

    // Create the outer rectangle
    this.outerRect = new Rect(
      type === "horizontal" ? longOuterSide : shortOuterSide,
      type === "horizontal" ? shortOuterSide : longOuterSide,
      4,
      4,
      { fill: "none", "pointer-events": "none" },
    );
    this.outerRect.pos.x = type === "horizontal"
      ? -Twine.PADDING - xd
      : -0.5 * (Twine.SIZE + levels.length * Twine.PADDING);
    this.add(this.outerRect);

    // Create the inner rectangle
    const longInnerSide = Twine.SIZE * levels.length;
    const shortInnerSide = Twine.SIZE;
    const innerRectRoundedness = 2;
    this.innerRect = new Rect(
      type === "horizontal" ? longInnerSide : shortInnerSide,
      type === "horizontal" ? shortInnerSide : longInnerSide,
      innerRectRoundedness,
      innerRectRoundedness,
      {
        fill: "none",
        "pointer-events": "none",
      },
    );
    this.innerRect.pos.x = type === "horizontal" ? -xd : -0.5 * Twine.SIZE;
    this.innerRect.pos.y = Twine.PADDING;
    this.add(this.innerRect);

    for (let i = 0; i < levels.length; i++) {
      if (i > 0) {
        if (type === "horizontal") {
          path.moveTo(-xd + i * Twine.SIZE, Twine.SIZE + Twine.PADDING);
          path.lineTo(-xd + i * Twine.SIZE, Twine.PADDING);
        } else {
          path.moveTo(-0.5 * Twine.SIZE, Twine.PADDING + i * Twine.SIZE);
          path.lineTo(0.5 * Twine.SIZE, Twine.PADDING + i * Twine.SIZE);
        }
      }

      if (levels[i] === null) {
        const c = innerRectRoundedness / 4;
        if (type === "horizontal") {
          path.moveTo(-xd + i * Twine.SIZE + c, Twine.SIZE + Twine.PADDING - c);
          path.lineTo(-xd + (i + 1) * Twine.SIZE - c, Twine.PADDING + c);
          path.moveTo(-xd + i * Twine.SIZE + c, Twine.PADDING + c);
          path.lineTo(
            -xd + (i + 1) * Twine.SIZE - c,
            Twine.SIZE + Twine.PADDING - c,
          );
        } else {
          path.moveTo(
            -0.5 * Twine.SIZE + c,
            Twine.PADDING + i * Twine.SIZE + c,
          );
          path.lineTo(
            0.5 * Twine.SIZE - c,
            Twine.PADDING + (i + 1) * Twine.SIZE - c,
          );
          path.moveTo(
            -0.5 * Twine.SIZE + c,
            Twine.PADDING + (i + 1) * Twine.SIZE - c,
          );
          path.lineTo(0.5 * Twine.SIZE - c, Twine.PADDING + i * Twine.SIZE + c);
        }
      } else {
        const levelText = new Text(levels[i]!);
        levelText.styles["font-size"] = "16px";

        if (type === "horizontal") {
          levelText.pos.x = -xd + i * Twine.SIZE + 0.5 * Twine.SIZE;
          levelText.pos.y = 0.55 * Twine.SIZE + Twine.PADDING;
        } else {
          levelText.pos.x = 0;
          levelText.pos.y = Twine.PADDING + i * Twine.SIZE + 0.55 * Twine.SIZE;
        }
        this.add(levelText);
      }
    }

    this.add(this.path);
    if (type === "horizontal") {
      this.bounds = {
        min: {
          x: -xd - Twine.PADDING - (Twine.SIZE / 2 - Twine.PADDING),
          y: -(Twine.SIZE / 2 - Twine.PADDING),
        },
        max: {
          x: xd + Twine.PADDING + (Twine.SIZE / 2 - Twine.PADDING),
          y: Twine.SIZE + 2 * Twine.PADDING + (Twine.SIZE / 2 - Twine.PADDING),
        },
      };
    } else {
      this.bounds = {
        min: {
          x: -Twine.SIZE / 2 - Twine.PADDING - (Twine.SIZE / 2 - Twine.PADDING),
          y: -(Twine.SIZE / 2 - Twine.PADDING),
        },
        max: {
          x: Twine.SIZE / 2 + Twine.PADDING + (Twine.SIZE / 2 - Twine.PADDING),
          y: Twine.SIZE * levels.length +
            Twine.PADDING * 2 +
            (Twine.SIZE / 2 - Twine.PADDING),
        },
      };
    }
  }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug?: boolean) {
    this.innerRect.attrs["fill"] = defaultFill(theme);
    this.outerRect.attrs["stroke"] = "none";
    if (this.color) {
      const opacity = theme === "light" ? "FF" : "CC";
      this.outerRect.attrs["fill"] = this.color + opacity;
    }

    if (this.onClick) {
      this.highlightRect.attrs = {
        stroke: "none",
        fill: OPTIMAL_HIGHLIGHT_COLOR,
      };

      const hX = this.highlightRect.globalPosition().x;
      const hY = this.highlightRect.globalPosition().y;
      const hWidth = this.highlightRect.width;
      const hHeight = this.highlightRect.height;

      const hXBig = hX - Twine.PADDING / 2;
      const hYBig = hY - Twine.PADDING / 2;
      const hWidthBig = hWidth + Twine.PADDING;
      const hHeightBig = hHeight + Twine.PADDING;

      this.highlightRect.eventHandlers = {
        click: this.onClick,
        touchend: this.onClick,
        mousedown: function () {
          d3.select(this as any)
            .attr("x", hX)
            .attr("y", hY)
            .attr("width", hWidth)
            .attr("height", hHeight);
        },
        mouseup: function () {
          d3.select(this as any)
            .attr("x", hXBig)
            .attr("y", hYBig)
            .attr("width", hWidthBig)
            .attr("height", hHeightBig);
        },
        mouseover: function () {
          d3.select(this as any)
            .attr("x", hXBig)
            .attr("y", hYBig)
            .attr("width", hWidthBig)
            .attr("height", hHeightBig)
            .attr("cursor", "pointer");
        },
        mouseout: function () {
          d3.select(this as any)
            .attr("x", hX)
            .attr("y", hY)
            .attr("width", hWidth)
            .attr("height", hHeight);
        },
        ...this.highlightRect.eventHandlers,
      };
    }
  }

  portDelta(i: number): number {
    return (i + 0.5 - this.levels.length / 2) * Twine.SIZE;
  }
}

// Colors
export const palette = {
  blue: "#4e79a7",
  orange: "#f28e2c",
  red: "#e15659",
  teal: "#76b7b2",
  green: "#59a14f",
  yellow: "#edc948",
  purple: "#b07aa1",
  pink: "#ff9da7",
  brown: "#9c755f",
  grey: "#bab0ac",
};
