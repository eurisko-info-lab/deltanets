import {
  Node2D, D,
  type Pos, type SVG, type Bounds,
} from "../core.ts";
import { Rect, Path, Label } from "../primitives.ts";
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
