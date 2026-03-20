// Wire: a vertical-horizontal-vertical path connecting two Node2D endpoints.

import * as d3 from "d3";
import {
  Node2D, D,
  OPTIMAL_HIGHLIGHT_COLOR,
  type Pos, type SVG,
} from "../core.ts";
import { Path } from "../primitives.ts";

// A wire (vertical-horizontal-vertical) whose endpoints are connected to nodes (and defined by their offsets from the nodes).
// The position of this node is ignored.
export class Wire extends Node2D {
  public static readonly CORNER_RADIUS = D;

  start: Node2D;
  end: Node2D;
  viaY: number; // The Y coordinate of the wire's horizontal section, relative to start.y
  startOffset: Pos = { x: 0, y: 0 };
  endOffset: Pos = { x: 0, y: 0 };
  arrowStart: boolean = false;
  arrowEnd: boolean = false;

  // Optional click handler
  onClick?: () => void;

  mainPath: Path;

  // Highlight path for clicking the wire and triggering e.g. an interaction/reduction
  highlightPath: Path;
  highlightColor?: string;

  // A colored highlight path for indicating the wire level
  colorPath: Path;
  color?: string;

  constructor(
    start: Node2D,
    end: Node2D,
    viaY: number,
    onClick?: () => void,
    color?: string,
  ) {
    super();
    this.start = start;
    this.end = end;
    this.viaY = viaY;
    this.onClick = onClick;

    this.mainPath = new Path(d3.path());
    this.mainPath.translate = false;
    this.mainPath.zIndex = 0;
    this.mainPath.attrs["pointer-events"] = "none";
    this.add(this.mainPath);

    this.highlightPath = new Path(d3.path());
    this.highlightPath.translate = false;
    this.highlightPath.zIndex = 2;
    this.add(this.highlightPath);

    this.colorPath = new Path(d3.path());
    this.colorPath.translate = false;
    this.colorPath.zIndex = 1;
    this.add(this.colorPath);
    this.color = color;
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
    debug = false,
  ): SVG | null {
    // Create a vertical-horizontal-vertical path with rounded corners,
    // falling back to bezier when segments are too short for arcs.
    const path = d3.path();
    const globalStart = this.start.globalPosition();
    const globalEnd = this.end.globalPosition();
    const startX = globalStart.x + this.startOffset.x;
    const startY = globalStart.y + this.startOffset.y;
    const endX = globalEnd.x + this.endOffset.x;
    const endY = globalEnd.y + this.endOffset.y;
    const viaY = startY + this.viaY;

    if (this.arrowStart) {
      this.mainPath.attrs["marker-start"] = "url(#arrowStart)";
    }
    if (this.arrowEnd) {
      this.mainPath.attrs["marker-end"] = "url(#arrowEnd)";
    }

    path.moveTo(startX, startY);
    if (
      Math.min(
        Math.abs(viaY - startY),
        Math.abs(endY - viaY),
        Math.abs(endX - startX) / 2,
      ) < Wire.CORNER_RADIUS
    ) {
      // Draw bezier curve
      if (startX !== endX) {
        const halfway = startY + (endY - startY) / 2;
        path.bezierCurveTo(startX, halfway, endX, halfway, endX, endY);
      } else {
        path.lineTo(endX, endY);
      }
    } else {
      path.arcTo(startX, viaY, endX, viaY, Wire.CORNER_RADIUS);
      path.arcTo(endX, viaY, endX, endY, Wire.CORNER_RADIUS);
      path.lineTo(endX, endY);
    }

    // Update the main Path
    this.mainPath.path = path;

    if (this.color !== undefined) {
      this.colorPath.path = path;
      this.colorPath.attrs = {
        stroke: this.color,
        "stroke-width": "5px",
        "stroke-linecap": "butt",
      };
      this.colorPath.zIndex = theme === "light" ? -1 : 1;
    }

    if (this.onClick) {
      this.highlightPath.path = path;
      this.highlightPath.attrs = {
        stroke: this.highlightColor ?? OPTIMAL_HIGHLIGHT_COLOR,
        "stroke-width": "36px",
        "stroke-linecap": "round",
      };
      this.highlightPath.eventHandlers = {
        click: this.onClick,
        touchend: this.onClick,
        mousedown: function () {
          d3.select(this as any).attr("stroke-width", "36px");
        },
        mouseup: function () {
          d3.select(this as any).attr("stroke-width", "40px");
        },
        mouseover: function () {
          d3.select(this as any)
            .attr("stroke-width", "40px")
            .attr("cursor", "pointer");
        },
        mouseout: function () {
          d3.select(this as any).attr("stroke-width", "36px");
        },
        ...this.highlightPath.eventHandlers,
      };
    }
  }
}
