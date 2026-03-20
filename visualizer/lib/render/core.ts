import * as d3 from "d3";
import { removeFromArrayIf } from "../util.ts";

// The type of an SVG node.
export type SVG = any;

// The type of an SVG node with z-index information.
export type zSVG = {
  zIndex: number;
  svg: SVG;
};

// 2-dimensional position.
export type Pos = {
  x: number;
  y: number;
};

// A 2-dimensional bounding box.
export type Bounds = {
  min: Pos;
  max: Pos;
};

// Minimal distance, mostly used in inets methods
export const D = 12;

export const DEFAULT_LINE_WIDTH = 1;
export const SHAPE_LINE_WIDTH = 1.4;

export const ARROW_TIP_DELTA = 4;

// The default stroke color for a theme.
export function defaultStroke(theme: "light" | "dark") {
  return theme === "light" ? "#222" : "#FFF";
}

// The default fill color for a theme.
export function defaultFill(theme: "light" | "dark") {
  return theme === "light" ? "#FFF" : "#1A1A1A";
}

// Color for optimal rules
export const OPTIMAL_HIGHLIGHT_COLOR = "#44e00040";

// Color for suboptimal rules
export const SUBOPTIMAL_HIGHLIGHT_COLOR = "#ff666645";

// Color for the node currently being type-checked
export const TYPECHECK_ACTIVE_COLOR = "#3b82f650";

// Color for nodes that have been successfully type-checked
export const TYPECHECK_DONE_COLOR = "#22c55e30";

// Color for type check errors
export const TYPECHECK_ERROR_COLOR = "#ef444460";

// A 2-dimensional node with an optional `Drawable`.
// It can have any number of children `Node`s.
export class Node2D {
  // The position of the node relative to its parent
  pos: Pos = { x: 0, y: 0 };
  // The children of the node
  children: Node2D[] = [];
  // The parent of the node (if any)
  parent?: Node2D;
  // The bounding box of the node (relative to its position) [The idea is to use this instead of wLeft + wRight + h]
  bounds: Bounds = {
    min: { x: 0, y: 0 },
    max: { x: 0, y: 0 },
  };
  // The z-index of the node
  zIndex = 0;
  // Whether the node is to be rendered
  visible = true;
  // Whether to skip debug bounding box rendering (e.g. for Enclosure)
  skipDebugBounds = false;
  // Whether this node represents a wire endpoint (used in deltanets rendering)
  isWireEndpoint = false;

  // The width of the node.
  getWidth() {
    return this.bounds.max.x - this.bounds.min.x;
  }

  // The height of the node.
  getHeight() {
    return this.bounds.max.y - this.bounds.min.y;
  }

  // Add a child to the node.
  add(child: Node2D, updateBounds = true) {
    this.children.push(child);
    child.parent = this;
    // Update bounds
    if (updateBounds) {
      this.includeBounds(child);
    }
  }

  // Include the bounds of a node inside this node.
  includeBounds(node: Node2D) {
    this.bounds.min.x = Math.min(
      this.bounds.min.x,
      node.pos.x + node.bounds.min.x,
    );
    this.bounds.min.y = Math.min(
      this.bounds.min.y,
      node.pos.y + node.bounds.min.y,
    );
    this.bounds.max.x = Math.max(
      this.bounds.max.x,
      node.pos.x + node.bounds.max.x,
    );
    this.bounds.max.y = Math.max(
      this.bounds.max.y,
      node.pos.y + node.bounds.max.y,
    );
  }

  // Update the bounds of the node based on its children.
  updateBounds() {
    this.children.forEach((child) => this.includeBounds(child));
  }

  // Remove children from the node.
  remove(...children: Node2D[]) {
    children.forEach((child) => (child.parent = undefined));
    removeFromArrayIf(this.children, (child) => children.includes(child));
  }

  // For each descendant of the node, call a function.
  forEachDescendant(f: (node: Node2D) => void) {
    this.children.forEach((child) => {
      f(this);
      child.forEachDescendant(f);
    });
  }

  // Compute the global position of the node.
  globalPosition(): Pos {
    let x = this.pos.x;
    let y = this.pos.y;
    let parent = this.parent;
    while (parent) {
      x += parent.pos.x;
      y += parent.pos.y;
      parent = parent.parent;
    }
    return { x, y };
  }

  // Render the node and its descendants to a set of zSVGs.
  render(
    theme: "light" | "dark",
    debug = false,
    offset: Pos = { x: 0, y: 0 },
  ): zSVG[] {
    const pos = {
      x: this.pos.x + offset.x,
      y: this.pos.y + offset.y,
    };
    const zSVGs: zSVG[] = [];

    // Render the node itself and add it to the zSVGs if needed
    if (this.visible) {
      const svg = this.renderSelf(pos, theme, debug);
      if (svg) {
        zSVGs.push({ svg, zIndex: this.zIndex });
      }
      // If in debug mode, render a rectangle to show the node's bounds
      if (debug && !this.skipDebugBounds) {
        const width = this.getWidth();
        const height = this.getHeight();
        if (width > 0 || height > 0) {
          const radius = Math.min(
            D / 2,
            width / 2,
            height / 2,
          );
          const stroke = theme === "light" ? "#AAA" : "#555";
          const fill = theme === "light" ? "#AAA0 " : "#5550";
          // Debug bounding box
          const boundsRectSVG = d3
            .create("svg:rect")
            .attr("x", pos.x + this.bounds.min.x)
            .attr("y", pos.y + this.bounds.min.y)
            .attr("width", width)
            .attr("height", height)
            .attr("rx", radius)
            .attr("ry", radius)
            .attr("fill", fill)
            .attr("stroke", stroke)
            .attr("stroke-width", 1)
            .attr("pointer-events", "none");
          zSVGs.push({ svg: boundsRectSVG, zIndex: this.zIndex - 1 });

          // Create X to mark the center
          const crossPath = d3.path();
          const delta = Math.cos(Math.PI / 4) * D / 2;
          crossPath.moveTo(pos.x - delta, pos.y - delta);
          crossPath.lineTo(pos.x + delta, pos.y + delta);
          crossPath.moveTo(pos.x + delta, pos.y - delta);
          crossPath.lineTo(pos.x - delta, pos.y + delta);
          const crossSVG = d3
            .create("svg:path")
            .attr("d", crossPath.toString())
            .attr("fill", "none")
            .attr("stroke", stroke)
            .attr("stroke-width", DEFAULT_LINE_WIDTH);
          zSVGs.push({
            svg: crossSVG,
            zIndex: this.zIndex - 1,
          });
        }
      }
    }

    // Render the children and add them to the zSVGs
    zSVGs.push(
      ...this.children.map((child) => child.render(theme, debug, pos)).flat(),
    );

    return zSVGs;
  }

  // Render the node itself. To be implemented by subclasses.
  renderSelf(pos: Pos, theme: "light" | "dark", debug = false): SVG | null {
    return null;
  }
}

// Renders a set of zSVGs.
export function render(zSVGs: zSVG[]): SVG[] {
  zSVGs.sort((a, b) => a.zIndex - b.zIndex);
  return zSVGs.map((zSVG) => zSVG.svg.node());
}

// Helper function to apply attributes, styles, and event handlers to an SVG.
export function applyEntries(
  svg: SVG,
  field: string,
  object: Record<string, any>,
) {
  for (const [k, v] of Object.entries(object)) {
    svg[field](k, v);
  }
}
