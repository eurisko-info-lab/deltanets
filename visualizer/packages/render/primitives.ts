import * as d3 from "d3";
import {
  applyEntries,
  D,
  DEFAULT_LINE_WIDTH,
  defaultFill,
  defaultStroke,
  Node2D,
  OPTIMAL_HIGHLIGHT_COLOR,
  type Pos,
  type SVG,
} from "./core.ts";

// deno-lint-ignore no-explicit-any
type Entries = Record<string, any>;

/** Apply attrs / styles / eventHandlers overrides to an SVG element. */
// deno-lint-ignore no-explicit-any
function applyOverrides(svg: any, o: { attrs: Entries; styles: Entries; eventHandlers: Entries }) {
  applyEntries(svg, "attr", o.attrs);
  applyEntries(svg, "style", o.styles);
  applyEntries(svg, "on", o.eventHandlers);
}

// Some text.
export class Text extends Node2D {
  constructor(
    public value: string = "",
    public attrs: Entries = {},
    public styles: Entries = {},
    public eventHandlers: Entries = {},
  ) { super(); }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug = false): SVG | null {
    const svg = d3.create("svg:text")
      .text(this.value)
      .attr("x", pos.x).attr("y", pos.y)
      .attr("text-anchor", "middle").attr("dominant-baseline", "middle")
      .attr("fill", defaultStroke(theme))
      .style("font-size", "20px")
      .attr("font-family", "Libertinus")
      .attr("pointer-events", "none");
    applyOverrides(svg, this);
    return svg;
  }
}

// A rectangle.
export class Rect extends Node2D {
  constructor(
    public width: number,
    public height: number,
    public rx: number = 0,
    public ry: number = 0,
    public attrs: Entries = {},
    public styles: Entries = {},
    public eventHandlers: Entries = {},
  ) { super(); }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug = false): SVG | null {
    const svg = d3.create("svg:rect")
      .attr("x", pos.x).attr("y", pos.y)
      .attr("width", this.width).attr("height", this.height)
      .attr("rx", this.rx).attr("ry", this.ry)
      .attr("fill", defaultFill(theme))
      .attr("stroke", defaultStroke(theme))
      .attr("stroke-width", DEFAULT_LINE_WIDTH);
    applyOverrides(svg, this);
    return svg;
  }
}

// A circle.
export class Circle extends Node2D {
  constructor(
    public radius: number,
    public attrs: Entries = {},
    public styles: Entries = {},
    public eventHandlers: Entries = {},
  ) { super(); }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug = false): SVG | null {
    const svg = d3.create("svg:circle")
      .attr("r", this.radius)
      .attr("cx", pos.x).attr("cy", pos.y)
      .attr("fill", defaultFill(theme))
      .attr("stroke", defaultStroke(theme))
      .attr("stroke-width", DEFAULT_LINE_WIDTH);
    applyOverrides(svg, this);
    return svg;
  }
}

// A path.
export class Path extends Node2D {
  translate = true;
  constructor(
    public path: d3.Path = d3.path(),
    public attrs: Entries = {},
    public styles: Entries = {},
    public eventHandlers: Entries = {},
  ) {
    super();
    this.attrs["stroke-linejoin"] = "round";
  }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug = false): SVG | null {
    const svg = d3.create("svg:path")
      .attr("d", this.path.toString())
      .attr("fill", "none")
      .attr("stroke", defaultStroke(theme))
      .attr("stroke-width", DEFAULT_LINE_WIDTH);
    if (this.translate) svg.attr("transform", `translate(${pos.x}, ${pos.y})`);
    applyOverrides(svg, this);
    return svg;
  }
}

// A label.
export class Label extends Node2D {
  public static readonly SIZE = 15;
  public static readonly SIZE_HIGHLIGHT = 18;

  text: Text;
  mainRect: Rect;
  highlightRect: Rect;
  highlightColor?: string;

  constructor(label: string = "") {
    super();
    this.text = new Text(label);
    this.text.zIndex = 3;

    this.mainRect = new Rect(
      Label.SIZE * 2,
      Label.SIZE * 2,
      Label.SIZE,
      Label.SIZE,
      {},
      { stroke: "none" },
    );
    this.mainRect.zIndex = 1;
    this.mainRect.pos.x = -Label.SIZE;
    this.mainRect.pos.y = -Label.SIZE;

    this.highlightRect = new Rect(
      Label.SIZE_HIGHLIGHT * 2,
      Label.SIZE_HIGHLIGHT * 2,
      Label.SIZE_HIGHLIGHT,
      Label.SIZE_HIGHLIGHT,
      { stroke: "none", display: "none" },
    );
    this.highlightRect.zIndex = 2;
    this.highlightRect.pos.x = -18;
    this.highlightRect.pos.y = -18;

    this.add(this.mainRect);
    this.add(this.highlightRect);
    this.add(this.text);

    this.bounds = {
      min: { x: -D, y: -D },
      max: { x: D, y: D },
    };
  }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug?: boolean) {
    this.highlightRect.attrs = {
      ...this.highlightRect.attrs,
      fill: this.highlightColor ?? OPTIMAL_HIGHLIGHT_COLOR,
    };
    if (this.highlightColor) {
      this.highlightRect.attrs.display = "block";
    }
  }
}

// 8 ports equally distributed around the circle
export type Port =
  | "n" // north
  | "ne" // north-east
  | "e" // east
  | "se" // south-east
  | "s" // south
  | "sw" // south-west
  | "w" // weast
  | "nw"; // north-west

// A simple edge between two points, with optional bezier control points.
export class Edge extends Node2D {
  public static readonly PORT_SCALE = 35;

  start: Pos;
  end: Pos;
  startPort?: Port;
  endPort?: Port;
  // Optional click handler
  onClick?: () => void;
  // Used to link a bound variable with its abstraction-application edge redex,
  // for highlighting the bound variables when hovering over the redex.
  className = "";

  mainPath: Path;
  highlightPath: Path;

  constructor(
    start: Pos,
    end: Pos,
    startPort?: Port,
    endPort?: Port,
    onClick?: () => void,
  ) {
    super();

    this.start = start;
    this.end = end;
    this.startPort = startPort;
    this.endPort = endPort;
    this.onClick = onClick;

    this.mainPath = new Path(d3.path());
    this.mainPath.zIndex = 0;
    this.add(this.mainPath);

    this.highlightPath = new Path(d3.path());
    this.highlightPath.zIndex = 2;
    this.add(this.highlightPath);
  }

  private static readonly PORT_DIRS: Record<Port, [number, number]> = {
    n: [0, -1], ne: [Math.SQRT1_2, -Math.SQRT1_2],
    e: [1, 0], se: [Math.SQRT1_2, Math.SQRT1_2],
    s: [0, 1], sw: [-Math.SQRT1_2, Math.SQRT1_2],
    w: [-1, 0], nw: [-Math.SQRT1_2, -Math.SQRT1_2],
  };

  portOffset(port: Port, s: number): Pos {
    const [dx, dy] = Edge.PORT_DIRS[port];
    return { x: dx * s, y: dy * s };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
    debug = false,
  ): SVG | null {
    // Create path based on start and end points
    const path = d3.path();
    const deltaStart = this.startPort
      ? this.portOffset(this.startPort, Edge.PORT_SCALE)
      : undefined;
    const deltaEnd = this.endPort
      ? this.portOffset(this.endPort, Edge.PORT_SCALE)
      : undefined;
    path.moveTo(this.start.x, this.start.y);
    if (deltaStart !== undefined || deltaEnd !== undefined) {
      path.bezierCurveTo(
        this.start.x + (deltaStart?.x ?? 0),
        this.start.y + (deltaStart?.y ?? 0),
        this.end.x + (deltaEnd?.x ?? 0),
        this.end.y + (deltaEnd?.y ?? 0),
        this.end.x,
        this.end.y,
      );
    } else {
      path.lineTo(this.end.x, this.end.y);
    }

    // Update the main Path
    this.mainPath.path = path;

    if (this.onClick) {
      this.highlightPath.path = path;
      this.highlightPath.attrs = {
        stroke: OPTIMAL_HIGHLIGHT_COLOR,
        "stroke-width": "36px",
        "stroke-linecap": "round",
      };
      this.highlightPath.eventHandlers = {
        click: this.onClick,
        touchend: this.onClick,
        // d3 event handlers receive the DOM element as `this`
        mousedown: function (this: Element) {
          d3.select(this).attr("stroke-width", "36px");
        },
        mouseup: function (this: Element) {
          d3.select(this).attr("stroke-width", "40px");
        },
        mouseover: function (this: Element) {
          d3.select(this)
            .attr("stroke-width", "40px")
            .attr("cursor", "pointer");
        },
        mouseout: function (this: Element) {
          d3.select(this).attr("stroke-width", "36px");
        },
        ...this.highlightPath.eventHandlers,
      };
    }
  }
}
