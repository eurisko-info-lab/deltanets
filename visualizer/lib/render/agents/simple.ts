// Simple fixed-shape interaction net agents: Fan, Fin, Eraser, Root, Fae.

import {
  Node2D, D, SHAPE_LINE_WIDTH,
  defaultStroke,
  type Pos,
} from "../core.ts";
import { Text, Circle, Path } from "../primitives.ts";

// A fan is a triangle-shaped interaction net agent with one principal port and two auxiliary ports.
export class Fan extends Node2D {
  public static readonly WIDTH = 5 * D;
  public static readonly HEIGHT = 3 * D;

  // A port delta of 2 makes it so that a stack of fans doesn't result in any curved wires
  public static readonly PORT_DELTA = 2 * D;

  type: "up" | "down";
  text: Text;
  path: Path;
  highlightColor?: string;

  constructor(type: "up" | "down", label: string = "") {
    super();
    this.type = type;
    this.text = new Text(label);
    this.path = new Path();
    this.path.attrs["stroke-width"] = SHAPE_LINE_WIDTH;
    const path = this.path.path;
    if (type === "up") {
      this.text.pos.y = 0.7 * Fan.HEIGHT;
      path.moveTo(0, 0);
      path.lineTo(Fan.WIDTH / 2, Fan.HEIGHT);
      path.lineTo(-Fan.WIDTH / 2, Fan.HEIGHT);
      path.lineTo(0, 0);
      path.closePath();
    } else {
      this.text.pos.y = 0.4 * Fan.HEIGHT;
      path.moveTo(-Fan.WIDTH / 2, 0);
      path.lineTo(Fan.WIDTH / 2, 0);
      path.lineTo(0, Fan.HEIGHT);
      path.lineTo(-Fan.WIDTH / 2, 0);
      path.closePath();
    }
    this.add(this.path);
    this.add(this.text);
    this.bounds = {
      min: { x: -3 * D, y: -D },
      max: { x: 3 * D, y: Fan.HEIGHT + D },
    };
  }

  portDelta(i: number): number {
    if (i === 0) {
      return -Fan.PORT_DELTA;
    } else {
      return Fan.PORT_DELTA;
    }
  }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug?: boolean) {
    if (this.highlightColor) {
      this.path.attrs.fill = this.highlightColor;
    }
  }
}

// A fin is an interaction net agent with one principal port at the top and one auxiliary port at the bottom.
export class Fin extends Node2D {
  // Fin is equilateral
  public static readonly WIDTH = 12;
  public static readonly HEIGHT = (Math.sqrt(3) * Fin.WIDTH) / 2;

  type: "up" | "down";
  scopeType: "+" | "-" | undefined;
  fv: boolean;
  text: Text;
  path: Path;

  constructor(
    type: "up" | "down",
    scopeType: "+" | "-" | undefined,
    fv: boolean,
    label: string = "",
  ) {
    super();
    this.type = type;
    this.scopeType = scopeType;
    this.fv = fv;
    this.text = new Text(/* fv ? "" :  */ label);
    this.text.pos.y = 0.7 * Fin.HEIGHT;
    this.path = new Path();
    const path = this.path.path;
    if (type === "up") {
      this.text.pos.y = 0.7 * Fin.HEIGHT;
      path.moveTo(0, 0);
      path.lineTo(Fin.WIDTH / 2, Fin.HEIGHT);
      path.lineTo(-Fin.WIDTH / 2, Fin.HEIGHT);
      path.lineTo(0, 0);
      path.closePath();
    } else {
      this.text.pos.y = 0.4 * Fin.HEIGHT;
      path.moveTo(-Fin.WIDTH / 2, 0);
      path.lineTo(Fin.WIDTH / 2, 0);
      path.lineTo(0, Fin.HEIGHT);
      path.lineTo(-Fin.WIDTH / 2, 0);
      path.closePath();
    }
    this.text.pos.x = Fin.WIDTH + 2;
    this.add(this.text);
    this.add(this.path);
    this.bounds = {
      min: { x: -D, y: -D / 2 },
      max: { x: 2 * D, y: Fin.HEIGHT + D / 2 },
    };
  }

  override renderSelf(pos: Pos, theme: "light" | "dark", debug?: boolean) {
    this.path.attrs.fill = this.fv
      ? "#0F0"
      : this.scopeType === undefined
      ? defaultStroke(theme)
      : this.scopeType === "+"
      ? "#F00"
      : "#00F";
    this.path.attrs["stroke-width"] = 0.4;
  }
}

// An eraser is a circle with a cross inside.
export class Eraser extends Node2D {
  // This way an eraser fits snugly when connected to a fan
  // i.e. it never horizontally overflows the fan's horizontal span
  public static readonly RADIUS = Fan.WIDTH / 2 - Fan.PORT_DELTA;

  circle: Circle;
  path: Path;

  constructor() {
    super();

    // Create the circle
    this.circle = new Circle(Eraser.RADIUS);
    this.circle.attrs["stroke-width"] = SHAPE_LINE_WIDTH;
    this.circle.zIndex = 1;
    this.add(this.circle);

    // Create an X inside the circle
    this.path = new Path();
    this.path.attrs["stroke-width"] = SHAPE_LINE_WIDTH;
    this.path.zIndex = 1;
    const path = this.path.path;
    const delta = Math.cos(Math.PI / 4) * Eraser.RADIUS;
    path.moveTo(-delta, -delta);
    path.lineTo(delta, delta);
    path.moveTo(delta, -delta);
    path.lineTo(-delta, delta);
    this.add(this.path);

    // Set the bounds
    this.bounds = {
      min: { x: -1 * D, y: -1 * D },
      max: { x: 1 * D, y: 1 * D },
    };
  }
}

// A root is a circle.
export class Root extends Node2D {
  public static readonly RADIUS = Eraser.RADIUS;

  circle: Circle;

  constructor() {
    super();

    // Create the circle
    this.circle = new Circle(Eraser.RADIUS);
    this.circle.attrs["stroke-width"] = SHAPE_LINE_WIDTH;
    this.circle.zIndex = 1;
    this.add(this.circle);

    // Set the bounds
    this.bounds = {
      min: { x: -1 * D, y: -1 * D },
      max: { x: 1 * D, y: 1 * D },
    };
  }
}

// A fae is a triangle-shaped interaction net agent with one principal port and any number of auxiliary ports.
// TODO: make min width like Fan and a Fan-width Fae can have two or three aux ports. For more ports, make it wider by AUX_WIDTH.
export class Fae extends Node2D {
  public static readonly AUX_WIDTH = 2 * D; // The width of each auxiliary port
  public static readonly HEIGHT = Fan.HEIGHT;

  type: "up" | "down";
  length: number;
  text: Text;
  path: Path;

  constructor(type: "up" | "down", label: string = "", length: number) {
    super();
    this.type = type;
    this.length = length;
    this.text = new Text(label);
    this.path = new Path();

    const xd = (Fae.AUX_WIDTH * length) / 2;

    this.path.attrs["stroke-width"] = SHAPE_LINE_WIDTH;
    const path = this.path.path;
    if (type === "up") {
      this.text.pos.y = 0.65 * (Fae.HEIGHT);
      path.moveTo(0, 0);
      path.lineTo(xd, Fae.HEIGHT);
      path.lineTo(-xd, Fae.HEIGHT);
      path.lineTo(0, 0);
      path.closePath();
    } else {
      this.text.pos.y = 0.4 * (Fae.HEIGHT);
      path.moveTo(-xd, 0);
      path.lineTo(xd, 0);
      path.lineTo(0, Fae.HEIGHT);
      path.lineTo(-xd, 0);
      path.closePath();
    }
    this.add(this.path);
    this.add(this.text);
    this.bounds = {
      min: { x: -(length / 2) * Fae.AUX_WIDTH - D, y: -D },
      max: {
        x: (length / 2) * Fae.AUX_WIDTH + D,
        y: Fae.HEIGHT + D,
      },
    };
  }

  portDelta(i: number): number {
    return (i + 0.5 - this.length / 2) * Fae.AUX_WIDTH;
  }
}
