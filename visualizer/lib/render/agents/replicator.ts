import {
  Node2D, D, SHAPE_LINE_WIDTH,
} from "../core.ts";
import { Text, Path } from "../primitives.ts";
import { Fan } from "./simple.ts";

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
