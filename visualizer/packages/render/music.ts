// ═══════════════════════════════════════════════════════════════════
// Music Notation Renderer
// Renders musical notes on staves using pitch labels (e.g. "C4")
// and duration values. Activated when a lane has a "clef" property.
// ═══════════════════════════════════════════════════════════════════

import * as d3 from "d3";
import { defaultStroke, Node2D, type Pos, type SVG } from "./core.ts";

// ─── Constants ─────────────────────────────────────────────────────

export const STAFF_LINE_SPACING = 10;
export const STAFF_HEIGHT = 4 * STAFF_LINE_SPACING; // 5 lines = 40px
export const MUSIC_LANE_HEIGHT = 120;
const NOTEHEAD_RX = 5.5;
const NOTEHEAD_RY = 4;
const NOTEHEAD_TILT = -15; // degrees
const STEM_LENGTH = 32;
const STEM_WIDTH = 1.2;
const FLAG_WIDTH = 8;
const CLEF_WIDTH = 30;
const ACCIDENTAL_OFFSET = 10;
const LEDGER_LINE_HALF = 8;

// ─── Pitch parsing ────────────────────────────────────────────────

type Pitch = {
  note: string; // C, D, E, F, G, A, B
  accidental: "" | "#" | "b";
  octave: number;
};

const NOTE_INDEX: Record<string, number> = {
  C: 0,
  D: 1,
  E: 2,
  F: 3,
  G: 4,
  A: 5,
  B: 6,
};

/** Parse a pitch label like "C4", "F#5", "Eb3" into components. */
export function parsePitch(label: string): Pitch | null {
  const m = label.match(/^([A-Ga-g])([#b]?)(\d)$/);
  if (!m) return null;
  return {
    note: m[1].toUpperCase(),
    accidental: (m[2] || "") as "" | "#" | "b",
    octave: parseInt(m[3]),
  };
}

/** Convert a pitch to diatonic scale position (C0 = 0, D0 = 1, ..., C1 = 7, ...). */
function diatonicPosition(pitch: Pitch): number {
  return pitch.octave * 7 + NOTE_INDEX[pitch.note];
}

// Reference positions: the bottom line of each clef
const CLEF_BOTTOM_LINE: Record<string, number> = {
  treble: diatonicPosition({ note: "E", accidental: "", octave: 4 }), // E4
  bass: diatonicPosition({ note: "G", accidental: "", octave: 2 }), // G2
  alto: diatonicPosition({ note: "F", accidental: "", octave: 3 }), // F3
};

/**
 * Get staff position of a pitch in half-line-spacings from bottom line.
 * 0 = bottom line, 1 = first space, 2 = second line, etc.
 */
export function pitchToStaffPosition(
  pitch: Pitch,
  clef: string,
): number {
  const ref = CLEF_BOTTOM_LINE[clef] ?? CLEF_BOTTOM_LINE.treble;
  return diatonicPosition(pitch) - ref;
}

/**
 * Get the Y offset of a staff position relative to the staff's top line.
 * Staff top line = position 8, bottom line = position 0.
 * Y increases downward in SVG, so higher positions → lower Y.
 */
export function staffPositionToY(staffPos: number): number {
  // Top line is at staff position 8, y = 0
  // Bottom line is at staff position 0, y = STAFF_HEIGHT
  return STAFF_HEIGHT - staffPos * (STAFF_LINE_SPACING / 2);
}

// ─── Music lane detection ──────────────────────────────────────────

/** Check if a lane has music properties (clef). */
export function isMusicLane(
  props: Record<string, string | number>,
): boolean {
  return typeof props.clef === "string" && props.clef in CLEF_BOTTOM_LINE;
}

// ─── Clef rendering ───────────────────────────────────────────────

export class ClefSymbol extends Node2D {
  constructor(
    private clef: string,
    private staffTop: number,
  ) {
    super();
    this.bounds = {
      min: { x: 0, y: 0 },
      max: { x: CLEF_WIDTH, y: STAFF_HEIGHT },
    };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const g = d3.create("svg:g");
    const color = defaultStroke(theme);
    const x = pos.x + CLEF_WIDTH / 2;

    if (this.clef === "treble") {
      // Treble clef — draw a stylized G-clef shape
      const top = pos.y + this.staffTop - 8;
      g.append("text")
        .text("\u{1D11E}")
        .attr("x", x)
        .attr("y", top + STAFF_HEIGHT / 2 + 14)
        .attr("text-anchor", "middle")
        .attr("dominant-baseline", "middle")
        .attr("fill", color)
        .style("font-size", "56px")
        .attr("font-family", "serif")
        .attr("pointer-events", "none");
    } else if (this.clef === "bass") {
      // Bass clef
      const top = pos.y + this.staffTop;
      g.append("text")
        .text("\u{1D122}")
        .attr("x", x)
        .attr("y", top + STAFF_HEIGHT / 2 + 4)
        .attr("text-anchor", "middle")
        .attr("dominant-baseline", "middle")
        .attr("fill", color)
        .style("font-size", "36px")
        .attr("font-family", "serif")
        .attr("pointer-events", "none");
    } else if (this.clef === "alto") {
      // Alto clef — C clef
      const top = pos.y + this.staffTop;
      g.append("text")
        .text("\u{1D121}")
        .attr("x", x)
        .attr("y", top + STAFF_HEIGHT / 2 + 4)
        .attr("text-anchor", "middle")
        .attr("dominant-baseline", "middle")
        .attr("fill", color)
        .style("font-size", "36px")
        .attr("font-family", "serif")
        .attr("pointer-events", "none");
    }

    return g;
  }
}

// ─── Staff lines ──────────────────────────────────────────────────

export class MusicStaffLines extends Node2D {
  constructor(
    private w: number,
    private staffTop: number,
  ) {
    super();
    this.bounds = { min: { x: 0, y: 0 }, max: { x: w, y: STAFF_HEIGHT } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const path = d3.path();
    for (let i = 0; i < 5; i++) {
      const y = pos.y + this.staffTop + i * STAFF_LINE_SPACING;
      path.moveTo(pos.x, y);
      path.lineTo(pos.x + this.w, y);
    }
    return d3
      .create("svg:path")
      .attr("d", path.toString())
      .attr("fill", "none")
      .attr("stroke", theme === "light" ? "#555" : "#888")
      .attr("stroke-width", 0.8)
      .attr("pointer-events", "none");
  }
}

// ─── Music note ───────────────────────────────────────────────────

export class MusicNoteNode extends Node2D {
  private filled: boolean;
  private hasStem: boolean;
  private flagCount: number;
  private stemUp: boolean;
  beatPosition = -1;

  constructor(
    private pitch: Pitch,
    duration: number,
    staffPos: number,
    private staffTop: number,
    private clef: string,
  ) {
    super();

    // Duration: 4=whole, 2=half, 1=quarter, 0.5=eighth, 0.25=sixteenth
    const dur = duration > 0 ? duration : 1;
    this.filled = dur <= 1; // quarter and shorter are filled
    this.hasStem = dur < 4; // whole notes have no stem
    this.flagCount = dur <= 0.25 ? 2 : dur <= 0.5 ? 1 : 0;
    this.stemUp = staffPos < 4; // below middle line: stem up

    const w = NOTEHEAD_RX * 2 + 20;
    const h = STEM_LENGTH + NOTEHEAD_RY * 2;
    this.bounds = { min: { x: -w / 2, y: -h }, max: { x: w / 2, y: h } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const g = d3.create("svg:g")
      .attr("class", "music-note")
      .attr("data-beat", this.beatPosition);
    const color = defaultStroke(theme);
    const pitch = this.pitch;
    const staffPos = pitchToStaffPosition(pitch, this.clef);
    const noteY = pos.y + this.staffTop + staffPositionToY(staffPos);
    const noteX = pos.x;

    // Ledger lines
    if (staffPos < 0) {
      // Below the staff
      const path = d3.path();
      for (let p = -2; p >= staffPos; p -= 2) {
        const ly = pos.y + this.staffTop + staffPositionToY(p);
        path.moveTo(noteX - LEDGER_LINE_HALF, ly);
        path.lineTo(noteX + LEDGER_LINE_HALF, ly);
      }
      g.append("path")
        .attr("d", path.toString())
        .attr("fill", "none")
        .attr("stroke", color)
        .attr("stroke-width", 0.8);
    }
    if (staffPos > 8) {
      // Above the staff
      const path = d3.path();
      for (let p = 10; p <= staffPos; p += 2) {
        const ly = pos.y + this.staffTop + staffPositionToY(p);
        path.moveTo(noteX - LEDGER_LINE_HALF, ly);
        path.lineTo(noteX + LEDGER_LINE_HALF, ly);
      }
      g.append("path")
        .attr("d", path.toString())
        .attr("fill", "none")
        .attr("stroke", color)
        .attr("stroke-width", 0.8);
    }

    // Notehead (tilted ellipse)
    g.append("ellipse")
      .attr("cx", noteX)
      .attr("cy", noteY)
      .attr("rx", NOTEHEAD_RX)
      .attr("ry", NOTEHEAD_RY)
      .attr("transform", `rotate(${NOTEHEAD_TILT}, ${noteX}, ${noteY})`)
      .attr("fill", this.filled ? color : "none")
      .attr("stroke", color)
      .attr("stroke-width", this.filled ? 0 : 1.2);

    // Stem
    if (this.hasStem) {
      const stemX = this.stemUp
        ? noteX + NOTEHEAD_RX - 0.5
        : noteX - NOTEHEAD_RX + 0.5;
      const stemY1 = noteY;
      const stemY2 = this.stemUp ? noteY - STEM_LENGTH : noteY + STEM_LENGTH;

      g.append("line")
        .attr("x1", stemX)
        .attr("y1", stemY1)
        .attr("x2", stemX)
        .attr("y2", stemY2)
        .attr("stroke", color)
        .attr("stroke-width", STEM_WIDTH);

      // Flags
      for (let f = 0; f < this.flagCount; f++) {
        const flagPath = d3.path();
        const flagOffset = f * 8;
        if (this.stemUp) {
          const fy = stemY2 + flagOffset;
          flagPath.moveTo(stemX, fy);
          flagPath.bezierCurveTo(
            stemX + FLAG_WIDTH * 0.5,
            fy + 4,
            stemX + FLAG_WIDTH,
            fy + 10,
            stemX + FLAG_WIDTH * 0.3,
            fy + 16,
          );
        } else {
          const fy = stemY2 - flagOffset;
          flagPath.moveTo(stemX, fy);
          flagPath.bezierCurveTo(
            stemX - FLAG_WIDTH * 0.5,
            fy - 4,
            stemX - FLAG_WIDTH,
            fy - 10,
            stemX - FLAG_WIDTH * 0.3,
            fy - 16,
          );
        }
        g.append("path")
          .attr("d", flagPath.toString())
          .attr("fill", "none")
          .attr("stroke", color)
          .attr("stroke-width", 1.2);
      }
    }

    // Accidental
    if (pitch.accidental) {
      const accText = pitch.accidental === "#" ? "\u266F" : "\u266D";
      g.append("text")
        .text(accText)
        .attr("x", noteX - NOTEHEAD_RX - ACCIDENTAL_OFFSET)
        .attr("y", noteY)
        .attr("text-anchor", "middle")
        .attr("dominant-baseline", "middle")
        .attr("fill", color)
        .style("font-size", "14px")
        .attr("font-family", "serif")
        .attr("pointer-events", "none");
    }

    return g;
  }
}

// ─── Tie / slur (curved link between notes) ───────────────────────

export class TieNode extends Node2D {
  constructor(
    private from: Pos,
    private to: Pos,
    private above: boolean,
  ) {
    super();
    this.bounds = {
      min: {
        x: Math.min(from.x, to.x),
        y: Math.min(from.y, to.y) - 20,
      },
      max: {
        x: Math.max(from.x, to.x),
        y: Math.max(from.y, to.y) + 20,
      },
    };
  }

  override renderSelf(
    _pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const { from, to, above } = this;
    const midX = (from.x + to.x) / 2;
    const curveY = above
      ? Math.min(from.y, to.y) - 15
      : Math.max(from.y, to.y) + 15;

    const path = d3.path();
    path.moveTo(from.x, from.y);
    path.quadraticCurveTo(midX, curveY, to.x, to.y);

    return d3
      .create("svg:path")
      .attr("d", path.toString())
      .attr("fill", "none")
      .attr("stroke", theme === "light" ? "#555" : "#aaa")
      .attr("stroke-width", 1.2)
      .attr("pointer-events", "none");
  }
}

// ─── Note name display (below note) ──────────────────────────────

export class NoteNameLabel extends Node2D {
  constructor(private label: string) {
    super();
    this.bounds = { min: { x: -10, y: -6 }, max: { x: 10, y: 6 } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    return d3
      .create("svg:text")
      .text(this.label)
      .attr("x", pos.x)
      .attr("y", pos.y)
      .attr("text-anchor", "middle")
      .attr("dominant-baseline", "middle")
      .attr("fill", theme === "light" ? "#888" : "#666")
      .style("font-size", "9px")
      .attr("font-family", "system-ui, sans-serif")
      .attr("pointer-events", "none");
  }
}
