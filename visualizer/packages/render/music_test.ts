// Tests for music notation rendering utilities
import { assertEquals } from "$std/assert/mod.ts";
import {
  isMusicLane,
  parsePitch,
  pitchToStaffPosition,
  STAFF_HEIGHT,
  STAFF_LINE_SPACING,
  staffPositionToY,
} from "./music.ts";

// ─── parsePitch ────────────────────────────────────────────────────

Deno.test("parsePitch: simple note", () => {
  const p = parsePitch("C4");
  assertEquals(p, { note: "C", accidental: "", octave: 4 });
});

Deno.test("parsePitch: sharp", () => {
  const p = parsePitch("F#5");
  assertEquals(p, { note: "F", accidental: "#", octave: 5 });
});

Deno.test("parsePitch: flat", () => {
  const p = parsePitch("Bb3");
  assertEquals(p, { note: "B", accidental: "b", octave: 3 });
});

Deno.test("parsePitch: lowercase normalizes to uppercase", () => {
  const p = parsePitch("e4");
  assertEquals(p, { note: "E", accidental: "", octave: 4 });
});

Deno.test("parsePitch: invalid returns null", () => {
  assertEquals(parsePitch("XY"), null);
  assertEquals(parsePitch(""), null);
  assertEquals(parsePitch("C"), null);
  assertEquals(parsePitch("12"), null);
});

// ─── pitchToStaffPosition ──────────────────────────────────────────

Deno.test("pitchToStaffPosition: treble clef E4 is bottom line (0)", () => {
  const p = parsePitch("E4")!;
  assertEquals(pitchToStaffPosition(p, "treble"), 0);
});

Deno.test("pitchToStaffPosition: treble clef F5 is top line (8)", () => {
  const p = parsePitch("F5")!;
  assertEquals(pitchToStaffPosition(p, "treble"), 8);
});

Deno.test("pitchToStaffPosition: treble clef C4 is below staff (-2)", () => {
  const p = parsePitch("C4")!;
  assertEquals(pitchToStaffPosition(p, "treble"), -2);
});

Deno.test("pitchToStaffPosition: treble clef B4 is middle line (4)", () => {
  const p = parsePitch("B4")!;
  assertEquals(pitchToStaffPosition(p, "treble"), 4);
});

Deno.test("pitchToStaffPosition: bass clef G2 is bottom line (0)", () => {
  const p = parsePitch("G2")!;
  assertEquals(pitchToStaffPosition(p, "bass"), 0);
});

Deno.test("pitchToStaffPosition: bass clef A3 is top line (8)", () => {
  const p = parsePitch("A3")!;
  assertEquals(pitchToStaffPosition(p, "bass"), 8);
});

// ─── staffPositionToY ──────────────────────────────────────────────

Deno.test("staffPositionToY: bottom line at STAFF_HEIGHT", () => {
  assertEquals(staffPositionToY(0), STAFF_HEIGHT);
});

Deno.test("staffPositionToY: top line at 0", () => {
  assertEquals(staffPositionToY(8), 0);
});

Deno.test("staffPositionToY: middle line at half height", () => {
  assertEquals(staffPositionToY(4), STAFF_HEIGHT / 2);
});

Deno.test("staffPositionToY: each step is half a line spacing", () => {
  const y0 = staffPositionToY(0);
  const y1 = staffPositionToY(1);
  assertEquals(y0 - y1, STAFF_LINE_SPACING / 2);
});

// ─── isMusicLane ───────────────────────────────────────────────────

Deno.test("isMusicLane: true for treble clef", () => {
  assertEquals(isMusicLane({ clef: "treble", lines: 5 }), true);
});

Deno.test("isMusicLane: true for bass clef", () => {
  assertEquals(isMusicLane({ clef: "bass", lines: 5 }), true);
});

Deno.test("isMusicLane: false without clef", () => {
  assertEquals(isMusicLane({ lines: 5 }), false);
});

Deno.test("isMusicLane: false for unknown clef", () => {
  assertEquals(isMusicLane({ clef: "unknown" }), false);
});
