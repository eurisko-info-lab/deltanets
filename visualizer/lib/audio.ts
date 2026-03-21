// ═══════════════════════════════════════════════════════════════════
// MIDI-like Audio Playback
// Converts lane view music data into scheduled Web Audio tones.
// ═══════════════════════════════════════════════════════════════════

import { signal } from "@preact/signals";
import { parsePitch } from "@deltanets/render";
import type { LaneViewInput } from "@deltanets/render";

// ─── State ─────────────────────────────────────────────────────────

export const isPlaying = signal(false);

// ─── Pitch → frequency ────────────────────────────────────────────

const SEMITONE_OFFSET: Record<string, number> = {
  C: 0,
  D: 2,
  E: 4,
  F: 5,
  G: 7,
  A: 9,
  B: 11,
};

/** Convert a pitch label like "C4", "F#5", "Eb3" to a frequency in Hz. */
function pitchToFrequency(label: string): number | null {
  const p = parsePitch(label);
  if (!p) return null;
  const midi = (p.octave + 1) * 12 + SEMITONE_OFFSET[p.note] +
    (p.accidental === "#" ? 1 : p.accidental === "b" ? -1 : 0);
  // A4 (MIDI 69) = 440 Hz
  return 440 * Math.pow(2, (midi - 69) / 12);
}

// ─── Playback engine ───────────────────────────────────────────────

let audioCtx: AudioContext | null = null;
let scheduledSources: OscillatorNode[] = [];
let stopTimeout: ReturnType<typeof setTimeout> | null = null;

function getAudioContext(): AudioContext {
  if (!audioCtx) audioCtx = new AudioContext();
  return audioCtx;
}

/** Schedule and play all music notes from a lane view. */
export function playLaneView(input: LaneViewInput, bpm = 120) {
  stop();

  const ctx = getAudioContext();
  if (ctx.state === "suspended") ctx.resume();

  const beatDuration = 60 / bpm; // seconds per beat
  const now = ctx.currentTime + 0.05; // small lookahead

  // Collect which lanes are music lanes (have a clef)
  const musicLanes = new Set<string>();
  for (const lane of input.lanes) {
    if (lane.props.clef) musicLanes.add(lane.name);
  }

  let maxEndTime = 0;

  for (const item of input.items) {
    if (!musicLanes.has(item.lane)) continue;
    const freq = pitchToFrequency(item.label);
    if (!freq) continue;

    const startTime = now + item.position * beatDuration;
    const dur = item.duration * beatDuration;

    // Oscillator
    const osc = ctx.createOscillator();
    osc.type = "triangle";
    osc.frequency.value = freq;

    // Envelope: gentle attack/release to avoid clicks
    const gain = ctx.createGain();
    gain.gain.setValueAtTime(0, startTime);
    gain.gain.linearRampToValueAtTime(0.25, startTime + 0.02);
    gain.gain.setValueAtTime(0.25, startTime + dur - 0.05);
    gain.gain.linearRampToValueAtTime(0, startTime + dur);

    osc.connect(gain);
    gain.connect(ctx.destination);

    osc.start(startTime);
    osc.stop(startTime + dur);
    scheduledSources.push(osc);

    const end = startTime + dur;
    if (end > maxEndTime) maxEndTime = end;
  }

  isPlaying.value = true;

  // Auto-stop when all notes finish
  const totalDuration = (maxEndTime - now) * 1000 + 100;
  stopTimeout = setTimeout(() => {
    isPlaying.value = false;
    scheduledSources = [];
  }, totalDuration);
}

/** Stop all currently playing audio. */
export function stop() {
  if (stopTimeout !== null) {
    clearTimeout(stopTimeout);
    stopTimeout = null;
  }
  for (const osc of scheduledSources) {
    try {
      osc.stop();
    } catch { /* already stopped */ }
  }
  scheduledSources = [];
  isPlaying.value = false;
}
