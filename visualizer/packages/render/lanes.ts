// ═══════════════════════════════════════════════════════════════════
// Lane View Renderer
// Renders parallel horizontal lanes with positioned items, vertical
// markers, and cross-lane links. Domain-agnostic: supports swimlane
// diagrams, staves, timelines, sequence diagrams, etc.
// ═══════════════════════════════════════════════════════════════════

import * as d3 from "d3";
import {
  DEFAULT_LINE_WIDTH,
  defaultStroke,
  Node2D,
  type Pos,
  SHAPE_LINE_WIDTH,
  type SVG,
} from "./core.ts";
import {
  ClefSymbol,
  isMusicLane,
  MUSIC_LANE_HEIGHT,
  MusicNoteNode,
  MusicStaffLines,
  NoteNameLabel,
  parsePitch,
  pitchToStaffPosition,
  STAFF_HEIGHT,
  staffPositionToY,
  TieNode,
} from "./music.ts";

// ─── Layout constants ──────────────────────────────────────────────

const LANE_HEIGHT = 60;
const LANE_GAP = 10;
const LANE_LABEL_WIDTH = 100;
const ITEM_WIDTH = 60;
const ITEM_HEIGHT = 28;
const ITEM_GAP = 8;
const MARKER_OVERSHOOT = 8;
const LINK_ARROW_SIZE = 6;
const PADDING = 16;

// ─── Types ─────────────────────────────────────────────────────────

export type LaneViewInput = {
  name: string;
  lanes: { name: string; props: Record<string, string | number> }[];
  items: {
    position: number;
    lane: string;
    label: string;
    duration: number;
  }[];
  markers: { position: number; label?: string }[];
  links: { from: string; to: string; label?: string }[];
};

// ─── Renderer ──────────────────────────────────────────────────────

/** Build a Node2D scene graph for a lane view. */
export function renderLaneView(input: LaneViewInput): Node2D {
  const root = new Node2D();

  // Detect music mode per-lane and compute variable heights
  const musicLanes = new Set<string>();
  const laneHeights: number[] = [];
  const laneYOffsets: number[] = [];
  let yOffset = 0;
  for (const lane of input.lanes) {
    if (isMusicLane(lane.props)) musicLanes.add(lane.name);
    const h = musicLanes.has(lane.name) ? MUSIC_LANE_HEIGHT : LANE_HEIGHT;
    laneHeights.push(h);
    laneYOffsets.push(yOffset);
    yOffset += h + LANE_GAP;
  }
  const hasMusic = musicLanes.size > 0;

  // Map lane names to vertical indices
  const laneIndex = new Map<string, number>();
  input.lanes.forEach((l, i) => laneIndex.set(l.name, i));

  // Compute horizontal positions: group items by position, map to x coords
  const positions = [...new Set(input.items.map((it) => it.position))].sort(
    (a, b) => a - b,
  );
  const posToX = new Map<number, number>();
  positions.forEach((p, i) => {
    posToX.set(p, LANE_LABEL_WIDTH + PADDING + i * (ITEM_WIDTH + ITEM_GAP));
  });

  // Also include marker positions not covered by items
  for (const m of input.markers) {
    if (!posToX.has(m.position)) {
      positions.push(m.position);
      positions.sort((a, b) => a - b);
      // Re-index all
      posToX.clear();
      positions.forEach((p, i) => {
        posToX.set(
          p,
          LANE_LABEL_WIDTH + PADDING + i * (ITEM_WIDTH + ITEM_GAP),
        );
      });
    }
  }

  const totalWidth = LANE_LABEL_WIDTH + PADDING +
    positions.length * (ITEM_WIDTH + ITEM_GAP) + PADDING;
  const totalHeight = yOffset - LANE_GAP;

  // ─── Lane backgrounds + labels ─────────────────────────────────

  for (let i = 0; i < input.lanes.length; i++) {
    const lane = input.lanes[i];
    const y = laneYOffsets[i];
    const h = laneHeights[i];
    const isMusic = musicLanes.has(lane.name);

    // Lane background
    const bg = new LaneBackground(totalWidth, h);
    bg.pos = { x: 0, y };
    root.add(bg);

    // Lane label
    const label = new LaneLabel(lane.name);
    label.pos = { x: LANE_LABEL_WIDTH / 2, y: y + h / 2 };
    root.add(label);

    if (isMusic) {
      // Music staff lines — 5 properly spaced lines
      const staffTop = (h - STAFF_HEIGHT) / 2;
      const staffLines = new MusicStaffLines(
        totalWidth - LANE_LABEL_WIDTH - PADDING,
        staffTop,
      );
      staffLines.pos = { x: LANE_LABEL_WIDTH + PADDING, y };
      root.add(staffLines);

      // Clef symbol
      const clef = new ClefSymbol(
        String(lane.props.clef),
        staffTop,
      );
      clef.pos = { x: LANE_LABEL_WIDTH + PADDING, y };
      root.add(clef);
    } else {
      // Generic guide lines
      const lineCount = typeof lane.props.lines === "number"
        ? lane.props.lines
        : 0;
      if (lineCount > 0) {
        const guideLines = new GuideLines(
          totalWidth - LANE_LABEL_WIDTH - PADDING,
          h,
          lineCount,
        );
        guideLines.pos = { x: LANE_LABEL_WIDTH + PADDING, y };
        root.add(guideLines);
      }
    }
  }

  // ─── Items ─────────────────────────────────────────────────────

  // Track item positions for link resolution
  const itemCenters = new Map<string, Pos>();

  for (const item of input.items) {
    const li = laneIndex.get(item.lane);
    if (li === undefined) continue;
    const x = posToX.get(item.position);
    if (x === undefined) continue;

    const y = laneYOffsets[li];
    const h = laneHeights[li];
    const isMusic = musicLanes.has(item.lane);

    if (isMusic) {
      // Music note rendering
      const lane = input.lanes[li];
      const clef = String(lane.props.clef);
      const staffTop = (h - STAFF_HEIGHT) / 2;
      const pitch = parsePitch(item.label);

      if (pitch) {
        const staffPos = pitchToStaffPosition(pitch, clef);
        const noteNode = new MusicNoteNode(
          pitch,
          item.duration,
          staffPos,
          staffTop,
          clef,
        );
        noteNode.beatPosition = item.position;
        noteNode.pos = { x, y };
        noteNode.zIndex = 1;
        root.add(noteNode);

        // Small pitch label below the staff for readability
        const nameLabel = new NoteNameLabel(item.label);
        nameLabel.pos = { x, y: y + staffTop + STAFF_HEIGHT + 14 };
        root.add(nameLabel);

        // Track note center for links (ties)
        const noteY = y + staffTop + staffPositionToY(staffPos);
        itemCenters.set(item.label, { x, y: noteY });
      } else {
        // Non-pitch label on a music lane — fall back to generic item
        const w = ITEM_WIDTH;
        const itemNode = new LaneItemNode(w, ITEM_HEIGHT, item.label);
        itemNode.pos = { x: x - w / 2, y: y + (h - ITEM_HEIGHT) / 2 };
        itemNode.zIndex = 1;
        root.add(itemNode);
        itemCenters.set(item.label, { x, y: y + h / 2 });
      }
    } else {
      // Generic item rendering
      const w = item.duration > 0
        ? Math.max(
          ITEM_WIDTH,
          item.duration * (ITEM_WIDTH + ITEM_GAP) - ITEM_GAP,
        )
        : ITEM_WIDTH;

      const itemNode = new LaneItemNode(w, ITEM_HEIGHT, item.label);
      itemNode.pos = {
        x: x - w / 2,
        y: y + (h - ITEM_HEIGHT) / 2,
      };
      itemNode.zIndex = 1;
      root.add(itemNode);

      itemCenters.set(item.label, { x, y: y + h / 2 });
    }
  }

  // ─── Markers (vertical bar lines) ─────────────────────────────

  for (const marker of input.markers) {
    const x = posToX.get(marker.position);
    if (x === undefined) continue;

    const markerNode = new LaneMarkerNode(
      totalHeight + 2 * MARKER_OVERSHOOT,
      marker.label,
      hasMusic,
    );
    markerNode.pos = { x: x, y: -MARKER_OVERSHOOT };
    root.add(markerNode);
  }

  // ─── Links (cross-lane arrows / ties) ─────────────────────────

  for (const link of input.links) {
    const from = itemCenters.get(link.from);
    const to = itemCenters.get(link.to);
    if (!from || !to) continue;

    if (hasMusic) {
      // Render as a tie (curved arc) in music mode
      const above = from.y <= to.y;
      const tieNode = new TieNode(from, to, above);
      tieNode.zIndex = 2;
      root.add(tieNode);
    } else {
      const linkNode = new LaneLinkNode(from, to, link.label);
      linkNode.zIndex = 2;
      root.add(linkNode);
    }
  }

  // Set root bounds
  root.bounds = {
    min: { x: -PADDING, y: -PADDING - MARKER_OVERSHOOT },
    max: {
      x: totalWidth + PADDING,
      y: totalHeight + PADDING + MARKER_OVERSHOOT,
    },
  };

  return root;
}

// ─── Scene graph primitives for lanes ──────────────────────────────

class LaneBackground extends Node2D {
  constructor(private w: number, private h: number) {
    super();
    this.bounds = { min: { x: 0, y: 0 }, max: { x: w, y: h } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    return d3
      .create("svg:rect")
      .attr("x", pos.x)
      .attr("y", pos.y)
      .attr("width", this.w)
      .attr("height", this.h)
      .attr("rx", 4)
      .attr("fill", theme === "light" ? "#f5f5f5" : "#2a2a2a")
      .attr("stroke", theme === "light" ? "#ddd" : "#444")
      .attr("stroke-width", DEFAULT_LINE_WIDTH);
  }
}

class LaneLabel extends Node2D {
  constructor(private label: string) {
    super();
    this.bounds = {
      min: { x: -LANE_LABEL_WIDTH / 2, y: -10 },
      max: { x: LANE_LABEL_WIDTH / 2, y: 10 },
    };
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
      .attr("fill", defaultStroke(theme))
      .style("font-size", "14px")
      .style("font-weight", "600")
      .attr("font-family", "system-ui, sans-serif")
      .attr("pointer-events", "none");
  }
}

class GuideLines extends Node2D {
  constructor(
    private w: number,
    private h: number,
    private count: number,
  ) {
    super();
    this.bounds = { min: { x: 0, y: 0 }, max: { x: w, y: h } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const path = d3.path();
    const spacing = this.h / (this.count + 1);
    for (let i = 1; i <= this.count; i++) {
      const y = pos.y + i * spacing;
      path.moveTo(pos.x, y);
      path.lineTo(pos.x + this.w, y);
    }
    return d3
      .create("svg:path")
      .attr("d", path.toString())
      .attr("fill", "none")
      .attr("stroke", theme === "light" ? "#ccc" : "#555")
      .attr("stroke-width", 0.5)
      .attr("pointer-events", "none");
  }
}

class LaneItemNode extends Node2D {
  constructor(
    private w: number,
    private h: number,
    private label: string,
  ) {
    super();
    this.bounds = { min: { x: 0, y: 0 }, max: { x: w, y: h } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    // Return a group with rect + text
    const g = d3.create("svg:g");

    g.append("rect")
      .attr("x", pos.x)
      .attr("y", pos.y)
      .attr("width", this.w)
      .attr("height", this.h)
      .attr("rx", 6)
      .attr("fill", theme === "light" ? "#e3f2fd" : "#1e3a5f")
      .attr("stroke", theme === "light" ? "#90caf9" : "#5c9ce6")
      .attr("stroke-width", SHAPE_LINE_WIDTH);

    g.append("text")
      .text(this.label)
      .attr("x", pos.x + this.w / 2)
      .attr("y", pos.y + this.h / 2)
      .attr("text-anchor", "middle")
      .attr("dominant-baseline", "middle")
      .attr("fill", defaultStroke(theme))
      .style("font-size", "12px")
      .attr("font-family", "system-ui, sans-serif")
      .attr("pointer-events", "none");

    return g;
  }
}

class LaneMarkerNode extends Node2D {
  constructor(
    private h: number,
    private label?: string,
    private solid?: boolean,
  ) {
    super();
    this.bounds = { min: { x: -1, y: 0 }, max: { x: 1, y: h } };
  }

  override renderSelf(
    pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const g = d3.create("svg:g");

    const line = g.append("line")
      .attr("x1", pos.x)
      .attr("y1", pos.y)
      .attr("x2", pos.x)
      .attr("y2", pos.y + this.h)
      .attr("stroke", theme === "light" ? "#999" : "#777")
      .attr("stroke-width", this.solid ? 1.2 : DEFAULT_LINE_WIDTH);

    if (!this.solid) {
      line.attr("stroke-dasharray", "4,3");
    }

    if (this.label) {
      g.append("text")
        .text(this.label)
        .attr("x", pos.x)
        .attr("y", pos.y - 4)
        .attr("text-anchor", "middle")
        .attr("fill", theme === "light" ? "#666" : "#999")
        .style("font-size", "10px")
        .attr("font-family", "system-ui, sans-serif")
        .attr("pointer-events", "none");
    }

    return g;
  }
}

class LaneLinkNode extends Node2D {
  constructor(
    private from: Pos,
    private to: Pos,
    private label?: string,
  ) {
    super();
    this.bounds = {
      min: {
        x: Math.min(from.x, to.x) - LINK_ARROW_SIZE,
        y: Math.min(from.y, to.y) - LINK_ARROW_SIZE,
      },
      max: {
        x: Math.max(from.x, to.x) + LINK_ARROW_SIZE,
        y: Math.max(from.y, to.y) + LINK_ARROW_SIZE,
      },
    };
  }

  override renderSelf(
    _pos: Pos,
    theme: "light" | "dark",
  ): SVG | null {
    const g = d3.create("svg:g");
    const { from, to } = this;

    // Offset start/end to exit/enter item boundaries
    const dx = to.x - from.x;
    const dy = to.y - from.y;
    const len = Math.sqrt(dx * dx + dy * dy);
    if (len === 0) return null;

    const ux = dx / len;
    const uy = dy / len;
    const startX = from.x + ux * (ITEM_WIDTH / 2 + 2);
    const startY = from.y + uy * (ITEM_HEIGHT / 2 + 2);
    const endX = to.x - ux * (ITEM_WIDTH / 2 + 2);
    const endY = to.y - uy * (ITEM_HEIGHT / 2 + 2);

    // Arrow path
    const path = d3.path();
    path.moveTo(startX, startY);
    path.lineTo(endX, endY);

    g.append("path")
      .attr("d", path.toString())
      .attr("fill", "none")
      .attr("stroke", theme === "light" ? "#666" : "#aaa")
      .attr("stroke-width", SHAPE_LINE_WIDTH)
      .attr("marker-end", "url(#laneLinkArrow)");

    // Arrowhead
    const ax = endX - ux * LINK_ARROW_SIZE;
    const ay = endY - uy * LINK_ARROW_SIZE;
    const perpX = -uy * LINK_ARROW_SIZE * 0.5;
    const perpY = ux * LINK_ARROW_SIZE * 0.5;
    const arrowPath = d3.path();
    arrowPath.moveTo(endX, endY);
    arrowPath.lineTo(ax + perpX, ay + perpY);
    arrowPath.lineTo(ax - perpX, ay - perpY);
    arrowPath.closePath();

    g.append("path")
      .attr("d", arrowPath.toString())
      .attr("fill", theme === "light" ? "#666" : "#aaa")
      .attr("stroke", "none");

    // Label
    if (this.label) {
      const midX = (startX + endX) / 2;
      const midY = (startY + endY) / 2;
      g.append("text")
        .text(this.label)
        .attr("x", midX)
        .attr("y", midY - 6)
        .attr("text-anchor", "middle")
        .attr("fill", theme === "light" ? "#555" : "#bbb")
        .style("font-size", "10px")
        .attr("font-family", "system-ui, sans-serif")
        .attr("pointer-events", "none");
    }

    return g;
  }
}
