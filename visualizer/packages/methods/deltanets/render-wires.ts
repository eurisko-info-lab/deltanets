// ═══════════════════════════════════════════════════════════════════
// Wire Rendering
// Pairs up endpoints and creates connecting wires between them.
// ═══════════════════════════════════════════════════════════════════

import { Signal } from "@preact/signals";
import { D, Node2D, Wire } from "@deltanets/render";
import { MethodState } from "../index.ts";
import {
  deltanets,
  type Graph,
  type NodePort,
  reciprocal,
  type Redex,
} from "@deltanets/core";
import type { Data } from "./config.ts";
import { applyReduction } from "./reduction.ts";

const { levelColor } = deltanets;

// The type of a graph endpoint
export type Endpoint = {
  nodePort: NodePort;
  node2D: Node2D;
  level?: number;
  used?: boolean;
  redex?: Redex;
};

// Renders wires between paired endpoints, and returns the remaining endpoints
export const renderWires = (
  node2D: Node2D,
  endpoints: Endpoint[],
  state: Signal<MethodState<Graph, Data>>,
) => {
  // Sort endpoints by x position
  endpoints.sort((a, b) =>
    a.node2D.globalPosition().x - b.node2D.globalPosition().x
  );

  // Compile pairs of endpoints that are connected
  const wiresToCreate: { i: number; j: number; redex?: Redex }[] = [];
  for (let i = 0; i < endpoints.length; i++) {
    for (let j = i + 1; j < endpoints.length; j++) {
      if (endpoints[i].used || endpoints[j].used) {
        continue;
      }
      if (
        reciprocal(endpoints[i].nodePort).node === endpoints[j].nodePort.node &&
        reciprocal(endpoints[i].nodePort).port === endpoints[j].nodePort.port
      ) {
        endpoints[i].used = true;
        endpoints[j].used = true;
        wiresToCreate.push({
          i,
          j,
          redex: endpoints[i].redex || endpoints[j].redex,
        });
      }
    }
  }

  // Sort wiresToCreate by length
  wiresToCreate.sort((a, b) => {
    const horizontalDist = (i: number, j: number) =>
      endpoints[j].node2D.globalPosition().x -
      endpoints[i].node2D.globalPosition().x;
    return horizontalDist(a.i, a.j) - horizontalDist(b.i, b.j);
  });

  // Create wires
  const wires: Wire[] = [];
  wiresToCreate.forEach(({ i, j, redex }) => {
    const leftX = endpoints[i].node2D.globalPosition().x;
    const rightX = endpoints[j].node2D.globalPosition().x;
    // Find wires between the left and right endpoints
    const wiresBetween = wires.filter((wire) =>
      !(
        wire.start.globalPosition().x > rightX ||
        wire.end.globalPosition().x < leftX
      )
    );
    // Get max height of endpoints in between i and j
    const maxH = Math.max(
      endpoints[i].node2D.globalPosition().y +
        endpoints[i].node2D.bounds.max.y + D,
      endpoints[j].node2D.globalPosition().y +
        endpoints[j].node2D.bounds.max.y + D,
      ...endpoints.slice(i + 1, j).map((endpoint) =>
        endpoint.node2D.globalPosition().y + endpoint.node2D.bounds.max.y + D
      ),
      ...wiresBetween.map((w) => w.start.globalPosition().y + w.viaY + 2 * D),
    );
    // Create wire
    // Set level as undefined if conflicting to indicate issue
    const level = (endpoints[i].level === endpoints[j].level &&
        endpoints[i].level !== undefined)
      ? endpoints[i].level
      : undefined;

    const wire = new Wire(
      endpoints[i].node2D,
      endpoints[j].node2D,
      maxH - endpoints[i].node2D.globalPosition().y,
      redex ? (() => applyReduction(state, redex.reduce)) : undefined,
      level !== undefined ? levelColor(level) : undefined,
    );
    wires.push(wire);
    node2D.add(wire);
    // Update bounds of node2D
    node2D.bounds.max.y = Math.max(node2D.bounds.max.y, maxH + D);
  });
};
