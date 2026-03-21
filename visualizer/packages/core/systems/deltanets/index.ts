// Δ-Nets interaction system: graph analysis, cleanup, and system object.

import { removeFromArrayIf } from "../../util.ts";
import { Ports } from "../../types.ts";
import type { Graph, InteractionSystem, Node, NodePort } from "../../types.ts";
import { link } from "../../graph.ts";
import { typeCheck } from "../../typechecker.ts";

import {
  countAuxErasers,
  type DeltaData,
  isConnectedToAllErasers,
  isExprAgent,
  isParentPort,
  type NodeType,
  type RepStatus,
} from "./helpers.ts";
import { buildGraph } from "./build.ts";
import { getRedex, getRedexes } from "./redexes.ts";
import { readbackGraph, readbackGraphToString } from "./readback.ts";

// Re-export types and helpers used by consumers
export type { DeltaData, NodeType, RepStatus };
export { countAuxErasers, isConnectedToAllErasers, isExprAgent, isParentPort };
export { readbackGraph, readbackGraphToString };

// --- Graph analysis ---

function findReachableNodes(graph: Graph): Set<Node> {
  const rootNode = graph.find((node) => node.type === "root")!;
  const reachable = new Set<Node>();
  reachable.add(rootNode);

  const traverse = (nodePort: NodePort) => {
    const node = nodePort.node;
    const port = nodePort.port;
    if (reachable.has(node)) {
      return;
    }
    reachable.add(node);
    if (node.type === "abs" && port === Ports.abs.principal) {
      if (node.ports[Ports.abs.bind].node.type === "era") {
        traverse(node.ports[Ports.abs.bind]);
      }
      traverse(node.ports[Ports.abs.body]);
      traverse(node.ports[Ports.abs.type]);
    } else if (node.type === "app" && port === Ports.app.result) {
      traverse(node.ports[Ports.app.func]);
      traverse(node.ports[Ports.app.arg]);
    } else if (
      node.type === "type-arrow" && port === Ports.typeArrow.principal
    ) {
      traverse(node.ports[Ports.typeArrow.domain]);
      traverse(node.ports[Ports.typeArrow.codomain]);
    } else if (node.type === "type-base" || node.type === "type-hole") {
      // Leaf type nodes — nothing to traverse
    } else if (node.type.startsWith("rep") && port !== 0) {
      traverse(node.ports[0]);
    } else if (node.type.startsWith("rep") && port === 0) {
      for (let i = 1; i < node.ports.length; i++) {
        traverse(node.ports[i]);
      }
    } else if (node.type === "era") {
      // nothing to do
    }
  };
  traverse(rootNode.ports[0]);

  return reachable;
}

function cleanupGraph(graph: Graph): void {
  const reachable = findReachableNodes(graph);

  for (const node of graph) {
    if (reachable.has(node)) {
      node.ports.forEach((p, i) => {
        if (!reachable.has(p.node)) {
          const eraser: Node = { type: "era", label: "era", ports: [] };
          link({ node, port: i }, { node: eraser, port: 0 });
        }
      });
    }
  }

  removeFromArrayIf(graph, (n) => !reachable.has(n));

  graph.forEach((node) => {
    if (!node.type.startsWith("rep")) {
      return;
    }
    node.ports.forEach((p, i) => {
      if (p.node.type !== "era" || i === 0) {
        return;
      }
      p.erase = true;
    });
    removeFromArrayIf(
      node.levelDeltas!,
      (ld, i) => node.ports[i + 1].erase === true,
    );
    removeFromArrayIf(node.ports, (p) => p.erase === true);
    node.ports.forEach((p, i) => {
      link(p, { node, port: i });
    });
  });

  const nodesToRemove: Node[] = [];
  graph.forEach((node) => {
    if (
      node.type.startsWith("rep") &&
      (node.ports.length === 2 && node.levelDeltas![0] === 0)
    ) {
      link(node.ports[0], node.ports[1]);
      nodesToRemove.push(node);
    }
  });
  for (const node of nodesToRemove) {
    removeFromArrayIf(graph, (n) => n === node);
  }
}

// --- Level colors ---

const levelColors = [
  "#ff666686",
  "#ffbd5586",
  "#ffff6686",
  "#9de24f86",
  "#87cefa86",
];

function levelColor(level: number): string | undefined {
  return levelColors[level % levelColors.length];
}

// --- System object ---

export const deltanets: InteractionSystem = {
  name: "Δ-Nets (2025)",
  buildGraph,
  getRedexes,
  getRedex,
  findReachableNodes,
  cleanupGraph,
  isParentPort,
  isConnectedToAllErasers,
  countAuxErasers,
  levelColor,
  typeCheck,
  isExprAgent,
};
