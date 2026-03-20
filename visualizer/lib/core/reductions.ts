// Universal interaction net reduction primitives.
// These implement the three fundamental reduction patterns shared by all interaction net systems.

import { removeFromArrayIf } from "../util.ts";
import type { Graph, Node } from "./types.ts";
import { link } from "./graph.ts";

// Annihilates two interacting nodes
export function reduceAnnihilate(node: Node, graph: Graph) {
  const other = node.ports[0].node;

  // Sanity check
  if (other.ports[0].node !== node) {
    throw new Error("nodes are not interacting!");
  }

  const minPorts = Math.min(node.ports.length, other.ports.length);

  // Connect matching aux ports
  for (let i = 1; i < minPorts; i++) {
    link(node.ports[i], other.ports[i]);
  }

  // Erase excess aux ports on the node with more ports
  const larger = node.ports.length > other.ports.length ? node : other;
  for (let i = minPorts; i < larger.ports.length; i++) {
    const newEraser: Node = { type: "era", label: "era", ports: [] };
    graph.push(newEraser);
    link({ node: newEraser, port: 0 }, larger.ports[i]);
  }

  // Remove the nodes
  removeFromArrayIf(graph, (n) => n === node || n === other);
}

export function reduceErase(node: Node, graph: Graph) {
  const eraser = node.ports[0].node;

  // Sanity checks
  if (eraser.ports[0].node !== node) {
    throw new Error("nodes are not interacting!");
  }
  if (eraser.type !== "era") {
    throw new Error("node is not an eraser!");
  }

  // Create and connect erasers to the auxiliary ports
  for (let i = 1; i < node.ports.length; i++) {
    const newEraser: Node = { type: "era", ports: [] };
    graph.push(newEraser);
    link({ node: newEraser, port: 0 }, node.ports[i]);
  }

  // Erase the node and original eraser
  removeFromArrayIf(graph, (n) => (n === node) || (n === eraser));
}

export function reduceCommute(node: Node, graph: Graph) {
  const other = node.ports[0].node;

  // Sanity checks
  if (other.ports[0].node !== node) {
    throw new Error("nodes are not interacting!");
  }

  // Create a copy of `other` once for each of the auxiliary ports of `node`
  const otherClones: Node[] = [];
  for (let i = 1; i < node.ports.length; i++) {
    const clone: Node = {
      ...other,
      levelDeltas: other.levelDeltas ? [...other.levelDeltas] : undefined,
      ports: [],
    };
    graph.unshift(clone);
    otherClones.push(clone);
    // Connect the clone's principal port with the external port
    link({ node: clone, port: 0 }, node.ports[i]);
  }

  // Create a copy of `node` once for each of the auxiliary ports of `other`
  const nodeClones: Node[] = [];
  for (let i = 1; i < other.ports.length; i++) {
    const clone: Node = {
      ...node,
      levelDeltas: node.levelDeltas ? [...node.levelDeltas] : undefined,
      ports: [],
    };
    graph.unshift(clone);
    nodeClones.push(clone);
    // Connect the clone's principal port with the external port
    link({ node: clone, port: 0 }, other.ports[i]);
  }

  // Connect the auxiliary ports of the clones of `node` to the auxiliary ports of the clones of `other`
  for (let i = 0; i < nodeClones.length; i++) {
    for (let j = 0; j < otherClones.length; j++) {
      link(
        { node: nodeClones[i], port: j + 1 },
        { node: otherClones[j], port: i + 1 },
      );
    }
  }

  // Remove the original nodes
  removeFromArrayIf(graph, (n) => n === node || n === other);

  // Return the new nodes in case the caller wants to do something with them
  return { nodeClones, otherClones };
}
