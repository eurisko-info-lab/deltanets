import { removeFromArrayIf } from "../util.ts";
import { Graph, Node, NodePort, link, parseRepLabel, formatRepLabel } from "./graph.ts";

// Annihilates two interacting nodes
export function reduceAnnihilate(node: Node, graph: Graph) {
  const other = node.ports[0].node;

  // Sanity checks
  if (other.ports[0].node !== node) {
    throw new Error("nodes are not interacting!");
  }
  if (node.ports.length !== other.ports.length) {
    throw new Error("nodes have different number of ports!");
  }

  // Connect the aux ports (if any)
  if (node.ports.length > 1) {
    for (let i = 1; i < node.ports.length; i++) {
      link(node.ports[i], other.ports[i]);
    }
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
    const newEraser: any = { type: "era", ports: [] };
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
    const clone: any = {
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
    const clone: any = {
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

// Reduces a fan and the node connected to its first auxiliary port (parent port).
export function reduceAuxFan(node: Node, graph: Graph, relativeLevel: boolean) {
  const firstAuxNode = node.ports[1].node;

  if (firstAuxNode.type === "era") {
    // Create a new eraser and link it to the node connected to the principal port
    const newEraser0: any = { type: "era", ports: [] };
    graph.push(newEraser0);
    link({ node: newEraser0, port: 0 }, node.ports[0]);

    // Create a new eraser and link it to the node connected to the second auxiliary port
    const newEraser1: any = { type: "era", ports: [] };
    graph.push(newEraser1);
    link({ node: newEraser1, port: 0 }, node.ports[2]);

    // Remove the fan node
    removeFromArrayIf(graph, (n) => (n === node) || (n === firstAuxNode));
  } else if (firstAuxNode.type.startsWith("rep")) {

    const origPorts = [...node.ports];
    link({ node, port: 0 }, origPorts[1]);
    link({ node, port: 1 }, origPorts[2]);
    link({ node, port: 2 }, origPorts[0]);

    const { nodeClones, otherClones } = reduceCommute(node, graph);

    if (relativeLevel) {
      const repLevel = parseRepLabel(otherClones[1].label!).level;
      otherClones[0].label = formatRepLabel(repLevel + 1, "unknown");
    }

    // Modify all clones of the application node back to the original port configuration
    nodeClones.forEach((nodeClone) => {
      const origPorts = [...nodeClone.ports];
      link({ node: nodeClone, port: 0 }, origPorts[2]);
      link({ node: nodeClone, port: 1 }, origPorts[0]);
      link({ node: nodeClone, port: 2 }, origPorts[1]);
    });
  }
}
