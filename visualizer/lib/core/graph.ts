// Universal graph utilities for interaction nets.

import type { NodePort } from "./types.ts";

// Get the reciprocal of a node port (the port on the other end of the wire).
export function reciprocal(nodePort: NodePort) {
  return nodePort.node.ports[nodePort.port];
}

// Link two node ports together bidirectionally.
export function link(nodePortA: NodePort, nodePortB: NodePort) {
  nodePortA.node.ports[nodePortA.port] = nodePortB;
  nodePortB.node.ports[nodePortB.port] = nodePortA;
}
