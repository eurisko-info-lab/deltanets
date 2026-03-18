// A graph is a list of nodes.
export type Graph = Node[];

// A port of a particular node.
export type NodePort = { node: Node; port: number };

// The node type determines the number of auxiliary ports.
export type NodeType =
  | "abs" // Abstraction (2 auxiliary ports)
  | "app" // Application (2 auxiliary ports)
  | "rep-in" // Replicator Fan-In (any number of auxiliary ports)
  | "rep-out" // Replicator Fan-Out (any number of auxiliary ports)
  | "era" // Eraser (0 auxiliary ports)
  | "var" // Variable (0 auxiliary ports; technically not an interaction net agent, just a label for a wire)
  | "root"; // Root (0 auxiliary ports; technically not an interaction net agent, just a special label for a wire)

// A node in the computational graph.
// Each element in `ports` is a NodePort (of any node, potentially even this same node) that is connected to this node, at port X, where X is the element index.
// The first NodePort in `ports` (with index 0) is the NodePort connected to this node's principal port.
// Indexes >=1 represent this node's auxiliary ports from left to right, assuming the principal port is facing down and auxiliary ports are facing up.
// Another way to think about this: indexes represent a node's ports ordered clockwise, starting from the principal port.
export type Node = {
  type: NodeType;
  ports: NodePort[];
  label?: string;
  isCreated?: boolean; // Used during rendering to track which nodes have been visualized
  levelDeltas?: number[]; // If `type` is "rep-in" or "rep-out", then this specifies the level delta of each aux port
};

// The status of a replicator
export type RepStatus = "unpaired" | "unknown";

// Helper function to get the reciprocal of a node port
export function reciprocal(nodePort: NodePort) {
  return nodePort.node.ports[nodePort.port];
}

// Helper function to link two node ports
export function link(
  nodePortA: NodePort,
  nodePortB: NodePort,
) {
  nodePortA.node.ports[nodePortA.port] = nodePortB;
  nodePortB.node.ports[nodePortB.port] = nodePortA;
}

// Parses a replicator label into a level and a flag
export function parseRepLabel(label: string): { level: number; status: RepStatus } {
  let level: number;
  let status: RepStatus;
  const marker = label[label.length - 1];
  if (marker === "*") {
    level = parseInt(label.slice(0, -1));
    status = "unknown";
  } else {
    level = parseInt(label);
    status = "unpaired";
  }
  return { level, status: status };
}

// Formats a replicator label, given a level and a flag
export function formatRepLabel(level: number, status: RepStatus): string {
  if (status === "unknown") {
    return level + "*";
  } /* unpaired */ else {
    return level.toString();
  }
}

// Returns true if the node port is a parent port
export function isParentPort(nodePort: NodePort): boolean {
  return (nodePort.node.type === "rep-out" && nodePort.port === 0) ||
    (nodePort.node.type === "rep-in" && nodePort.port !== 0) ||
    (nodePort.node.type === "abs" && nodePort.port === 0) ||
    (nodePort.node.type === "app" && nodePort.port === 1) ||
    (nodePort.node.type === "era" && nodePort.port === 0) ||
    (nodePort.node.type === "var" && nodePort.port === 0);
}

// Returns true if the node is connected to erasers on all its aux ports
export const isConnectedToAllErasers = (node: Node) => {
  return node.ports.every((p, i) => i > 0 ? p.node.type === "era" : true);
};

// Returns true if the node is connected to erasers on some of its aux ports
export const isConnectedToSomeErasers = (node: Node) => {
  return node.ports.some((p, i) => i > 0 ? p.node.type === "era" : false);
};

// Counts erasers connected to aux ports
export const countAuxErasers = (node: Node) => {
  return node.ports.reduce((count, p, i) => {
    if (i > 0 && p.node.type === "era") {
      count++;
    }
    return count;
  }, 0);
}
