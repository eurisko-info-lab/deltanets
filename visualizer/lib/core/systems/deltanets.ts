// Δ-Nets interaction net system implementation.
// This module contains all delta-nets specific logic: node types, reductions,
// graph building, redex detection, and analysis.

import { removeFromArrayIf } from "../../util.ts";
import type { AstNode, SystemType } from "../../ast.ts";
import type { Graph, Node, NodePort, Redex, InteractionSystem } from "../types.ts";
import { link, reciprocal } from "../graph.ts";
import { reduceAnnihilate, reduceErase, reduceCommute } from "../reductions.ts";

// --- Delta-nets specific types ---

export type NodeType =
  | "abs"     // Abstraction (2 auxiliary ports)
  | "app"     // Application (2 auxiliary ports)
  | "rep-in"  // Replicator Fan-In (any number of auxiliary ports)
  | "rep-out" // Replicator Fan-Out (any number of auxiliary ports)
  | "era"     // Eraser (0 auxiliary ports)
  | "var"     // Variable (0 auxiliary ports)
  | "root";   // Root (0 auxiliary ports)

export type RepStatus = "unpaired" | "unknown";

export type DeltaData = { appliedFinalStep: boolean; isFinalStep: boolean };

// --- Delta-nets specific helpers ---

function parseRepLabel(label: string): { level: number; status: RepStatus } {
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
  return { level, status };
}

function formatRepLabel(level: number, status: RepStatus): string {
  if (status === "unknown") {
    return level + "*";
  } else {
    return level.toString();
  }
}

function isParentPort(nodePort: NodePort): boolean {
  return (nodePort.node.type === "rep-out" && nodePort.port === 0) ||
    (nodePort.node.type === "rep-in" && nodePort.port !== 0) ||
    (nodePort.node.type === "abs" && nodePort.port === 0) ||
    (nodePort.node.type === "app" && nodePort.port === 1) ||
    (nodePort.node.type === "era" && nodePort.port === 0) ||
    (nodePort.node.type === "var" && nodePort.port === 0);
}

function isConnectedToAllErasers(node: Node): boolean {
  return node.ports.every((p, i) => i > 0 ? p.node.type === "era" : true);
}

function isConnectedToSomeErasers(node: Node): boolean {
  return node.ports.some((p, i) => i > 0 ? p.node.type === "era" : false);
}

function countAuxErasers(node: Node): number {
  return node.ports.reduce((count, p, i) => {
    if (i > 0 && p.node.type === "era") {
      count++;
    }
    return count;
  }, 0);
}

// --- Delta-nets specific reduction ---

function reduceAuxFan(node: Node, graph: Graph, relativeLevel: boolean) {
  const firstAuxNode = node.ports[1].node;

  if (firstAuxNode.type === "era") {
    const newEraser0: any = { type: "era", ports: [] };
    graph.push(newEraser0);
    link({ node: newEraser0, port: 0 }, node.ports[0]);

    const newEraser1: any = { type: "era", ports: [] };
    graph.push(newEraser1);
    link({ node: newEraser1, port: 0 }, node.ports[2]);

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

    nodeClones.forEach((nodeClone) => {
      const origPorts = [...nodeClone.ports];
      link({ node: nodeClone, port: 0 }, origPorts[2]);
      link({ node: nodeClone, port: 1 }, origPorts[0]);
      link({ node: nodeClone, port: 2 }, origPorts[1]);
    });
  }
}

// --- Graph building ---

function addAstNodeToGraph(
  astNode: AstNode,
  graph: Graph,
  vars: Map<string, { level: number; nodePort: NodePort; firstUsageLevel?: number }>,
  level: number,
  relativeLevel: boolean,
): NodePort {
  if (astNode.type === "abs") {
    const eraser: Node = { type: "era", label: "era", ports: [] };
    graph.push(eraser);
    const node: Node = { type: "abs", label: "λ" + astNode.name, ports: [] };
    graph.push(node);
    link({ node: eraser, port: 0 }, { node, port: 2 });

    const orig = vars.get(astNode.name);
    vars.set(astNode.name, { level, nodePort: { node, port: 2 } });

    const bodyPort = addAstNodeToGraph(astNode.body, graph, vars, level, relativeLevel);
    link(bodyPort, { node, port: 1 });

    if (orig) {
      vars.set(astNode.name, orig);
    } else {
      vars.delete(astNode.name);
    }

    return { node, port: 0 };
  } else if (astNode.type === "app") {
    const node: Node = { type: "app", label: "@", ports: [] };
    graph.push(node);

    const funcPort = addAstNodeToGraph(astNode.func, graph, vars, level, relativeLevel);
    link(funcPort, { node, port: 0 });

    const argPort = addAstNodeToGraph(astNode.arg, graph, vars, level + 1, relativeLevel);
    link(argPort, { node, port: 2 });

    return { node, port: 1 };
  } else if (astNode.type === "var") {
    if (vars.has(astNode.name)) {
      const varData = vars.get(astNode.name)!;
      let sourceNodePort = varData.nodePort;
      const destNodePort = reciprocal(varData.nodePort);
      if (destNodePort.node.type === "era") {
        removeFromArrayIf(graph, (node) => node === destNodePort.node);
        const node: Node = {
          type: "rep-in",
          label: relativeLevel ? "0" : (varData.level + 1).toString(),
          ports: [],
          levelDeltas: [level - (varData.level + 1)],
        };
        graph.push(node);
        link({ ...sourceNodePort }, { node, port: 0 });
        sourceNodePort = { node, port: 1 };
      } else {
        const rep = destNodePort.node;
        rep.levelDeltas = [...rep.levelDeltas!, level - varData.level - 1];
        sourceNodePort = { node: rep, port: rep.ports.length };
      }

      return sourceNodePort;
    } else {
      const node: Node = { type: "var", label: astNode.name, ports: [] };
      graph.push(node);
      let portToReturn = { node, port: 0 };

      const rep: Node = {
        type: "rep-in",
        label: "0",
        ports: [],
        levelDeltas: [level - 1],
      };
      graph.push(rep);
      link({ ...portToReturn }, { node: rep, port: 0 });
      portToReturn = { node: rep, port: 1 };

      vars.set(astNode.name, { level: 0, nodePort: { node, port: 0 } });

      return portToReturn;
    }
  } else {
    throw new Error("Unknown node type: " + (astNode as any).type);
  }
}

function buildGraph(ast: AstNode, systemType: SystemType, relativeLevel: boolean): Graph {
  const graph: Graph = [];

  const rootPort = addAstNodeToGraph(ast, graph, new Map(), 0, relativeLevel);

  const rootNode: Node = { type: "root", label: "root", ports: [rootPort] };
  graph.push(rootNode);
  link(rootPort, { node: rootNode, port: 0 });

  let removeAllReps: boolean = systemType === "linear" || systemType === "affine";
  graph.forEach((node) => {
    if (node.type.startsWith("rep") && node.ports.length !== 2) {
      removeAllReps = false;
    }
  });

  const nodesToRemove: Node[] = [];
  graph.forEach((node) => {
    if (node.type.startsWith("rep") &&
      (removeAllReps === true ||
        (node.ports.length === 2 && node.levelDeltas![0] === 0))
    ) {
      link(node.ports[0], node.ports[1]);
      nodesToRemove.push(node);
    }
  });
  for (const node of nodesToRemove) {
    removeFromArrayIf(graph, (n) => n === node);
  }

  return graph;
}

// --- Redex detection ---

function getRedex(a: Node, b: Node, redexes: Redex[]): Redex | undefined {
  for (const redex of redexes) {
    if ((redex.a === a && redex.b === b) || (redex.a === b && redex.b === a)) {
      return redex;
    }
  }
  return undefined;
}

function getRedexes(graph: Graph, systemType: SystemType, relativeLevel: boolean): Redex[] {
  const redexes: Redex[] = [];

  graph.forEach((node) => {
    (node as any).traversed = undefined;
    (node as any).traversed2 = undefined;
  });

  const createRedex = (a: Node, b: Node, optimal: boolean, reduce: () => void) => {
    if (redexes.some((redex) => {
      if ((redex.a === a && redex.b === b) || (redex.a === b && redex.b === a)) {
        if (redex.optimal !== optimal) {
          console.error("Error: mismatching optimality for redex", redex, a, b, optimal, reduce);
        }
        return true;
      }
      return false;
    })) {
      return;
    }
    redexes.push({ a, b, optimal, reduce: () => {
      if (graph.find((n) => n === a) === undefined || graph.find((n) => n === b) === undefined) {
        return;
      }
      reduce();
    }});
  }

  // Linear system
  if (systemType === "linear") {
    for (const node of graph) {
      if (node.ports[0].port === 0) {
        if (node.type === "era") {
          console.error("Error: eraser in linear system", node);
        }
        if (node.type.startsWith("rep")) {
          console.error("Error: rep in linear system", node);
        }
        if (node.type === "var" || node.ports[0].node.type === "var" || node.type === "root" || node.ports[0].node.type === "root") {
          continue
        }
        if (node.type === "abs" && node.ports[0].node.type !== "app" || node.type === "app" && node.ports[0].node.type !== "abs") {
          console.error("Error: non app-abs annihilation pair in linear system", node, node.ports[0].node);
        }
        createRedex(node, node.ports[0].node, true, () => reduceAnnihilate(node, graph));
      }
    }
  }

  // Affine/Relevant/Full systems
  else {
    for (const node of graph) {
      if (systemType === "relevant" && node.type === "era") {
        console.error("Error: eraser in relevant system", node);
      }
      if (node.ports[0].port === 0) {
        if (node.type === "var" || node.ports[0].node.type === "var" || node.type === "root" || node.ports[0].node.type === "root") {
          continue
        }
        if (node.type === "era") {
          createRedex(node, node.ports[0].node, false, () => reduceErase(node.ports[0].node, graph));
        } else if (node.ports[0].node.type === "era") {
          createRedex(node, node.ports[0].node, false, () => reduceErase(node, graph));
        } else if (
          node.type === "abs" && node.ports[0].node.type === "app"
        ) {
          createRedex(node, node.ports[0].node, false, () => reduceAnnihilate(node, graph));
        } else if (
          ((node.type.startsWith("rep") && (node.ports[0].node.type === "abs" ||
            node.ports[0].node.type === "app")))
        ) {
          const rep = node.type.startsWith("rep") ? node : node.ports[0].node;
          const level = parseRepLabel(rep.label!).level;
          createRedex(node, node.ports[0].node, false, () => {
            const { nodeClones } = reduceCommute(rep, graph);
            nodeClones[0].label = formatRepLabel(level, "unknown");
            nodeClones[1].label = formatRepLabel(relativeLevel ? level + 1 :level, "unknown");
            nodeClones[1].type = nodeClones[1].type === "rep-in" ? "rep-out" : "rep-in";
          });
        } else if (
          node.type.startsWith("rep") && node.ports[0].node.type.startsWith("rep")
        ) {
          const a = node;
          const b = node.ports[0].node;
          const { level: top, status: topFlag } = parseRepLabel(a.label!);
          const { level: bottom, status: bottomFlag } = parseRepLabel(b.label!);
          if (top === bottom) {
            createRedex(a, b, false, () => reduceAnnihilate(b, graph));
          } else {
            createRedex(a, b, false, () => {
              const { nodeClones, otherClones } = reduceCommute(b, graph);
              if (top > bottom) {
                otherClones.forEach((node, i) => {
                  node.label = formatRepLabel(top + b.levelDeltas![i], topFlag);
                });
              } else {
                nodeClones.forEach((node, i) => {
                  node.label = formatRepLabel(bottom + a.levelDeltas![i], bottomFlag);
                });
              }
            });
          }
        }
      } else if (
        node.type.startsWith("rep") &&
        node.ports[0].node.type.startsWith("rep") &&
        parseRepLabel(node.ports[0].node.label!).status === "unpaired"
      ) {
        const firstReplicator = node.ports[0].node;
        const secondReplicator = node;
        const secondReplicatorPort = secondReplicator.ports[0].port;

        let secondUnpaired =
          parseRepLabel(secondReplicator.label!).status === "unpaired";
        const levelDeltaBetween =
          firstReplicator.levelDeltas![secondReplicatorPort - 1];
        if (!secondUnpaired) {
          const { level: firstLevel } = parseRepLabel(firstReplicator.label!);
          const { level: secondLevel } = parseRepLabel(secondReplicator.label!);
          const diff = secondLevel - firstLevel;
          if (0 <= diff && diff <= levelDeltaBetween) {
            secondUnpaired = true;
          }
        }

        if (secondUnpaired) {
          (firstReplicator as any).isToBeMerged = true;
          createRedex(firstReplicator, secondReplicator, false, () => {
            (firstReplicator as any).isToBeMerged = false;

            firstReplicator.ports.splice(secondReplicatorPort, 1, ...secondReplicator.ports.slice(1));
            firstReplicator.levelDeltas!.splice(secondReplicatorPort - 1, 1, ...secondReplicator.levelDeltas!.map((ld) => ld + levelDeltaBetween));

            const portsWithLevelDeltas: { nodePort: NodePort; levelDelta: number }[] = firstReplicator.ports.slice(1).map((nodePort, i) => {
              return { nodePort, levelDelta: firstReplicator.levelDeltas![i] };
            });

            portsWithLevelDeltas.sort(({ levelDelta: levelDeltaA }, { levelDelta: levelDeltaB }) => {
              return levelDeltaA - levelDeltaB;
            });

            const auxPorts: NodePort[] = [];
            const levelDeltas: number[] = [];
            portsWithLevelDeltas.forEach(({ nodePort, levelDelta }) => {
              auxPorts.push(nodePort);
              levelDeltas.push(levelDelta);
            });

            firstReplicator.ports = [firstReplicator.ports[0], ...auxPorts];
            firstReplicator.levelDeltas = [...levelDeltas];

            firstReplicator.ports.forEach((p, i) => link(p, { node: firstReplicator, port: i }));

            removeFromArrayIf(graph, (n) => n === secondReplicator);
          });
        }
      } else if (
        node.type.startsWith("rep") &&
        node.ports[0].node.type === "app" && node.ports[0].port === 1
      ) {
        createRedex(node, node.ports[0].node, false, () => reduceAuxFan(node.ports[0].node, graph, relativeLevel));
      }
    }

    // Traverse net and mark the leftmost-outermost redex as optimal
    const rootNode = graph.find((node) => node.type === "root")!;
    let firstAuxFanReplication: Redex | undefined = undefined;
    const traverse = (nodePort: NodePort) => {
      const node = nodePort.node;
      const port = nodePort.port;

      if (nodePort.port === 0 && nodePort.node.ports[0].node.ports[0].node === nodePort.node) {
        const redex = getRedex(nodePort.node, nodePort.node.ports[0].node, redexes);
        if (redex) {
          redex.optimal = true;
          return true;
        }
      }

      if (node.type.startsWith("rep") && node.ports[0].node.type.startsWith("rep")) {
        const redex = getRedex(node, node.ports[0].node, redexes);
        if (redex) {
          redex.optimal = true;
          return true;
        }
      }

      if (firstAuxFanReplication === undefined && node.type.startsWith("rep") && node.ports[0].node.type === "app" && node.ports[0].port === 1) {
        firstAuxFanReplication = getRedex(node, node.ports[0].node, redexes);
      }

      if ((node as any).traversed) {
        return false;
      }
      (node as any).traversed = true;
      if (node.type === "abs" && port === 0) {
        if (node.ports[2].node.type === "era") {
          if (traverse(node.ports[2])) {
            return true;
          }
        }
        if (traverse(node.ports[1])) {
          return true;
        }
      } else if (node.type === "app" && port === 1) {
        if (traverse(node.ports[0])) {
          return true;
        }
        if (traverse(node.ports[2])) {
          return true;
        }
      } else if (node.type === "rep-in" && port !== 0) {
        return traverse(node.ports[0]);
      } else if (node.type === "rep-out" && port === 0) {
        for (let i = 1; i < node.ports.length; i++) {
          if (traverse(node.ports[i])) {
            return true;
          }
        }
      } else if (node.type === "era") {
        // nothing to do
      }
      return false;
    }
    const res = traverse(rootNode.ports[0]);
    if (res === false && firstAuxFanReplication !== undefined) {
      (firstAuxFanReplication as Redex).optimal = true;
    };

    redexes.sort((a, b) => a.optimal ? -1 : b.optimal ? 1 : 0);

    // Mark certain redexes in the spine as optimal as well
    const traverse2 = (nodePort: NodePort) => {
      const node = nodePort.node;
      const port = nodePort.port;
      const other = nodePort.node.ports[0].node;

      if (port === 0 && other.ports[0].node === node && (!node.type.startsWith("rep") || parseRepLabel(node.label!).status === "unknown") && (!other.type.startsWith("rep") || parseRepLabel(other.label!).status === "unknown")) {
        const redex = getRedex(nodePort.node, other, redexes);
        if (redex) {
          redex.optimal = true;
        }
      }

      if ((node as any).traversed2) {
        return;
      }
      (node as any).traversed2 = true;
      if (node.type === "abs" && port === 0) {
        if (node.ports[2].node.type === "era") {
          traverse2(node.ports[2]);
        }
        traverse2(node.ports[1]);
      } else if (node.type === "app" && port === 1) {
        traverse2(node.ports[0]);
        return;
      } else if (node.type === "rep-in" && port !== 0) {
        traverse2(node.ports[0]);
      } else if (node.type === "rep-out" && port === 0) {
        return;
      } else if (node.type === "era") {
        // nothing to do
      }
      return;
    }
    traverse2(rootNode.ports[0]);
  }

  return redexes;
}

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
    if (node.type === "abs" && port === 0) {
      if (node.ports[2].node.type === "era") {
        traverse(node.ports[2]);
      }
      traverse(node.ports[1]);
    } else if (node.type === "app" && port === 1) {
      traverse(node.ports[0]);
      traverse(node.ports[2]);
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
      (p as any).erase = true;
    })
    removeFromArrayIf(node.levelDeltas!, (ld, i) => (node.ports[i+1] as any).erase === true)
    removeFromArrayIf(node.ports, (p) => (p as any).erase === true)
    node.ports.forEach((p, i) => {
      link(p, { node, port: i })
    })
  })

  const nodesToRemove: Node[] = [];
  graph.forEach((node) => {
    if (node.type.startsWith("rep") &&
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
  return undefined
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
};
