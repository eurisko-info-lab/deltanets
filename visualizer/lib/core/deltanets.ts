import { removeFromArrayIf } from "../util.ts";
import { AstNode, SystemType } from "../ast.ts";
import { Graph, Node, NodePort, link, reciprocal, parseRepLabel, formatRepLabel } from "./graph.ts";
import { reduceAnnihilate, reduceErase, reduceCommute, reduceAuxFan } from "./reductions.ts";

// The type of a redex.
export type Redex = { a: Node; b: Node; optimal: boolean; reduce: () => void };

// State data specific to Δ-Nets reduction.
export type DeltaData = { appliedFinalStep: boolean; isFinalStep: boolean };

// Returns the redex that contains the pair of nodes (a, b) if it exists, or undefined otherwise.
export function getRedex(a: Node, b: Node, redexes: Redex[]): Redex | undefined {
  for (const redex of redexes) {
    if ((redex.a === a && redex.b === b) || (redex.a === b && redex.b === a)) {
      return redex;
    }
  }
  return undefined;
}

// Builds an interaction net graph from an AST.
export function buildGraph(ast: AstNode, systemType: SystemType, relativeLevel: boolean): Graph {
  const graph: Graph = [];

  // Build graph
  const rootPort = addAstNodeToGraph(ast, graph, new Map(), 0, relativeLevel);

  // Add root node
  const rootNode: Node = { type: "root", label: "root", ports: [rootPort] };
  graph.push(rootNode);
  link(rootPort, { node: rootNode, port: 0 });

  // If all replicators have exactly one auxiliary port, then remove all replicators below, not just those with zero level delta.
  let removeAllReps: boolean = systemType === "linear" || systemType === "affine";
  graph.forEach((node) => {
    if (node.type.startsWith("rep") && node.ports.length !== 2) {
      removeAllReps = false;
    }
  });

  // Remove replicators with a single aux port that has a zero level delta
  const nodesToRemove: Node[] = [];
  graph.forEach((node) => {
    if (node.type.startsWith("rep") &&
      (removeAllReps === true ||
        (node.ports.length === 2 &&
          node.levelDeltas![0] === 0))
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

// Returns all the redexes (core interactions and canonicalizations) and the current reduction state.
export function getRedexes(graph: Graph, systemType: SystemType, relativeLevel: boolean): Redex[] {
  const redexes: Redex[] = [];

  // Clear internal traversal flags
  graph.forEach((node) => {
    (node as any).traversed = undefined;
    (node as any).traversed2 = undefined;
  });

  const createRedex = (a: Node, b: Node, optimal: boolean, reduce: () => void) => {
    // Skip if the redex has already been created
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
      // Ignore if any of the nodes have been removed
      if (graph.find((n) => n === a) === undefined || graph.find((n) => n === b) === undefined) {
        return;
      }
      reduce();
    }});
  }

  // Linear system
  if (systemType === "linear") {
    // There are only app-abs annihilation pairs and they are always optimal
    for (const node of graph) {
      if (node.ports[0].port === 0) {
        if (node.type === "era") {
          console.error("Error: eraser in linear system", node);
        }
        if (node.type.startsWith("rep")) {
          console.error("Error: rep in linear system", node);
        }
        // Skip pairs with variables or with the root node
        if (node.type === "var" || node.ports[0].node.type === "var" || node.type === "root" || node.ports[0].node.type === "root") {
          continue
        }
        // Check for app-abs annihilation pairs
        if (node.type === "abs" && node.ports[0].node.type !== "app" || node.type === "app" && node.ports[0].node.type !== "abs") {
          console.error("Error: non app-abs annihilation pair in linear system", node, node.ports[0].node);
        }
        createRedex(node, node.ports[0].node, true, () => reduceAnnihilate(node, graph));
      }
    }
  }

  // Affine/Relevant/Full systems
  else /*if (systemType === "affine" || systemType === "relevant" || systemType === "full") */ {
    for (const node of graph) {
      if (systemType === "relevant" && node.type === "era") {
        console.error("Error: eraser in relevant system", node);
      }
      if (node.ports[0].port === 0) {
        // Skip pairs with variables or with the root node
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
          // Fan-Rep commutation
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
          // Rep-Rep commutation
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
                // Need to update the levels of the top replicator copies (otherClones) according to the level deltas of the bottom replicator
                otherClones.forEach((node, i) => {
                  node.label = formatRepLabel(
                    top + b.levelDeltas![i],
                    topFlag,
                  );
                });
              } else {
                // Need to update the levels of the bottom replicator copies (nodeClones) according to the level deltas of the top replicator
                nodeClones.forEach((node, i) => {
                  node.label = formatRepLabel(
                    bottom + a.levelDeltas![i],
                    bottomFlag,
                  );
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

        // Check if the second replicator is unpaired
        let secondUnpaired =
          parseRepLabel(secondReplicator.label!).status === "unpaired";
        // Get the level delta between the two replicators
        const levelDeltaBetween =
          firstReplicator.levelDeltas![secondReplicatorPort - 1];
        // Check for constraint that helps determine whether the second replicator is unpaired
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
          // Merge the two replicators
          createRedex(firstReplicator, secondReplicator, false, () => {
            // Reset isToBeMerged flag
            (firstReplicator as any).isToBeMerged = false;

            firstReplicator.ports.splice(secondReplicatorPort, 1, ...secondReplicator.ports.slice(1));
            firstReplicator.levelDeltas!.splice(secondReplicatorPort - 1, 1, ...secondReplicator.levelDeltas!.map((ld) => ld + levelDeltaBetween));

            // Reorder ports of firstReplicator according to level deltas

            // Zip aux ports with level deltas
            const portsWithLevelDeltas: { nodePort: NodePort; levelDelta: number }[] = firstReplicator.ports.slice(1).map((nodePort, i) => {
              return { nodePort, levelDelta: firstReplicator.levelDeltas![i] };
            });

            // Sort by level delta
            portsWithLevelDeltas.sort(({ levelDelta: levelDeltaA }, { levelDelta: levelDeltaB }) => {
              return levelDeltaA - levelDeltaB;
            });

            // Unzip aux ports and level deltas
            const auxPorts: NodePort[] = [];
            const levelDeltas: number[] = [];
            portsWithLevelDeltas.forEach(({ nodePort, levelDelta }) => {
              auxPorts.push(nodePort);
              levelDeltas.push(levelDelta);
            });

            // // Assign aux ports to firstReplicator
            firstReplicator.ports = [firstReplicator.ports[0], ...auxPorts];
            firstReplicator.levelDeltas = [...levelDeltas];

            // Link external ports
            firstReplicator.ports.forEach((p, i) => link(p, { node: firstReplicator, port: i }));

            // Remove secondReplicator from graph
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
    // Traverse all nodes starting at the root and mark the first redex found as optimal
    let firstAuxFanReplication: Redex | undefined = undefined;
    const traverse = (nodePort: NodePort) => {
      const node = nodePort.node;
      const port = nodePort.port;

      // If nodes form an active pair
      if (nodePort.port === 0 && nodePort.node.ports[0].node.ports[0].node === nodePort.node) {
        const redex = getRedex(nodePort.node, nodePort.node.ports[0].node, redexes);
        if (redex) {
          redex.optimal = true;
          return true;
        }
      }

      // Check for rep merges
      if (node.type.startsWith("rep") && node.ports[0].node.type.startsWith("rep")) {
        const redex = getRedex(node, node.ports[0].node, redexes);
        if (redex) {
          redex.optimal = true;
          return true;
        }
      }

      // Check for aux fan replication
      if (firstAuxFanReplication === undefined && node.type.startsWith("rep") && node.ports[0].node.type === "app" && node.ports[0].port === 1) {
        firstAuxFanReplication = getRedex(node, node.ports[0].node, redexes);
      }

      if ((node as any).traversed) {
        // Avoid infinite loop
        return false;
      }
      (node as any).traversed = true;
      // Only traverse child ports
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

    // Move the optimal redex (if any) to the beginning of the redexes array
    // so that it is reduced when pressing right arrow key
    redexes.sort((a, b) => a.optimal ? -1 : b.optimal ? 1 : 0);

    // Mark certain redexes in the spine as optimal as well
    const traverse2 = (nodePort: NodePort) => {
      const node = nodePort.node;
      const port = nodePort.port;
      const other = nodePort.node.ports[0].node;

      // If annihilation or commutation with only unknown replicators
      if (port === 0 && other.ports[0].node === node && (!node.type.startsWith("rep") || parseRepLabel(node.label!).status === "unknown") && (!other.type.startsWith("rep") || parseRepLabel(other.label!).status === "unknown")) {
        const redex = getRedex(nodePort.node, other, redexes);
        if (redex) {
          redex.optimal = true;
        }
      }

      if ((node as any).traversed2) {
        // Avoid infinite loop
        return;
      }
      (node as any).traversed2 = true;
      // Only traverse child ports
      if (node.type === "abs" && port === 0) {
        if (node.ports[2].node.type === "era") {
          traverse2(node.ports[2]);
        }
        traverse2(node.ports[1]);
      } else if (node.type === "app" && port === 1) {
        traverse2(node.ports[0]);
        // quit traversal since we only consider redexes on the spine
        return;
      } else if (node.type === "rep-in" && port !== 0) {
        traverse2(node.ports[0]);
      } else if (node.type === "rep-out" && port === 0) {
        // quit traversal since we would need to traverse a specific port (so we would need to keep track of prior fan-ins)
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

// Finds all reachable nodes from the root of the graph.
export function findReachableNodes(graph: Graph): Set<Node> {
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
    // Only traverse child ports
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

// Removes unreachable nodes from the graph and cleans up replicators.
export function cleanupGraph(graph: Graph): void {
  const reachable = findReachableNodes(graph);

  // Replace connections to unreachable nodes with erasers
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

  // Remove unreachable nodes
  removeFromArrayIf(graph, (n) => !reachable.has(n));

  // Remove erasers connected to replicator aux ports (all replicators are unpaired at this point)
  graph.forEach((node) => {
    // Skip non replicators
    if (!node.type.startsWith("rep")) {
      return;
    }
    // Loop through replicator ports marking ports to erase
    node.ports.forEach((p, i) => {
      // Only consider aux ports connected to erasers
      if (p.node.type !== "era" || i === 0) {
        return;
      }
      (p as any).erase = true; // Mark port to erase
    })
    // Remove level deltas and ports
    removeFromArrayIf(node.levelDeltas!, (ld, i) => (node.ports[i+1] as any).erase === true)
    removeFromArrayIf(node.ports, (p) => (p as any).erase === true)
    // Relink node ports
    node.ports.forEach((p, i) => {
      link(p, { node, port: i })
    })
  })

  // Remove replicators with a single aux port that has a zero level delta
  const nodesToRemove: Node[] = [];
  graph.forEach((node) => {
    if (node.type.startsWith("rep") &&
        (node.ports.length === 2 &&
          node.levelDeltas![0] === 0)
    ) {
      link(node.ports[0], node.ports[1]);
      nodesToRemove.push(node);
    }
  });
  for (const node of nodesToRemove) {
    removeFromArrayIf(graph, (n) => n === node);
  }
}

// Parses an AST and appends nodes into the specified graph.
function addAstNodeToGraph(
  astNode: AstNode,
  graph: Graph,
  vars: Map<
    string,
    { level: number; nodePort: NodePort; firstUsageLevel?: number }
  > = new Map(),
  level: number = 0,
  relativeLevel: boolean,
): NodePort {
  if (astNode.type === "abs") {
    // Create abstraction node with eraser
    const eraser: Node = { type: "era", label: "era", ports: [] };
    graph.push(eraser);
    const node: Node = { type: "abs", label: "λ" + astNode.name, ports: [] };
    graph.push(node);
    link({ node: eraser, port: 0 }, { node, port: 2 });

    // Add abstraction variable to vars
    const orig = vars.get(astNode.name);
    vars.set(astNode.name, { level, nodePort: { node, port: 2 } });

    // Parse body port
    const bodyPort = addAstNodeToGraph(astNode.body, graph, vars, level, relativeLevel);
    link(bodyPort, { node, port: 1 });

    // Need to restore original vars (if any) instead of deleting
    if (orig) {
      vars.set(astNode.name, orig);
    } else {
      vars.delete(astNode.name);
    }

    return { node, port: 0 };
  } else if (astNode.type === "app") {
    // Create application node
    const node: Node = { type: "app", label: "@", ports: [] };
    graph.push(node);

    // Parse function port
    const funcPort = addAstNodeToGraph(astNode.func, graph, vars, level, relativeLevel);
    link(funcPort, { node, port: 0 });

    // Parse argument port
    const argPort = addAstNodeToGraph(astNode.arg, graph, vars, level + 1, relativeLevel);
    link(argPort, { node, port: 2 });

    // Return parent port
    return { node, port: 1 };
  } else if (astNode.type === "var") {
    if (vars.has(astNode.name)) {
      // Get the node port that leads to the variable
      const varData = vars.get(astNode.name)!;
      let sourceNodePort = varData.nodePort;
      // Get the "destination" NodePort of the variable
      const destNodePort = reciprocal(varData.nodePort);
      // If this is the first time we're using this bound variable it will be connected to an eraser
      if (destNodePort.node.type === "era") {
        // Delete the eraser
        removeFromArrayIf(graph, (node) => node === destNodePort.node);
        // Create a replicator fan-in
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
        // If this is not the first time that we're using this bound variable, then a replicator has already been created and we need to connect to it and update sourceNodePort
        const rep = destNodePort.node;
        rep.levelDeltas = [...rep.levelDeltas!, level - varData.level - 1];
        sourceNodePort = { node: rep, port: rep.ports.length };
      }

      return sourceNodePort;
    } else {
      // Create free variable node
      const node: Node = {
        type: "var",
        label: astNode.name,
        ports: [],
      };
      graph.push(node);
      let portToReturn = { node, port: 0 };

      // Create a replicator fan-in to share the free variable
      const rep: Node = {
        type: "rep-in",
        label: "0",
        ports: [],
        levelDeltas: [level - 1],
      };
      graph.push(rep);
      link({ ...portToReturn }, { node: rep, port: 0 });
      portToReturn = { node: rep, port: 1 };

      // Set variable in vars
      vars.set(astNode.name, { level: 0, nodePort: { node, port: 0 } });

      // Return parent port
      return portToReturn;
    }
  } else {
    throw new Error("Unknown node type: " + (astNode as any).type);
  }
}

// Colors for the levels
const levelColors = [
  "#ff666686",
  "#ffbd5586",
  "#ffff6686",
  "#9de24f86",
  "#87cefa86",
];

// Returns the color for a given level
export const levelColor = (level: number): string | undefined => {
  return undefined
  return levelColors[level % levelColors.length];
};
