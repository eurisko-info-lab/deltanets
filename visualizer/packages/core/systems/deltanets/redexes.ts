// Redex detection and traversal for δ-nets.
//
// A "redex" (reducible expression) is a pair of nodes interacting via their
// principal ports. This module scans the graph for all such pairs, classifies
// each by reduction rule (annihilate, erase, commute, or system-specific),
// marks the "optimal" (leftmost-outermost) redex, and provides the reduce()
// closure for each.

import { removeFromArrayIf } from "../../util.ts";
import type { SystemType } from "../../ast.ts";
import { Ports } from "../../types.ts";
import type { Graph, Node, NodePort, Redex } from "../../types.ts";
import { link, reciprocal } from "../../graph.ts";
import {
  reduceAnnihilate,
  reduceCommute,
  reduceErase,
} from "../../reductions.ts";
import {
  ANNIHILATION_PAIRS,
  ERASE_RULE_PAIRS,
  formatRepLabel,
  isExprAgent,
  isParentPort,
  isTypeNode,
  parseRepLabel,
  reduceAuxFan,
  reduceEraseRule,
} from "./helpers.ts";
import type { AgentPortDefs, InteractionRule } from "../../types.ts";
import { reduceCustomRule } from "./custom-rules.ts";

export function getRedex(
  a: Node,
  b: Node,
  redexes: Redex[],
): Redex | undefined {
  for (const redex of redexes) {
    if ((redex.a === a && redex.b === b) || (redex.a === b && redex.b === a)) {
      return redex;
    }
  }
  return undefined;
}

/** Look up a rule by the two interacting agent types. */
function findRule(
  typeA: string,
  typeB: string,
  rules: InteractionRule[],
): InteractionRule | undefined {
  return rules.find(
    (r) =>
      (r.agentA === typeA && r.agentB === typeB) ||
      (r.agentA === typeB && r.agentB === typeA),
  );
}

export function getRedexes(
  graph: Graph,
  systemType: SystemType,
  relativeLevel: boolean,
  rules?: InteractionRule[],
  agentPorts?: AgentPortDefs,
): Redex[] {
  const redexes: Redex[] = [];

  graph.forEach((node) => {
    node.traversed = undefined;
    node.traversed2 = undefined;
  });

  const createRedex = (
    a: Node,
    b: Node,
    optimal: boolean,
    reduce: () => void,
  ) => {
    if (
      redexes.some((redex) => {
        if (
          (redex.a === a && redex.b === b) || (redex.a === b && redex.b === a)
        ) {
          if (redex.optimal !== optimal) {
            console.error(
              "Error: mismatching optimality for redex",
              redex,
              a,
              b,
              optimal,
              reduce,
            );
          }
          return true;
        }
        return false;
      })
    ) {
      return;
    }
    redexes.push({
      a,
      b,
      optimal,
      reduce: () => {
        if (
          graph.find((n) => n === a) === undefined ||
          graph.find((n) => n === b) === undefined
        ) {
          return;
        }
        reduce();
      },
    });
  };

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
        if (
          node.type === "var" || node.ports[0].node.type === "var" ||
          node.type === "root" || node.ports[0].node.type === "root" ||
          isTypeNode(node) || isTypeNode(node.ports[0].node)
        ) {
          continue;
        }
        if (
          node.type === "abs" && node.ports[0].node.type !== "app" ||
          node.type === "app" && node.ports[0].node.type !== "abs"
        ) {
          console.error(
            "Error: non app-abs annihilation pair in linear system",
            node,
            node.ports[0].node,
          );
        }
        createRedex(
          node,
          node.ports[0].node,
          true,
          () => reduceAnnihilate(node, graph),
        );
      }
    }
  } // Affine/Relevant/Full systems
  else {
    for (const node of graph) {
      if (systemType === "relevant" && node.type === "era") {
        console.error("Error: eraser in relevant system", node);
      }
      if (node.ports[0].port === 0) {
        const other = node.ports[0].node;
        if (
          node.type === "var" || other.type === "var" ||
          node.type === "root" || other.type === "root" ||
          isTypeNode(node) || isTypeNode(other)
        ) {
          continue;
        }

        const matchesPair = (pairs: [string, string][]) =>
          pairs.some(([a, b]) =>
            (node.type === a && other.type === b) ||
            (node.type === b && other.type === a)
          );

        if (node.type === "era") {
          createRedex(node, other, false, () => reduceErase(other, graph));
        } else if (other.type === "era") {
          createRedex(node, other, false, () => reduceErase(node, graph));
        } else if (
          (node.type === "abs" && other.type === "app") ||
          matchesPair(ANNIHILATION_PAIRS)
        ) {
          createRedex(node, other, false, () => reduceAnnihilate(node, graph));
        } else if (matchesPair(ERASE_RULE_PAIRS)) {
          createRedex(node, other, false, () => reduceEraseRule(node, other, graph));
        } else if (rules !== undefined && findRule(node.type, other.type, rules) !== undefined) {
          // Dynamic rule lookup from .inet system definitions
          const rule = findRule(node.type, other.type, rules)!;
          if (rule.action.kind === "builtin") {
            if (rule.action.name === "annihilate") {
              createRedex(node, other, false, () => reduceAnnihilate(node, graph));
            } else if (rule.action.name === "erase") {
              createRedex(node, other, false, () => reduceEraseRule(node, other, graph));
            } else if (rule.action.name === "commute") {
              createRedex(node, other, false, () => reduceCommute(node, graph));
            }
          } else if (rule.action.kind === "custom" && agentPorts) {
            const left = node.type === rule.agentA ? node : other;
            const right = left === node ? other : node;
            createRedex(node, other, false, () => {
              reduceCustomRule(left, right, graph, rule, agentPorts);
            });
          }
        } else if (
          node.type.startsWith("rep") &&
          !other.type.startsWith("rep") &&
          !isExprAgent(other.type) &&
          !isTypeNode(other) &&
          other.type !== "var" &&
          other.type !== "root"
        ) {
          // Rep commutation with lambda cube agents
          const rep = node;
          const level = parseRepLabel(rep.label!).level;
          createRedex(node, other, false, () => {
            const { nodeClones } = reduceCommute(rep, graph);
            nodeClones.forEach((clone, i) => {
              clone.label = formatRepLabel(
                i === 0 ? level : (relativeLevel ? level + 1 : level),
                "unknown",
              );
              if (i > 0) {
                clone.type = clone.type === "rep-in" ? "rep-out" : "rep-in";
              }
            });
          });
        } else if (
          (node.type.startsWith("rep") && (other.type === "abs" ||
            other.type === "app"))
        ) {
          const rep = node.type.startsWith("rep") ? node : other;
          const level = parseRepLabel(rep.label!).level;
          createRedex(node, other, false, () => {
            const { nodeClones } = reduceCommute(rep, graph);
            nodeClones[0].label = formatRepLabel(level, "unknown");
            nodeClones[1].label = formatRepLabel(
              relativeLevel ? level + 1 : level,
              "unknown",
            );
            nodeClones[1].type = nodeClones[1].type === "rep-in"
              ? "rep-out"
              : "rep-in";
            // Handle type port replicator for abs nodes (3 aux ports)
            if (nodeClones.length > 2) {
              nodeClones[2].label = formatRepLabel(level, "unknown");
            }
          });
        } else if (
          node.type.startsWith("rep") &&
          other.type.startsWith("rep")
        ) {
          const a = node;
          const b = other;
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
        node.ports[0].node?.type.startsWith("rep") &&
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
          firstReplicator.isToBeMerged = true;
          createRedex(firstReplicator, secondReplicator, false, () => {
            firstReplicator.isToBeMerged = false;

            firstReplicator.ports.splice(
              secondReplicatorPort,
              1,
              ...secondReplicator.ports.slice(1),
            );
            firstReplicator.levelDeltas!.splice(
              secondReplicatorPort - 1,
              1,
              ...secondReplicator.levelDeltas!.map((ld) =>
                ld + levelDeltaBetween
              ),
            );

            const portsWithLevelDeltas: {
              nodePort: NodePort;
              levelDelta: number;
            }[] = firstReplicator.ports.slice(1).map((nodePort, i) => {
              return { nodePort, levelDelta: firstReplicator.levelDeltas![i] };
            });

            portsWithLevelDeltas.sort(
              ({ levelDelta: levelDeltaA }, { levelDelta: levelDeltaB }) => {
                return levelDeltaA - levelDeltaB;
              },
            );

            const auxPorts: NodePort[] = [];
            const levelDeltas: number[] = [];
            portsWithLevelDeltas.forEach(({ nodePort, levelDelta }) => {
              auxPorts.push(nodePort);
              levelDeltas.push(levelDelta);
            });

            firstReplicator.ports = [firstReplicator.ports[0], ...auxPorts];
            firstReplicator.levelDeltas = [...levelDeltas];

            firstReplicator.ports.forEach((p, i) =>
              link(p, { node: firstReplicator, port: i })
            );

            removeFromArrayIf(graph, (n) => n === secondReplicator);
          });
        }
      } else if (
        node.type.startsWith("rep") &&
        node.ports[0].node.type === "app" &&
        node.ports[0].port === Ports.app.result
      ) {
        createRedex(
          node,
          node.ports[0].node,
          false,
          () => reduceAuxFan(node.ports[0].node, graph, relativeLevel),
        );
      }
    }

    // Traverse net and mark the leftmost-outermost redex as optimal
    const rootNode = graph.find((node) => node.type === "root")!;
    let firstAuxFanReplication: Redex | undefined = undefined;
    const traverse = (nodePort: NodePort) => {
      const node = nodePort.node;
      const port = nodePort.port;

      if (
        nodePort.port === 0 &&
        nodePort.node.ports[0].node.ports[0].node === nodePort.node
      ) {
        const redex = getRedex(
          nodePort.node,
          nodePort.node.ports[0].node,
          redexes,
        );
        if (redex) {
          redex.optimal = true;
          return true;
        }
      }

      if (
        node.type.startsWith("rep") && node.ports[0].node.type.startsWith("rep")
      ) {
        const redex = getRedex(node, node.ports[0].node, redexes);
        if (redex) {
          redex.optimal = true;
          return true;
        }
      }

      if (
        firstAuxFanReplication === undefined && node.type.startsWith("rep") &&
        node.ports[0].node.type === "app" &&
        node.ports[0].port === Ports.app.result
      ) {
        firstAuxFanReplication = getRedex(node, node.ports[0].node, redexes);
      }

      if (node.traversed) {
        return false;
      }
      node.traversed = true;
      if (node.type === "abs" && port === Ports.abs.principal) {
        if (node.ports[Ports.abs.bind].node.type === "era") {
          if (traverse(node.ports[Ports.abs.bind])) {
            return true;
          }
        }
        if (traverse(node.ports[Ports.abs.body])) {
          return true;
        }
      } else if (node.type === "app" && port === Ports.app.result) {
        if (traverse(node.ports[Ports.app.func])) {
          return true;
        }
        if (traverse(node.ports[Ports.app.arg])) {
          return true;
        }
      } else if (isTypeNode(node)) {
        // Type subgraphs don't contain redexes
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
      } else if (!isExprAgent(node.type) && !node.type.startsWith("rep")) {
        // Generic/custom agent: check principal port for redex,
        // traverse all auxiliary ports.
        if (port !== 0) {
          // Arrived at aux port: check if principal forms a redex
          const other = node.ports[0].node;
          if (node.ports[0].port === 0 && other.ports[0].node === node) {
            const redex = getRedex(node, other, redexes);
            if (redex) {
              redex.optimal = true;
              return true;
            }
          } else {
            // Principal is not in a redex — continue traversal through it
            if (traverse(node.ports[0])) return true;
          }
        }
        // Traverse other auxiliary ports
        for (let i = 1; i < node.ports.length; i++) {
          if (i === port) continue;
          if (traverse(node.ports[i])) return true;
        }
      }
      return false;
    };
    const res = traverse(rootNode.ports[0]);
    if (res === false && firstAuxFanReplication !== undefined) {
      (firstAuxFanReplication as Redex).optimal = true;
    }

    redexes.sort((a, b) => a.optimal ? -1 : b.optimal ? 1 : 0);

    // Mark certain redexes in the spine as optimal as well
    const traverse2 = (nodePort: NodePort) => {
      const node = nodePort.node;
      const port = nodePort.port;
      const other = nodePort.node.ports[0].node;

      if (
        port === 0 && other.ports[0].node === node &&
        (!node.type.startsWith("rep") ||
          parseRepLabel(node.label!).status === "unknown") &&
        (!other.type.startsWith("rep") ||
          parseRepLabel(other.label!).status === "unknown")
      ) {
        const redex = getRedex(nodePort.node, other, redexes);
        if (redex) {
          redex.optimal = true;
        }
      }

      if (node.traversed2) {
        return;
      }
      node.traversed2 = true;
      if (node.type === "abs" && port === Ports.abs.principal) {
        if (node.ports[Ports.abs.bind].node.type === "era") {
          traverse2(node.ports[Ports.abs.bind]);
        }
        traverse2(node.ports[Ports.abs.body]);
      } else if (node.type === "app" && port === Ports.app.result) {
        traverse2(node.ports[Ports.app.func]);
        return;
      } else if (node.type === "rep-in" && port !== 0) {
        traverse2(node.ports[0]);
      } else if (node.type === "rep-out" && port === 0) {
        return;
      } else if (node.type === "era") {
        // nothing to do
      } else if (!isExprAgent(node.type) && !node.type.startsWith("rep")) {
        // Generic/custom agent: check principal port, traverse aux ports.
        if (port !== 0) {
          const o = node.ports[0].node;
          if (node.ports[0].port === 0 && o.ports[0].node === node) {
            const redex = getRedex(node, o, redexes);
            if (redex) {
              redex.optimal = true;
            }
          } else {
            // Principal is not in a redex — continue traversal through it
            traverse2(node.ports[0]);
          }
        }
        for (let i = 1; i < node.ports.length; i++) {
          if (i === port) continue;
          traverse2(node.ports[i]);
        }
      }
      return;
    };
    traverse2(rootNode.ports[0]);
  }

  return redexes;
}
