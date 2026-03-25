// Redex detection and traversal for δ-nets.
//
// A "redex" (reducible expression) is a pair of nodes interacting via their
// principal ports. This module scans the graph for all such pairs, classifies
// each by reduction rule (annihilate, erase, commute, or system-specific),
// marks the "optimal" (leftmost-outermost) redex, and provides the reduce()
// closure for each.

import { asMut, removeFromArrayIf } from "../../util.ts";
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
  DEFAULT_RULES,
  formatRepLabel,
  isExprAgent,
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

/** Parameterized net traversal for marking optimal redexes. */
function walkNet(
  start: NodePort,
  redexes: Redex[],
  config: {
    preVisit: (nodePort: NodePort) => boolean | undefined;
    stopOnOptimal: boolean;
    traverseAppArg: boolean;
    traverseRepOutAux: boolean;
    traversedKey: "traversed" | "traversed2";
  },
): boolean {
  const walk = (nodePort: NodePort): boolean => {
    const node = nodePort.node;
    const port = nodePort.port;
    const preResult = config.preVisit(nodePort);
    if (preResult !== undefined) return preResult;
    if (node[config.traversedKey]) return false;
    node[config.traversedKey] = true;
    if (node.type === "abs" && port === Ports.abs.principal) {
      if (node.ports[Ports.abs.bind].node.type === "era") {
        if (walk(node.ports[Ports.abs.bind])) return true;
      }
      return walk(node.ports[Ports.abs.body]);
    }
    if (node.type === "app" && port === Ports.app.result) {
      if (walk(node.ports[Ports.app.func])) return true;
      return config.traverseAppArg ? walk(node.ports[Ports.app.arg]) : false;
    }
    if (isTypeNode(node)) return false;
    if (node.type === "rep-in" && port !== 0) return walk(node.ports[0]);
    if (node.type === "rep-out" && port === 0) {
      if (!config.traverseRepOutAux) return false;
      for (let i = 1; i < node.ports.length; i++) {
        if (walk(node.ports[i])) return true;
      }
      return false;
    }
    if (node.type === "era") return false;
    if (!isExprAgent(node.type) && !node.type.startsWith("rep")) {
      if (port !== 0) {
        const other = node.ports[0].node;
        if (node.ports[0].port === 0 && other.ports[0].node === node) {
          const redex = getRedex(node, other, redexes);
          if (redex) {
            redex.optimal = true;
            if (config.stopOnOptimal) return true;
          }
        } else {
          if (walk(node.ports[0])) return true;
        }
      }
      for (let i = 1; i < node.ports.length; i++) {
        if (i === port) continue;
        if (walk(node.ports[i])) return true;
      }
    }
    return false;
  };
  return walk(start);
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
          () => reduceAnnihilate(node, asMut(graph)),
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

        const activeRules = rules ?? DEFAULT_RULES;

        if (node.type === "era") {
          createRedex(node, other, false, () => reduceErase(other, asMut(graph)));
        } else if (other.type === "era") {
          createRedex(node, other, false, () => reduceErase(node, asMut(graph)));
        } else if (node.type === "abs" && other.type === "app") {
          createRedex(node, other, false, () => reduceAnnihilate(node, asMut(graph)));
        } else {
          const rule = findRule(node.type, other.type, activeRules);
          if (rule !== undefined) {
            if (rule.action.kind === "builtin") {
              if (rule.action.name === "annihilate") {
                createRedex(node, other, false, () => reduceAnnihilate(node, asMut(graph)));
              } else if (rule.action.name === "erase") {
                createRedex(node, other, false, () => reduceEraseRule(node, other, asMut(graph)));
              } else if (rule.action.name === "commute") {
                createRedex(node, other, false, () => reduceCommute(node, asMut(graph)));
              }
            } else if (rule.action.kind === "custom" && agentPorts) {
              const left = node.type === rule.agentA ? node : other;
              const right = left === node ? other : node;
              createRedex(node, other, false, () => {
                reduceCustomRule(left, right, asMut(graph), rule, agentPorts);
              });
            } else if (rule.action.kind === "meta") {
              const handler = rule.action.handler;
              const left = node.type === rule.agentA ? node : other;
              const right = left === node ? other : node;
              createRedex(node, other, false, () => {
                handler(left, right, graph, agentPorts ?? new Map());
              });
            }
          } else if (
            node.type.startsWith("rep") &&
            !other.type.startsWith("rep")
          ) {
            // Rep commutation with expression agents (abs, app, custom)
            const level = parseRepLabel(node.label!).level;
            createRedex(node, other, false, () => {
              const { nodeClones } = reduceCommute(node, asMut(graph));
              nodeClones.forEach((clone, i) => {
                if (i === 0) {
                  clone.label = formatRepLabel(level, "unknown");
                } else if (other.type === "abs" && i >= 2) {
                  // Abs type-port clone: base level, no type flip
                  clone.label = formatRepLabel(level, "unknown");
                } else {
                  clone.label = formatRepLabel(
                    relativeLevel ? level + 1 : level, "unknown",
                  );
                  clone.type = clone.type === "rep-in" ? "rep-out" : "rep-in";
                }
              });
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
              createRedex(a, b, false, () => reduceAnnihilate(b, asMut(graph)));
            } else {
              createRedex(a, b, false, () => {
                const { nodeClones, otherClones } = reduceCommute(b, asMut(graph));
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
          () => reduceAuxFan(node.ports[0].node, asMut(graph), relativeLevel),
        );
      }
    }

    // Traverse net and mark the leftmost-outermost redex as optimal
    const rootNode = graph.find((node) => node.type === "root")!;
    let firstAuxFanReplication: Redex | undefined = undefined;
    const res = walkNet(rootNode.ports[0], redexes, {
      traversedKey: "traversed",
      stopOnOptimal: true,
      traverseAppArg: true,
      traverseRepOutAux: true,
      preVisit: (np) => {
        const node = np.node;
        if (
          np.port === 0 &&
          node.ports[0].node.ports[0].node === node
        ) {
          const redex = getRedex(node, node.ports[0].node, redexes);
          if (redex) { redex.optimal = true; return true; }
        }
        if (
          node.type.startsWith("rep") &&
          node.ports[0].node.type.startsWith("rep")
        ) {
          const redex = getRedex(node, node.ports[0].node, redexes);
          if (redex) { redex.optimal = true; return true; }
        }
        if (
          firstAuxFanReplication === undefined &&
          node.type.startsWith("rep") &&
          node.ports[0].node.type === "app" &&
          node.ports[0].port === Ports.app.result
        ) {
          firstAuxFanReplication = getRedex(node, node.ports[0].node, redexes);
        }
        return undefined;
      },
    });
    if (res === false && firstAuxFanReplication !== undefined) {
      (firstAuxFanReplication as Redex).optimal = true;
    }

    redexes.sort((a, b) => a.optimal ? -1 : b.optimal ? 1 : 0);

    // Mark certain redexes in the spine as optimal as well
    walkNet(rootNode.ports[0], redexes, {
      traversedKey: "traversed2",
      stopOnOptimal: false,
      traverseAppArg: false,
      traverseRepOutAux: false,
      preVisit: (np) => {
        const node = np.node;
        const other = node.ports[0].node;
        if (
          np.port === 0 && other.ports[0].node === node &&
          (!node.type.startsWith("rep") ||
            parseRepLabel(node.label!).status === "unknown") &&
          (!other.type.startsWith("rep") ||
            parseRepLabel(other.label!).status === "unknown")
        ) {
          const redex = getRedex(node, other, redexes);
          if (redex) { redex.optimal = true; }
        }
        return undefined;
      },
    });
  }

  return redexes;
}
