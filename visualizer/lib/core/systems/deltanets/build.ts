// Graph building from AST nodes.

import { removeFromArrayIf } from "../../../util.ts";
import type { AstNode, SystemType, Type } from "../../../ast.ts";
import { Ports } from "../../types.ts";
import type { Graph, Node, NodePort } from "../../types.ts";
import { link, reciprocal } from "../../graph.ts";

function buildTypeGraph(ty: Type, graph: Graph): NodePort {
  if (ty.kind === "hole") {
    const node: Node = { type: "type-hole", label: "?", ports: [] };
    graph.push(node);
    return { node, port: Ports.typeHole.principal };
  } else if (ty.kind === "base") {
    const node: Node = { type: "type-base", label: ty.name, ports: [] };
    graph.push(node);
    return { node, port: Ports.typeBase.principal };
  } else if (ty.kind === "arrow") {
    const node: Node = { type: "type-arrow", label: "→", ports: [] };
    graph.push(node);
    const domainPort = buildTypeGraph(ty.from, graph);
    link(domainPort, { node, port: Ports.typeArrow.domain });
    const codomainPort = buildTypeGraph(ty.to, graph);
    link(codomainPort, { node, port: Ports.typeArrow.codomain });
    return { node, port: Ports.typeArrow.principal };
  } else {
    throw new Error("Unknown type kind: " + (ty as any).kind);
  }
}

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
    const node: Node = { type: "abs", label: "λ" + astNode.name, ports: [], astRef: astNode };
    graph.push(node);
    link({ node: eraser, port: Ports.era.principal }, { node, port: Ports.abs.bind });

    // Build type subgraph and connect to abs type port
    const typeAnnotation: Type = astNode.typeAnnotation || { kind: "hole" };
    const typePort = buildTypeGraph(typeAnnotation, graph);
    link(typePort, { node, port: Ports.abs.type });

    const orig = vars.get(astNode.name);
    vars.set(astNode.name, { level, nodePort: { node, port: Ports.abs.bind } });

    const bodyPort = addAstNodeToGraph(astNode.body, graph, vars, level, relativeLevel);
    link(bodyPort, { node, port: Ports.abs.body });

    if (orig) {
      vars.set(astNode.name, orig);
    } else {
      vars.delete(astNode.name);
    }

    return { node, port: Ports.abs.principal };
  } else if (astNode.type === "app") {
    const node: Node = { type: "app", label: "@", ports: [], astRef: astNode };
    graph.push(node);

    const funcPort = addAstNodeToGraph(astNode.func, graph, vars, level, relativeLevel);
    link(funcPort, { node, port: Ports.app.func });

    const argPort = addAstNodeToGraph(astNode.arg, graph, vars, level + 1, relativeLevel);
    link(argPort, { node, port: Ports.app.arg });

    return { node, port: Ports.app.result };
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
      const node: Node = { type: "var", label: astNode.name, ports: [], astRef: astNode };
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

export function buildGraph(ast: AstNode, systemType: SystemType, relativeLevel: boolean): Graph {
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
