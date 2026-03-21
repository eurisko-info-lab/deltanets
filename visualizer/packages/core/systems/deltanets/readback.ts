// Readback: convert a delta-net graph back into a lambda calculus AST.
//
// Traverses from the root node following data-flow direction, reconstructing
// abs/app/var AST nodes. Handles replicators (variable sharing), erasers,
// and free variables.

import { Ports } from "../../types.ts";
import type { Graph, Node, NodePort } from "../../types.ts";
import type { AstNode, Abstraction, Application, Variable } from "../../ast.ts";
import { fancyNameToName } from "../../util.ts";

// Strip λ/Λ prefix from a node label and convert fancy unicode to plain ASCII.
function extractName(label: string | undefined, prefix: string): string {
  const raw = label?.replace(prefix, "") ?? "_";
  return fancyNameToName(raw);
}

// Readback a graph into an AST. Returns null if the graph has no root.
export function readbackGraph(graph: Graph): AstNode | null {
  const rootNode = graph.find((n) => n.type === "root");
  if (!rootNode) return null;

  const visited = new Set<Node>();

  function readback(nodePort: NodePort): AstNode {
    const { node, port } = nodePort;

    // --- Base cases (no recursion, safe before visited check) ---

    // Variable reference via bind port (linear case: body wired directly to bind)
    if (node.type === "abs" && port === Ports.abs.bind) {
      return { type: "var", name: extractName(node.label, "λ") } as Variable;
    }

    // Replicator fan-in at auxiliary port (≥1): variable reference
    if (node.type === "rep-in" && port >= 1) {
      return resolveRepVariable(node);
    }

    // Replicator fan-out at auxiliary port: follow to principal
    if (node.type === "rep-out" && port >= 1) {
      return readback(node.ports[0]);
    }

    // Eraser: represents an erased subterm
    if (node.type === "era") {
      return { type: "var", name: "*" } as Variable;
    }

    // Free variable
    if (node.type === "var") {
      return { type: "var", name: fancyNameToName(node.label ?? "_") } as Variable;
    }

    // --- Recursive cases (need visited check) ---

    if (visited.has(node)) {
      return { type: "var", name: "…" } as Variable;
    }
    visited.add(node);

    // Lambda abstraction: entered at principal port (0)
    if (node.type === "abs" && port === Ports.abs.principal) {
      const name = extractName(node.label, "λ");
      const body = readback(node.ports[Ports.abs.body]);
      return { type: "abs", name, body } as Abstraction;
    }

    // Application: entered at result port (1)
    if (node.type === "app" && port === Ports.app.result) {
      const func = readback(node.ports[Ports.app.func]);
      const arg = readback(node.ports[Ports.app.arg]);
      return { type: "app", func, arg } as Application;
    }

    // Replicator fan-in at principal (0): entered from binding side
    if (node.type === "rep-in" && port === 0) {
      if (node.ports.length > 1) {
        return readback(node.ports[1]);
      }
      return { type: "var", name: node.label ?? "_" } as Variable;
    }

    // Replicator fan-out at principal (0): sharing point, follow first aux
    if (node.type === "rep-out" && port === 0) {
      if (node.ports.length > 1) {
        return readback(node.ports[1]);
      }
      return { type: "var", name: node.label ?? "_" } as Variable;
    }

    // Root node: follow through
    if (node.type === "root") {
      return readback(node.ports[0]);
    }

    // Type nodes: skip (they're not part of the term)
    if (node.type.startsWith("type-")) {
      return { type: "var", name: node.label ?? "?" } as Variable;
    }

    // Lambda cube agents
    if (node.type === "tyabs" && port === Ports.tyabs.principal) {
      const body = readback(node.ports[Ports.tyabs.body]);
      return { type: "abs", name: extractName(node.label, "Λ"), body } as Abstraction;
    }
    if (node.type === "tyapp" && port === Ports.tyapp.result) {
      const func = readback(node.ports[Ports.tyapp.principal]);
      const arg = readback(node.ports[Ports.tyapp.arg]);
      return { type: "app", func, arg } as Application;
    }

    // Fallback: unknown node type
    return { type: "var", name: node.label ?? "?" } as Variable;
  }

  // Resolve a variable name by following rep-in's principal to its binding site
  function resolveRepVariable(rep: Node): Variable {
    const bindTarget = rep.ports[0];
    if (bindTarget.node.type === "abs" && bindTarget.port === Ports.abs.bind) {
      return { type: "var", name: extractName(bindTarget.node.label, "λ") };
    }
    if (bindTarget.node.type === "var") {
      return { type: "var", name: fancyNameToName(bindTarget.node.label ?? "_") };
    }
    // Replicator chain: follow through
    if (bindTarget.node.type === "rep-in" || bindTarget.node.type === "rep-out") {
      let current = bindTarget;
      const seen = new Set<Node>();
      while (
        (current.node.type === "rep-in" || current.node.type === "rep-out") &&
        !seen.has(current.node)
      ) {
        seen.add(current.node);
        current = current.node.ports[0];
      }
      if (current.node.type === "abs" && current.port === Ports.abs.bind) {
        return { type: "var", name: extractName(current.node.label, "λ") };
      }
      if (current.node.type === "var") {
        return { type: "var", name: fancyNameToName(current.node.label ?? "_") };
      }
    }
    return { type: "var", name: rep.label ?? "?" };
  }

  return readback(rootNode.ports[0]);
}

// Readback a graph directly to a string representation.
// More robust than readbackGraph + astToString for partially-reduced graphs.
export function readbackGraphToString(graph: Graph): string {
  const rootNode = graph.find((n) => n.type === "root");
  if (!rootNode) return "(empty)";

  const visited = new Set<Node>();

  function rb(nodePort: NodePort): string {
    const { node, port } = nodePort;

    // --- Base cases (no recursion, safe before visited check) ---

    if (node.type === "abs" && port === Ports.abs.bind) {
      return extractName(node.label, "λ");
    }

    if (node.type === "rep-in" && port >= 1) {
      return resolveRepName(node);
    }

    if (node.type === "rep-out" && port >= 1) {
      return rb(node.ports[0]);
    }

    if (node.type === "era") return "*";

    if (node.type === "var") return fancyNameToName(node.label ?? "_");

    // --- Recursive cases (need visited check) ---

    if (visited.has(node)) return "…";
    visited.add(node);

    if (node.type === "abs" && port === Ports.abs.principal) {
      const name = extractName(node.label, "λ");
      const body = rb(node.ports[Ports.abs.body]);
      return "λ" + name + "." + body;
    }

    if (node.type === "app" && port === Ports.app.result) {
      const func = rb(node.ports[Ports.app.func]);
      const arg = rb(node.ports[Ports.app.arg]);
      const fStr = func.startsWith("λ") || func.includes(" ") ? "(" + func + ")" : func;
      const aStr = arg.includes(" ") ? "(" + arg + ")" : arg;
      return fStr + " " + aStr;
    }

    if (node.type === "rep-in" && port === 0) {
      return node.ports.length > 1 ? rb(node.ports[1]) : (node.label ?? "_");
    }

    if (node.type === "rep-out" && port === 0) {
      return node.ports.length > 1 ? rb(node.ports[1]) : (node.label ?? "_");
    }

    if (node.type === "root") return rb(node.ports[0]);

    if (node.type.startsWith("type-")) return node.label ?? "?";

    if (node.type === "tyabs" && port === Ports.tyabs.principal) {
      const name = extractName(node.label, "Λ");
      return "Λ" + name + "." + rb(node.ports[Ports.tyabs.body]);
    }

    if (node.type === "tyapp" && port === Ports.tyapp.result) {
      const func = rb(node.ports[Ports.tyapp.principal]);
      const arg = rb(node.ports[Ports.tyapp.arg]);
      return func + " [" + arg + "]";
    }

    return node.label ?? "?";
  }

  function resolveRepName(rep: Node): string {
    const bindTarget = rep.ports[0];
    if (bindTarget.node.type === "abs" && bindTarget.port === Ports.abs.bind) {
      return extractName(bindTarget.node.label, "λ");
    }
    if (bindTarget.node.type === "var") {
      return fancyNameToName(bindTarget.node.label ?? "_");
    }
    if (bindTarget.node.type === "rep-in" || bindTarget.node.type === "rep-out") {
      let current = bindTarget;
      const seen = new Set<Node>();
      while (
        (current.node.type === "rep-in" || current.node.type === "rep-out") &&
        !seen.has(current.node)
      ) {
        seen.add(current.node);
        current = current.node.ports[0];
      }
      if (current.node.type === "abs" && current.port === Ports.abs.bind) {
        return extractName(current.node.label, "λ");
      }
      if (current.node.type === "var") {
        return fancyNameToName(current.node.label ?? "_");
      }
    }
    return rep.label ?? "?";
  }

  return rb(rootNode.ports[0]);
}
