// Readback: convert a delta-net graph back into a lambda calculus AST.
//
// Traverses from the root node following data-flow direction, reconstructing
// abs/app/var AST nodes. Handles replicators (variable sharing), erasers,
// and free variables.

import { Ports } from "../../types.ts";
import type { Graph, Node, NodePort } from "../../types.ts";
import type { Abstraction, Application, AstNode, Variable } from "../../ast.ts";
import { fancyNameToName } from "../../util.ts";

// Strip λ/Λ prefix from a node label and convert fancy unicode to plain ASCII.
function extractName(label: string | undefined, prefix: string): string {
  const raw = label?.replace(prefix, "") ?? "_";
  return fancyNameToName(raw);
}

// ─── Generic readback traversal ────────────────────────────────────
// Parameterized by visitor callbacks so the same traversal logic can
// produce either an AST tree or a formatted string.

interface ReadbackVisitor<T> {
  variable(name: string): T;
  abstraction(prefix: string, name: string, body: T): T;
  application(func: T, arg: T, typeLevel: boolean): T;
  cycle(): T;
}

function readbackWith<T>(graph: Graph, v: ReadbackVisitor<T>): T | null {
  const rootNode = graph.find((n) => n.type === "root");
  if (!rootNode) return null;

  const visited = new Set<Node>();

  function rb(nodePort: NodePort): T {
    const { node, port } = nodePort;

    // --- Base cases (no recursion, safe before visited check) ---

    if (node.type === "abs" && port === Ports.abs.bind) {
      return v.variable(extractName(node.label, "λ"));
    }

    if (node.type === "rep-in" && port >= 1) {
      return v.variable(resolveRepName(node));
    }

    if (node.type === "rep-out" && port >= 1) {
      return rb(node.ports[0]);
    }

    if (node.type === "era") return v.variable("*");
    if (node.type === "var") return v.variable(fancyNameToName(node.label ?? "_"));

    // --- Recursive cases (need visited check) ---

    if (visited.has(node)) return v.cycle();
    visited.add(node);

    if (node.type === "abs" && port === Ports.abs.principal) {
      return v.abstraction("λ", extractName(node.label, "λ"), rb(node.ports[Ports.abs.body]));
    }

    if (node.type === "app" && port === Ports.app.result) {
      return v.application(rb(node.ports[Ports.app.func]), rb(node.ports[Ports.app.arg]), false);
    }

    if ((node.type === "rep-in" || node.type === "rep-out") && port === 0) {
      return node.ports.length > 1 ? rb(node.ports[1]) : v.variable(node.label ?? "_");
    }

    if (node.type === "root") return rb(node.ports[0]);
    if (node.type.startsWith("type-")) return v.variable(node.label ?? "?");

    // Lambda cube agents
    if (node.type === "tyabs" && port === Ports.tyabs.principal) {
      return v.abstraction("Λ", extractName(node.label, "Λ"), rb(node.ports[Ports.tyabs.body]));
    }
    if (node.type === "tyapp" && port === Ports.tyapp.result) {
      return v.application(rb(node.ports[Ports.tyapp.principal]), rb(node.ports[Ports.tyapp.arg]), true);
    }

    return v.variable(node.label ?? "?");
  }

  // Resolve a variable name by following rep-in's principal to its binding site
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

// ─── AST readback ──────────────────────────────────────────────────

const astVisitor: ReadbackVisitor<AstNode> = {
  variable: (name) => ({ type: "var", name }) as Variable,
  abstraction: (_, name, body) => ({ type: "abs", name, body }) as Abstraction,
  application: (func, arg) => ({ type: "app", func, arg }) as Application,
  cycle: () => ({ type: "var", name: "…" }) as Variable,
};

export function readbackGraph(graph: Graph): AstNode | null {
  return readbackWith(graph, astVisitor);
}

// ─── String readback ───────────────────────────────────────────────

const stringVisitor: ReadbackVisitor<string> = {
  variable: (name) => name,
  abstraction: (prefix, name, body) => prefix + name + "." + body,
  application: (func, arg, typeLevel) => {
    const fStr = func.startsWith("λ") || func.startsWith("Λ") || func.includes(" ")
      ? "(" + func + ")" : func;
    if (typeLevel) return fStr + " [" + arg + "]";
    const aStr = arg.includes(" ") ? "(" + arg + ")" : arg;
    return fStr + " " + aStr;
  },
  cycle: () => "…",
};

export function readbackGraphToString(graph: Graph): string {
  return readbackWith(graph, stringVisitor) ?? "(empty)";
}
