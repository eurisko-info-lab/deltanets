// Tests for delta-nets helpers: parseRepLabel, formatRepLabel, isParentPort,
// isTypeNode, isExprAgent, countAuxErasers, isConnectedToAllErasers,
// reduceEraseRule, tagAstWithTypeCheckIndices.

import { assertEquals } from "$std/assert/mod.ts";
import type { Node, NodePort } from "./types.ts";
import { link } from "./graph.ts";
import {
  countAuxErasers,
  formatRepLabel,
  isConnectedToAllErasers,
  isExprAgent,
  isParentPort,
  isTypeNode,
  parseRepLabel,
  reduceEraseRule,
} from "./systems/deltanets/helpers.ts";
import { tagAstWithTypeCheckIndices } from "./typechecker.ts";
import type { AstNode } from "./ast.ts";

// ─── parseRepLabel ─────────────────────────────────────────────────

Deno.test("parseRepLabel: unpaired integer", () => {
  assertEquals(parseRepLabel("3"), { level: 3, status: "unpaired" });
});

Deno.test("parseRepLabel: unknown (star suffix)", () => {
  assertEquals(parseRepLabel("5*"), { level: 5, status: "unknown" });
});

Deno.test("parseRepLabel: zero level", () => {
  assertEquals(parseRepLabel("0"), { level: 0, status: "unpaired" });
  assertEquals(parseRepLabel("0*"), { level: 0, status: "unknown" });
});

// ─── formatRepLabel ────────────────────────────────────────────────

Deno.test("formatRepLabel: unknown appends star", () => {
  assertEquals(formatRepLabel(3, "unknown"), "3*");
});

Deno.test("formatRepLabel: unpaired is plain number", () => {
  assertEquals(formatRepLabel(7, "unpaired"), "7");
});

Deno.test("formatRepLabel: roundtrips with parseRepLabel", () => {
  for (const status of ["unknown", "unpaired"] as const) {
    for (const level of [0, 1, 5, 42]) {
      assertEquals(parseRepLabel(formatRepLabel(level, status)), { level, status });
    }
  }
});

// ─── isParentPort ──────────────────────────────────────────────────

function makeNodePort(type: string, port: number, nPorts: number): NodePort {
  const node: Node = { type, ports: Array.from({ length: nPorts }, () => ({ node: null!, port: 0 })) };
  return { node, port };
}

Deno.test("isParentPort: abs entry is port 0", () => {
  assertEquals(isParentPort(makeNodePort("abs", 0, 4)), true);
  assertEquals(isParentPort(makeNodePort("abs", 1, 4)), false);
});

Deno.test("isParentPort: app entry is port 1", () => {
  assertEquals(isParentPort(makeNodePort("app", 1, 3)), true);
  assertEquals(isParentPort(makeNodePort("app", 0, 3)), false);
});

Deno.test("isParentPort: rep-out entry is port 0", () => {
  assertEquals(isParentPort(makeNodePort("rep-out", 0, 3)), true);
  assertEquals(isParentPort(makeNodePort("rep-out", 1, 3)), false);
});

Deno.test("isParentPort: rep-in entry is non-zero port", () => {
  assertEquals(isParentPort(makeNodePort("rep-in", 0, 3)), false);
  assertEquals(isParentPort(makeNodePort("rep-in", 1, 3)), true);
  assertEquals(isParentPort(makeNodePort("rep-in", 2, 3)), true);
});

Deno.test("isParentPort: leaf (1-port) entry is port 0", () => {
  assertEquals(isParentPort(makeNodePort("var", 0, 1)), true);
  assertEquals(isParentPort(makeNodePort("era", 0, 1)), true);
});

Deno.test("isParentPort: destructor (fst/snd) entry is port 1", () => {
  assertEquals(isParentPort(makeNodePort("fst", 1, 2)), true);
  assertEquals(isParentPort(makeNodePort("fst", 0, 2)), false);
  assertEquals(isParentPort(makeNodePort("snd", 1, 2)), true);
});

// ─── isTypeNode ────────────────────────────────────────────────────

Deno.test("isTypeNode: type nodes", () => {
  assertEquals(isTypeNode({ type: "type-base", ports: [] }), true);
  assertEquals(isTypeNode({ type: "type-arrow", ports: [] }), true);
  assertEquals(isTypeNode({ type: "type-hole", ports: [] }), true);
});

Deno.test("isTypeNode: non-type nodes", () => {
  assertEquals(isTypeNode({ type: "abs", ports: [] }), false);
  assertEquals(isTypeNode({ type: "app", ports: [] }), false);
  assertEquals(isTypeNode({ type: "rep-in", ports: [] }), false);
});

// ─── isExprAgent ───────────────────────────────────────────────────

Deno.test("isExprAgent: expression agents", () => {
  for (const type of ["abs", "app", "var", "era", "root"]) {
    assertEquals(isExprAgent(type), true, type);
  }
});

Deno.test("isExprAgent: replicators are expr agents", () => {
  assertEquals(isExprAgent("rep-in"), true);
  assertEquals(isExprAgent("rep-out"), true);
});

Deno.test("isExprAgent: type/custom agents are not", () => {
  assertEquals(isExprAgent("type-base"), false);
  assertEquals(isExprAgent("type-arrow"), false);
  assertEquals(isExprAgent("tyabs"), false);
  assertEquals(isExprAgent("custom"), false);
});

// ─── countAuxErasers / isConnectedToAllErasers ─────────────────────

function makeNodeWithAuxTypes(principalType: string, auxTypes: string[]): Node {
  const node: Node = { type: principalType, ports: [] };
  // Port 0 = principal (self-loop as placeholder)
  node.ports.push({ node, port: 0 });
  for (const auxType of auxTypes) {
    const auxNode: Node = { type: auxType, ports: [] };
    node.ports.push({ node: auxNode, port: 0 });
  }
  return node;
}

Deno.test("countAuxErasers: all erasers", () => {
  const node = makeNodeWithAuxTypes("abs", ["era", "era", "era"]);
  assertEquals(countAuxErasers(node), 3);
});

Deno.test("countAuxErasers: no erasers", () => {
  const node = makeNodeWithAuxTypes("abs", ["var", "app"]);
  assertEquals(countAuxErasers(node), 0);
});

Deno.test("countAuxErasers: mixed", () => {
  const node = makeNodeWithAuxTypes("abs", ["era", "var", "era"]);
  assertEquals(countAuxErasers(node), 2);
});

Deno.test("isConnectedToAllErasers: true when all aux are erasers", () => {
  const node = makeNodeWithAuxTypes("abs", ["era", "era"]);
  assertEquals(isConnectedToAllErasers(node), true);
});

Deno.test("isConnectedToAllErasers: false when some are not", () => {
  const node = makeNodeWithAuxTypes("abs", ["era", "var"]);
  assertEquals(isConnectedToAllErasers(node), false);
});

Deno.test("isConnectedToAllErasers: true for leaf nodes (no aux ports)", () => {
  const node = makeNodeWithAuxTypes("var", []);
  assertEquals(isConnectedToAllErasers(node), true);
});

// ─── reduceEraseRule ───────────────────────────────────────────────

Deno.test("reduceEraseRule: both nodes replaced by erasers", () => {
  // Create two 3-port nodes linked at principal ports
  const a: Node = { type: "custom-a", ports: [] };
  const b: Node = { type: "custom-b", ports: [] };
  const aAux1: Node = { type: "var", ports: [] };
  const aAux2: Node = { type: "var", ports: [] };
  const bAux1: Node = { type: "var", ports: [] };

  // Set up ports: port 0 = principal, ports 1+ = auxiliary
  a.ports = [{ node: b, port: 0 }, { node: aAux1, port: 0 }, { node: aAux2, port: 0 }];
  b.ports = [{ node: a, port: 0 }, { node: bAux1, port: 0 }];
  aAux1.ports = [{ node: a, port: 1 }];
  aAux2.ports = [{ node: a, port: 2 }];
  bAux1.ports = [{ node: b, port: 1 }];

  const graph = [a, b, aAux1, aAux2, bAux1];
  reduceEraseRule(a, b, graph);

  // Both original nodes should be removed
  assertEquals(graph.includes(a), false);
  assertEquals(graph.includes(b), false);

  // New erasers should be linked to the old aux ports' neighbors
  const erasers = graph.filter((n) => n.type === "era");
  assertEquals(erasers.length, 3, "3 erasers: 2 for a's aux, 1 for b's aux");
});

// ─── tagAstWithTypeCheckIndices ────────────────────────────────────

Deno.test("tagAstWithTypeCheckIndices: post-order indexing", () => {
  // Build: (λx.x) y — app(abs(var:x), var:y)
  const varX: AstNode = { type: "var", name: "x" };
  const abs: AstNode = { type: "abs", name: "x", body: varX };
  const varY: AstNode = { type: "var", name: "y" };
  const app: AstNode = { type: "app", func: abs, arg: varY };

  tagAstWithTypeCheckIndices(app);

  // Post-order: varX(0), abs(1), varY(2), app(3)
  assertEquals(varX.extra?.typeCheckIdx, 0);
  assertEquals(abs.extra?.typeCheckIdx, 1);
  assertEquals(varY.extra?.typeCheckIdx, 2);
  assertEquals(app.extra?.typeCheckIdx, 3);
});

Deno.test("tagAstWithTypeCheckIndices: single variable", () => {
  const v: AstNode = { type: "var", name: "x" };
  tagAstWithTypeCheckIndices(v);
  assertEquals(v.extra?.typeCheckIdx, 0);
});
