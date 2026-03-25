// Tests for the custom rule body interpreter (reduceCustomRule).

import { assertEquals } from "$std/assert/mod.ts";
import { link } from "./graph.ts";
import type { AgentPortDefs, Graph, InteractionRule, Node } from "./types.ts";
import { asMut } from "./util.ts";
import { reduceCustomRule } from "./systems/deltanets/custom-rules.ts";

/** Create a node with self-looped ports. */
function makeNode(type: string, numPorts: number, label?: string): Node {
  const node: Node = { type, ports: [], label: label ?? type };
  for (let i = 0; i < numPorts; i++) {
    node.ports.push({ node, port: i });
  }
  return node;
}

// ─── relink ────────────────────────────────────────────────────────

Deno.test("custom rule: relink reconnects neighbors", () => {
  // Two interacting nodes: add(x, y) >< zero
  // Rule body: relink left.1 to right.1  (pass through result)
  const add = makeNode("add", 3); // 0=principal, 1=result, 2=accum
  const zero = makeNode("zero", 1); // 0=principal
  const extResult = makeNode("var", 1);
  const extAccum = makeNode("var", 1);

  link({ node: add, port: 0 }, { node: zero, port: 0 });
  link({ node: add, port: 1 }, { node: extResult, port: 0 });
  link({ node: add, port: 2 }, { node: extAccum, port: 0 });

  const graph: Graph = [add, zero, extResult, extAccum];

  const agentPorts: AgentPortDefs = new Map([
    ["add", new Map([["principal", 0], ["result", 1], ["accum", 2]])],
    ["zero", new Map([["principal", 0]])],
  ]);

  const rule: InteractionRule = {
    agentA: "add",
    agentB: "zero",
    action: {
      kind: "custom",
      body: [
        // add(x, zero) → relink: result connects to accum's neighbor
        { kind: "relink", portA: { node: "left", port: "accum" }, portB: { node: "left", port: "result" } },
      ],
    },
  };

  reduceCustomRule(add, zero, asMut(graph), rule, agentPorts);

  // add and zero should be removed
  assertEquals(graph.includes(add), false);
  assertEquals(graph.includes(zero), false);
  // extAccum's neighbor (was add.accum) should now be connected to extResult's neighbor (was add.result)
  assertEquals(extAccum.ports[0].node, extResult);
  assertEquals(extResult.ports[0].node, extAccum);
});

// ─── let + wire ────────────────────────────────────────────────────

Deno.test("custom rule: let creates new node, wire connects ports", () => {
  // add(x, succ(y)) → succ(add(x, y))
  const add = makeNode("add", 3); // 0=principal, 1=result, 2=accum
  const succ = makeNode("succ", 2); // 0=principal, 1=pred
  const extResult = makeNode("var", 1);
  const extAccum = makeNode("var", 1);
  const extPred = makeNode("var", 1);

  link({ node: add, port: 0 }, { node: succ, port: 0 });
  link({ node: add, port: 1 }, { node: extResult, port: 0 });
  link({ node: add, port: 2 }, { node: extAccum, port: 0 });
  link({ node: succ, port: 1 }, { node: extPred, port: 0 });

  const graph: Graph = [add, succ, extResult, extAccum, extPred];

  const agentPorts: AgentPortDefs = new Map([
    ["add", new Map([["principal", 0], ["result", 1], ["accum", 2]])],
    ["succ", new Map([["principal", 0], ["pred", 1]])],
  ]);

  const rule: InteractionRule = {
    agentA: "add",
    agentB: "succ",
    action: {
      kind: "custom",
      body: [
        // let s = succ, let a = add
        { kind: "let", varName: "s", agentType: "succ" },
        { kind: "let", varName: "a", agentType: "add" },
        // relink: s.principal ← left.result neighbor
        { kind: "relink", portA: { node: "left", port: "result" }, portB: { node: "s", port: "principal" } },
        // wire: s.pred ↔ a.result
        { kind: "wire", portA: { node: "s", port: "pred" }, portB: { node: "a", port: "result" } },
        // relink: a.accum ← left.accum neighbor
        { kind: "relink", portA: { node: "left", port: "accum" }, portB: { node: "a", port: "accum" } },
        // relink: a.principal ← right.pred neighbor
        { kind: "relink", portA: { node: "right", port: "pred" }, portB: { node: "a", port: "principal" } },
      ],
    },
  };

  reduceCustomRule(add, succ, asMut(graph), rule, agentPorts);

  // Original nodes removed
  assertEquals(graph.includes(add), false);
  assertEquals(graph.includes(succ), false);

  // Two new nodes created (succ + add)
  const newSucc = graph.find((n) => n.type === "succ");
  const newAdd = graph.find((n) => n.type === "add");
  assertEquals(newSucc !== undefined, true);
  assertEquals(newAdd !== undefined, true);

  // s.principal is connected to extResult (via relink from left.result)
  assertEquals(extResult.ports[0].node, newSucc!);
  assertEquals(newSucc!.ports[0].node, extResult);

  // s.pred is connected to a.result (via wire)
  assertEquals(newSucc!.ports[1].node, newAdd!);
  assertEquals(newAdd!.ports[1].node, newSucc!);

  // a.accum is connected to extAccum (via relink from left.accum)
  assertEquals(newAdd!.ports[2].node, extAccum);
  assertEquals(extAccum.ports[0].node, newAdd!);

  // a.principal is connected to extPred (via relink from right.pred)
  assertEquals(newAdd!.ports[0].node, extPred);
  assertEquals(extPred.ports[0].node, newAdd!);
});

// ─── erase ─────────────────────────────────────────────────────────

Deno.test("custom rule: erase-stmt inserts eraser", () => {
  const a = makeNode("foo", 2);
  const b = makeNode("bar", 2);
  const ext1 = makeNode("var", 1);
  const ext2 = makeNode("var", 1);

  link({ node: a, port: 0 }, { node: b, port: 0 });
  link({ node: a, port: 1 }, { node: ext1, port: 0 });
  link({ node: b, port: 1 }, { node: ext2, port: 0 });

  const graph: Graph = [a, b, ext1, ext2];

  const agentPorts: AgentPortDefs = new Map([
    ["foo", new Map([["principal", 0], ["aux", 1]])],
    ["bar", new Map([["principal", 0], ["aux", 1]])],
  ]);

  const rule: InteractionRule = {
    agentA: "foo",
    agentB: "bar",
    action: {
      kind: "custom",
      body: [
        // Erase right's aux neighbor, relink left's aux
        { kind: "erase-stmt", port: { node: "right", port: "aux" } },
        { kind: "relink", portA: { node: "left", port: "aux" }, portB: { node: "left", port: "aux" } },
      ],
    },
  };

  reduceCustomRule(a, b, asMut(graph), rule, agentPorts);

  assertEquals(graph.includes(a), false);
  assertEquals(graph.includes(b), false);
  // Eraser should have been created and linked to ext2
  const eraser = graph.find((n) => n.type === "era");
  assertEquals(eraser !== undefined, true);
  assertEquals(ext2.ports[0].node, eraser!);
});

// ─── numeric ports ─────────────────────────────────────────────────

Deno.test("custom rule: numeric port strings work", () => {
  const a = makeNode("x", 2);
  const b = makeNode("y", 2);
  const ext1 = makeNode("var", 1);
  const ext2 = makeNode("var", 1);

  link({ node: a, port: 0 }, { node: b, port: 0 });
  link({ node: a, port: 1 }, { node: ext1, port: 0 });
  link({ node: b, port: 1 }, { node: ext2, port: 0 });

  const graph: Graph = [a, b, ext1, ext2];
  const agentPorts: AgentPortDefs = new Map();

  const rule: InteractionRule = {
    agentA: "x",
    agentB: "y",
    action: {
      kind: "custom",
      body: [
        { kind: "relink", portA: { node: "left", port: "1" }, portB: { node: "right", port: "1" } },
      ],
    },
  };

  reduceCustomRule(a, b, asMut(graph), rule, agentPorts);

  assertEquals(ext1.ports[0].node, ext2);
  assertEquals(ext2.ports[0].node, ext1);
});
