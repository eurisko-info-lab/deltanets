// Standard λ-calculus tree system implementation.
// Beta reduction via naive copying with capture-avoiding substitution.

import type {
  Abstraction,
  AstNode,
  Variable,
} from "../../ast.ts";
import { clone, astToString } from "../../ast.ts";
import { nameToFancyName } from "../../util.ts";
import type { TreeSystem } from "../types.ts";

// Replaces a node with a new node. Returns true if the node is now the root node.
function replace(astNode: AstNode, newNode: AstNode): boolean {
  if (astNode.parent) {
    if (astNode.parent.type === "abs") {
      astNode.parent.body = newNode;
    } else if (astNode.parent.type === "app") {
      if (astNode.parent.func === astNode) {
        astNode.parent.func = newNode;
      } else {
        astNode.parent.arg = newNode;
      }
    }
  }
  newNode.parent = astNode.parent;
  return !newNode.parent;
}

// Executes a function for each descendant.
function forEachDescendant(
  astNode: AstNode,
  f: (astNode: AstNode) => boolean,
) {
  if (f(astNode)) {
    return;
  }
  if (astNode.type === "abs") {
    forEachDescendant(astNode.body, f);
  } else if (astNode.type === "app") {
    forEachDescendant(astNode.func, f);
    forEachDescendant(astNode.arg, f);
  }
}

// Collect all bound variables with a given name under the provided node.
function boundVars(astNode: AstNode, name: string): Variable[] {
  const bVars: Variable[] = [];
  forEachDescendant(astNode, (astNode) => {
    if (astNode.type === "var" && astNode.name === name) {
      bVars.push(astNode);
    }
    return false;
  });
  return bVars;
}

// Returns the free variables in an AST.
function freeVars(node: AstNode): string[] {
  const result: string[] = [];
  const visit = (node: AstNode, bound: string[] = []) => {
    if (node.type === "abs") {
      visit(node.body, [...bound, node.name]);
    } else if (node.type === "app") {
      visit(node.func, bound);
      visit(node.arg, bound);
    } else if (!bound.includes(node.name)) {
      result.push(node.name);
    }
  };
  visit(node);
  return result;
}

// Returns whether an abstraction is closed.
function isAbstractionClosed(node: Abstraction): boolean {
  const freeVarsInBody = new Set(freeVars(node.body));
  return freeVarsInBody.size === 1 && freeVarsInBody.has(node.name);
}

// Generates a new identifier that does not collide with any of the ones in `vars`.
function newVarName(name: string, vars: string[]): string {
  let i = 1;
  let newName = nameToFancyName(name + i);
  while (vars.includes(newName)) {
    newName = nameToFancyName(name + i);
    i += 1;
  }
  return newName;
}

// Recursively alpha-converts `name` to `newName`.
function alphaConvert(node: AstNode, name: string, newName: string) {
  if (node.type === "abs") {
    if (node.name !== name) {
      alphaConvert(node.body, name, newName);
    }
  } else if (node.type === "app") {
    alphaConvert(node.func, name, newName);
    alphaConvert(node.arg, name, newName);
  } else if (node.name === name) {
    node.name = newName;
  }
}

// Substitutes all variables with a given name in an AST with a new node.
function substitute(
  tree: AstNode,
  varToSubstitute: string,
  substituteBy: AstNode,
  varsFreeInArg: string[],
  varsBoundInFunc: string[] = [],
): AstNode {
  if (tree.type === "abs") {
    if (tree.name !== varToSubstitute) {
      if (varsFreeInArg.includes(tree.name)) {
        const oldName = tree.name;
        tree.name = newVarName(tree.name, [
          ...varsFreeInArg,
          ...freeVars(tree.body),
          ...varsBoundInFunc,
        ]);
        alphaConvert(tree.body, oldName, tree.name);
      }
      const newVarsBoundInFunc = [...varsBoundInFunc];
      newVarsBoundInFunc.push(tree.name);
      tree.body = substitute(
        tree.body,
        varToSubstitute,
        substituteBy,
        varsFreeInArg,
        newVarsBoundInFunc,
      );
      tree.body.parent = tree;
    }
  } else if (tree.type === "app") {
    tree.func = substitute(
      tree.func,
      varToSubstitute,
      substituteBy,
      varsFreeInArg,
      varsBoundInFunc,
    );
    tree.func.parent = tree;
    tree.arg = substitute(
      tree.arg,
      varToSubstitute,
      substituteBy,
      varsFreeInArg,
      varsBoundInFunc,
    );
    tree.arg.parent = tree;
  } else if (tree.type === "var" && tree.name === varToSubstitute) {
    return clone(substituteBy);
  }
  return tree;
}

export const lambdacalc: TreeSystem = {
  name: "λ-Calculus (Standard)",
  clone,
  substitute,
  replace,
  freeVars,
  boundVars,
  isAbstractionClosed,
  astToString,
};
