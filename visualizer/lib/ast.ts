import { ASTKinds, type EXPR, parse, SyntaxErr } from "./parser.gen.ts";
import { fancyNameToName, nameToFancyName } from "./util.ts";

// A `Node` is either an `Abstraction`, an `Application` or a `Variable`.
// TODO: rename to "Expression"
export type AstNode = Abstraction | Application | Variable;

// An abstraction is a parameter name and a body.
export type Abstraction = {
  type: "abs";
  parent?: AstNode;
  name: string;
  body: AstNode;
  extra?: any;
};

// An application of a function to an argument.
export type Application = {
  type: "app";
  parent?: AstNode;
  func: AstNode;
  arg: AstNode;
  extra?: any;
};

// A variable is a node with a name.
export type Variable = {
  type: "var";
  parent?: AstNode;
  name: string;
  extra?: any;
};

export type Definitions = { [name: string]: AstNode };

// Parses a lambda calculi expression into an `AST`.
// Returns an array of `SyntaxErr` instead if there are parsing errors.
export function parseSource(
  source: string,
): { ast?: AstNode | null, errs?: SyntaxErr[] } {
  // Parse using tsPEG
  const rawAst = parse(source);

  // If there are parsing errors, return them
  if (rawAst.errs.length > 0) {
    return { errs: rawAst.errs };
  }

  const definitions: Definitions = {}
  let lastExpr: EXPR | null = null;

  // Loop through statements, storing definitions and the last expression
  // Definitions are expected to only reference previous definitions
  // If a definition is referenced before it is defined, it is assumed to be a free variable
  for (const stmt of rawAst.ast!.statements) {
    if (stmt.stmt.kind === ASTKinds.DEF) {
      definitions[stmt.stmt.identifier.identifier] =
        parseRawExpressionNode(stmt.stmt.value, definitions);
    } else {
      lastExpr = stmt.stmt;
    }
  }

  // Parse the last expression (if any)
  if (lastExpr !== null) {
    return { ast: parseRawExpressionNode(lastExpr, definitions) };
  }

  return { ast: null };
}

// Parses a raw AST node, updating the AST in place.
// Returns the index of the newly inserted node.
function parseRawExpressionNode(rawNode: EXPR, definitions: Definitions, parent?: any): AstNode {
  if (
    rawNode.kind === ASTKinds.APPLICATION
  ) {
    // Application
    const node: Partial<AstNode> = { type: "app", parent };
    node.func = parseRawExpressionNode(rawNode.func, definitions, node);
    node.arg = parseRawExpressionNode(rawNode.arg, definitions, node);
    return node as AstNode;
  } else if (rawNode.kind === ASTKinds.IDENT) {
    // Check if it's a definition
    const definition = definitions[rawNode.identifier];
    if (definition) {
      return clone(definition, parent);
    }
    // Otherwise it's a variable
    return {
      type: "var",
      parent,
      name: nameToFancyName(rawNode.identifier),
    };
  } else if (rawNode.kind === ASTKinds.ABSTRACTION) {
    // Abstraction
    const node: Partial<AstNode> = {
      type: "abs",
      parent,
      name: nameToFancyName(rawNode.parameter.identifier),
    };
    node.body = parseRawExpressionNode(rawNode.body, definitions, node);
    return node as AstNode;
  } else if (rawNode.kind === ASTKinds.GROUP) {
    // Group (simply pass through)
    return parseRawExpressionNode(rawNode.group, definitions, parent);
  } else {
    /*Could be any of (
      astNode.kind === ASTKinds.main_2 ||
      astNode.kind === ASTKinds.term_1 ||
      astNode.kind === ASTKinds.term_3 ||
      astNode.kind === ASTKinds.identifier ||
      astNode.kind === ASTKinds.$EOF
      )*/
    throw `Unreachable (${rawNode})`;
  }
}

// Clones a node and its descendants.
export function clone(astNode: AstNode, parent?: any): AstNode {
  if (astNode.type === "abs") {
    const node: Partial<AstNode> = {
      type: "abs",
      parent,
      name: astNode.name,
    };
    node.body = clone(astNode.body, node);
    return node as AstNode;
  } else if (astNode.type === "app") {
    const node: Partial<AstNode> = {
      type: "app",
      parent,
    };
    node.func = clone(astNode.func, node);
    node.arg = clone(astNode.arg, node);
    return node as AstNode;
  } else {
    return {
      type: "var",
      parent,
      name: astNode.name,
    };
  }
}

// Renders an AST node as a string.
export const astToString = (astNode: AstNode): string => {
  if (astNode.type === "abs") {
    return (
      "λ" + fancyNameToName(astNode.name) + "." + astToString(astNode.body)
    );
  } else if (astNode.type === "app") {
    let funcString = astToString(astNode.func);
    let argString = astToString(astNode.arg);
    // Add parentheses where necessary
    if (astNode.func.type === "abs" || astNode.func.type === "app") {
      funcString = "(" + funcString + ")";
    }
    if (astNode.arg.type === "app") {
      argString = "(" + argString + ")";
    }
    return funcString + " " + argString;
  } else {
    // astNode.type === "var"
    return fancyNameToName(astNode.name);
  }
};

export type SystemType = "linear" | "affine" | "relevant" | "full";

export const getExpressionType = (astNode: AstNode): SystemType => {
  let sharing = false;
  let erasure = false;

  const visit = (node: AstNode, boundVars: Map<string, number> = new Map()) => {
    if (node.type === "abs") {
      boundVars.set(node.name, 0);
      visit(node.body, boundVars);
      const count = boundVars.get(node.name);
      if (count !== undefined) {
        if (count === 0) {
          erasure = true;
        } else if (count > 1) {
          sharing = true;
        }
      }
    } else if (node.type === "app") {
      visit(node.func, boundVars);
      visit(node.arg, boundVars);
    } else /* if (node.type === "var") */ {
      const count = boundVars.get(node.name);
      if (count !== undefined) {
        const newCount = count + 1;
        boundVars.set(node.name, newCount);
        if (newCount > 1) {
          sharing = true;
        }
      }
    }
  };
  visit(astNode, new Map());

  console.debug(sharing, erasure);
  if (sharing) {
    if (erasure) {
      return "full";
    } else {
      return "relevant";
    }
  } else {
    if (erasure) {
      return "affine";
    } else {
      return "linear";
    }
  }
};
