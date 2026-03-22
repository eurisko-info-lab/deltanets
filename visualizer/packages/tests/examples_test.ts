// Test that all .inet and .iview example files compile without errors.

import { assert } from "$std/assert/mod.ts";
import { compileCore, compileView } from "@deltanets/lang";

const EXAMPLES_DIR = new URL("../lang/examples/", import.meta.url);

function checkFile(
  file: string,
  compiler: (s: string) => { errors: string[] },
) {
  const source = Deno.readTextFileSync(new URL(file, EXAMPLES_DIR));
  const result = compiler(source);
  assert(result.errors.length === 0, `${file}: ${result.errors.join(", ")}`);
}

// Core examples
for (
  const file of [
    "deltanets.inet",
    "deltanets-composed.inet",
    "functional-music.inet",
    "lambda.inet",
    "typing.inet",
    "lambda-cube.inet",
    "lanes.inet",
  ]
) {
  Deno.test(`example: ${file} compiles`, () => {
    checkFile(file, compileCore);
  });
}

// View examples
for (
  const file of [
    "deltanets.iview",
    "lambda.iview",
    "lambda-cube.iview",
  ]
) {
  Deno.test(`example: ${file} compiles`, () => {
    checkFile(file, compileView);
  });
}
