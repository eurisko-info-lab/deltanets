// Test that all .inet and .iview example files compile without errors.

import { assert } from "$std/assert/mod.ts";
import { compileCore, compileView } from "./index.ts";

async function checkFile(
  path: string,
  compiler: (s: string) => { errors: string[] },
) {
  const source = await Deno.readTextFile(new URL(path, import.meta.url));
  const result = compiler(source);
  assert(result.errors.length === 0, `${path}: ${result.errors.join(", ")}`);
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
  Deno.test(`example: ${file} compiles`, async () => {
    await checkFile(`./examples/${file}`, compileCore);
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
  Deno.test(`example: ${file} compiles`, async () => {
    await checkFile(`./examples/${file}`, compileView);
  });
}
