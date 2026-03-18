// Test the example .inet and .iview files.
// Run: deno run --allow-read lib/lang/test_examples.ts

import { compileCore, compileView } from "./index.ts";

async function testFile(path: string, compiler: (s: string) => { errors: string[] }) {
  const source = await Deno.readTextFile(path);
  const result = compiler(source);
  if (result.errors.length > 0) {
    console.error(`✗ ${path}:`, result.errors);
    return false;
  }
  console.log(`✓ ${path}`);
  return true;
}

let ok = true;

// Core examples
ok = await testFile("lib/lang/examples/deltanets.inet", compileCore) && ok;
ok = await testFile("lib/lang/examples/deltanets-composed.inet", compileCore) && ok;
ok = await testFile("lib/lang/examples/lambda.inet", compileCore) && ok;
ok = await testFile("lib/lang/examples/typing.inet", compileCore) && ok;
ok = await testFile("lib/lang/examples/lambda-cube.inet", compileCore) && ok;

// View examples
ok = await testFile("lib/lang/examples/deltanets.iview", compileView) && ok;
ok = await testFile("lib/lang/examples/lambda.iview", compileView) && ok;

if (ok) {
  console.log("\n✓ All example files pass.");
} else {
  console.error("\n✗ Some files had errors.");
  Deno.exit(1);
}
