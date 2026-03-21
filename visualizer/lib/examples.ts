// Examples are discovered from static/examples/ at module initialization time.
// Each file's display name is extracted from its first "# ..." comment line.
// Files are grouped by extension (.lam first, then .inet), sorted by name within each group.

const examplesDir = new URL("../static/examples/", import.meta.url).pathname;

const files = [...Deno.readDirSync(examplesDir)]
  .filter((e) =>
    e.isFile && (e.name.endsWith(".lam") || e.name.endsWith(".inet"))
  )
  .map((e) => e.name);

// .lam files first, then .inet files, alphabetical within each group.
files.sort((a, b) => {
  const extA = a.endsWith(".inet") ? 1 : 0;
  const extB = b.endsWith(".inet") ? 1 : 0;
  return extA - extB || a.localeCompare(b);
});

const examples: { name: string; code: string }[] = files.map((file) => {
  const code = Deno.readTextFileSync(`${examplesDir}${file}`);
  const firstLine = code.match(/^# (.+)/)?.[1] ?? file;
  return { name: firstLine, code };
});

export default examples;
