// ═══════════════════════════════════════════════════════════════════
// INet Core Language — Built-in Prelude
// Structural agents shared by all interaction net systems.
// This is the canonical source for `include "prelude"`.
// ═══════════════════════════════════════════════════════════════════

export const PRELUDE_SOURCE = `\
system "Prelude" {
  agent root(principal)
  agent var(principal)
}
`;
