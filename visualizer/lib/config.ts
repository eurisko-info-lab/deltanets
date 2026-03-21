// Shared UI constants — single source of truth for magic numbers and storage keys.

/** Minimum zoom scale for the graph view. */
export const MIN_SCALE = 0.1;

/** Maximum zoom scale for the graph view. */
export const MAX_SCALE = 10;

/** Maximum scale applied during auto-centering. */
export const MAX_AUTO_SCALE = 1.5;

/** Minimum width (px) for either editor or graph pane. */
export const MIN_PANE_SIZE = 200;

/** localStorage keys used by appState. */
export const STORAGE_KEYS = {
  method: "method",
  theme: "theme",
  editorWidth: "editorWidth",
  center: "center",
  debug: "debug",
  source: "source",
  sonify: "sonify",
} as const;
