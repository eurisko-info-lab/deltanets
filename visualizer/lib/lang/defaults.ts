// ═══════════════════════════════════════════════════════════════════
// Default .iview definitions
// Embedded .iview sources for browser-side compilation.
// These match the system names used in .inet files.
// ═══════════════════════════════════════════════════════════════════

export const DEFAULT_IVIEW: Record<string, string> = {
  "delta-nets": `
render abs {
  shape: fan(up)
  role: binder
  level: expr
  fill: level-color
  z: 2
}
render app {
  shape: fan(down)
  role: applicator
  level: expr
  fill: level-color
  z: 2
}
render rep-in {
  shape: replicator(up)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render rep-out {
  shape: replicator(down)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render era {
  shape: eraser
  role: leaf
  level: expr
  fill: #888888
  z: 0
}
render var {
  shape: circle
  role: leaf
  level: expr
  fill: #cccccc
  z: 1
}
render root {
  shape: circle
  role: leaf
  level: expr
  fill: wire-color
  z: 3
}
render type-base {
  shape: rect
  role: leaf
  level: type
  fill: #b0bec5
  z: 1
}
render type-arrow {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #90a4ae
  z: 1
}
render type-hole {
  shape: circle
  role: leaf
  level: type
  fill: #78909c
  z: 1
}
`,
  "lambda-calculus": `
render abs {
  shape: fan(up)
  role: binder
  level: expr
  fill: #5c6bc0
  z: 2
}
render app {
  shape: fan(down)
  role: applicator
  level: expr
  fill: #26a69a
  z: 2
}
render var {
  shape: circle
  role: leaf
  level: expr
  fill: #ef5350
  z: 1
}
render root {
  shape: circle
  role: leaf
  level: expr
  fill: wire-color
  z: 3
}
`,
  "lambda-cube": `
render abs {
  shape: fan(up)
  role: binder
  level: expr
  fill: level-color
  z: 2
}
render app {
  shape: fan(down)
  role: applicator
  level: expr
  fill: level-color
  z: 2
}
render var {
  shape: circle
  role: leaf
  level: expr
  fill: #cccccc
  z: 1
}
render era {
  shape: eraser
  role: leaf
  level: expr
  fill: #888888
  z: 0
}
render root {
  shape: circle
  role: leaf
  level: expr
  fill: wire-color
  z: 3
}
render type-base {
  shape: circle
  role: leaf
  level: type
  fill: #b0bec5
  z: 1
}
render type-arrow {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #90a4ae
  z: 1
}
render type-hole {
  shape: circle
  role: leaf
  level: type
  fill: #78909c
  z: 1
}
render rep-in {
  shape: replicator(up)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render rep-out {
  shape: replicator(down)
  role: replicator
  level: expr
  fill: level-color
  show-deltas: true
  z: 1
}
render tyabs {
  shape: fan(up)
  role: binder
  level: type
  fill: #7986cb
  z: 2
}
render tyapp {
  shape: fan(down)
  role: applicator
  level: type
  fill: #7986cb
  z: 2
}
render forall {
  shape: fan(up)
  role: binder
  level: type
  fill: #9fa8da
  z: 1
}
render pi {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #80cbc4
  z: 1
}
render sigma {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #80cbc4
  z: 1
}
render pair {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #80cbc4
  z: 1
}
render fst {
  shape: fan(down)
  role: destructor
  level: type
  fill: #a5d6a7
  z: 1
}
render snd {
  shape: fan(down)
  role: destructor
  level: type
  fill: #a5d6a7
  z: 1
}
render type-abs {
  shape: fan(up)
  role: binder
  level: type
  fill: #ce93d8
  z: 2
}
render type-app {
  shape: fan(down)
  role: applicator
  level: type
  fill: #ce93d8
  z: 2
}
render kind-star {
  shape: circle
  role: leaf
  level: type
  fill: #e1bee7
  z: 1
}
render kind-arrow {
  shape: fan(up)
  role: type-constructor
  level: type
  fill: #e1bee7
  z: 1
}
`,
};
