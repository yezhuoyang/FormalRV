# SurfaceLCViz — Surface-Code Lattice-Surgery Visualizer

Interactive **3D pipe diagrams** + a flattened **2D animation** of *verified*
surface-code lattice surgery. Every piece you see is a primitive that Lean proved
exists — routing, blue(Z)/red(X) correlation surfaces, ports — not an artistic mock-up.

```
Lean verified object            exporter                 renderer
  LaSre + Surf + Port  ──▶  SceneExport.lean  ──▶  scenes/*.json  ──▶  Three.js (main.js)
  (LaSCorrectFull)         (#eval writeGallery)                        index.html
```

## Run

The page uses ES-modules + `fetch`, so it must be served over **http** (not `file://`):

```powershell
cd SurfaceLCViz
python -m http.server 8777
# then open  http://localhost:8777/
```

Controls: **drag** rotate · **scroll** zoom · **right-drag** pan · **hover** a piece
for its meaning · scene picker + reset (⟲) + surface/per-flow toggles top-left.

## Regenerating the scenes from Lean

```powershell
chcp 65001
$env:LEAN_NUM_THREADS=6
lake env lean FormalRV/QEC/LatticeSurgery/SceneExport.lean   # #eval writeGallery
```

This rewrites all of `scenes/*.json` (zmerge, xmerge, zzz-merge, routed, cnot, cz,
majority, crosslayer) from the current verified Lean objects.

## Coordinate & colour convention

Lattice `(i, j, k)` → world `(x = i, y = k [time, up], z = j)`. Worldlines are the
K-pipes (patch tubes); merge seams are I-pipes / J-pipes; Y-cubes are green octahedra.
Translucent sheets are the per-flow correlation surfaces.

**Boundary colour** is the verified surface-code convention (`GadgetToLaS` §1: blue =
`Z` = `KI` plane, red = `X` = `KJ` plane). Every patch has a **smooth (Z, blue)**
boundary pair and a **rough (X, red)** pair. Which spatial axis carries the smooth
(blue) boundary is the diagram's z-basis, read from a K-pipe port's `blueSel`
(`4`=`KI`→I-axis, `5`=`KJ`→J-axis) and emitted as the scene's `blueAxis` — *not* from
the `ColorI`/`ColorJ` fields, which the functionality checker ignores (audit dead-field
note). A merge seam is drawn solid in its merge colour (blue = Z̄Z̄ join, red = X̄X̄).

## Scenes (all pass `LaSCorrectFull`, or `LaSCorrect` for the majority gate)

`zmerge` · `xmerge` · `zzz-merge` (weight-3) · `routed` (long-range {0,3} ancilla
highway) · `cnot` · `cz` (mixed-basis) · `majority` (CCZ junction, 9 flows) ·
`crosslayer`. CNOT/CZ use the J-axis z-basis (so their smooth boundary is red↔blue
swapped vs. the merges — read from the verified ports, not hand-set).
