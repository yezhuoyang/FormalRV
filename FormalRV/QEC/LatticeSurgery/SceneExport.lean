/-
  FormalRV.QEC.LatticeSurgery.SceneExport
  ---------------------------------------
  **★ EXPORT a VERIFIED lattice-surgery diagram to a JSON scene for the 3D/2D
  visualizer. ★**

  The visualizer renders EXACTLY the object Lean verified (`LaSre` geometry +
  `Surf` correlation surfaces + `Port` boundary), so the routing, the
  blue(Z)/red(X) correlated surfaces, and every piece's meaning are not artistic
  approximations — they are the proven data.  This walks the bounded grid and
  emits typed, LABELLED primitives (`#eval` the JSON; the standalone Three.js app
  reads it).

  COLOR CONVENTION (verified, from `GadgetToLaS` §1): blue = `Z` piece = `KI`
  plane, red = `X` piece = `KJ` plane, threaded along the K-worldline.  A
  surface-code patch therefore has a SMOOTH (`Z`, blue) boundary pair and a
  ROUGH (`X`, red) boundary pair.  WHICH spatial axis carries the smooth (blue)
  boundary is the diagram's z-basis direction, read from a K-pipe PORT's
  `blueSel` (`4`=`KI`⇒I-axis smooth, `5`=`KJ`⇒J-axis smooth) — the VERIFIED port
  data, NOT the `ColorI`/`ColorJ` fields (which the functionality checker
  ignores, per the audit's dead-field note).  Surface PLANES split blue
  {IK,JI,KI} / red {IJ,JK,KJ} (swapped when the z-basis is the J-axis).
-/
import FormalRV.QEC.LatticeSurgery.LaSre
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.QEC.LatticeSurgery.CrossLayerHetero
import FormalRV.QEC.LatticeSurgery.CNOTFromLaSsynth
import FormalRV.QEC.LatticeSurgery.CZFromLaSsynth
import FormalRV.QEC.LatticeSurgery.HFromLaSsynth
import FormalRV.QEC.LatticeSurgery.RoutedMerge
import FormalRV.QEC.LatticeSurgery.MajorityGateLaS

namespace FormalRV.QEC.LaSre.Viz

open FormalRV.QEC
open FormalRV.QEC.LaSre

/-! ## §1. Tiny JSON builders (no external dep). -/

def jnum (n : Nat) : String := toString n
def jstr (s : String) : String := "\"" ++ s ++ "\""
def jbool (b : Bool) : String := if b then "true" else "false"
/-- join a list of already-rendered JSON fragments with commas. -/
def jjoin (xs : List String) : String := String.intercalate "," xs
def jarr (xs : List String) : String := "[" ++ jjoin xs ++ "]"

/-- all `(i,j,k)` cells of a `mi×mj×mk` grid. -/
def gridCells (mi mj mk : Nat) : List (Nat × Nat × Nat) :=
  (List.range mi).flatMap fun i =>
    (List.range mj).flatMap fun j =>
      (List.range mk).map fun k => (i, j, k)

/-! ## §2. The z-basis direction — which spatial axis carries the smooth (blue,
`Z`) boundary — read from a K-pipe port's `blueSel` (VERIFIED data). -/

/-- `true` ⇔ the I-axis carries the smooth (blue, `Z`) boundary (`blueSel = KI`);
`false` ⇔ the J-axis does (`blueSel = KJ`).  Defaults to the I-axis (the base
convention) when no port sits on a K-pipe. -/
def blueAxisI (ports : List Port) : Bool :=
  match ports.find? (fun p => p.blueSel == 4 || p.blueSel == 5) with
  | some p => p.blueSel == 4
  | none   => true

/-- A surface PLANE's colour under the diagram's z-basis: base-blue planes are
{IK, JI, KI}; the assignment swaps when the J-axis is the smooth one. -/
def planeBlue (bi : Bool) (plane : String) : Bool :=
  let baseBlue := plane == "IK" || plane == "JI" || plane == "KI"
  baseBlue == bi

/-! ## §3. Geometry primitives → JSON. -/

/-- A geometry primitive: a cube/pipe at `(i,j,k)` of a given `kind`, carrying a
`color` hint and a human-readable hover `label`. -/
def prim (kind : String) (i j k : Nat) (color label : String) : String :=
  "{" ++ jjoin
    [ "\"kind\":" ++ jstr kind, "\"i\":" ++ jnum i, "\"j\":" ++ jnum j,
      "\"k\":" ++ jnum k, "\"color\":" ++ jstr color, "\"label\":" ++ jstr label ] ++ "}"

/-- Walk the LaSre and emit worldlines (`K`-pipes), `Z`/`X`-merge seams
(`I`/`J`-pipes), and `Y`-cubes — each LABELLED, the seam colour resolved by the
diagram's z-basis (`bi`). -/
def cubesJSON (bi : Bool) (L : LaSre) : List String :=
  let smooth := if bi then "I" else "J"
  let rough  := if bi then "J" else "I"
  let iType  := if bi then "Z" else "X"          -- I-pipe merge type under this z-basis
  let iCol   := if bi then "blue" else "red"
  let jType  := if bi then "X" else "Z"          -- J-pipe merge type
  let jCol   := if bi then "red" else "blue"
  (gridCells L.maxI L.maxJ L.maxK).filterMap (fun p =>
    let (i, j, k) := p
    if L.ExistK i j k then
      some (prim "worldline" i j k "patch"
        s!"patch ({i},{j}) worldline @ t={k} — smooth(Z,blue) on {smooth}-faces, rough(X,red) on {rough}-faces")
    else none)
  ++ (gridCells L.maxI L.maxJ L.maxK).filterMap (fun p =>
    let (i, j, k) := p
    if L.ExistI i j k then
      some (prim "zseam" i j k iCol
        s!"{iType}̄-merge seam (I-pipe) joining patches ({i},{j})-({i+1},{j}) @ t={k}")
    else none)
  ++ (gridCells L.maxI L.maxJ L.maxK).filterMap (fun p =>
    let (i, j, k) := p
    if L.ExistJ i j k then
      some (prim "xseam" i j k jCol
        s!"{jType}̄-merge seam (J-pipe) joining patches ({i},{j})-({i},{j+1}) @ t={k}")
    else none)
  ++ (gridCells L.maxI L.maxJ L.maxK).filterMap (fun p =>
    let (i, j, k) := p
    if L.YCube i j k then
      some (prim "ycube" i j k "green" s!"Ȳ init/measure (Y-cube) @ patch ({i},{j}) t={k}")
    else none)

/-! ## §4. Correlation surfaces → JSON (blue = Z, red = X, by z-basis). -/

/-- One correlation-surface cell: flow `s`, plane name, colour, position. -/
def surfCell (s : Nat) (plane colour : String) (i j k : Nat) (label : String) : String :=
  "{" ++ jjoin
    [ "\"flow\":" ++ jnum s, "\"plane\":" ++ jstr plane, "\"color\":" ++ jstr colour,
      "\"i\":" ++ jnum i, "\"j\":" ++ jnum j, "\"k\":" ++ jnum k, "\"label\":" ++ jstr label ] ++ "}"

/-- Walk the `Surf` for every flow `s < nStab` and emit the colored membrane
cells, each plane's blue(`Z`)/red(`X`) colour resolved by the z-basis `bi`. -/
def surfacesJSON (bi : Bool) (S : Surf) (nStab : Nat) (L : LaSre) : List String :=
  (List.range nStab).flatMap fun s =>
    (gridCells L.maxI L.maxJ L.maxK).flatMap fun p =>
      let (i, j, k) := p
      let emit (pl : String) (present : Bool) : List String :=
        if present then
          let col := if planeBlue bi pl then "blue" else "red"
          let pa  := if planeBlue bi pl then "Z̄" else "X̄"
          [surfCell s pl col i j k s!"flow {s}: {pa} correlation ({pl}) @ ({i},{j},{k})"]
        else []
      emit "KI" (S.KI s i j k) ++ emit "IK" (S.IK s i j k)
      ++ emit "JI" (S.JI s i j k) ++ emit "KJ" (S.KJ s i j k)
      ++ emit "JK" (S.JK s i j k) ++ emit "IJ" (S.IJ s i j k)

/-! ## §4½. Color ROTATIONS (Hadamard / patch rotation) → a yellow marker.

A patch rotation (H) SWAPS the smooth/rough boundary, so the diagram's boundary
colours genuinely interleave — denoted by a short YELLOW tube.  We detect it the
honest way: a worldline column whose ports carry BOTH z-basis conventions
(`blueSel = KI` at one end, `KJ` at the other) is rotating between them; mark the
column's midpoint. -/

/-- Columns `(i,j,k≈mid)` that rotate basis, evidenced by ports of both
conventions (`blueSel ∈ {4,5}` disagreeing) on the same column. -/
def rotationCells (ports : List Port) : List (Nat × Nat × Nat) :=
  let cols := (ports.map (fun p => (p.pi, p.pj))).dedup
  cols.filterMap (fun c =>
    let cp := ports.filter (fun p => p.pi == c.1 && p.pj == c.2)
    if (cp.any (fun p => p.blueSel == 4)) && (cp.any (fun p => p.blueSel == 5)) then
      let ks := cp.map (·.pk)
      some (c.1, c.2, (ks.foldl (· + ·) 0) / (max 1 ks.length))
    else none)

def rotationsJSON (ports : List Port) : List String :=
  (rotationCells ports).map (fun c =>
    let (i, j, k) := c
    "{" ++ jjoin
      [ "\"kind\":" ++ jstr "rotation", "\"i\":" ++ jnum i, "\"j\":" ++ jnum j,
        "\"k\":" ++ jnum k, "\"color\":" ++ jstr "yellow",
        "\"label\":" ++ jstr s!"H / patch rotation @ ({i},{j}) t≈{k} — X̄↔Z̄ boundary swap" ] ++ "}")

/-! ## §5. Ports → JSON. -/

def portsJSON (ports : List Port) (paulis : Nat → Nat → Pauli) (_nStab : Nat) : List String :=
  ports.zipIdx.map (fun pp =>
    let p := pp.1
    let idx := pp.2
    let pa := paulis 0 idx
    let paStr := match pa with | .X => "X" | .Y => "Y" | .Z => "Z" | .I => "I"
    "{" ++ jjoin
      [ "\"i\":" ++ jnum p.pi, "\"j\":" ++ jnum p.pj, "\"k\":" ++ jnum p.pk,
        "\"blueSel\":" ++ jnum p.blueSel, "\"redSel\":" ++ jnum p.redSel,
        "\"label\":" ++ jstr s!"port @ ({p.pi},{p.pj},{p.pk}) — flow0 reads {paStr}" ] ++ "}")

/-! ## §6. The whole scene. -/

/-- Export a verified `(LaSre, Surf, ports, paulis, nStab)` as one JSON scene.
The top-level `blueAxis` ("I"/"J") tells the renderer which spatial axis carries
the smooth (blue, `Z`) boundary. -/
def sceneJSON (name : String) (L : LaSre) (S : Surf) (ports : List Port)
    (paulis : Nat → Nat → Pauli) (nStab : Nat) : String :=
  let bi := blueAxisI ports
  "{" ++ jjoin
    [ "\"name\":" ++ jstr name,
      "\"blueAxis\":" ++ jstr (if bi then "I" else "J"),
      "\"dims\":{\"maxI\":" ++ jnum L.maxI ++ ",\"maxJ\":" ++ jnum L.maxJ ++ ",\"maxK\":" ++ jnum L.maxK ++ "}",
      "\"nStab\":" ++ jnum nStab,
      "\"cubes\":" ++ jarr (cubesJSON bi L ++ rotationsJSON ports),
      "\"surfaces\":" ++ jarr (surfacesJSON bi S nStab L),
      "\"ports\":" ++ jarr (portsJSON ports paulis nStab) ] ++ "}"

/-! ## §7. Export the verified example diagrams (run with `lake env lean`). -/

open FormalRV.QEC.Gidney21 in
/-- Write the gallery JSON files into `SurfaceLCViz/scenes/`.  Every scene is a Lean
object that passes `LaSCorrectFull` (or `LaSCorrect` for the majority gate). -/
def writeGallery : IO Unit := do
  IO.FS.createDirAll "SurfaceLCViz/scenes"
  -- single-basis joint measurements (constructed surfaces, native_decide-checked)
  IO.FS.writeFile "SurfaceLCViz/scenes/zmerge.json"
    (sceneJSON "Z-merge (Z̄₀Z̄₁)" mergeZLaS mergeZSurf mergeZPorts mergeZPaulis 3)
  IO.FS.writeFile "SurfaceLCViz/scenes/xmerge.json"
    (sceneJSON "X-merge (X̄₀X̄₁)" mergeXLaS mergeXSurf mergeXPorts mergeXPaulis 3)
  IO.FS.writeFile "SurfaceLCViz/scenes/zzz-merge.json"
    (sceneJSON "Weight-3 Z-merge (Z̄₀Z̄₁Z̄₂)" mergeZ3LaS mergeZ3Surf mergeZ3Ports mergeZ3Paulis 4)
  -- routed long-range merge — data only at cols {0,3}, ancilla HIGHWAY through 1–2
  IO.FS.writeFile "SurfaceLCViz/scenes/routed.json"
    (sceneJSON "Routed long-range Z-merge {0,3} (ancilla highway)"
      (routedZMerge [0,3]) (routedZMergeSurf [0,3]) (routedZMergePorts [0,3]) (routedZMergePaulis [0,3]) 3)
  -- LaSsynth-synthesized multi-merge gates (imported verbatim, re-verified in Lean)
  IO.FS.writeFile "SurfaceLCViz/scenes/cnot.json"
    (sceneJSON "CNOT (LaSsynth multi-merge)" cnotSynthLaS cnotSynthSurf cnotPorts cnotPaulis 4)
  IO.FS.writeFile "SurfaceLCViz/scenes/cz.json"
    (sceneJSON "CZ (mixed-basis multi-merge, LaSsynth)" czLaS czSurf czPorts czPaulis 4)
  -- Hadamard = a patch ROTATION (X̄↔Z̄ boundary swap) → a yellow rotation marker
  IO.FS.writeFile "SurfaceLCViz/scenes/hadamard.json"
    (sceneJSON "Hadamard (patch rotation, LaSsynth)" hLaS hSurf hPorts hPaulis 2)
  IO.FS.writeFile "SurfaceLCViz/scenes/majority.json"
    (sceneJSON "Majority / CCZ junction (LaSsynth, 9 flows)" majorityLaS majoritySurf majPorts majPaulis 9)
  -- cross-layer heterogeneous chain (Z-merge then Ȳ-readout)
  IO.FS.writeFile "SurfaceLCViz/scenes/crosslayer.json"
    (sceneJSON "Cross-layer: Z-merge then Y-readout" hcL1 hcS1 hcPorts hcPaulis 4)
  IO.println "wrote SurfaceLCViz/scenes/{zmerge,xmerge,zzz-merge,routed,cnot,cz,hadamard,majority,crosslayer}.json"

#eval writeGallery

end FormalRV.QEC.LaSre.Viz
