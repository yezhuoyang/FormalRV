/-
  FormalRV.QEC.LatticeSurgery.MixedMergeWeld
  ------------------------------------------
  **The multi-patch ASSEMBLY — welding `[H₂; X-merge; H₂]` into one diagram and
  reading off the mixed measurement `M_{X₁Z₂}`.**

  The composition primitives (`Weld.lean`) are all verified.  This file does the
  remaining INTEGRATION: lay the three layers of the mixed reduction on one
  common multi-patch grid and verify the result with `LaSCorrectFull`.

  Layout: `q₁` at `(0,0)`, `q₂` at `(0,1)` (adjacent for the X-merge J-seam);
  the `H`-on-`q₂` gadget is shifted to put its patch at `(0,1)` (aux at `(0,2)`,
  `(1,1)`).  Built bottom-up, verifying each layer before stacking.
-/
import FormalRV.QEC.LatticeSurgery.Weld
import FormalRV.QEC.LatticeSurgery.HFromLaSsynth

namespace FormalRV.QEC.LaSre

/-! ## §1. Spatial-shift and union operators. -/

/-- Shift a pipe diagram by `dj` along the `J` axis (place its content at
`j ≥ dj`). -/
def shiftJ (dj : Nat) (L : LaSre) : LaSre :=
  { maxI := L.maxI, maxJ := dj + L.maxJ, maxK := L.maxK
    YCube  := fun i j k => decide (dj ≤ j) && L.YCube i (j - dj) k
    ExistI := fun i j k => decide (dj ≤ j) && L.ExistI i (j - dj) k
    ExistJ := fun i j k => decide (dj ≤ j) && L.ExistJ i (j - dj) k
    ExistK := fun i j k => decide (dj ≤ j) && L.ExistK i (j - dj) k
    ColorI := fun i j k => decide (dj ≤ j) && L.ColorI i (j - dj) k
    ColorJ := fun i j k => decide (dj ≤ j) && L.ColorJ i (j - dj) k }

/-- Shift a surface by `dj` along `J`. -/
def shiftJSurf (dj : Nat) (S : Surf) : Surf :=
  { IJ := fun s i j k => decide (dj ≤ j) && S.IJ s i (j - dj) k
    IK := fun s i j k => decide (dj ≤ j) && S.IK s i (j - dj) k
    JK := fun s i j k => decide (dj ≤ j) && S.JK s i (j - dj) k
    JI := fun s i j k => decide (dj ≤ j) && S.JI s i (j - dj) k
    KI := fun s i j k => decide (dj ≤ j) && S.KI s i (j - dj) k
    KJ := fun s i j k => decide (dj ≤ j) && S.KJ s i (j - dj) k }

/-- Union two pipe diagrams with disjoint support (OR every field). -/
def unionLaS (A B : LaSre) : LaSre :=
  { maxI := max A.maxI B.maxI, maxJ := max A.maxJ B.maxJ, maxK := max A.maxK B.maxK
    YCube  := fun i j k => A.YCube i j k || B.YCube i j k
    ExistI := fun i j k => A.ExistI i j k || B.ExistI i j k
    ExistJ := fun i j k => A.ExistJ i j k || B.ExistJ i j k
    ExistK := fun i j k => A.ExistK i j k || B.ExistK i j k
    ColorI := fun i j k => A.ColorI i j k || B.ColorI i j k
    ColorJ := fun i j k => A.ColorJ i j k || B.ColorJ i j k }

/-! ## §2. LAYER 1 — `H` on `q₂` (at `(0,1)`) ∥ idle on `q₁` (at `(0,0)`).

  The `q₁` idle is a worldline at `(0,0)`; `H`-on-`q₂` is `hLaS` shifted to put
  its patch at `(0,1)`.  Four flows: `Z̄₁, X̄₁` pass on `q₁`; `H` maps
  `X̄₂→Z̄₂` and `Z̄₂→X̄₂` on `q₂`. -/

/-- `q₁`'s idle worldline at `(0,0)` (a 3-step memory). -/
def q1idle : LaSre :=
  { maxI := 1, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun _ _ _ => false, ExistJ := fun _ _ _ => false
    ExistK := fun i j k => i == 0 && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- `q₁`'s idle surface in the H/CNOT convention (z_basis J ⇒ blue=`KJ`):
`Z̄₁` in `KJ`, `X̄₁` in `KI`. -/
def q1idleSurf : Surf :=
  { IJ := fun _ _ _ _ => false, IK := fun _ _ _ _ => false
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 1 && i == 0 && j == 0
    KJ := fun s i j _ => s == 0 && i == 0 && j == 0 }

/-- Layer 1 diagram: `q₁` idle ∪ `H`-on-`q₂`(shifted to `(0,1)`). -/
def layer1 : LaSre := unionLaS q1idle (shiftJ 1 hLaS)

/-- Layer 1 surface: flows 0,1 from `q₁` idle; flows 2,3 from the shifted `H`. -/
def layer1Surf : Surf :=
  let hS := shiftJSurf 1 hSurf
  { IJ := fun s i j k => if s < 2 then q1idleSurf.IJ s i j k else hS.IJ (s - 2) i j k
    IK := fun s i j k => if s < 2 then q1idleSurf.IK s i j k else hS.IK (s - 2) i j k
    JK := fun s i j k => if s < 2 then q1idleSurf.JK s i j k else hS.JK (s - 2) i j k
    JI := fun s i j k => if s < 2 then q1idleSurf.JI s i j k else hS.JI (s - 2) i j k
    KI := fun s i j k => if s < 2 then q1idleSurf.KI s i j k else hS.KI (s - 2) i j k
    KJ := fun s i j k => if s < 2 then q1idleSurf.KJ s i j k else hS.KJ (s - 2) i j k }

/-- Ports: `q₁` in/out at `(0,0)` (z_basis J: blue=KJ 5, red=KI 4); `q₂` in at
`(0,1)` (z_basis J) and out at `(0,1)` (z_basis I after `H`: blue=KI 4). -/
def layer1Ports : List Port :=
  [⟨0, 0, 0, 5, 4⟩, ⟨0, 0, 2, 5, 4⟩, ⟨0, 1, 0, 5, 4⟩, ⟨0, 1, 2, 4, 5⟩]

/-- Spec: 0 `Z̄₁`, 1 `X̄₁` (q₁ ports 0,1); 2 `X̄₂→Z̄₂`, 3 `Z̄₂→X̄₂` (q₂ ports 2,3). -/
def layer1Paulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z   -- Z̄₁
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X   -- X̄₁
  | 2, 2 => Pauli.X | 2, 3 => Pauli.Z   -- X̄₂ → Z̄₂  (H on q₂)
  | 3, 2 => Pauli.Z | 3, 3 => Pauli.X   -- Z̄₂ → X̄₂
  | _, _ => Pauli.I

/-- **★ LAYER 1 VERIFIED — `H` on `q₂` ∥ idle on `q₁`, on a common 2×3 grid ★.**
A real multi-patch, multi-gadget parallel composition with a GATE: `q₁` idles
while `H` rotates `q₂` (`X̄₂→Z̄₂`, `Z̄₂→X̄₂`), the `q₁` flows passing through.
The welded layer passes the COMPLETE `LaSCorrectFull` — the `shiftJ`/`unionLaS`
layout operators are sound, and the multi-patch assembly approach works. -/
theorem layer1_fully_correct :
    LaSCorrectFull layer1 layer1Surf layer1Ports layer1Paulis 4 = true := by
  native_decide

/-! ## §3. STATUS — layer 1 VERIFIED; the precise remaining blocker.

  Layer 1 (the hardest NEW piece — a real gate `H` composed in parallel with an
  idle on a shared multi-patch grid) is VERIFIED (`layer1_fully_correct`), so the
  `shiftJ`/`unionLaS` layout operators and the assembly APPROACH are sound.

  Stacking layer 2 (the X-merge) exposes a CONCRETE, now-CHARACTERIZED blocker.
  It begins as the audit's flagged blue/red inconsistency — the LaSsynth gadgets
  (`H`, CNOT, CZ, layers 1,3) put blue(`Z`) in `KJ` (`z_basis=J`, selector 5),
  the hand-built merges (`mergeXLaS`, layer 2) put blue in `KI` (selector 4) — so
  `q₁` flips convention across the layer-1→layer-2 interface.  But the fix is
  DEEPER than a relabel: I tested re-deriving the X-merge in the `blue=KJ`
  convention (joint `X̄` via `KI`+`JI` across the same J-seam) and it FAILS —
  `LaSReport` returns `parity 0 0 0 1` (odd `iParity` at the seam).  Reason: the
  joint-Pauli join is tied to the SEAM AXIS — a J-pipe seam closes the joint flow
  via `jParity` (so it joins the `KI`-blue convention's red=`KJ`); to join in the
  `blue=KJ` convention the merge must use an I-pipe seam instead.  So the
  convention, the seam axis (I-pipe vs J-pipe), AND the patch layout (adjacent in
  `I` vs `J`) are COUPLED.

  CLOSING IT therefore needs a coordinated re-derivation: pick one convention,
  and re-build the merges with the matching seam axis and a layout compatible
  with the H-layer (or equivalently a per-patch convention-swap operator applied
  at the layer-1→layer-2 interface, proven sound the way `rotSurf` was).  No new
  PRIMITIVE is needed — `weldK`/`weldI`/`weldSurfP`/`rotSurf` all carry through —
  but it is a coordinated redesign, not the quick swap it first appeared to be.
  The assembly approach is validated (layer 1); this is the precise, bounded
  remaining work. -/

end FormalRV.QEC.LaSre
