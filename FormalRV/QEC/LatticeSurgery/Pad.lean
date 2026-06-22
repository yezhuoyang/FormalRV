/-
  FormalRV.QEC.LatticeSurgery.Pad
  -------------------------------
  **Uniform-footprint padding + parallel layers — the primitives the automated
  threader needs to make every chain layer the same `w × 1 × 3` box.**

  `chainOK` requires every gadget in the chain to share one footprint
  `(maxI=w, maxJ=wj, maxK=h)`.  The catalog gadgets do NOT (widths 1..4).  This
  file supplies:
    * `idleStrip m` — `m` bare worldlines (no flows), the filler;
    * `padITo w a L` — pad a width-`a` gadget to width `w` by unioning an idle
      strip on columns `[a, w)` (so its footprint becomes `w`);
    * a VERIFIED PARALLEL LAYER — two disjoint `Z̄Z̄` merges side by side on one
      `4×1×3` grid, certified by `LaSCorrectFull`.  This is the parallelism the
      threader exploits: gadgets on disjoint qubits share a TIME LAYER.

  Convention (global, rigid): I-axis normalized, blue=`KI`(4)=`Z`, red=`KJ`(5)=`X`,
  `j` always `0`.
-/
import FormalRV.QEC.LatticeSurgery.ChainComposition

namespace FormalRV.QEC.LaSre

open FormalRV.QEC.Gidney21 (mergeZLaS mergeZSurf mergeZPorts mergeZPaulis)

/-! ## §1. The idle strip + width padding. -/

/-- `m` bare worldlines at `j=0`, height 3, carrying no flows — the filler that
pads a layer out to the board width. -/
def idleStrip (m : Nat) : LaSre :=
  { maxI := m, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun _ _ _ => false
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => decide (i < m) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Pad a width-`a`, height-3, `j`-extent-1 gadget `L` to a `w × 1 × 3` box by
unioning an idle strip on columns `[a, w)`. -/
def padITo (w a : Nat) (L : LaSre) : LaSre :=
  unionLaS L (shiftI a (idleStrip (w - a)))

/-! ## §2. ★ A VERIFIED PARALLEL LAYER — two disjoint `Z̄Z̄` merges side by side. -/

/-- Two `Z`-merges in parallel: merge on columns `(0,1)`, merge on `(2,3)`, one
`4×1×3` grid (`weldI` places the second to the right of the first). -/
def twoMergeLaS : LaSre := weldI 2 mergeZLaS mergeZLaS

/-- The two merge surfaces, direct-summed by flow offset (`weldISurf`): composite
flows `[0,3)` = merge-1 (`Z̄₀Z̄₁`, `X̄₀`, `X̄₁`), `[3,6)` = merge-2 (`Z̄₂Z̄₃`, `X̄₂`,
`X̄₃`). -/
def twoMergeSurf : Surf := weldISurf 2 3 mergeZSurf mergeZSurf

/-- Eight ports: in/out for each of the four qubit columns, blue=`KI`(4). -/
def twoMergePorts : List Port :=
  [⟨0, 0, 0, 4, 5⟩, ⟨0, 0, 2, 4, 5⟩, ⟨1, 0, 0, 4, 5⟩, ⟨1, 0, 2, 4, 5⟩,
   ⟨2, 0, 0, 4, 5⟩, ⟨2, 0, 2, 4, 5⟩, ⟨3, 0, 0, 4, 5⟩, ⟨3, 0, 2, 4, 5⟩]

/-- Spec: flow 0 `Z̄₀Z̄₁` (Z on ports 0–3); 1 `X̄₀`; 2 `X̄₁`; 3 `Z̄₂Z̄₃` (Z on
ports 4–7); 4 `X̄₂`; 5 `X̄₃`. -/
def twoMergePaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => Pauli.Z | 0, 1 => Pauli.Z | 0, 2 => Pauli.Z | 0, 3 => Pauli.Z
  | 1, 0 => Pauli.X | 1, 1 => Pauli.X
  | 2, 2 => Pauli.X | 2, 3 => Pauli.X
  | 3, 4 => Pauli.Z | 3, 5 => Pauli.Z | 3, 6 => Pauli.Z | 3, 7 => Pauli.Z
  | 4, 4 => Pauli.X | 4, 5 => Pauli.X
  | 5, 6 => Pauli.X | 5, 7 => Pauli.X
  | _, _ => Pauli.I

theorem twoMerge_report :
    LaSReport twoMergeLaS twoMergeSurf twoMergePorts twoMergePaulis 6 = [] := by native_decide

/-- **★ A PARALLEL LAYER IS VERIFIED LATTICE SURGERY ★** — two disjoint `Z̄Z̄`
measurements, placed side by side by `weldI`/`weldISurf` on one `4×1×3` grid,
pass the complete `LaSCorrectFull` for all six flows.  So gadgets on disjoint
qubits genuinely run in ONE time layer — the parallelism the threader needs. -/
theorem twoMerge_correct :
    LaSCorrectFull twoMergeLaS twoMergeSurf twoMergePorts twoMergePaulis 6 = true := by
  native_decide

/-- Footprint of the parallel layer: `4 × 1 × 3` (uniform `h=3`, `wj=1`). -/
theorem twoMerge_footprint :
    twoMergeLaS.maxI = 4 ∧ twoMergeLaS.maxJ = 1 ∧ twoMergeLaS.maxK = 3 := by
  native_decide

end FormalRV.QEC.LaSre
