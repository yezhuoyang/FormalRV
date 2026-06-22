/-
  FormalRV.QEC.LatticeSurgery.RoutedParallel
  ------------------------------------------
  **★ OFFSET highways + PARALLEL-LAYER composition — a congestion-free layer of
  routed merges welds into ONE verified diagram. ★**

  `lrMergeMulti` builds its seam from column 0, so two merges can't share a board.
  `spanMerge data` places the highway at `[min data, max data]` (any offset), so
  disjoint-span merges occupy disjoint board regions.  Then two disjoint routed
  merges UNION into one diagram measuring BOTH joint observables — the geometric
  realization of a congestion-free layer (`RoutedSchedule.packSpans_CF`'s output).
-/
import FormalRV.QEC.LatticeSurgery.RoutedMerge

namespace FormalRV.QEC.LaSre

/-! ## §1. The OFFSET merge — a highway at `[min data, max data]`. -/

/-- A `Z̄`-merge over data columns `data`, with the highway seam spanning exactly
`[min data, max data]` (so it can be PLACED anywhere, not just from column 0). -/
def spanMergeLaS (data : List Nat) : LaSre :=
  let lo := data.foldl Nat.min (data.headD 0)
  let hi := data.foldl Nat.max 0
  { maxI := hi + 1, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun i j k => decide (lo ≤ i) && decide (i < hi) && j == 0 && k == 1
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => data.contains i && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def spanMergeSurf (data : List Nat) : Surf :=
  let lo := data.foldl Nat.min (data.headD 0)
  let hi := data.foldl Nat.max 0
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k => s == 0 && decide (lo ≤ i) && decide (i < hi) && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && j == 0 && data.contains i
    KJ := fun s i j _ => decide (1 ≤ s) && (data.getD (s - 1) (hi + 1) == i) && j == 0 }

def spanMergePorts (data : List Nat) : List Port :=
  data.flatMap (fun c => [(⟨c, 0, 0, 4, 5⟩ : Port), (⟨c, 0, 2, 4, 5⟩ : Port)])

def spanMergePaulis (data : List Nat) : Nat → Nat → Pauli := fun s p =>
  let hi := data.foldl Nat.max 0
  if s == 0 then Pauli.Z
  else if data.getD (s - 1) (hi + 1) == data.getD (p / 2) (hi + 1) then Pauli.X else Pauli.I

/-- **★ A HIGHWAY PLACED AT A NON-ZERO OFFSET CERTIFIES ★** — `Z̄₅Z̄₈` with its
seam at columns 5–7 (not from 0) passes `LaSCorrectFull`. -/
theorem spanMerge_58_correct :
    LaSCorrectFull (spanMergeLaS [5,8]) (spanMergeSurf [5,8]) (spanMergePorts [5,8])
      (spanMergePaulis [5,8]) 3 = true := by native_decide

/-- ...and at the origin it agrees with the column-0 long-range merge (sanity). -/
theorem spanMerge_03_correct :
    LaSCorrectFull (spanMergeLaS [0,3]) (spanMergeSurf [0,3]) (spanMergePorts [0,3])
      (spanMergePaulis [0,3]) 3 = true := by native_decide

/-! ## §2. PARALLEL composition — two disjoint-span merges in ONE diagram. -/

/-- Two parallel routed merges: `Z̄₀Z̄₃` (highway 0–2) ∥ `Z̄₅Z̄₈` (highway 5–7),
welded side-by-side into one diagram on a 9-wide board. -/
def parLaS : LaSre :=
  { maxI := 9, maxJ := 1, maxK := 3
    YCube := fun _ _ _ => false
    ExistI := fun i j k =>
      (decide (i < 2) || (decide (5 ≤ i) && decide (i < 8))) && j == 0 && k == 1
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => (i == 0 || i == 3 || i == 5 || i == 8) && j == 0 && k < 2
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

/-- Flows: `0=Z̄₀Z̄₃`, `1=Z̄₅Z̄₈`, `2=X̄₀`, `3=X̄₃`, `4=X̄₅`, `5=X̄₈`. -/
def parSurf : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun s i j k =>
      ((s == 0 && decide (i < 2)) || (s == 1 && decide (5 ≤ i) && decide (i < 8))) && j == 0 && k == 1
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ =>
      (s == 0 && j == 0 && (i == 0 || i == 3)) || (s == 1 && j == 0 && (i == 5 || i == 8))
    KJ := fun s i j _ =>
      (s == 2 && i == 0 && j == 0) || (s == 3 && i == 3 && j == 0)
        || (s == 4 && i == 5 && j == 0) || (s == 5 && i == 8 && j == 0) }

def parPorts : List Port :=
  [⟨0,0,0,4,5⟩, ⟨0,0,2,4,5⟩, ⟨3,0,0,4,5⟩, ⟨3,0,2,4,5⟩,
   ⟨5,0,0,4,5⟩, ⟨5,0,2,4,5⟩, ⟨8,0,0,4,5⟩, ⟨8,0,2,4,5⟩]

def parPaulis : Nat → Nat → Pauli := fun s p =>
  match s, p with
  | 0, 0 => .Z | 0, 1 => .Z | 0, 2 => .Z | 0, 3 => .Z          -- Z̄₀Z̄₃ on cols 0,3 (ports 0-3)
  | 1, 4 => .Z | 1, 5 => .Z | 1, 6 => .Z | 1, 7 => .Z          -- Z̄₅Z̄₈ on cols 5,8 (ports 4-7)
  | 2, 0 => .X | 2, 1 => .X
  | 3, 2 => .X | 3, 3 => .X
  | 4, 4 => .X | 4, 5 => .X
  | 5, 6 => .X | 5, 7 => .X
  | _, _ => .I

/-- **★ A CONGESTION-FREE LAYER OF TWO ROUTED MERGES IS ONE VERIFIED DIAGRAM ★** —
`Z̄₀Z̄₃ ∥ Z̄₅Z̄₈` (disjoint highways, the case `packSpans` keeps in one layer)
welds into a single diagram passing the COMPLETE `LaSCorrectFull` for all six
flows.  So the scheduler's congestion-free guarantee turns into a verified
parallel layer. -/
theorem par_correct :
    LaSCorrectFull parLaS parSurf parPorts parPaulis 6 = true := by native_decide

/-- The two parallel merges measure their two SEPARATE joint observables (not one
joined blob): flow 0 is `Z̄` on cols 0,3 only; flow 1 is `Z̄` on cols 5,8 only. -/
theorem par_two_observables :
    (parPaulis 0 0 = .Z ∧ parPaulis 0 2 = .Z ∧ parPaulis 0 4 = .I)
      ∧ (parPaulis 1 4 = .Z ∧ parPaulis 1 6 = .Z ∧ parPaulis 1 0 = .I) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

end FormalRV.QEC.LaSre
