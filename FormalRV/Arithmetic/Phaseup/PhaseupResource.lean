/-
  FormalRV.Arithmetic.Phaseup.PhaseupResource
  ─────────────────────────────────────────────
  COST for the reusable phaseup gadget — and the √-ADVANTAGE as a THEOREM.

  Phaseup is a DIAGONAL `BaseUCom`, which carries no T-counter; following the
  `PhaseLookupFixup`/`SplitPhaseFixup` convention, the Toffoli count lives on the
  literal Gate-level twin `phaseupSkeleton` (same one-hot reads + lo-walk
  classical skeleton; its CZ leaves are Clifford and contribute no T).

  ## The point of the gadget: the SELECT-SWAP √-cost

      `toffoli_phaseup … = 4·(2^w1 − 1) + 2·(2^w2 − 1)`   (the split count)
      `toffoli_phaseupFull w = 2·(2^w − 1)`               (the full table read)

  and the SPLIT BEATS THE FULL LOOKUP — `phaseup_toffoli_sqrt`:

      `4·(2^w1 − 1) + 2·(2^w2 − 1)  ≤  2·(2^(w1+w2) − 1)`   for `w2 ≥ 1`,

  strictly `<` once both halves are real (`w1 ≥ 1, w2 ≥ 2`), and at the balanced
  split `w1 = w2 = w/2` the count is `≈ 4·(2^(w/2) − 1)` — the `O(√(2^w))`
  SELECT-SWAP advantage Gidney 2025 charges to the phaseup subroutine.

  Every count and inequality REUSES the verified `SplitPhaseFixup` skeleton
  lemmas; this file only restates them under the gadget's public names.

  Refs: Gidney 2025 (phaseup, √(2^w) SELECT-SWAP); proof reuse from
  `Shor.SplitPhaseFixup`.
-/
import FormalRV.Arithmetic.Phaseup.PhaseupDef

namespace FormalRV.Arithmetic.Phaseup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.PhaseLookupFixup
open FormalRV.Shor.SplitPhaseFixup

noncomputable section

/-! ## §1. The counts. -/

/-- **★ Toffoli count of phaseup — the SELECT-SWAP √-cost.**
    `4·(2^w1 − 1) + 2·(2^w2 − 1)` (two one-hot reads + the lo-walk skeleton),
    i.e. `O(2^(w/2))` at the balanced split.  Reuses
    `toffoliCount_splitPhaseLookupSkeleton`. -/
theorem toffoli_phaseup (w1 w2 base : Nat) :
    toffoliCount (phaseupSkeleton w1 w2 base)
      = 4 * (2 ^ w1 - 1) + 2 * (2 ^ w2 - 1) :=
  toffoliCount_splitPhaseLookupSkeleton w1 w2 base

/-- Toffoli count of phaseup, closed form: `4·2^w1 + 2·2^w2 − 6`. -/
theorem toffoli_phaseup_closed (w1 w2 base : Nat) :
    toffoliCount (phaseupSkeleton w1 w2 base) = 4 * 2 ^ w1 + 2 * 2 ^ w2 - 6 :=
  toffoliCount_splitPhaseLookupSkeleton_closed w1 w2 base

/-- **Toffoli count of the UNSPLIT phaseup — the full table read.**
    `2·(2^w − 1)`.  Reuses `toffoliCount_phaseLookupSkeleton`. -/
theorem toffoli_phaseupFull (w : Nat) :
    toffoliCount (phaseupFullSkeleton w) = 2 * (2 ^ w - 1) :=
  toffoliCount_phaseLookupSkeleton w

/-! ## §2. The √-advantage — the VALUE of the gadget, as a theorem. -/

/-- **★ HEADLINE — the phaseup SELECT-SWAP √-advantage.**  Whenever the lo half is
    nonempty (`w2 ≥ 1`), the split phaseup costs NO MORE than the full table read:

        `toffoli_phaseup (w1, w2)  ≤  toffoli_phaseupFull (w1 + w2)`,
        i.e. `4·(2^w1 − 1) + 2·(2^w2 − 1)  ≤  2·(2^(w1+w2) − 1)`.

    This is the paper's `√(2^w)` SELECT-SWAP claim: the address-split lookup
    replaces the linear `2^w` table read by `O(2^w1 + 2^w2)`.  Reuses
    `toffoliCount_split_le_unsplit`. -/
theorem phaseup_toffoli_sqrt (w1 w2 base : Nat) (hw2 : 1 ≤ w2) :
    toffoliCount (phaseupSkeleton w1 w2 base)
      ≤ toffoliCount (phaseupFullSkeleton (w1 + w2)) :=
  toffoliCount_split_le_unsplit w1 w2 base hw2

/-- **The √-advantage is STRICT** once both halves are real (`w1 ≥ 1, w2 ≥ 2`):
    the split phaseup is strictly cheaper than the full table read.  Reuses
    `toffoliCount_split_lt_unsplit`. -/
theorem phaseup_toffoli_sqrt_strict (w1 w2 base : Nat) (hw1 : 1 ≤ w1) (hw2 : 2 ≤ w2) :
    toffoliCount (phaseupSkeleton w1 w2 base)
      < toffoliCount (phaseupFullSkeleton (w1 + w2)) :=
  toffoliCount_split_lt_unsplit w1 w2 base hw1 hw2

/-- **The balanced-split headline** — at `w1 = w2 = w/2` (any `w = 2k ≥ 4`) the
    phaseup is STRICTLY cheaper than the full table read.  Here the count is
    `4·(2^k − 1) + 2·(2^k − 1) = 6·(2^k − 1) ≈ 6·2^(w/2) = O(√(2^w))`, vs the
    full `2·(2^(2k) − 1) = O(2^w)`.  Reuses `toffoliCount_split_halves_lt_unsplit`. -/
theorem phaseup_toffoli_sqrt_balanced (k base : Nat) (hk : 2 ≤ k) :
    toffoliCount (phaseupSkeleton k k base)
      < toffoliCount (phaseupFullSkeleton (k + k)) :=
  toffoliCount_split_halves_lt_unsplit k base hk

/-- The balanced-split count is exactly `6·(2^k − 1)` — `O(√(2^(2k)))`. -/
theorem toffoli_phaseup_balanced (k base : Nat) :
    toffoliCount (phaseupSkeleton k k base) = 6 * (2 ^ k - 1) := by
  rw [toffoli_phaseup]; ring

end -- noncomputable section

end FormalRV.Arithmetic.Phaseup
