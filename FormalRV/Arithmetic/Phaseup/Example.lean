/-
  FormalRV.Arithmetic.Phaseup.Example
  ─────────────────────────────────────
  Concrete demonstration of the reusable phaseup gadget on small cases.  We
  `#eval` the Toffoli counts of the split phaseup vs the full table read — showing
  the SELECT-SWAP √-advantage numerically (`phaseup_toffoli_sqrt`) — and verify
  both the counts and the diagonal phase action with `decide` / the proven
  `phaseup_diagonal_addr` on real inputs.

  Everything here is `#eval` / `decide` of verified, kernel-clean objects (no
  axioms, no `native_decide`).
-/
import FormalRV.Arithmetic.Phaseup

open FormalRV.Framework
open FormalRV.Shor.WindowedCircuit
open FormalRV.Arithmetic.Phaseup

noncomputable section

/-! ## §1. Toffoli counts — the split phaseup BEATS the full table read.

At address width `w = 4`, split as `w1 = w2 = 2` (one-hot block at `base = 9`):
  • split phaseup     `4·(2^2 − 1) + 2·(2^2 − 1) = 12 + 6 = 18` Toffoli,
  • full table read   `2·(2^4 − 1) = 30` Toffoli.
So the split is 18 vs 30 — the √(2^w) SELECT-SWAP advantage. -/

#eval IO.println s!"split phaseup  (w=4 as 2+2) : toffoli = {toffoliCount (phaseupSkeleton 2 2 9)} (full table read would be {toffoliCount (phaseupFullSkeleton 4)}; CHEAPER)"

/-! At a bigger width `w = 8`, split `w1 = w2 = 4`:
  • split  `4·15 + 2·15 = 90`,
  • full   `2·255 = 510`.
The advantage widens as `w` grows. -/
#eval IO.println s!"split phaseup  (w=8 as 4+4) : toffoli = {toffoliCount (phaseupSkeleton 4 4 17)} (full table read would be {toffoliCount (phaseupFullSkeleton 8)}; √-advantage)"

/-- Machine-checked counts (the same facts as `toffoli_phaseup` / `toffoli_phaseupFull`,
    here `decide`d numerically). -/
example : toffoliCount (phaseupSkeleton 2 2 9) = 18 := by decide
example : toffoliCount (phaseupFullSkeleton 4) = 30 := by decide
example : toffoliCount (phaseupSkeleton 4 4 17) = 90 := by decide
example : toffoliCount (phaseupFullSkeleton 8) = 510 := by decide

/-- The √-advantage, numerically: split < full at `w = 4` (split as 2+2). -/
example : toffoliCount (phaseupSkeleton 2 2 9)
    < toffoliCount (phaseupFullSkeleton (2 + 2)) :=
  phaseup_toffoli_sqrt_balanced 2 9 (by norm_num)

/-! ## §2. The diagonal phase action on real query states.

Layout at `w1 = w2 = 1, base = 5, dim = 7`: ctrl at 0, lo address at 1, lo ladder
at 2, hi address at 3, hi ladder at 4, one-hot wires at 5–6.  The phaseup is the
diagonal operator that stamps `(−1)^(F v)` when the address holds `v`. -/

/-- Phase ON: address holds `v = 2` (lo = 0, hi = 1), table `F = [· = 2]`
    ⟹ phaseup applies the phase `−1`.  Via the proven `phaseup_diagonal_addr`. -/
example :
    uc_eval (phaseup 7 (fun v => v == 2) 1 1 5)
        * f_to_vec 7 (fun p => p == 0 || p == 3)
      = (-1 : ℂ) • f_to_vec 7 (fun p => p == 0 || p == 3) := by
  have h := phaseup_diagonal_addr 7 1 1 5 (fun v => v == 2) 2
    (fun p => p == 0 || p == 3) (by norm_num) (by norm_num) (by norm_num) rfl
    (fun i hi => by interval_cases i <;> decide)
    (fun i hi => by interval_cases i <;> decide)
    (fun h hh => by interval_cases h <;> decide)
  simpa using h

/-- Phase OFF: address holds `v = 1` (lo = 1, hi = 0), table `F = [· = 2]`
    ⟹ phaseup is the identity (no phase). -/
example :
    uc_eval (phaseup 7 (fun v => v == 2) 1 1 5)
        * f_to_vec 7 (fun p => p == 0 || p == 1)
      = f_to_vec 7 (fun p => p == 0 || p == 1) := by
  have h := phaseup_diagonal_addr 7 1 1 5 (fun v => v == 2) 1
    (fun p => p == 0 || p == 1) (by norm_num) (by norm_num) (by norm_num) rfl
    (fun i hi => by interval_cases i <;> decide)
    (fun i hi => by interval_cases i <;> decide)
    (fun h hh => by interval_cases h <;> decide)
  simpa using h

end -- noncomputable section
