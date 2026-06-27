/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Headline
  ──────────────────────────────────────────────────────
  Submodule of `ParallelDepth` (split out for per-file compile memory).
  Contains §10: the headline that the runway adder's parallel depth is constant
  in `k` (`parallelDepth_runwayAddK_eq_max` … `parallelDepth_runwayAddK_eq`).

  Re-exported VERBATIM from the original `ParallelDepth.lean`; the declarations,
  statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Shift

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

/-! ## §10. THE HEADLINE: runway parallel depth is constant in `k`. -/

/-- **THE STRUCTURAL FACT (max, not sum).**  Adding one more disjoint segment
    does not ADD to the parallel depth — it is the `max` with the new segment's
    depth.  This alone proves no segment serializes against the others. -/
theorem parallelDepth_runwayAddK_eq_max (gSep k : Nat) :
    parallelDepth (runwayAddK gSep (k + 1))
      = max (parallelDepth (runwayAddK gSep k)) (parallelDepth (segAdd gSep k)) := by
  rw [show runwayAddK gSep (k + 1)
        = Gate.seq (runwayAddK gSep k) (segAdd gSep k) from rfl]
  exact parallelDepth_seq_disjoint _ _ (runwayAddK_segAdd_disjoint gSep k)

/-- **HEADLINE — the realized depth advantage.**  For `k ≥ 1`, the ASAP parallel
    depth of the `k`-segment oblivious-carry-runway adder equals ONE segment's
    parallel depth, INDEPENDENT of `k`.  The `k` disjoint segments run
    concurrently, so adding more segments never increases the depth.  (Achieved
    via SHIFT-INVARIANCE: `parallelDepth_segAdd_const`, every segment has the same
    depth as the base-`0` segment.) -/
theorem parallelDepth_runwayAddK_eq (gSep : Nat) :
    ∀ k, 1 ≤ k →
      parallelDepth (runwayAddK gSep k)
        = parallelDepth (cuccaroAdder.circuit (gSep + 1) (segBase gSep 0)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- base case k = 1: runwayAddK gSep 1 = seq I (segAdd gSep 0).
        subst hm
        rw [parallelDepth_runwayAddK_eq_max]
        -- parallelDepth (runwayAddK gSep 0) = parallelDepth I = 0.
        have h0 : parallelDepth (runwayAddK gSep 0) = 0 := by
          show parallelDepth Gate.I = 0
          rfl
        rw [h0, parallelDepth_segAdd_const, Nat.zero_max]
      · -- inductive step m ≥ 1.
        rw [parallelDepth_runwayAddK_eq_max, ih hm, parallelDepth_segAdd_const]
        exact Nat.max_self _

end FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
