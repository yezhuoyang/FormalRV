/-
  FormalRV.Shor.CosetEigenstate.CosetFold — the fold-level coset-embedding agreement:
  `cosetState (r + q·N)` (unreduced) agrees with `E_data` of the canonical `cosetState r`
  off the symmetric-difference bad set.
  ════════════════════════════════════════════════════════════════════════════

  The concrete runway multiplier applies ordinary (non-modular) additions to the coset
  accumulator.  Off wrap, the unreduced result `cosetState (r + q·N)` (where `q` is the
  number of wraps `≤ T`) agrees with `E_data` of the canonical residue `cosetState r`.
  This file proves that fold-level off-bad agreement, with the bad set the SYMMETRIC
  DIFFERENCE of the two windows stated in the CANONICAL residue (`r`) coordinate — the
  representatives in exactly one window — NOT a naive union in a drifting coordinate.

    * `agree_off_trans` — the chaining primitive (off-bad agreements compose by union).
    * `cosetState_bornWeightOn_eq` — the coset Born weight on `B` is `|B ∩ window|/2^m`.
    * `cosetState_bornWeightOn_le` — hence `≤ |B|/2^m` (each rep carries `1/2^m`).
    * `cosetState_multiWrap_agree_off` — the unreduced `cosetState (r+q·N)` agrees with
      `cosetState r` OFF the window symmetric difference `B`, with each side's Born mass
      `≤ |B|/2^m`.  Off `B` every position is in both windows (amplitude `1/√2^m` each)
      or neither (`0` each), so the amplitudes agree exactly; on `B` the non-shared reps
      carry the deviation.

  QUANTITATIVE REFINEMENT (flagged): the tight per-side bound `≤ q/2^m` follows from
  `|B ∩ window| ≤ q` (the `q` non-shared boundary reps) — the symmetric-difference
  cardinality count, which combined with `CosetTableSum.idealAcc_cosetWindowConst`
  gives the windowed multiplier embedding `cosetState z ↦ E_data ((a·z) % N)` off bad
  with mass `≤ numWin/2^m` per side.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp

namespace FormalRV.Shor.CosetEigenstate.CosetFold

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState cosetState_normSq)
open FormalRV.Shor.CosetEigenstate.CosetClass (cosetWindow mem_cosetWindow)

/-- **Off-bad agreement TRANSITIVITY (the chaining primitive).**  If `A = B` off
    `bad1` and `B = C` off `bad2`, then `A = C` off `bad1 ∪ bad2` — so per-step
    boundary sets accumulate by union. -/
theorem agree_off_trans {dim : Nat} (A B C : QState dim) (bad1 bad2 : Finset (Fin dim))
    (h1 : ∀ i, i ∉ bad1 → A i 0 = B i 0) (h2 : ∀ i, i ∉ bad2 → B i 0 = C i 0) :
    ∀ i, i ∉ bad1 ∪ bad2 → A i 0 = C i 0 := by
  intro i hi
  rw [Finset.mem_union, not_or] at hi
  rw [h1 i hi.1, h2 i hi.2]

/-- The coset Born weight on a set `B` is `|B ∩ window| / 2^m`. -/
theorem cosetState_bornWeightOn_eq {dim N m a : Nat} (B : Finset (Fin dim)) :
    bornWeightOn (cosetState dim N m a) B
      = ((B.filter (· ∈ cosetWindow dim N m a)).card : ℝ) / 2 ^ m := by
  rw [bornWeightOn, Finset.sum_congr rfl (fun i _ => cosetState_normSq dim N m a i),
      Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- Hence the coset Born weight on `B` is at most `|B| / 2^m` (each rep carries
    `1/2^m`).  The tight refinement uses `|B ∩ window| ≤ q`. -/
theorem cosetState_bornWeightOn_le {dim N m a : Nat} (B : Finset (Fin dim)) :
    bornWeightOn (cosetState dim N m a) B ≤ (B.card : ℝ) / 2 ^ m := by
  rw [cosetState_bornWeightOn_eq]
  gcongr
  exact Finset.filter_subset _ B

/-- **THE FOLD-LEVEL COSET-EMBEDDING AGREEMENT (off bad).**  The unreduced coset state
    `cosetState (r + q·N)` agrees with `E_data` of the canonical residue `cosetState r`
    off the symmetric difference `B` of their windows, and each side carries Born mass
    `≤ |B|/2^m`.  Off `B`, every position is in both windows or neither, so the
    amplitudes agree exactly. -/
theorem cosetState_multiWrap_agree_off (dim N m r q : Nat) :
    ∃ B : Finset (Fin dim),
      (∀ i, i ∉ B → cosetState dim N m (r + q * N) i 0 = cosetState dim N m r i 0)
      ∧ bornWeightOn (cosetState dim N m (r + q * N)) B ≤ (B.card : ℝ) / 2 ^ m
      ∧ bornWeightOn (cosetState dim N m r) B ≤ (B.card : ℝ) / 2 ^ m := by
  classical
  set W1 : Finset (Fin dim) := Finset.univ.filter (· ∈ cosetWindow dim N m (r + q * N)) with hW1
  set W2 : Finset (Fin dim) := Finset.univ.filter (· ∈ cosetWindow dim N m r) with hW2
  refine ⟨(W1 \ W2) ∪ (W2 \ W1), ?_, cosetState_bornWeightOn_le _, cosetState_bornWeightOn_le _⟩
  intro i hi
  simp only [Finset.mem_union, Finset.mem_sdiff, hW1, hW2, Finset.mem_filter,
    Finset.mem_univ, true_and, not_or, not_and, not_not] at hi
  rw [cosetState, cosetState]
  by_cases h1 : i ∈ cosetWindow dim N m (r + q * N)
  · rw [if_pos h1, if_pos (hi.1 h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (hi.2 h2))]

end FormalRV.Shor.CosetEigenstate.CosetFold
