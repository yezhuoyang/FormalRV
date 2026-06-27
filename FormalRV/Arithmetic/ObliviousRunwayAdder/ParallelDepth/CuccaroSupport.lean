/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.CuccaroSupport
  ──────────────────────────────────────────────────────
  Submodule of `ParallelDepth` (split out for per-file compile memory).
  Contains §6–§7: the Cuccaro support-containment bounds
  (`supp_cuccaro_maj_chain` … `supp_cuccaro_subset`) and the runway-segment
  support/disjointness lemmas (`supp_segAdd_subset` … `runwayAddK_segAdd_disjoint`).

  Re-exported VERBATIM from the original `ParallelDepth.lean`; the declarations,
  statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.Scheduler

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

/-! ## §6. Support of the Cuccaro circuit lies in its block. -/

open FormalRV.BQAlgo in
/-- A two-sided support bound: every qubit of `cuccaro_maj_chain n q` lies in
    `[q, q + 2n + 1)` (= `[q, q + span n)`). -/
theorem supp_cuccaro_maj_chain (n q : Nat) :
    ∀ p, p ∈ supp (cuccaro_maj_chain n q) → q ≤ p ∧ p < q + 2 * n + 1 := by
  induction n generalizing q with
  | zero => intro p hp; simp [cuccaro_maj_chain, supp] at hp
  | succ k ih =>
      intro p hp
      -- chain (k+1) q = seq (MAJ q (q+1) (q+2)) (chain k (q+2))
      rw [show cuccaro_maj_chain (k + 1) q
            = Gate.seq (cuccaro_MAJ q (q + 1) (q + 2)) (cuccaro_maj_chain k (q + 2))
          from rfl] at hp
      simp only [supp, List.mem_append] at hp
      rcases hp with hp | hp
      · -- MAJ q (q+1) (q+2) = seq (CX (q+2) (q+1)) (seq (CX (q+2) q) (CCX q (q+1) (q+2)))
        unfold cuccaro_MAJ at hp
        simp only [supp, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hp
        omega
      · have := ih (q + 2) p hp; omega

open FormalRV.BQAlgo in
/-- Every qubit of `cuccaro_uma_chain_reverse n q` lies in `[q, q + 2n + 1)`. -/
theorem supp_cuccaro_uma_chain_reverse (n q : Nat) :
    ∀ p, p ∈ supp (cuccaro_uma_chain_reverse n q) → q ≤ p ∧ p < q + 2 * n + 1 := by
  induction n generalizing q with
  | zero => intro p hp; simp [cuccaro_uma_chain_reverse, supp] at hp
  | succ k ih =>
      intro p hp
      rw [show cuccaro_uma_chain_reverse (k + 1) q
            = Gate.seq (cuccaro_uma_chain_reverse k (q + 2))
                       (cuccaro_UMA q (q + 1) (q + 2))
          from rfl] at hp
      simp only [supp, List.mem_append] at hp
      rcases hp with hp | hp
      · have := ih (q + 2) p hp; omega
      · unfold cuccaro_UMA at hp
        simp only [supp, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hp
        omega

open FormalRV.BQAlgo in
/-- **Support of the Cuccaro `n`-bit adder is contained in its block.**
    Every qubit it touches lies in `[base, base + (2n+1)) = [base, base + span n)`. -/
theorem supp_cuccaro_subset (n base : Nat) :
    ∀ p, p ∈ supp (cuccaroAdder.circuit n base) → base ≤ p ∧ p < base + (2 * n + 1) := by
  intro p hp
  -- circuit n base = cuccaro_n_bit_adder_full n base = seq maj_chain uma_chain_reverse
  rw [show cuccaroAdder.circuit n base = cuccaro_n_bit_adder_full n base from rfl] at hp
  rw [show cuccaro_n_bit_adder_full n base
        = Gate.seq (cuccaro_maj_chain n base) (cuccaro_uma_chain_reverse n base)
      from rfl] at hp
  simp only [supp, List.mem_append] at hp
  rcases hp with hp | hp
  · have := supp_cuccaro_maj_chain n base p hp; omega
  · have := supp_cuccaro_uma_chain_reverse n base p hp; omega

/-! ## §7. Runway-segment support & disjointness. -/

/-- `segAdd gSep m` (a width-`(gSep+1)` Cuccaro at `segBase gSep m`) touches only
    qubits in its segment block `[segBase m, segBase m + (2·gSep+3))`. -/
theorem supp_segAdd_subset (gSep m : Nat) :
    ∀ p, p ∈ supp (segAdd gSep m) →
      segBase gSep m ≤ p ∧ p < segBase gSep m + (2 * gSep + 3) := by
  intro p hp
  unfold segAdd at hp
  have := supp_cuccaro_subset (gSep + 1) (segBase gSep m) p hp
  -- 2*(gSep+1)+1 = 2*gSep+3.
  constructor
  · exact this.1
  · have h2 : 2 * (gSep + 1) + 1 = 2 * gSep + 3 := by ring
    omega

/-- `runwayAddK gSep k` (segments `0…k-1`) touches only qubits strictly below
    `segBase gSep k = k·stride`. -/
theorem supp_runwayAddK_lt (gSep : Nat) :
    ∀ (k : Nat) p, p ∈ supp (runwayAddK gSep k) → p < segBase gSep k := by
  intro k
  induction k with
  | zero => intro p hp; simp [runwayAddK, supp] at hp
  | succ m ih =>
      intro p hp
      rw [show runwayAddK gSep (m + 1)
            = Gate.seq (runwayAddK gSep m) (segAdd gSep m) from rfl] at hp
      simp only [supp, List.mem_append] at hp
      have hbase : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
        unfold segBase segStride; ring
      rcases hp with hp | hp
      · have := ih p hp
        -- segBase m ≤ segBase (m+1).
        have hmono : segBase gSep m ≤ segBase gSep (m + 1) := by omega
        omega
      · have := supp_segAdd_subset gSep m p hp; omega

/-- **Segment disjointness.**  `runwayAddK gSep k` and `segAdd gSep k` touch no
    common qubit: the former lives below `segBase k`, the latter at or above it. -/
theorem runwayAddK_segAdd_disjoint (gSep k : Nat) :
    ∀ x, x ∈ supp (runwayAddK gSep k) → x ∉ supp (segAdd gSep k) := by
  intro x hx hxseg
  have h1 := supp_runwayAddK_lt gSep k x hx
  have h2 := supp_segAdd_subset gSep k x hxseg
  omega

end FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth
