/-
  FormalRV.Shor.EncodingAgnostic — making Shor's success bound encoding-agnostic.

  The verified headline `Shor_correct_verified_no_modmult_axioms` is specialised
  to ORDER-FINDING: its `probability_of_success` sums `r_found(x)` (the
  continued-fraction post-processing) against the QPE measurement probability of
  outcome `x`.  The proof concentrates the probability on a set of "good" QPE
  peaks (`s_closest(k/r)` for `k` coprime to `r`) and lower-bounds the total.

  That concentration argument is NOT specific to order-finding.  This file
  extracts it as a reusable **peak-sum lower bound** (`success_ge_card_mul`) and
  bundles its hypotheses into an encoding-agnostic **`ShorPostProcessing`
  contract**: any algorithm (order-finding, Ekerå–Håstad short-DLP, …) that
  exhibits a set of accepted QPE peaks, each with probability `≥ p`, gets the
  success bound `≥ |peaks| · p` for free.  Order-finding is shown to instantiate
  the contract; Ekerå–Håstad would supply a different peak set / acceptance and
  the (lattice) post-processing success — without re-deriving the concentration.

  This is ADDITIVE: it does not modify the verified headline.
-/
import FormalRV.Shor.MainAlgorithm.SuccessProbability

namespace FormalRV.Shor.EncodingAgnostic

open scoped BigOperators
open FormalRV.SQIRPort

/-! ## §1. The keystone: a peak-sum lower bound (encoding-agnostic).

For any acceptance weighting `accept` and outcome probabilities `measProb` over
`[0, 2^m)`, a set `K` of accepted (`accept = 1`), each `≥ p`, contributes
`≥ |K|·p` to the total `∑ accept·measProb`.  This is the abstract core of the
Shor concentration argument. -/
theorem success_ge_card_mul {m : Nat} (accept measProb : Nat → ℝ) (p : ℝ)
    (K : Finset Nat)
    (h_measProb_nonneg : ∀ x, 0 ≤ measProb x)
    (h_accept_nonneg : ∀ x, 0 ≤ accept x)
    (h_K_sub : K ⊆ Finset.range (2 ^ m))
    (h_accept_one : ∀ x ∈ K, accept x = 1)
    (h_prob_ge : ∀ x ∈ K, p ≤ measProb x) :
    (K.card : ℝ) * p ≤ ∑ x ∈ Finset.range (2 ^ m), accept x * measProb x := by
  calc (K.card : ℝ) * p
      = ∑ _x ∈ K, p := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ K, measProb x := Finset.sum_le_sum (fun x hx => h_prob_ge x hx)
    _ = ∑ x ∈ K, accept x * measProb x :=
        Finset.sum_congr rfl (fun x hx => by rw [h_accept_one x hx, one_mul])
    _ ≤ ∑ x ∈ Finset.range (2 ^ m), accept x * measProb x :=
        Finset.sum_le_sum_of_subset_of_nonneg h_K_sub
          (fun x _ _ => mul_nonneg (h_accept_nonneg x) (h_measProb_nonneg x))

/-! ## §2. The pluggable post-processing contract.

A `ShorPostProcessing m` witness is what ANY Shor-style algorithm must exhibit
to inherit a success bound: outcome probabilities, a post-processing acceptance,
and a set of accepted peaks each concentrated with probability `≥ p`.  Its
`bound` is the encoding-agnostic success guarantee `≥ |peaks| · p`. -/
structure ShorPostProcessing (m : Nat) where
  /-- post-processing acceptance weighting on measurement outcomes. -/
  accept : Nat → ℝ
  /-- QPE measurement probability of each outcome. -/
  measProb : Nat → ℝ
  /-- the set of "good" peaks the algorithm relies on. -/
  peaks : Finset Nat
  /-- per-peak probability lower bound. -/
  p : ℝ
  measProb_nonneg : ∀ x, 0 ≤ measProb x
  accept_nonneg : ∀ x, 0 ≤ accept x
  peaks_sub : peaks ⊆ Finset.range (2 ^ m)
  accept_one : ∀ x ∈ peaks, accept x = 1
  prob_ge : ∀ x ∈ peaks, p ≤ measProb x

/-- **The encoding-agnostic success bound.**  Any post-processing witness yields
    total accepted probability `≥ |peaks| · p`. -/
theorem ShorPostProcessing.bound {m : Nat} (S : ShorPostProcessing m) :
    (S.peaks.card : ℝ) * S.p ≤ ∑ x ∈ Finset.range (2 ^ m), S.accept x * S.measProb x :=
  success_ge_card_mul S.accept S.measProb S.p S.peaks
    S.measProb_nonneg S.accept_nonneg S.peaks_sub S.accept_one S.prob_ge

/-! ## §3. Order-finding fits the contract.

The headline `probability_of_success` (order-finding) is exactly
`∑ r_found(x) · prob_partial_meas(x)`, so the keystone applies directly: for any
set `K` of outcomes that the continued-fraction post-processing accepts
(`r_found = 1`) and on which the QPE concentrates (`≥ p`), the success
probability is `≥ |K| · p`.  This is the reusable concentration step factored
out of `Shor_correct_var_conditional`; Ekerå–Håstad gets the analogue from the
same keystone with its own acceptance and peak set. -/
theorem probability_of_success_ge_peaks
    (a r N m n anc : Nat) (f : Nat → BaseUCom (n + anc))
    (K : Finset Nat) (p : ℝ)
    (h_K_sub : K ⊆ Finset.range (2 ^ m))
    (h_accept : ∀ x ∈ K, r_found x m r a N = 1)
    (h_qpe : ∀ x ∈ K,
      p ≤ prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f)) :
    (K.card : ℝ) * p ≤ probability_of_success a r N m n anc f := by
  unfold probability_of_success
  exact success_ge_card_mul (fun x => r_found x m r a N)
    (fun x => prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state m n anc f)) p K
    (fun _ => prob_partial_meas_nonneg _ _)
    (fun x => by show (0 : ℝ) ≤ r_found x m r a N; unfold r_found; split_ifs <;> norm_num)
    h_K_sub h_accept h_qpe

end FormalRV.Shor.EncodingAgnostic

