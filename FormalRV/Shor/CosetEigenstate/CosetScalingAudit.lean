/-
  FormalRV.Shor.CosetEigenstate.CosetScalingAudit — the ADVERSARIAL step-1 sanity check
  for the approximate orbit-shift phase: the literal `v ↦ c·v` coset multiplier does NOT
  preserve the coset runway (OPTION B, proven).
  ════════════════════════════════════════════════════════════════════════════

  Before attempting an approximate-orbit-shift bound, this file runs the pure ℕ/Finset
  support audit NEUTRALLY (no small-deviation assumption, no `uc_eval`) and finds the
  hoped-for approximation is FALSE for the literal scaling map.

  Setup.  The coset window of `k` (step `N`, `M = 2^m` reps) is `{k + j·N | j < M}`.  The
  literal in-place coset multiplier acts as `v ↦ c·v` (`CuccaroPhysCoset`/`cosetMulGate`),
  so the image is `{c·(k+j·N) | j < M}`.  Writing `c·k = r + q·N` (`r = c·k % N`,
  `q = c·k / N`):

    * `scaled_image_eq` — `c·(k+j·N) = r + (q + c·j)·N`.  So the image element has residue
      `r` and QUOTIENT INDEX `q + c·j` — an arithmetic progression of STEP `c`.
    * `overlap_quotient_card_le` — the image quotient indices that land back in the
      canonical coset window of `r` (indices `{0,…,M-1}`) number `≤ (M-1)/c + 1 ≈ M/c`.
    * `overlap_sparse_of_two_le` — for `c ≥ 2`, `2·overlap ≤ M + 1`: at most about HALF
      (in general `≈ M/c`) of the `M` window indices survive.

  ⚠ CONCLUSION — OPTION B (the naive approximate-shift theorem is FALSE).  The Born overlap
  between the scaled coset and the canonical coset is `overlap / M ≈ 1/c`, BOUNDED AWAY FROM
  1 for `c ≥ 2`.  So the literal `v ↦ c·v` map does NOT approximately preserve the coset
  runway (the spacing coarsens `N ↦ cN`).  Therefore:

    • the `ApproxCosetOrbitShift` frontier (CosetRoute2Consolidated) is NOT satisfiable with
      SMALL `ε` by the literal `cosetMulGate` — its `hstep` would force `ε = Ω(1)`, making
      the success bound `P ≥ P_ideal − 2ε` vacuous;
    • the remaining frontier is therefore NOT "prove a small-boundary bound" — it is an
      ORACLE-MODEL correction: the coset multiplier must be RUNWAY-PRESERVING by
      construction (`k + j·N ↦ (c·k mod N) + j·N`, step `N` kept), NOT the literal `v ↦ c·v`.

  The verified facts below are neutral arithmetic; the conclusion is what they force.

  Self-contained Mathlib lemmas.  Kernel-clean: no `sorry`, no `native_decide`, no axioms
  beyond the prelude.  De-risked via 3 parallel verified attempts (all concluded OPTION B).
-/
import Mathlib

namespace FormalRV.Shor.CosetEigenstate.CosetScalingAudit

open scoped BigOperators

/-- **The EXACT support image identity.**  The literal coset-multiplier map `v ↦ c·v` sends
    the runway element `k + j·N` to residue `(c·k)%N` with quotient index `(c·k)/N + c·j` —
    an arithmetic progression of STEP `c` in the quotient index. -/
theorem scaled_image_eq (c k j N : Nat) :
    c * (k + j * N) = (c * k) % N + ((c * k) / N + c * j) * N := by
  have h := Nat.div_add_mod (c * k) N
  -- h : N * (c * k / N) + (c * k) % N = c * k
  nlinarith [h, Nat.mul_add c k (j * N), Nat.add_mul (c * k / N) (c * j) N]

/-- **The SPARSE overlap cardinality bound.**  The image quotient indices `j < M` that land
    back in the canonical coset window `{0,…,M-1}` (i.e. `q + c·j < M`, `q = (c·k)/N`) number
    at most `(M-1)/c + 1 ≈ M/c`. -/
theorem overlap_quotient_card_le (c M q : Nat) (hc : 0 < c) :
    ((Finset.range M).filter (fun j => q + c * j < M)).card ≤ (M - 1) / c + 1 := by
  apply le_trans (Finset.card_le_card (s := (Finset.range M).filter (fun j => q + c * j < M))
    (t := Finset.range ((M - 1) / c + 1)) ?_)
  · rw [Finset.card_range]
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨_, hlt⟩ := hj
    rw [Finset.mem_range]
    have hcj : c * j ≤ M - 1 := by omega
    have hjc : j * c ≤ M - 1 := by rw [Nat.mul_comm] at hcj; exact hcj
    have : j ≤ (M - 1) / c := (Nat.le_div_iff_mul_le hc).mpr hjc
    omega

/-- **The BAD-NEWS sparsity for `c ≥ 2`.**  For `c ≥ 2` the overlap is at most about half of
    `M`: `2·overlap ≤ M + 1` (and `≈ M/c` in general) — so it is NOT `M − O(c)`.  This is
    what makes the literal `v ↦ c·v` map fail to preserve the coset (OPTION B). -/
theorem overlap_sparse_of_two_le (c M q : Nat) (hc : 2 ≤ c) :
    2 * ((Finset.range M).filter (fun j => q + c * j < M)).card ≤ M + 1 := by
  have hc0 : 0 < c := by omega
  have h2 : ((Finset.range M).filter (fun j => q + c * j < M)).card ≤ (M - 1) / c + 1 :=
    overlap_quotient_card_le c M q hc0
  have hdiv : (M - 1) / c ≤ (M - 1) / 2 := Nat.div_le_div_left hc (by norm_num)
  have hself : (M - 1) / 2 * 2 ≤ M - 1 := Nat.div_mul_le_self (M - 1) 2
  have hcardM : ((Finset.range M).filter (fun j => q + c * j < M)).card ≤ M := by
    apply le_trans (Finset.card_filter_le _ _)
    rw [Finset.card_range]
  revert h2 hdiv hself hcardM
  generalize (M - 1) / c = A
  generalize (M - 1) / 2 = B
  intro h2 hdiv hself hcardM
  omega

end FormalRV.Shor.CosetEigenstate.CosetScalingAudit
