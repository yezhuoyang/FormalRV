/-
  FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedMarginal — F1: the marginal isometry
  of the two-register embedding E₂ (the `E_phys_marginal` analogue for E₂).
  ════════════════════════════════════════════════════════════════════════════

  The generic Route-2 engine (`CosetRoute2Consolidated.ApproxCosetOrbitShift`) requires of its
  `E_phys` parameter the field `hmarg`: `E_phys` preserves the ideal's per-outcome Born marginal.
  This file proves the DATA-FACTOR core of that for the two-register embedding
    `E₂data ψ y = ∑_z (cosetInputVec z 0)(y) · ψ(z)`   (column z = the faithful state cosetInputVec z 0):

    ∑_y ‖E₂data ψ y‖²  =  ∑_z ‖ψ z‖²      (for ψ supported on canonical residues z < N).

  This is exactly the `CosetEphys.E_phys_marginal` statement with `cosetEmbedMat` replaced by E₂'s
  columns — proven by the SAME structure (used only as a template), but on the NEW orthonormal
  family: at most one canonical column is nonzero at a given row (A3 disjoint support,
  `cosetInputVec_support_disjoint`), and each column has unit Born mass (T1
  `cosetInputVec_normalized`).  NO `cosetEmbedMat`, NO `prepB`.

  The `I_phase ⊗ E₂data` wrap to the full Shor-register `hmarg` shape
  (`prob_partial_meas (E₂ · ideal) = prob_partial_meas ideal`) is the mechanical `E_phys_acts`-style
  completion (mirrors `CosetEphys.E_phys_marginal`'s outer layer); this file is the isometry core.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Embedding.Proof.InPlaceTwoRegEmbedProbe

namespace FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedMarginal

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm (cosetInputVec_normalized)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedProbe (cosetInputVec_support_disjoint)

/-- **The two-register data embedding E₂** (column `z` = the faithful state `cosetInputVec z 0`,
    whose b-block is `cosetState 0`). -/
noncomputable def E2data (w bits N cm : Nat)
    (ψ : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ) :
    Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ :=
  fun y _ => ∑ z : Fin (2 ^ cosetDim w bits), cosetInputVec w bits N cm z.val 0 y 0 * ψ z 0

/-- `normSq` distributes over a Finset sum with at most one nonzero summand (cross terms vanish).
    Local copy of the (private) `CosetEphys.normSq_sum_canon_pairwise`. -/
private theorem normSq_sum_canon_pairwise {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → f a = 0 ∨ f b = 0) :
    Complex.normSq (∑ i ∈ s, f i) = ∑ i ∈ s, Complex.normSq (f i) := by
  classical
  set t : Finset ι := s.filter (fun i => f i ≠ 0) with ht
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hcard : t.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [ht, Finset.mem_filter] at ha hb
    by_contra hab
    rcases hpair a ha.1 b hb.1 hab with h | h
    · exact ha.2 h
    · exact hb.2 h
  have hsum1 : ∑ i ∈ s, f i = ∑ i ∈ t, f i := by
    symm; apply Finset.sum_subset hts
    intro i _ hi
    simp only [ht, Finset.mem_filter, not_and, not_not] at hi
    exact hi (by assumption)
  have hsum2 : ∑ i ∈ s, Complex.normSq (f i) = ∑ i ∈ t, Complex.normSq (f i) := by
    symm; apply Finset.sum_subset hts
    intro i _ hi
    simp only [ht, Finset.mem_filter, not_and, not_not] at hi
    rw [hi (by assumption), Complex.normSq_zero]
  rw [hsum1, hsum2]
  rcases Nat.eq_zero_or_pos t.card with h0 | h1
  · rw [Finset.card_eq_zero] at h0; rw [h0]; simp
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp h1
    have hseq : t = {a} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun b hb => Finset.card_le_one.mp hcard b hb a ha⟩
    rw [hseq, Finset.sum_singleton, Finset.sum_singleton]

/-- **F1 — E₂ marginal isometry (data-factor core).**  For a state `ψ` supported on canonical
    residues `z < N`, the two-register embedding `E₂data` preserves the total Born mass:
    `∑_y ‖E₂data ψ y‖² = ∑_z ‖ψ z‖²`.  The `hmarg` field of `ApproxCosetOrbitShift` is the
    `I_phase ⊗ ·` wrap of this.  Proven from A3 (disjoint columns ⇒ at most one nonzero per row)
    + T1 (each column has unit Born mass) — NOT from `cosetEmbedMat`. -/
theorem E2data_marginal (w bits numWin N cm : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (ψ : Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ)
    (hsupp : ∀ z : Fin (2 ^ cosetDim w bits), N ≤ z.val → ψ z 0 = 0) :
    (∑ y : Fin (2 ^ cosetDim w bits), Complex.normSq (E2data w bits N cm ψ y 0))
      = ∑ z : Fin (2 ^ cosetDim w bits), Complex.normSq (ψ z 0) := by
  classical
  set canon : Finset (Fin (2 ^ cosetDim w bits)) := Finset.univ.filter (fun z => z.val < N)
    with hcanon
  -- per-row collapse: at most one canonical column contributes
  have hcollapse : ∀ y : Fin (2 ^ cosetDim w bits),
      Complex.normSq (E2data w bits N cm ψ y 0)
        = ∑ z ∈ canon, Complex.normSq (cosetInputVec w bits N cm z.val 0 y 0)
            * Complex.normSq (ψ z 0) := by
    intro y
    have hrestrict : E2data w bits N cm ψ y 0
        = ∑ z ∈ canon, cosetInputVec w bits N cm z.val 0 y 0 * ψ z 0 := by
      unfold E2data
      symm; apply Finset.sum_subset (Finset.subset_univ canon)
      intro z _ hz
      simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hz
      rw [hsupp z hz, mul_zero]
    rw [hrestrict]
    have hpair : ∀ a ∈ canon, ∀ b ∈ canon, a ≠ b →
        cosetInputVec w bits N cm a.val 0 y 0 * ψ a 0 = 0
          ∨ cosetInputVec w bits N cm b.val 0 y 0 * ψ b 0 = 0 := by
      intro a ha b hb hab
      simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_cases hya : cosetInputVec w bits N cm a.val 0 y 0 = 0
      · exact Or.inl (by rw [hya, zero_mul])
      · by_cases hyb : cosetInputVec w bits N cm b.val 0 y 0 = 0
        · exact Or.inr (by rw [hyb, zero_mul])
        · exact absurd (cosetInputVec_support_disjoint w bits N cm a.val b.val hN ha hb
            (fun h => hab (Fin.ext h)) y hya hyb) (not_false)
    rw [normSq_sum_canon_pairwise canon _ hpair]
    exact Finset.sum_congr rfl (fun z _ => Complex.normSq_mul _ _)
  -- assemble: swap sums, each column has unit Born mass (T1)
  rw [Finset.sum_congr rfl (fun y _ => hcollapse y), Finset.sum_comm]
  have hcol : ∀ z ∈ canon,
      (∑ y : Fin (2 ^ cosetDim w bits), Complex.normSq (cosetInputVec w bits N cm z.val 0 y 0)
          * Complex.normSq (ψ z 0)) = Complex.normSq (ψ z 0) := by
    intro z hz
    simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hid : (2 ^ cm - 1) * N + N = 2 ^ cm * N := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left N (Nat.two_pow_pos cm))]
    have hlt : z.val + (2 ^ cm - 1) * N < 2 ^ bits := by
      have hzlt : z.val + (2 ^ cm - 1) * N < (2 ^ cm - 1) * N + N := by omega
      rw [hid] at hzlt
      exact lt_of_lt_of_le hzlt hMN
    have hnorm : (∑ y : Fin (2 ^ cosetDim w bits),
        Complex.normSq (cosetInputVec w bits N cm z.val 0 y 0)) = 1 := by
      have h := cosetInputVec_normalized w bits numWin N cm z.val hw hbits hN hlt
      unfold bornWeightOn at h
      exact h
    rw [← Finset.sum_mul, hnorm, one_mul]
  rw [Finset.sum_congr rfl hcol]
  apply Finset.sum_subset (Finset.subset_univ canon)
  intro z _ hz
  simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hz
  rw [hsupp z hz, Complex.normSq_zero]

end FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedMarginal
