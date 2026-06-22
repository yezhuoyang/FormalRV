/-
  FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedIsometry — F1 (engine-facing form):
  the E₂ canonical-residue isometry, in the EXACT shape `physCosetEmbed_isometry` occupies.
  ════════════════════════════════════════════════════════════════════════════

  `ApproxCosetOrbitShift.hmarg` (the prob_partial_meas marginal-preservation field) is, for the
  single-register embedding, discharged from `PhysEmbedMarginal.physCosetEmbed_isometry`:

      bornWeightOn (fun i => ∑_{w<N} α_w · physCosetState w i) univ = ∑_{w<N} ‖α_w‖².

  This file proves the EXACT E₂ analogue — same shape, with `physCosetState w` replaced by the
  faithful two-register column `cosetInputVec w 0`:

      bornWeightOn (fun i => ∑_{z<N} α_z · cosetInputVec z 0 i) univ = ∑_{z<N} ‖α_z‖².

  So E₂'s columns form an orthonormal family on canonical residues `z < N` — the marginal-isometry
  the generic Route-2 engine's `hmarg` needs, in the SAME interface shape the repo already uses.
  Proven by mirroring `physCosetEmbed_isometry`'s structure on the NEW family: at most one column
  is nonzero at a given row (A3 `cosetInputVec_support_disjoint`), each column has unit Born mass
  (T1 `cosetInputVec_normalized`).  NO `cosetEmbedMat`, NO `prepB`.

  REMAINING F1 (mechanical, identical to the cosetEmbedMat → hmarg path; convention locked by
  `physCosetEmbed_isometry`'s existing usage): wrap this into the `prob_partial_meas` `hmarg`
  shape by defining E₂ = `I_phase ⊗ ·` on the Shor register (`n=bits`, `anc=cosetAnc`) and applying
  `prob_partial_meas_basis_eq` per phase outcome — threading the `workDim_eq`/`cosetWork_dim_eq`
  data-factor cast.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Embedding.Proof.InPlaceTwoRegEmbedProbe

namespace FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedIsometry

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm (cosetInputVec_normalized)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedProbe (cosetInputVec_support_disjoint)

/-- **F1 (engine-facing) — E₂ canonical-residue isometry.**  The `physCosetEmbed_isometry` analogue
    for the two-register embedding: `∑_{z<N} α_z · cosetInputVec z 0` preserves total Born mass
    `∑_{z<N} ‖α_z‖²`.  This is the `hmarg`-feeding isometry, in the repo's own interface shape. -/
theorem cosetInputVec_embed_isometry (w bits numWin N cm : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits) (α : Nat → ℂ) :
    bornWeightOn
        (fun (i : Fin (2 ^ cosetDim w bits)) (_ : Fin 1) =>
          ∑ z ∈ Finset.range N, α z * cosetInputVec w bits N cm z 0 i 0) Finset.univ
      = ∑ z ∈ Finset.range N, Complex.normSq (α z) := by
  classical
  unfold bornWeightOn
  set f : Fin (2 ^ cosetDim w bits) → ℂ :=
    fun i => ∑ z ∈ Finset.range N, α z * cosetInputVec w bits N cm z 0 i 0 with hf
  -- per-row: at most one canonical column is nonzero at `i`
  have hper : ∀ i : Fin (2 ^ cosetDim w bits),
      Complex.normSq (f i)
        = ∑ z ∈ Finset.range N, Complex.normSq (α z)
            * Complex.normSq (cosetInputVec w bits N cm z 0 i 0) := by
    intro i
    by_cases hex : ∃ z ∈ Finset.range N, cosetInputVec w bits N cm z 0 i 0 ≠ 0
    · obtain ⟨z0, hz0r, hz0ne⟩ := hex
      rw [Finset.mem_range] at hz0r
      have hfi : f i = α z0 * cosetInputVec w bits N cm z0 0 i 0 := by
        rw [hf]
        apply Finset.sum_eq_single z0
        · intro z hz hzne
          by_cases hzi : cosetInputVec w bits N cm z 0 i 0 = 0
          · rw [hzi, mul_zero]
          · exact (cosetInputVec_support_disjoint w bits N cm z z0 hN (Finset.mem_range.mp hz)
              hz0r hzne i hzi hz0ne).elim
        · intro hni; rw [Finset.mem_range] at hni; exact absurd hz0r hni
      have hrhs : (∑ z ∈ Finset.range N, Complex.normSq (α z)
            * Complex.normSq (cosetInputVec w bits N cm z 0 i 0))
          = Complex.normSq (α z0) * Complex.normSq (cosetInputVec w bits N cm z0 0 i 0) := by
        apply Finset.sum_eq_single z0
        · intro z hz hzne
          by_cases hzi : cosetInputVec w bits N cm z 0 i 0 = 0
          · rw [hzi, Complex.normSq_zero, mul_zero]
          · exact (cosetInputVec_support_disjoint w bits N cm z z0 hN (Finset.mem_range.mp hz)
              hz0r hzne i hzi hz0ne).elim
        · intro hni; rw [Finset.mem_range] at hni; exact absurd hz0r hni
      rw [hfi, Complex.normSq_mul, hrhs]
    · simp only [not_exists, not_and, not_not] at hex
      have hfi : f i = 0 := by
        rw [hf]; exact Finset.sum_eq_zero (fun z hz => by rw [hex z hz, mul_zero])
      rw [hfi, Complex.normSq_zero]
      symm
      exact Finset.sum_eq_zero (fun z hz => by rw [hex z hz, Complex.normSq_zero, mul_zero])
  -- assemble: swap sums, each column has unit Born mass (T1)
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mem_range] at hz
  rw [← Finset.mul_sum]
  have hfit : z + (2 ^ cm - 1) * N < 2 ^ bits := by
    have hid : (2 ^ cm - 1) * N + N = 2 ^ cm * N := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left N (Nat.two_pow_pos cm))]
    have hlt : z + (2 ^ cm - 1) * N < (2 ^ cm - 1) * N + N := by omega
    rw [hid] at hlt
    exact lt_of_lt_of_le hlt hMN
  have hnorm : (∑ i : Fin (2 ^ cosetDim w bits),
      Complex.normSq (cosetInputVec w bits N cm z 0 i 0)) = 1 := by
    have h := cosetInputVec_normalized w bits numWin N cm z hw hbits hN hfit
    unfold bornWeightOn at h
    exact h
  rw [hnorm, mul_one]

end FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedIsometry
