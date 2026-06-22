/-
  FormalRV.Shor.GidneyInPlace.InPlaceComposedMass
  ─────────────────────────────────────────────────
  PACKAGING checkpoint 2d (part 1 — transport + reduction): the index-space-correct
  reduction of the OUTPUT bad set's Born mass to the INPUT bad set's Born mass.

  The agree-off bad set `B` lives on OUTPUT basis indices `Fin (2^cosetDim)`; the input
  state `cosetInputVec x 0` has ≈ no mass there.  The correct statement measures the
  EVOLVED state's mass over `B`, and transports it (the permutation is a pushforward) to
  the INPUT state's mass over the PREIMAGE `σ.symm '' B`, then reduces to the input bad set:

      bornWeightOn (uc_eval(G)·input) B
        = bornWeightOn (permState σ.symm input) B        -- uc_eval_eq_permState
        = bornWeightOn input (σ.symm '' B)               -- `bornWeightOn_permState_symm`
        ≤ bornWeightOn input badInput                    -- `bornWeightOn_le_of_support_subset`,
                                                          --   given `σ.symm '' B ∩ supp ⊆ badInput`

  These two lemmas are GENERIC (any permutation / any subset-on-support); the concrete
  `σ.symm '' B ∩ supp ⊆ badInput` and the wrap-band count of `badInput` are the next bricks.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  NO `normSqDist`.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceComposedAgree
import FormalRV.Shor.CosetBornWeight

namespace FormalRV.Shor.GidneyInPlace.InPlaceComposedMass

open FormalRV.Framework
open FormalRV.SQIRPort
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.ApproxOp (permState)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (cosetInputVec_nonzero_eq)

/-- **Born-mass transport under a permutation pushforward.**  The mass of `permState σ.symm s`
    over an OUTPUT set `B` equals the mass of `s` over the PREIMAGE `σ.symm '' B` — the
    permutation just reindexes the Born distribution. -/
theorem bornWeightOn_permState_symm {dim : Nat} (σ : Equiv.Perm (Fin dim)) (s : QState dim)
    (B : Finset (Fin dim)) :
    bornWeightOn (permState σ.symm s) B = bornWeightOn s (B.image σ.symm) := by
  unfold bornWeightOn
  rw [Finset.sum_image (fun a _ b _ h => σ.symm.injective h)]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- **Born-mass monotonicity through a support-respecting subset.**  If every index of `S`
    on which `s` is nonzero lies in `T`, then `s`'s mass over `S` is at most its mass over
    `T` (the off-`T` part of `S` carries zero mass). -/
theorem bornWeightOn_le_of_support_subset {dim : Nat} (s : QState dim) (S T : Finset (Fin dim))
    (h : ∀ j ∈ S, s j 0 ≠ 0 → j ∈ T) :
    bornWeightOn s S ≤ bornWeightOn s T := by
  have heq : bornWeightOn s S = bornWeightOn s (S ∩ T) := by
    unfold bornWeightOn
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro j hjS hjni
    have hjnT : j ∉ T := fun hjT => hjni (Finset.mem_inter.mpr ⟨hjS, hjT⟩)
    by_contra hne
    exact hjnT (h j hjS (fun h0 => hne (by rw [h0]; exact Complex.normSq_zero)))
  rw [heq]
  unfold bornWeightOn
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun _ _ _ => Complex.normSq_nonneg _)

/-- **The combined transport+reduction.**  Given that the preimage of `B` meets the support
    of `s` only inside `badInput`, the mass of `permState σ.symm s` over `B` is at most the
    mass of `s` over `badInput`. -/
theorem bornWeightOn_evolved_le_badInput {dim : Nat} (σ : Equiv.Perm (Fin dim)) (s : QState dim)
    (B badInput : Finset (Fin dim))
    (hred : ∀ j ∈ B.image σ.symm, s j 0 ≠ 0 → j ∈ badInput) :
    bornWeightOn (permState σ.symm s) B ≤ bornWeightOn s badInput := by
  rw [bornWeightOn_permState_symm]
  exact bornWeightOn_le_of_support_subset s (B.image σ.symm) badInput hred

/-! ## §2. Per-point mass of the two-register coset input (Checkpoint D1). -/

/-- **Per-point Born mass** (Checkpoint D1).  Each support branch of `cosetInputVec x 0` carries
    Born mass `(1/2^cm)·(1/2^cm)` (= `1/4^cm`), so the mass of any finite set is `≤ card · that`. -/
theorem cosetInputVec_bornWeight_le_card (w bits N cm x : Nat)
    (S : Finset (Fin (2 ^ cosetDim w bits))) :
    bornWeightOn (cosetInputVec w bits N cm x 0) S
      ≤ (S.card : ℝ) * (1 / 2 ^ cm * (1 / 2 ^ cm)) := by
  have hc : Complex.normSq ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) = 1 / 2 ^ cm := by
    rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  have hpoint : ∀ i ∈ S, Complex.normSq (cosetInputVec w bits N cm x 0 i 0)
      ≤ 1 / 2 ^ cm * (1 / 2 ^ cm) := by
    intro i _
    by_cases hz : cosetInputVec w bits N cm x 0 i 0 = 0
    · rw [hz, Complex.normSq_zero]; positivity
    · apply le_of_eq
      rw [cosetInputVec_nonzero_eq w bits N cm x 0 i hz, Complex.normSq_mul, hc]
  calc bornWeightOn (cosetInputVec w bits N cm x 0) S
      = ∑ i ∈ S, Complex.normSq (cosetInputVec w bits N cm x 0 i 0) := rfl
    _ ≤ ∑ _i ∈ S, (1 / 2 ^ cm * (1 / 2 ^ cm)) := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (1 / 2 ^ cm * (1 / 2 ^ cm)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end FormalRV.Shor.GidneyInPlace.InPlaceComposedMass
