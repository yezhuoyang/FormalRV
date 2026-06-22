/-
  FormalRV.Shor.GidneyInPlace.E2ResidueEmbed — P1.3 of the coset-Shor hybrid route:
  the LAYOUT-AWARE residue embedding `E2residueEmbedZ` and the ideal representation bridge
  from the ideal RUNWAY machine to ordinary residue Shor success.
  ════════════════════════════════════════════════════════════════════════════

  WHY (and the distinction from the OLD `E2shorZ`).  The ideal RUNWAY machine
  (`Shor_final_state_E2coset f_runwayIdeal`, over `E2runwayInit`, whose work columns are the
  two-register coset inputs `cosetInputVec z 0`) must be bridged to ordinary residue Shor
  (`Shor_final_state f_residueIdeal`, whose work columns are the plain basis vectors `|z⟩` at
  the LAYOUT value `z·2^anc`).  The OLD `E2shorZ(qpeInit)` is the ZERO state (degenerate) and
  `E2shorZ` reads residue `z` at *value* `z` — WRONG for the `z·2^anc` layout.  So we define a
  NEW layout-aware embedding `E2residueEmbedZ` whose column `b` reads the residue
  `z = b.val / 2^anc` and is nonzero only at the canonical residue-LAYOUT columns
  (`b.val % 2^anc = 0 ∧ b.val/2^anc < N`).

  After QFTinv the phase marginal depends on the work-states' GRAM matrix, so a scalar-only
  argument is unsound — the isometry embedding makes Gram preservation structural (the nonzero
  columns are the orthonormal `cosetInputVec`s, A3 + T1).

  KEY scope rules (mirrored from P1.2):
    * `f_runwayIdeal` (acts on `cosetInputVec`) is DISTINCT from `f_residueIdeal` (acts on `|z⟩`);
    * NO self-commutation `M·E = E·M` (same oracle);
    * NO old `E2shorZ`; NO physical gate; NO bad sets.

  Kernel-clean target: no `sorry`, no `native_decide`, no axioms beyond the prelude
  `{propext, Classical.choice, Quot.sound}`.
-/
import FormalRV.Shor.GidneyInPlace.Deviation.Proof.InPlaceE2HintertwineLift
import FormalRV.Shor.GidneyInPlace.Ideal.Proof.InPlaceE2IdealTrajectory
import FormalRV.Shor.GidneyInPlace.Embedding.Proof.InPlaceTwoRegEmbedProbe
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputNorm

namespace FormalRV.Shor.GidneyInPlace.E2ResidueEmbed

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.BranchFactor (jointEquiv jointEquiv_apply)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputNorm (cosetInputVec_normalized)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedProbe (cosetInputVec_support_disjoint)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeInit qpeStageMap)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (E2runwayInit E2runwayInit_acts Shor_final_state_E2coset)
open FormalRV.Shor.GidneyInPlace.InPlaceE2IdealTrajectory (qpeInit_jointIdx)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq)

/-! ## §0. The layout-aware residue matrix and embedding. -/

/-- **The layout-aware residue column matrix.**  The column `b` is the two-register coset
    input `cosetInputVec (b.val/2^anc) 0` (read at the `E2shor_dim_eq`-cast row) when `b` is a
    canonical residue-LAYOUT index — `b.val % 2^(cosetAnc w bits) = 0 ∧ b.val/2^(cosetAnc w bits)
    < N` — else `0`.  (Residue `z` lives at value `z·2^anc`; extract `z = b.val/2^anc`.)  This
    is the data matrix of `E2residueEmbedZ`. -/
noncomputable def E2residueMat (m w bits N cm : Nat)
    (a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) : ℂ :=
  if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N then
    cosetInputVec w bits N cm (b.val / 2 ^ (cosetAnc w bits)) 0
      (Fin.cast (E2shor_dim_eq m w bits) a) 0
  else 0

/-- **The layout-aware residue embedding** `E2residueEmbedZ = I_phase ⊗ E2residueMat`.  Mirrors
    `E2shorZ`'s `jointEquiv.symm` structure, but the data matrix is the layout-aware
    `E2residueMat` (reading residue `b.val/2^anc` at the canonical layout columns). -/
noncomputable def E2residueEmbedZ (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))) :
    QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) :=
  fun i _ =>
    let p := (jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i
    ∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      E2residueMat m w bits N cm p.2 yp
        * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) p.1 yp) 0

/-- `E2residueEmbedZ` touches only the data factor (the `E2shorZ_acts` analogue). -/
theorem E2residueEmbedZ_acts (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2residueEmbedZ m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
          E2residueMat m w bits N cm y yp
            * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 := by
  unfold E2residueEmbedZ
  simp only
  rw [show jointIdx (shorDvd m bits (cosetAnc w bits)) x y
        = jointEquiv (shorDvd m bits (cosetAnc w bits)) (x, y) from
      (jointEquiv_apply (shorDvd m bits (cosetAnc w bits)) x y).symm,
    Equiv.symm_apply_apply]

/-- `E2residueEmbedZ` acts on the data factor through its matrix `E2residueMat` (the form the
    generic intertwining lift wants). -/
theorem E2residueEmbedZ_acts_mat (m w bits N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    E2residueEmbedZ m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = ∑ yp, E2residueMat m w bits N cm y yp
          * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0 :=
  E2residueEmbedZ_acts m w bits N cm phi x y

/-! ## §1. The base init equality `E2residueEmbedZ (qpeInit) = E2runwayInit`. -/

/-- **The base init equality** — applying the layout-aware embedding to the H-prepared ideal
    Shor init `qpeInit` recovers the corrected DIRECT runway init `E2runwayInit`.  `qpeInit`'s
    per-phase work register is the canonical basis vector at work value `2^(cosetAnc w bits)`
    (the value of `|1⟩_bits ⊗ |0⟩_anc`); this is the CANONICAL residue-LAYOUT column `b` with
    `b.val = 1·2^anc`, residue `z = b.val/2^anc = 1` (canonical since `1 < N`), so the embedding
    column sum collapses to the single column `cosetInputVec 1 0`, matching `E2runwayInit_acts`.
    Requires `0 < m` (for `qpeInit_jointIdx`'s H-uniform-sum) and `1 < N` (the residue `1` is
    canonical-layout) and `0 < bits` (the value `2^anc` is a valid work index, i.e.
    `2^anc < 2^(bits+anc)`). -/
theorem E2residueEmbedZ_qpeInit (m w bits N cm : Nat)
    (hm : 0 < m) (hbits : 0 < bits) (hN1 : 1 < N) :
    E2residueEmbedZ m w bits N cm (qpeInit m bits (cosetAnc w bits))
      = E2runwayInit m w bits N cm := by
  classical
  funext i col
  have hcol : col = 0 := Subsingleton.elim _ _
  subst hcol
  -- read both sides at jointIdx x y
  obtain ⟨x, y, hxy⟩ : ∃ (x : Fin (2 ^ m))
      (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        jointIdx (shorDvd m bits (cosetAnc w bits)) x y = i :=
    ⟨(jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i |>.1,
     (jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i |>.2, by
       rw [show jointIdx (shorDvd m bits (cosetAnc w bits)) _ _
             = jointEquiv (shorDvd m bits (cosetAnc w bits)) (_, _) from
           (jointEquiv_apply (shorDvd m bits (cosetAnc w bits)) _ _).symm,
         Equiv.apply_symm_apply]⟩
  subst hxy
  -- the canonical-layout column at work value 2^anc (= 1·2^anc), residue 1
  have hzlt : 2 ^ (cosetAnc w bits) < (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m := by
    rw [workDim_eq m bits (cosetAnc w bits)]
    calc 2 ^ (cosetAnc w bits) < 2 ^ (bits + cosetAnc w bits) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 2 ^ (bits + cosetAnc w bits) := rfl
  -- the canonicality facts about the surviving column value 2^anc
  have hmod0 : (2 ^ (cosetAnc w bits)) % 2 ^ (cosetAnc w bits) = 0 := Nat.mod_self _
  have hdiv1 : (2 ^ (cosetAnc w bits)) / 2 ^ (cosetAnc w bits) = 1 :=
    Nat.div_self (Nat.two_pow_pos _)
  rw [E2residueEmbedZ_acts m w bits N cm (qpeInit m bits (cosetAnc w bits)) x y,
      E2runwayInit_acts m w bits N cm x y]
  -- substitute qpeInit's value: only yp.val = 2^anc survives
  rw [Finset.sum_congr rfl (fun yp _ => by
        rw [qpeInit_jointIdx m w bits hm x yp])]
  -- pull the surviving column
  rw [Finset.sum_eq_single (⟨2 ^ (cosetAnc w bits), hzlt⟩ :
        Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))]
  · -- the surviving term: E2residueMat y ⟨2^anc⟩ · (1/√2^m)·1 = (1/√2^m)·cosetInputVec 1 0
    show E2residueMat m w bits N cm y ⟨2 ^ (cosetAnc w bits), hzlt⟩
          * (((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
              * (if (⟨2 ^ (cosetAnc w bits), hzlt⟩ :
                    Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)).val
                  = 2 ^ (cosetAnc w bits) then 1 else 0))
        = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
            * cosetInputVec w bits N cm 1 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0
    rw [if_pos rfl, mul_one]
    rw [E2residueMat, if_pos ⟨hmod0, by rw [hdiv1]; exact hN1⟩]
    show cosetInputVec w bits N cm
          ((⟨2 ^ (cosetAnc w bits), hzlt⟩ :
            Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)).val
              / 2 ^ (cosetAnc w bits)) 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0
          * ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
        = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
            * cosetInputVec w bits N cm 1 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0
    rw [show (⟨2 ^ (cosetAnc w bits), hzlt⟩ :
            Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)).val
              / 2 ^ (cosetAnc w bits) = 1 from hdiv1]
    ring
  · -- all other yp vanish (the work register is 0 there)
    intro yp _ hyp
    have hne : yp.val ≠ 2 ^ (cosetAnc w bits) := fun h => hyp (Fin.ext h)
    rw [if_neg hne, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## §2. The data-factor marginal isometry (layout-aware). -/

/-- The data-factor layout-aware embedding: `(E2residueData ψ) y = ∑_z E2residueMat y z · ψ z`. -/
noncomputable def E2residueData (m w bits N cm : Nat)
    (ψ : Matrix (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) (Fin 1) ℂ) :
    Matrix (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) (Fin 1) ℂ :=
  fun y _ => ∑ z, E2residueMat m w bits N cm y z * ψ z 0

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

/-- **The layout-aware data-factor marginal isometry.**  For a state `ψ` supported on the
    canonical residue-LAYOUT indices (`z.val % 2^anc = 0 ∧ z.val/2^anc < N`), the layout-aware
    data embedding `E2residueData` preserves the total Born mass:
    `∑_y ‖E2residueData ψ y‖² = ∑_z ‖ψ z‖²`.  The nonzero columns are the orthonormal
    `cosetInputVec (z.val/2^anc) 0` (A3 disjoint support — distinct canonical layout indices give
    distinct residues — + T1 unit norm). -/
theorem E2residueData_marginal (m w bits numWin N cm : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (ψ : Matrix (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) (Fin 1) ℂ)
    (hsupp : ∀ z : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        ¬ (z.val % 2 ^ (cosetAnc w bits) = 0 ∧ z.val / 2 ^ (cosetAnc w bits) < N) → ψ z 0 = 0) :
    (∑ y, Complex.normSq (E2residueData m w bits N cm ψ y 0))
      = ∑ z, Complex.normSq (ψ z 0) := by
  classical
  -- canonical residue-layout indices
  set canon : Finset (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :=
    Finset.univ.filter
      (fun z => z.val % 2 ^ (cosetAnc w bits) = 0 ∧ z.val / 2 ^ (cosetAnc w bits) < N)
    with hcanon
  -- residue extraction is injective on canon (distinct canonical layout indices ⇒ distinct z)
  have hinj : ∀ a ∈ canon, ∀ b ∈ canon,
      a.val / 2 ^ (cosetAnc w bits) = b.val / 2 ^ (cosetAnc w bits) → a = b := by
    intro a ha b hb heq
    simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    have hav : a.val = a.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits) := by
      conv_lhs => rw [← Nat.div_add_mod a.val (2 ^ (cosetAnc w bits)), ha.1, Nat.add_zero]
      rw [Nat.mul_comm]
    have hbv : b.val = b.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits) := by
      conv_lhs => rw [← Nat.div_add_mod b.val (2 ^ (cosetAnc w bits)), hb.1, Nat.add_zero]
      rw [Nat.mul_comm]
    rw [hav, hbv, heq]
  -- per-row collapse: at most one canonical layout column contributes
  have hcollapse : ∀ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      Complex.normSq (E2residueData m w bits N cm ψ y 0)
        = ∑ z ∈ canon,
            Complex.normSq (cosetInputVec w bits N cm (z.val / 2 ^ (cosetAnc w bits)) 0
              (Fin.cast (E2shor_dim_eq m w bits) y) 0)
              * Complex.normSq (ψ z 0) := by
    intro y
    have hrestrict : E2residueData m w bits N cm ψ y 0
        = ∑ z ∈ canon, E2residueMat m w bits N cm y z * ψ z 0 := by
      show (∑ z, E2residueMat m w bits N cm y z * ψ z 0) = _
      symm; apply Finset.sum_subset (Finset.subset_univ canon)
      intro z _ hz
      simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [E2residueMat, if_neg hz, zero_mul]
    rw [hrestrict]
    have hpair : ∀ a ∈ canon, ∀ b ∈ canon, a ≠ b →
        E2residueMat m w bits N cm y a * ψ a 0 = 0
          ∨ E2residueMat m w bits N cm y b * ψ b 0 = 0 := by
      intro a ha b hb hab
      have haC := ha; have hbC := hb
      simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at haC hbC
      -- residues differ
      have hzne : a.val / 2 ^ (cosetAnc w bits) ≠ b.val / 2 ^ (cosetAnc w bits) := by
        intro h; exact hab (hinj a ha b hb h)
      by_cases hya : E2residueMat m w bits N cm y a = 0
      · exact Or.inl (by rw [hya, zero_mul])
      · by_cases hyb : E2residueMat m w bits N cm y b = 0
        · exact Or.inr (by rw [hyb, zero_mul])
        · -- both columns nonzero at row y ⇒ contradiction via disjoint support
          exfalso
          rw [E2residueMat, if_pos haC] at hya
          rw [E2residueMat, if_pos hbC] at hyb
          exact cosetInputVec_support_disjoint w bits N cm
            (a.val / 2 ^ (cosetAnc w bits)) (b.val / 2 ^ (cosetAnc w bits))
            hN haC.2 hbC.2 hzne (Fin.cast (E2shor_dim_eq m w bits) y) hya hyb
    rw [normSq_sum_canon_pairwise canon _ hpair]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Complex.normSq_mul, E2residueMat, if_pos hz]
  -- assemble: swap sums, each column has unit Born mass (T1)
  rw [Finset.sum_congr rfl (fun y _ => hcollapse y), Finset.sum_comm]
  have hcol : ∀ z ∈ canon,
      (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
          Complex.normSq (cosetInputVec w bits N cm (z.val / 2 ^ (cosetAnc w bits)) 0
            (Fin.cast (E2shor_dim_eq m w bits) y) 0)
          * Complex.normSq (ψ z 0)) = Complex.normSq (ψ z 0) := by
    intro z hz
    simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hid : (2 ^ cm - 1) * N + N = 2 ^ cm * N := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left N (Nat.two_pow_pos cm))]
    have hlt : z.val / 2 ^ (cosetAnc w bits) + (2 ^ cm - 1) * N < 2 ^ bits := by
      have hzlt : z.val / 2 ^ (cosetAnc w bits) + (2 ^ cm - 1) * N < (2 ^ cm - 1) * N + N := by
        have := hz.2; omega
      rw [hid] at hzlt
      exact lt_of_lt_of_le hzlt hMN
    have hnorm : (∑ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        Complex.normSq (cosetInputVec w bits N cm (z.val / 2 ^ (cosetAnc w bits)) 0
          (Fin.cast (E2shor_dim_eq m w bits) y) 0)) = 1 := by
      have h := cosetInputVec_normalized w bits numWin N cm (z.val / 2 ^ (cosetAnc w bits))
        hw hbits hN hlt
      unfold bornWeightOn at h
      rw [← h]
      exact Fintype.sum_equiv (finCongr (E2shor_dim_eq m w bits)) _ _ (fun y => by rfl)
    rw [← Finset.sum_mul, hnorm, one_mul]
  rw [Finset.sum_congr rfl hcol]
  apply Finset.sum_subset (Finset.subset_univ canon)
  intro z _ hz
  simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  rw [hsupp z hz, Complex.normSq_zero]

/-! ## §3. The full Shor-register marginal preservation `E2residueEmbedZ_hmarg`. -/

/-- **The layout-aware `hmarg`** (the `E2shor_hmarg` analogue).  For a state `φ` supported on the
    canonical residue-LAYOUT indices (`φ(jointIdx x b) = 0` whenever
    `¬(b.val % 2^anc = 0 ∧ b.val/2^anc < N)`), the layout-aware embedding `E2residueEmbedZ`
    preserves the per-outcome Born marginal.  Reduces through `prob_partial_meas_basis_eq` + the
    `E2shor_dim_eq` cast to the data-factor isometry `E2residueData_marginal` (the nonzero columns
    are the orthonormal `cosetInputVec (b.val/2^anc) 0`). -/
theorem E2residueEmbedZ_hmarg (m w bits numWin N cm : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 0 < N) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hsupp : ∀ (x : Fin (2 ^ m)) (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0)
    (x : Fin (2 ^ m)) :
    prob_partial_meas (basis_vector (2 ^ m) x.val) (E2residueEmbedZ m w bits N cm phi)
      = prob_partial_meas (basis_vector (2 ^ m) x.val) phi := by
  classical
  rw [prob_partial_meas_basis_eq (E2residueEmbedZ m w bits N cm phi) x
        (shorDvd m bits (cosetAnc w bits)),
      prob_partial_meas_basis_eq phi x (shorDvd m bits (cosetAnc w bits))]
  set e := finCongr (E2shor_dim_eq m w bits) with he
  -- the per-phase work slice as a column matrix
  set ψ : Matrix (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) (Fin 1) ℂ :=
    fun z _ => phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x z) 0 with hψ
  have hψsupp : ∀ z : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      ¬ (z.val % 2 ^ (cosetAnc w bits) = 0 ∧ z.val / 2 ^ (cosetAnc w bits) < N) → ψ z 0 = 0 := by
    intro z hz
    show phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x z) 0 = 0
    exact hsupp x z hz
  -- per-`y` collapse: E2residueEmbedZ(phi) at jointIdx x y = E2residueData ψ at y
  have hpoint : ∀ y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
      Complex.normSq (E2residueEmbedZ m w bits N cm phi
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0)
        = Complex.normSq (E2residueData m w bits N cm ψ y 0) := by
    intro y
    congr 1
    rw [E2residueEmbedZ_acts m w bits N cm phi x y]
    rfl
  -- assemble both sides
  rw [Finset.sum_congr rfl (fun y _ => hpoint y),
      E2residueData_marginal m w bits numWin N cm hw hbits hN hMN ψ hψsupp]

/-! ## §4. P1.3b — the TWO-ORACLE intertwining `hwork_int` (the crux). -/

open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)

/-- **P1.3b — the layout-aware two-oracle `hwork_int` matrix identity.**  For EVERY pair of work
    columns `(y, y2)` (bad_step = ∅, ∀ y), the work-level intertwining
    `workMat(f_runwayIdeal)·E2residueMat = E2residueMat·workMat(f_residueIdeal)` holds.

    TWO realization hypotheses are carried EXPLICITLY (dischargeable later, `f_runwayIdeal` and
    `f_residueIdeal` kept DISTINCT, `mult` threaded identically on both sides):
      • `hf_runway` — the runway active work action = the clean coset shift (the matrix-vector
        form of `IdealPermLift.idealShift_cosetInputVec`, already used in
        `InPlaceE2IdealTrajectory`): for `z < N`,
        `∑ yp, workMat(f_runwayIdeal) y yp · cosetInputVec z 0 (cast yp) =
            cosetInputVec ((mult kstep · z) % N) 0 (cast y)`;
      • `hf_residue` — the residue permutation on the `z·2^anc` LAYOUT:
        `workMat(f_residueIdeal) a b = [a.val = if (b canonical residue-layout) then
            ((mult kstep · (b.val/2^anc)) % N)·2^anc else b.val]`.

    Proof by cases on whether `y2` is a canonical residue-LAYOUT column (residue
    `z2 = y2.val/2^anc`).  Canonical: both sides = `cosetInputVec ((mult·z2)%N) 0 (cast y)`
    (LHS via the runway shift on the column; RHS via the layout permutation picking the
    target-value column `((mult·z2)%N)·2^anc`, which is itself a canonical layout index).
    Non-canonical: both sides 0. -/
theorem E2residue_hwork_int
    (m w bits N cm kstep : Nat) (mult : Nat → Nat)
    (hN : 0 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hf_runway : ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0)
    (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))
    (y2 : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (∑ yp, workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
        * E2residueMat m w bits N cm yp y2)
      = (∑ yp, E2residueMat m w bits N cm y yp
          * workMat m bits (cosetAnc w bits) kstep f_residueIdeal yp y2) := by
  classical
  -- the data dimension equals 2^bits · 2^anc
  have hdimEq : (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m
      = 2 ^ bits * 2 ^ (cosetAnc w bits) := by
    rw [workDim_eq m bits (cosetAnc w bits), pow_add]
  by_cases hy2 : y2.val % 2 ^ (cosetAnc w bits) = 0 ∧ y2.val / 2 ^ (cosetAnc w bits) < N
  · -- canonical residue-layout column; let z2 = y2.val/2^anc
    set z2 := y2.val / 2 ^ (cosetAnc w bits) with hz2
    have hz2N : z2 < N := hy2.2
    -- the target value t = ((mult·z2)%N)·2^anc, which is a canonical layout index
    have hmodN : (mult kstep * z2) % N < N := Nat.mod_lt _ hN
    have hres_bits : (mult kstep * z2) % N < 2 ^ bits := lt_of_lt_of_le hmodN hNbits
    have ht_lt : (mult kstep * z2) % N * 2 ^ (cosetAnc w bits)
        < (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m := by
      rw [hdimEq]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hres_bits
    set t : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m) :=
      ⟨(mult kstep * z2) % N * 2 ^ (cosetAnc w bits), ht_lt⟩ with ht
    have htmod : t.val % 2 ^ (cosetAnc w bits) = 0 := by
      show ((mult kstep * z2) % N * 2 ^ (cosetAnc w bits)) % 2 ^ (cosetAnc w bits) = 0
      exact Nat.mul_mod_left _ _
    have htdiv : t.val / 2 ^ (cosetAnc w bits) = (mult kstep * z2) % N := by
      show ((mult kstep * z2) % N * 2 ^ (cosetAnc w bits)) / 2 ^ (cosetAnc w bits) = _
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
    -- LHS = cosetInputVec ((mult·z2)%N) 0 (cast y) via hf_runway on the canonical column
    have hLHS : (∑ yp, workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
            * E2residueMat m w bits N cm yp y2)
        = cosetInputVec w bits N cm ((mult kstep * z2) % N) 0
            (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      rw [← hf_runway z2 hz2N y]
      refine Finset.sum_congr rfl (fun yp _ => ?_)
      rw [E2residueMat, if_pos hy2]
    -- RHS = E2residueMat y t (single surviving term) = cosetInputVec ((mult·z2)%N) 0 (cast y)
    have hRHS : (∑ yp, E2residueMat m w bits N cm y yp
            * workMat m bits (cosetAnc w bits) kstep f_residueIdeal yp y2)
        = cosetInputVec w bits N cm ((mult kstep * z2) % N) 0
            (Fin.cast (E2shor_dim_eq m w bits) y) 0 := by
      rw [Finset.sum_eq_single t]
      · rw [hf_residue t y2, if_pos hy2, if_pos rfl, mul_one, E2residueMat,
            if_pos ⟨htmod, by rw [htdiv]; exact hmodN⟩, htdiv]
      · intro yp _ hypne
        rw [hf_residue yp y2, if_pos hy2,
            if_neg (fun h => hypne (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS, hRHS]
  · -- non-canonical column: both sides 0
    have hLHS0 : (∑ yp, workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
            * E2residueMat m w bits N cm yp y2) = 0 := by
      refine Finset.sum_eq_zero (fun yp _ => ?_)
      rw [E2residueMat, if_neg hy2, mul_zero]
    have hRHS0 : (∑ yp, E2residueMat m w bits N cm y yp
            * workMat m bits (cosetAnc w bits) kstep f_residueIdeal yp y2) = 0 := by
      rw [Finset.sum_eq_single y2]
      · rw [hf_residue y2 y2, if_neg hy2, if_pos rfl, mul_one, E2residueMat, if_neg hy2]
      · intro yp _ hypne
        rw [hf_residue yp y2, if_neg hy2,
            if_neg (fun h => hypne (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS0, hRHS0]

/-! ## §5. P1.3b — the per-stage everywhere intertwining (oracle stages `k < m`). -/

open FormalRV.Shor.GidneyInPlace.InPlaceE2HintertwineLift (controlled_oracle_hintertwine_generic)

/-- **P1.3b — the per-stage everywhere two-oracle intertwining** (for the oracle stages `k < m`).
    Instantiates the generic controlled-oracle intertwining lift
    (`controlled_oracle_hintertwine_generic`) at the layout-aware embedding
    `(E2residueEmbedZ, E2residueMat, E2residueEmbedZ_acts_mat)`, `f_coset := f_runwayIdeal`,
    `f_ideal := f_residueIdeal`, `bad_step := ∅`, fed by the `E2residue_hwork_int` matrix identity.
    Yields the EVERYWHERE per-stage intertwining
      `qpeStageMap f_runwayIdeal kstep (E2residueEmbedZ φ) = E2residueEmbedZ (qpeStageMap f_residueIdeal kstep φ)`
    (∀ jointIdx, for `kstep < m`).  The realization hypotheses `hf_runway`/`hf_residue` are carried
    explicitly (`f_runwayIdeal`/`f_residueIdeal` distinct, `mult` threaded identically). -/
theorem E2residueEmbedZ_intertwine (m w bits N cm kstep : Nat) (hk : kstep < m) (mult : Nat → Nat)
    (hN : 0 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0)
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal kstep (E2residueEmbedZ m w bits N cm phi))
        (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = (E2residueEmbedZ m w bits N cm
          (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal kstep phi))
          (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0 :=
  controlled_oracle_hintertwine_generic m bits (cosetAnc w bits) kstep hk
    f_runwayIdeal f_residueIdeal hwt_c hwt_i
    (E2residueEmbedZ m w bits N cm) (E2residueMat m w bits N cm)
    (E2residueEmbedZ_acts_mat m w bits N cm)
    (∅ : Finset (Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)))
    (fun y _ y2 => E2residue_hwork_int m w bits N cm kstep mult hN hNbits
      f_runwayIdeal f_residueIdeal hf_runway hf_residue y y2)
    phi x y (Finset.notMem_empty y)

/-! ## §6. The QFTinv (`k = m`) stage acts PHASE-LOCALLY, and commutes with the embedding. -/

open FormalRV.Framework
open FormalRV.Framework.BaseUCom
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp
  (qpeStageMap_cast qstate_cast_cast qpeStageUCom)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge
  (workDim_eq workBlock vec_eq_sum_phase_kron cast_jointIdx_eq_combine)

/-- **The QFTinv (`k = m`) stage acts PHASE-LOCALLY.**  Reading the `k = m` stage map at
    `jointIdx x y`, the result is a phase-register matrix `M := uc_eval(real_QFTinv_layer m)` mixing
    only the phase index `x`, with the work index `y` held fixed:
      `qpeStageMap m n anc f m φ (jointIdx x y) 0 = ∑ x', M x x' · φ (jointIdx x' y) 0`.
    Proof: the stage circuit is `BaseUCom.QFTinv m` (independent of `f`), which lifts to
    `map_qubits id (real_QFTinv_layer m)` — a control-register-only circuit — so on each
    phase-kron block `|x'⟩ ⊗ workBlock` it acts as `(M · |x'⟩) ⊗ workBlock`
    (`uc_eval_control_register_circuit_kron_vec`); reading the resulting sum at the combined index
    `kron_vec_combine x (cast y)` leaves the work factor untouched. -/
theorem qpeStage_qftinv_jointIdx (m n anc : Nat) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)) :
    qpeStageMap m n anc f m phi (jointIdx (shorDvd m n anc) x y) 0
      = ∑ x' : Fin (2 ^ m),
          FormalRV.Framework.uc_eval
              (FormalRV.SQIRPort.real_QFTinv_layer m : FormalRV.Framework.BaseUCom m) x x'
            * phi (jointIdx (shorDvd m n anc) x' y) 0 := by
  classical
  -- Expose the native Framework product under a single outer cast.
  set s : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ :=
    QState.cast (dim_assoc_eq m n anc).symm phi with hs
  have hphi : phi = QState.cast (dim_assoc_eq m n anc) s := by
    rw [hs]; exact (qstate_cast_cast (dim_assoc_eq m n anc).symm phi).symm
  rw [hphi]
  rw [qpeStageMap_cast m n anc f m s]
  -- The stage circuit (k = m) is QFTinv m.
  have hstage : qpeStageUCom m n anc f m
      = (FormalRV.Framework.BaseUCom.QFTinv m : FormalRV.Framework.BaseUCom (m + (n + anc))) := by
    unfold qpeStageUCom; rw [if_neg (Nat.lt_irrefl m)]
  rw [hstage]
  -- bridge QFTinv to the control-register-circuit lift of real_QFTinv_layer
  have hbridge : (FormalRV.Framework.BaseUCom.QFTinv m
        : FormalRV.Framework.BaseUCom (m + (n + anc)))
      = map_qubits (fun q => q)
          (FormalRV.SQIRPort.real_QFTinv_layer m : FormalRV.Framework.BaseUCom m) := by
    show (FormalRV.Framework.BaseUCom.real_QFTinv_layer m
          : FormalRV.Framework.BaseUCom (m + (n + anc))) = _
    rw [show (FormalRV.Framework.BaseUCom.real_QFTinv_layer m
            : FormalRV.Framework.BaseUCom (m + (n + anc)))
          = (@FormalRV.Framework.BaseUCom.real_QFTinv_layer (m + (n + anc)) m
              : FormalRV.Framework.BaseUCom (m + (n + anc))) from rfl,
        FormalRV.SQIRPort.real_QFTinv_layer_map_id_bridge m (n + anc) m]
    congr 1
    exact (FormalRV.SQIRPort.real_QFTinv_layer_bridge m).symm
  rw [hbridge]
  set c : FormalRV.Framework.BaseUCom m :=
    (FormalRV.SQIRPort.real_QFTinv_layer m : FormalRV.Framework.BaseUCom m) with hc
  have hwtc : UCom.WellTyped m c := FormalRV.SQIRPort.wellTyped_real_QFTinv_layer m hm
  -- read the outer cast at jointIdx as a native read at kron_vec_combine
  have hread : ∀ (v : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)
      (xz : Fin (2 ^ m)) (z : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)),
      (QState.cast (dim_assoc_eq m n anc) v) (jointIdx (shorDvd m n anc) xz z) 0
        = v (kron_vec_combine xz (Fin.cast (workDim_eq m n anc) z)) 0 := by
    intro v xz z
    show v (Fin.cast (dim_assoc_eq m n anc).symm (jointIdx (shorDvd m n anc) xz z)) 0
        = v (kron_vec_combine xz (Fin.cast (workDim_eq m n anc) z)) 0
    rw [cast_jointIdx_eq_combine]
  rw [hread]
  simp only [hread]
  -- the matrix product, decomposed over the phase register
  have hblock : ∀ xp : Fin (2 ^ m),
      (FormalRV.Framework.uc_eval (map_qubits (fun q => q) c)
          * kron_vec (FormalRV.Framework.basis_vector (2 ^ m) xp.val) (workBlock s xp))
        = kron_vec (FormalRV.Framework.uc_eval c
            * FormalRV.Framework.basis_vector (2 ^ m) xp.val) (workBlock s xp) :=
    fun xp => FormalRV.SQIRPort.uc_eval_control_register_circuit_kron_vec c hwtc _ (workBlock s xp)
  have hM : FormalRV.Framework.uc_eval (map_qubits (fun q => q) c) * s
      = ∑ xp : Fin (2 ^ m),
          kron_vec (FormalRV.Framework.uc_eval c
              * FormalRV.Framework.basis_vector (2 ^ m) xp.val) (workBlock s xp) := by
    conv_lhs => rw [vec_eq_sum_phase_kron s]
    refine Eq.trans (Matrix.mul_sum _ _ _) ?_
    exact Finset.sum_congr rfl (fun xp _ => hblock xp)
  refine Eq.trans
    (congrFun (congrFun hM (kron_vec_combine x (Fin.cast (workDim_eq m n anc) y))) 0) ?_
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun xp _ => ?_)
  -- read each phase block at the combined index
  rw [kron_vec_apply, kron_vec_high_combine, kron_vec_low_combine]
  -- uc_eval c * basis_vector xp, read at row x, equals the matrix entry (x, xp)
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single xp]
  · rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl, mul_one]
    rfl
  · intro b _ hb
    rw [FormalRV.Framework.basis_vector_apply_ne _ _ _ _ (by
      intro h; exact hb (Fin.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`E2residueEmbedZ` commutes with the QFTinv (`k = m`) stage.**  The QFTinv stage map is
    phase-local (`qpeStage_qftinv_jointIdx`, mixing only the phase index) and `E2residueEmbedZ` is
    `I_phase ⊗ E2residueMat` (touching only the data factor), so they commute pointwise at every
    `jointIdx x y`.  The QFTinv stage is independent of `f`, so this holds for any oracle family
    `f` (in particular both `f_runwayIdeal` and `f_residueIdeal`). -/
theorem E2residueEmbedZ_qftinv_comm (m w bits N cm : Nat) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (phi : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (qpeStageMap m bits (cosetAnc w bits) f m (E2residueEmbedZ m w bits N cm phi))
        (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
      = (E2residueEmbedZ m w bits N cm (qpeStageMap m bits (cosetAnc w bits) f m phi))
          (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0 := by
  classical
  -- LHS: phase-local stage then read the embedding column on each phase branch
  rw [qpeStage_qftinv_jointIdx m bits (cosetAnc w bits) hm f (E2residueEmbedZ m w bits N cm phi) x y]
  rw [Finset.sum_congr rfl (fun x' _ => by
        rw [E2residueEmbedZ_acts m w bits N cm phi x' y] :
      ∀ x' ∈ Finset.univ,
        FormalRV.Framework.uc_eval
            (FormalRV.SQIRPort.real_QFTinv_layer m : FormalRV.Framework.BaseUCom m) x x'
          * E2residueEmbedZ m w bits N cm phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x' y) 0
        = FormalRV.Framework.uc_eval
            (FormalRV.SQIRPort.real_QFTinv_layer m : FormalRV.Framework.BaseUCom m) x x'
          * ∑ yp, E2residueMat m w bits N cm y yp
              * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x' yp) 0)]
  -- RHS: read the embedding column, then phase-local stage on each work index
  rw [E2residueEmbedZ_acts m w bits N cm (qpeStageMap m bits (cosetAnc w bits) f m phi) x y]
  rw [Finset.sum_congr rfl (fun yp _ => by
        rw [qpeStage_qftinv_jointIdx m bits (cosetAnc w bits) hm f phi x yp] :
      ∀ yp ∈ Finset.univ,
        E2residueMat m w bits N cm y yp
          * (qpeStageMap m bits (cosetAnc w bits) f m phi)
              (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0
        = E2residueMat m w bits N cm y yp
          * ∑ x', FormalRV.Framework.uc_eval
              (FormalRV.SQIRPort.real_QFTinv_layer m : FormalRV.Framework.BaseUCom m) x x'
              * phi (jointIdx (shorDvd m bits (cosetAnc w bits)) x' yp) 0)]
  -- both sides equal the double sum; reorder
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun yp _ => Finset.sum_congr rfl (fun x' _ => by ring))

/-! ## §7. P1.3c — the ORBIT BRIDGE. -/

open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)
open FormalRV.SQIRPort (Shor_final_state)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (shor_final_eq_orbitState)

/-- A per-`jointIdx` equality of two states upgrades to a full `QState` equality
    (the `jointIdx (shorDvd …)` factorization is a bijection of the full index space). -/
theorem qstate_ext_jointIdx (m bits anc : Nat)
    {Φ Ψ : QState (2 ^ m * 2 ^ bits * 2 ^ anc)}
    (h : ∀ (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ anc) / 2 ^ m)),
        Φ (jointIdx (shorDvd m bits anc) x y) 0 = Ψ (jointIdx (shorDvd m bits anc) x y) 0) :
    Φ = Ψ := by
  funext i col
  have hcol : col = 0 := Subsingleton.elim _ _
  subst hcol
  obtain ⟨x, y, hxy⟩ : ∃ (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ anc) / 2 ^ m)),
      jointIdx (shorDvd m bits anc) x y = i :=
    ⟨(jointEquiv (shorDvd m bits anc)).symm i |>.1,
     (jointEquiv (shorDvd m bits anc)).symm i |>.2, by
       rw [show jointIdx (shorDvd m bits anc) _ _
             = jointEquiv (shorDvd m bits anc) (_, _) from
           (jointEquiv_apply (shorDvd m bits anc) _ _).symm,
         Equiv.apply_symm_apply]⟩
  subst hxy
  exact h x y

/-- The QFTinv (`k = m`) stage map is INDEPENDENT of the oracle family `f` (the stage circuit is
    `QFTinv m`, which does not mention `f`).  Hence the runway and residue QFTinv stages coincide. -/
theorem qpeStageMap_qftinv_indep (m n anc : Nat)
    (f g : Nat → FormalRV.Framework.BaseUCom (n + anc)) :
    qpeStageMap m n anc f m = qpeStageMap m n anc g m := by
  funext psi
  show QState.cast (dim_assoc_eq m n anc)
        (uc_eval (qpeStageUCom m n anc f m) (QState.cast (dim_assoc_eq m n anc).symm psi))
      = QState.cast (dim_assoc_eq m n anc)
        (uc_eval (qpeStageUCom m n anc g m) (QState.cast (dim_assoc_eq m n anc).symm psi))
  have hfg : qpeStageUCom m n anc f m = qpeStageUCom m n anc g m := by
    unfold qpeStageUCom; rw [if_neg (Nat.lt_irrefl m), if_neg (Nat.lt_irrefl m)]
  rw [hfg]

/-- **The oracle-stage orbit bridge** (oracle stages `0 .. numIter-1`, for `numIter ≤ m`).  Every
    runway orbit state (over `E2runwayInit`) after `numIter ≤ m` controlled-oracle stages of
    `qpeStageMap … f_runwayIdeal` equals the layout-aware embedding of the corresponding residue
    orbit state (over `qpeInit`).  Induction on `numIter`: base = `E2residueEmbedZ_qpeInit`; step
    = `E2residueEmbedZ_intertwine` (the per-stage everywhere intertwining), upgraded to a full
    `QState` equality by `qstate_ext_jointIdx`. -/
theorem orbit_oracle_bridge (m w bits N cm : Nat) (hm : 0 < m) (hbits : 0 < bits)
    (mult : Nat → Nat) (hN : 0 < N) (hN1 : 1 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (kstep : Nat), kstep < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0) :
    ∀ numIter, numIter ≤ m →
      orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2runwayInit m w bits N cm) numIter
        = E2residueEmbedZ m w bits N cm
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
              (qpeInit m bits (cosetAnc w bits)) numIter) := by
  intro numIter
  induction numIter with
  | zero =>
      intro _
      show E2runwayInit m w bits N cm = E2residueEmbedZ m w bits N cm (qpeInit m bits (cosetAnc w bits))
      exact (E2residueEmbedZ_qpeInit m w bits N cm hm hbits hN1).symm
  | succ p ih =>
      intro hp
      have hpm : p < m := hp
      show qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal p
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
              (E2runwayInit m w bits N cm) p)
          = E2residueEmbedZ m w bits N cm
              (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal p
                (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
                  (qpeInit m bits (cosetAnc w bits)) p))
      rw [ih (Nat.le_of_lt hpm)]
      apply qstate_ext_jointIdx m bits (cosetAnc w bits)
      intro x y
      exact E2residueEmbedZ_intertwine m w bits N cm p hpm mult hN hNbits
        f_runwayIdeal f_residueIdeal hwt_c hwt_i
        (hf_runway p hpm) (hf_residue p hpm)
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
          (qpeInit m bits (cosetAnc w bits)) p) x y

/-- **P1.3c — the ORBIT BRIDGE.**  The full ideal runway machine's final state equals the
    layout-aware embedding of the ordinary residue Shor final state:
      `Shor_final_state_E2coset f_runwayIdeal = E2residueEmbedZ (Shor_final_state f_residueIdeal)`.
    The `m` controlled-oracle stages are carried by `orbit_oracle_bridge` (per-stage intertwining);
    the last (`k = m`) QFTinv stage is phase-local and commutes with `E2residueEmbedZ`
    (`E2residueEmbedZ_qftinv_comm`), with the runway and residue QFTinv stages identical
    (`qpeStageMap_qftinv_indep`).  Uses `shor_final_eq_orbitState` (needs
    `0 < m + (bits + cosetAnc w bits)`). -/
theorem Shor_final_state_E2coset_eq_embed (m w bits N cm : Nat)
    (hm : 0 < m) (hbits : 0 < bits)
    (mult : Nat → Nat) (hN : 0 < N) (hN1 : 1 < N) (hNbits : N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (kstep : Nat), kstep < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0) :
    Shor_final_state_E2coset m w bits N cm f_runwayIdeal
      = E2residueEmbedZ m w bits N cm
          (Shor_final_state m bits (cosetAnc w bits) f_residueIdeal) := by
  -- both finals are orbit states after m+1 stages
  have hdim_pos : 0 < m + (bits + cosetAnc w bits) := by omega
  rw [show Shor_final_state_E2coset m w bits N cm f_runwayIdeal
        = orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
            (E2runwayInit m w bits N cm) (m + 1) from rfl,
      shor_final_eq_orbitState m bits (cosetAnc w bits) f_residueIdeal hdim_pos]
  -- peel the last (QFTinv) stage on both sides
  show qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal m
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2runwayInit m w bits N cm) m)
      = E2residueEmbedZ m w bits N cm
          (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal m
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
              (qpeInit m bits (cosetAnc w bits)) m))
  -- the QFTinv stage is f-independent: rewrite the runway stage to the residue stage
  rw [orbit_oracle_bridge m w bits N cm hm hbits mult hN hN1 hNbits
        f_runwayIdeal f_residueIdeal hwt_c hwt_i hf_runway hf_residue m (Nat.le_refl m)]
  rw [show qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal m
        = qpeStageMap m bits (cosetAnc w bits) f_residueIdeal m from
      qpeStageMap_qftinv_indep m bits (cosetAnc w bits) f_runwayIdeal f_residueIdeal]
  -- now both sides differ only by the order of E2residueEmbedZ and the QFTinv stage
  apply qstate_ext_jointIdx m bits (cosetAnc w bits)
  intro x y
  exact E2residueEmbedZ_qftinv_comm m w bits N cm hm f_residueIdeal
    (orbitState (qpeStageMap m bits (cosetAnc w bits) f_residueIdeal)
      (qpeInit m bits (cosetAnc w bits)) m) x y

/-! ## §8. P1.3d — the SUCCESS BRIDGE (the capstone). -/

open FormalRV.SQIRPort (probability_of_success r_found basis_vector prob_partial_meas)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess (probability_of_success_E2coset)

/-- **P1.3d — the SUCCESS BRIDGE (capstone).**  The ideal runway machine's Shor success
    probability EQUALS the ordinary residue Shor success probability:
      `probability_of_success_E2coset a r N m w bits cm f_runwayIdeal
          = probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal`.
    Both unfold to `∑ x, r_found x m r a N · prob_partial_meas (|x⟩) (final)`.  Rewriting the runway
    final via the orbit bridge (P1.3c) makes it `E2residueEmbedZ (residue final)`, and
    `E2residueEmbedZ_hmarg` gives the per-outcome marginal equality (the residue final IS
    canonically supported on the residue LAYOUT — carried as the explicit hypothesis `hsupp_res`,
    the standard `MultiplyCircuitProperty` ancilla-clean/residue-`< N` invariant), so the two sums
    match term by term (`Finset.sum_congr`).

    Realization hypotheses carried EXPLICITLY (dischargeable later): `hf_runway`/`hf_residue` (the
    two distinct oracle realizations, `mult` threaded identically) and `hsupp_res` (the residue
    final's canonical residue-layout support). -/
theorem probability_of_success_E2coset_eq (a r N m w bits cm : Nat)
    (hm : 0 < m) (hbits : 0 < bits)
    (mult : Nat → Nat) (hN : 0 < N) (hN1 : 1 < N)
    (numWin : Nat) (hw : 0 < w) (hbitsWin : numWin * w = bits) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (f_runwayIdeal f_residueIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt_c : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (hwt_i : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_residueIdeal j))
    (hf_runway : ∀ (kstep : Nat), kstep < m → ∀ (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              workMat m bits (cosetAnc w bits) kstep f_runwayIdeal y yp
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult kstep * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (hf_residue : ∀ (kstep : Nat), kstep < m →
        ∀ a b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
        workMat m bits (cosetAnc w bits) kstep f_residueIdeal a b
          = if a.val = (if b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N
                then ((mult kstep * (b.val / 2 ^ (cosetAnc w bits))) % N) * 2 ^ (cosetAnc w bits)
                else b.val)
              then 1 else 0)
    (hsupp_res : ∀ (x : Fin (2 ^ m))
        (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
        ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N) →
        Shor_final_state m bits (cosetAnc w bits) f_residueIdeal
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0) :
    probability_of_success_E2coset a r N m w bits cm f_runwayIdeal
      = probability_of_success a r N m bits (cosetAnc w bits) f_residueIdeal := by
  -- both unfold to the same outcome-weighted marginal sum
  show (∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N
            * prob_partial_meas (FormalRV.SQIRPort.basis_vector (2 ^ m) x)
                (Shor_final_state_E2coset m w bits N cm f_runwayIdeal))
      = ∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N
            * prob_partial_meas (FormalRV.SQIRPort.basis_vector (2 ^ m) x)
                (Shor_final_state m bits (cosetAnc w bits) f_residueIdeal)
  -- rewrite the runway final via the orbit bridge (P1.3c)
  rw [Shor_final_state_E2coset_eq_embed m w bits N cm hm hbits mult hN hN1
        (le_trans (Nat.le_mul_of_pos_left N (Nat.two_pow_pos cm)) hMN)
        f_runwayIdeal f_residueIdeal hwt_c hwt_i hf_runway hf_residue]
  -- per-outcome marginal equality via E2residueEmbedZ_hmarg
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_range] at hx
  congr 1
  -- match the Nat outcome `x` to the Fin (2^m) form `hmarg` consumes
  have hxeq : x = (⟨x, hx⟩ : Fin (2 ^ m)).val := rfl
  rw [hxeq]
  exact E2residueEmbedZ_hmarg m w bits numWin N cm hw hbitsWin hN hMN
    (Shor_final_state m bits (cosetAnc w bits) f_residueIdeal) hsupp_res ⟨x, hx⟩

end FormalRV.Shor.GidneyInPlace.E2ResidueEmbed
