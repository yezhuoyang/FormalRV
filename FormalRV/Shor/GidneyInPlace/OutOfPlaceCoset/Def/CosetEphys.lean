/-
  FormalRV.Shor.GidneyInPlace.CosetEphys — SAFE foundational E_phys infra.
  E_phys = I_phase ⊗ E_data, where E_data is the cosetState embedder.
-/
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Proof.BranchFactor
import FormalRV.Shor.GidneyInPlace.Primitives.Def.PhaseMarginalLift
import FormalRV.Shor.GidneyInPlace.Primitives.Def.ApproxOp
import FormalRV.Shor.CosetMarginalShorBound

namespace FormalRV.Shor.GidneyInPlace.CosetEphys

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (jointIdx jointIdx_eq_finProdFinEquiv)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.BranchFactor (jointEquiv jointEquiv_apply)
open FormalRV.Shor.GidneyInPlace.PhaseMarginalLift (PhaseLocal)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState cosetState_normSq)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)

/-! ## §0. The coset embedding matrix on the data register. -/

/-- The coset embedding matrix entry `(y, yp)`: embeds residue `yp` into the coset
    state `cosetState d N cm yp.val`.  A column of this matrix IS a `cosetState`. -/
noncomputable def cosetEmbedMat (d N cm : Nat) (y yp : Fin d) : ℂ :=
  if (y : Nat) ∈ (cosetWindow d N cm (yp.val)).image (Fin.val) then
    ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0

/-- A column of `cosetEmbedMat` is exactly a `cosetState`: `cosetEmbedMat y yp =
    cosetState d N cm yp.val y 0`. -/
theorem cosetEmbedMat_eq_cosetState (d N cm : Nat) (y yp : Fin d) :
    cosetEmbedMat d N cm y yp = cosetState d N cm yp.val y 0 := by
  unfold cosetEmbedMat cosetState
  by_cases h : y ∈ cosetWindow d N cm yp.val
  · rw [if_pos h, if_pos]
    simp only [Finset.mem_image]
    exact ⟨y, h, rfl⟩
  · rw [if_neg h, if_neg]
    simp only [Finset.mem_image, not_exists, not_and]
    intro x hx hxy
    exact h (Fin.ext hxy ▸ hx)

/-! ## §1. E_data and E_phys. -/

/-- The data-register coset embedder: `(E_data psi) y = ∑_{yp} cosetEmbedMat y yp · psi yp`. -/
noncomputable def E_data (d N cm : Nat) (psi : QState d) : QState d :=
  fun y _ => ∑ yp : Fin d, cosetEmbedMat d N cm y yp * psi yp 0

/-- The Shor-level embedding `E_phys = I_phase ⊗ E_data`, lifted via `jointEquiv`. -/
noncomputable def E_phys (m n anc N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc)) : QState (2 ^ m * 2 ^ n * 2 ^ anc) :=
  fun i _ =>
    let p := (jointEquiv (shorDvd m n anc)).symm i
    ∑ yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
      cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm p.2 yp *
        phi (jointIdx (shorDvd m n anc) p.1 yp) 0

/-! ## §2. D1 — the ACTS-FORM evaluation lemma. -/

/-- **D1.**  `E_phys` touches ONLY the data factor `y`, leaving the phase factor `x`
    fixed — the `I_phase ⊗ E_data` structure. -/
theorem E_phys_acts (m n anc N cm : Nat) (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)) :
    E_phys m n anc N cm phi (jointIdx (shorDvd m n anc) x y) 0
      = ∑ yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
          cosetEmbedMat ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m) N cm y yp *
            phi (jointIdx (shorDvd m n anc) x yp) 0 := by
  unfold E_phys
  simp only
  rw [show jointIdx (shorDvd m n anc) x y = jointEquiv (shorDvd m n anc) (x, y) from
        (jointEquiv_apply (shorDvd m n anc) x y).symm,
      Equiv.symm_apply_apply]

/-! ## §3. D2 — phase-local commute. -/

/-- **D2.**  `E_phys` commutes with every phase-only operation `P` (the `I_phase` part
    acts on `x`, the `E_data` part acts on `y`, on independent indices). -/
theorem E_phys_comm (m n anc N cm : Nat)
    (P : QState (2 ^ m * 2 ^ n * 2 ^ anc) → QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (hP : PhaseLocal (shorDvd m n anc) P)
    (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc))
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)) :
    (P (E_phys m n anc N cm phi)) (jointIdx (shorDvd m n anc) x y) 0
      = (E_phys m n anc N cm (P phi)) (jointIdx (shorDvd m n anc) x y) 0 := by
  rw [hP.acts (E_phys m n anc N cm phi) x y, E_phys_acts]
  simp_rw [E_phys_acts m n anc N cm phi _ y, hP.acts phi x _, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun yp _ => Finset.sum_congr rfl (fun x' _ => by ring))

/-! ## §4. cosetWindow disjointness (the D3 combinatorial core). -/

/-- **Disjoint windows.**  For distinct canonical residues `k ≠ kp` (both `< N`,
    `N > 0`), the coset windows are disjoint — every element `v` of the window has
    `v ≡ k (mod N)`, so it lies in at most one canonical window. -/
theorem cosetWindow_disjoint (d N cm k kp : Nat) (hN : 0 < N)
    (hk : k < N) (hkp : kp < N) (hne : k ≠ kp) :
    Disjoint (cosetWindow d N cm k) (cosetWindow d N cm kp) := by
  rw [Finset.disjoint_left]
  intro v hvk hvkp
  rw [mem_cosetWindow d N cm k hN] at hvk
  rw [mem_cosetWindow d N cm kp hN] at hvkp
  obtain ⟨j, _, hvj⟩ := hvk
  obtain ⟨jp, _, hvjp⟩ := hvkp
  have heq : k + j * N = kp + jp * N := hvj ▸ hvjp
  have hk0 : (k + j * N) % N = k % N := by
    rw [Nat.add_mul_mod_self_right]
  have hkp0 : (kp + jp * N) % N = kp % N := by
    rw [Nat.add_mul_mod_self_right]
  rw [heq, hkp0, Nat.mod_eq_of_lt hkp] at hk0
  rw [Nat.mod_eq_of_lt hk] at hk0
  exact hne hk0.symm

/-! ## §5. D3 — the generic marginal isometry. -/

/-- **`normSq` distributes over a Finset sum with at most one nonzero term.**  If the
    summands `f` over `s` are pairwise "at most one nonzero" (any two distinct indices
    in `s` have at least one zero), then `‖∑_{i∈s} f‖² = ∑_{i∈s} ‖f‖²`.  (At most one
    term survives, so the cross terms vanish.) -/
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
    symm
    apply Finset.sum_subset hts
    intro i _ hi
    simp only [ht, Finset.mem_filter, not_and, not_not] at hi
    exact hi (by assumption)
  have hsum2 : ∑ i ∈ s, Complex.normSq (f i) = ∑ i ∈ t, Complex.normSq (f i) := by
    symm
    apply Finset.sum_subset hts
    intro i _ hi
    simp only [ht, Finset.mem_filter, not_and, not_not] at hi
    rw [hi (by assumption), Complex.normSq_zero]
  rw [hsum1, hsum2]
  rcases Nat.eq_zero_or_pos t.card with h0 | h1
  · rw [Finset.card_eq_zero] at h0
    rw [h0]; simp
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp h1
    have hseq : t = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨ha, fun b hb => Finset.card_le_one.mp hcard b hb a ha⟩
    rw [hseq, Finset.sum_singleton, Finset.sum_singleton]

/-- **D3 — the generic per-phase-branch marginal isometry.**  For a state supported on
    canonical residues (`yp < N`, killed by `hsupp` above), `E_phys` preserves the
    phase marginal: each row `y` lands in at most one canonical coset window (window
    disjointness), the inner sum collapses to a single `1/√2^cm`-weighted residue, and
    summing `2^cm` window rows recovers the residue's Born mass. -/
theorem E_phys_marginal (m n anc N cm : Nat)
    (phi : QState (2 ^ m * 2 ^ n * 2 ^ anc)) (hN : 0 < N)
    (hMN : 2 ^ cm * N ≤ (2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)
    (hsupp : ∀ (x : Fin (2 ^ m)) (yp : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)),
      N ≤ yp.val → phi (jointIdx (shorDvd m n anc) x yp) 0 = 0)
    (x : Fin (2 ^ m)) :
    (∑ y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
        Complex.normSq (E_phys m n anc N cm phi (jointIdx (shorDvd m n anc) x y) 0))
      = (∑ y : Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m),
          Complex.normSq (phi (jointIdx (shorDvd m n anc) x y) 0)) := by
  classical
  set d := (2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m with hd
  set phiCol : Fin d → ℂ := fun yp => phi (jointIdx (shorDvd m n anc) x yp) 0 with hpc
  -- canonical residues
  set canon : Finset (Fin d) := Finset.univ.filter (fun yp => yp.val < N) with hcanon
  have hfit : ∀ yp : Fin d, yp.val < N → yp.val + (2 ^ cm - 1) * N < d := by
    intro yp hyp
    have hpos : 0 < 2 ^ cm := Nat.two_pow_pos cm
    have hle : N ≤ 2 ^ cm * N := Nat.le_mul_of_pos_left N hpos
    have hsplit : (2 ^ cm - 1) * N + N = 2 ^ cm * N := by
      rw [Nat.sub_mul, one_mul]
      omega
    omega
  -- STEP 1: each marginal term collapses to a single residue's Born mass via disjointness.
  have hcollapse : ∀ y : Fin d,
      Complex.normSq (∑ yp : Fin d, cosetEmbedMat d N cm y yp * phiCol yp)
        = ∑ yp ∈ canon, (if y ∈ cosetWindow d N cm yp.val then (1 / 2 ^ cm : ℝ) else 0)
            * Complex.normSq (phiCol yp) := by
    intro y
    -- restrict the inner sum to canonical residues (others have phiCol = 0).
    have hrestrict : (∑ yp : Fin d, cosetEmbedMat d N cm y yp * phiCol yp)
        = ∑ yp ∈ canon, cosetEmbedMat d N cm y yp * phiCol yp := by
      symm
      apply Finset.sum_subset (Finset.subset_univ canon)
      intro yp _ hyp
      simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hyp
      have : phiCol yp = 0 := hsupp x yp hyp
      rw [this, mul_zero]
    rw [hrestrict]
    -- at most one canonical residue's window contains y.
    have hpair : ∀ a ∈ canon, ∀ b ∈ canon, a ≠ b →
        cosetEmbedMat d N cm y a * phiCol a = 0 ∨ cosetEmbedMat d N cm y b * phiCol b = 0 := by
      intro a ha b hb hab
      simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_cases hya : y ∈ cosetWindow d N cm a.val
      · by_cases hyb : y ∈ cosetWindow d N cm b.val
        · exact absurd (Finset.disjoint_left.mp
            (cosetWindow_disjoint d N cm a.val b.val hN ha hb
              (fun h => hab (Fin.ext h))) hya) (by simpa using hyb)
        · right
          have : cosetEmbedMat d N cm y b = 0 := by
            rw [cosetEmbedMat_eq_cosetState, cosetState, if_neg hyb]
          rw [this, zero_mul]
      · left
        have : cosetEmbedMat d N cm y a = 0 := by
          rw [cosetEmbedMat_eq_cosetState, cosetState, if_neg hya]
        rw [this, zero_mul]
    -- normSq of the restricted sum: at most one nonzero term.
    rw [normSq_sum_canon_pairwise canon (fun yp => cosetEmbedMat d N cm y yp * phiCol yp) hpair]
    apply Finset.sum_congr rfl
    intro yp _
    rw [Complex.normSq_mul, cosetEmbedMat_eq_cosetState, cosetState_normSq]
  -- STEP 2: rewrite the LHS via E_phys_acts and hcollapse.
  have hLHS : (∑ y : Fin d,
      Complex.normSq (E_phys m n anc N cm phi (jointIdx (shorDvd m n anc) x y) 0))
      = ∑ y : Fin d, ∑ yp ∈ canon,
          (if y ∈ cosetWindow d N cm yp.val then (1 / 2 ^ cm : ℝ) else 0)
            * Complex.normSq (phiCol yp) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [show E_phys m n anc N cm phi (jointIdx (shorDvd m n anc) x y) 0
          = ∑ yp : Fin d, cosetEmbedMat d N cm y yp * phiCol yp from
        E_phys_acts m n anc N cm phi x y]
    exact hcollapse y
  rw [hLHS, Finset.sum_comm]
  -- STEP 3: ∑_y [if y ∈ window yp then 1/2^cm else 0] = card(window) / 2^cm = 1.
  have hinner : ∀ yp ∈ canon,
      (∑ y : Fin d, (if y ∈ cosetWindow d N cm yp.val then (1 / 2 ^ cm : ℝ) else 0)
        * Complex.normSq (phiCol yp))
      = Complex.normSq (phiCol yp) := by
    intro yp hyp
    simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and] at hyp
    rw [← Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
        cosetWindow_card d N cm yp.val hN (hfit yp hyp), nsmul_eq_mul]
    rw [show ((2 ^ cm : ℕ) : ℝ) * (1 / 2 ^ cm) = 1 by
      push_cast; field_simp]
    rw [one_mul]
  rw [Finset.sum_congr rfl hinner]
  -- STEP 4: ∑_{yp ∈ canon} normSq(phiCol yp) = ∑_yp normSq(phiCol yp) (hsupp).
  show (∑ yp ∈ canon, Complex.normSq (phiCol yp)) = ∑ y : Fin d, Complex.normSq (phiCol y)
  apply Finset.sum_subset (Finset.subset_univ canon)
  intro yp _ hyp
  simp only [hcanon, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hyp
  show Complex.normSq (phi (jointIdx (shorDvd m n anc) x yp) 0) = 0
  rw [hsupp x yp hyp, Complex.normSq_zero]

end FormalRV.Shor.GidneyInPlace.CosetEphys
