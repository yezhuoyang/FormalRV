/-
  FormalRV.Shor.CosetMarginalShorBound — the SOUND approximate-Shor bound for
  GE2021's coset modexp gate, via PHASE-REGISTER MARGINAL invariance.
  ════════════════════════════════════════════════════════════════════════════

  WHY THIS FILE EXISTS (no-cheating audit, 2026-06-13).  The earlier
  `ApproxCosetShorBound` / `CosetBornWeight` route compared the coset family
  against the CANONICAL-residue family via the FULL-STATE `normSqDist`.  That
  obligation is UNSATISFIABLE: the GE2021 coset gadget keeps the data register
  UNREDUCED (`WindowedCoset.cosetRep_of_modProduct`: the accumulator holds `a·x`,
  generally `≥ N`), so the coset and canonical final states sit on DIFFERENT
  data-register supports — their `normSqDist` is `Ω(1)`, not `≤ 2·7.64·10⁻⁸`.

  THE SOUND COMPARISON.  `probability_of_success` reads ONLY the phase register;
  `prob_partial_meas (|x⟩) φ` is the Born MARGINAL `∑_y ‖φ_{x·k+y}‖²` over the
  data register `y` (`ApproxTransfer.prob_partial_meas_basis_eq`).  This marginal
  is INVARIANT under any permutation `σ` of the data register: relabeling which
  basis state holds which residue cannot change the phase-register statistics.
  GE2021's coset trick is exactly such a relabeling (off wrap): the coset orbit
  `{cosetrep(a^j)}` is the canonical orbit `{a^j mod N}` with each residue moved
  to its coset representative.  So OFF WRAP the two final states are related by a
  data-register permutation and have IDENTICAL phase marginals; the wrap set
  carries Born weight `≤ totalDeviation = 7.64·10⁻⁸`, which is all the deviation
  the approximate bound pays.

  ════════════════════════════════════════════════════════════════════════════
  WHAT IS PROVEN HERE (kernel-clean, no `sorry`/`native_decide`/axioms)
  ════════════════════════════════════════════════════════════════════════════

  §1  `prob_partial_meas_basis_dataPerm` — THE KEYSTONE (exact).  If `φ₁`'s
      `x`-slice equals `φ₂`'s `x`-slice composed with a data permutation `σ`, the
      two Born marginals at `|x⟩` are EQUAL.  (Reindex by `Equiv.sum_comp`.)
      This is the precise statement that the data representation is irrelevant to
      the measured outcome.

  §2  `prob_partial_meas_basis_dataPerm_offBad` — the approximate version.  If the
      slices agree under `σ` off a finite data "bad" set `badY`, the marginals
      differ by at most the Born weight each state places on `badY`.

  §3  `prob_of_success_dataPerm_offBad` — lifts §2 through the `r_found`-weighted
      success sum (`r_found ≤ 1`): `|ΔP_success| ≤ (coset wrap weight) + (ideal
      wrap weight)`.

  §4  `CosetMarginalRelabel` — the CORRECTED, TRUE-shaped frontier (replacing the
      false `CosetIdealL1Bound`): a data-register permutation `σ`, a per-outcome
      wrap set, the off-wrap relabel agreement, and the two wrap Born-weight
      bounds.  From it `coset_shor_succeeds_marginal` PROVES
      `P_success(coset) ≥ P_ideal − 2·ε`.  Its `agree`/`wrap_le` fields are now
      SATISFIABLE in principle (the coset IS a data permutation off wrap), unlike
      the discredited full-state obligation.

  The remaining (genuine, TRUE) work is to BUILD a `CosetMarginalRelabel` witness
  from the real coset gadget by lifting `WindowedCoset.cosetAdd_correct` (exact
  off wrap) through the orbit machinery — the eigenvalue-preservation lift.  That
  is named, not assumed proven, and is no longer an unsatisfiable obligation.
-/
import FormalRV.Shor.ApproxTransfer

namespace FormalRV.Shor.CosetMarginalShorBound

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer

/-! ## §1. THE KEYSTONE — Born marginal is invariant under a data-register
       permutation (exact). -/

/-- **Marginal invariance (exact).**  If the `x`-slice of `φ₁` equals the
    `x`-slice of `φ₂` reindexed by a data-register permutation `σ`, the Born
    marginals at `|x⟩` coincide.  This is why the coset representation cannot
    change Shor's measured statistics: it only permutes which data basis state
    carries which residue. -/
theorem prob_partial_meas_basis_dataPerm
    {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ₁ φ₂ : QState full_dim) (x : Fin m_dim)
    (σ : Equiv.Perm (Fin (full_dim / m_dim)))
    (hrel : ∀ y, φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ y)) 0) :
    prob_partial_meas (basis_vector m_dim x.val) φ₁
      = prob_partial_meas (basis_vector m_dim x.val) φ₂ := by
  rw [prob_partial_meas_basis_eq φ₁ x h, prob_partial_meas_basis_eq φ₂ x h]
  calc ∑ y, Complex.normSq (φ₁ (jointIdx h x y) 0)
      = ∑ y, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0) :=
        Finset.sum_congr rfl (fun y _ => by rw [hrel y])
    _ = ∑ y, Complex.normSq (φ₂ (jointIdx h x y) 0) :=
        Equiv.sum_comp σ (fun y => Complex.normSq (φ₂ (jointIdx h x y) 0))

/-! ## §2. The approximate version — agreement under `σ` off a finite data bad
       set bounds the marginal gap by the bad-set Born weight. -/

/-- **Marginal invariance off a bad set.**  If the `x`-slices agree under `σ`
    everywhere off a finite data set `badY`, the marginals at `|x⟩` differ by at
    most the Born weight each state carries on `badY` (the wrap offsets). -/
theorem prob_partial_meas_basis_dataPerm_offBad
    {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (φ₁ φ₂ : QState full_dim) (x : Fin m_dim)
    (σ : Equiv.Perm (Fin (full_dim / m_dim)))
    (badY : Finset (Fin (full_dim / m_dim)))
    (hrel : ∀ y, y ∉ badY → φ₁ (jointIdx h x y) 0 = φ₂ (jointIdx h x (σ y)) 0) :
    |prob_partial_meas (basis_vector m_dim x.val) φ₁
        - prob_partial_meas (basis_vector m_dim x.val) φ₂|
      ≤ (∑ y ∈ badY, Complex.normSq (φ₁ (jointIdx h x y) 0))
          + (∑ y ∈ badY, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)) := by
  rw [prob_partial_meas_basis_eq φ₁ x h, prob_partial_meas_basis_eq φ₂ x h]
  -- Reindex the φ₂ marginal by σ so both sums range over the same index.
  have h2 : (∑ y, Complex.normSq (φ₂ (jointIdx h x y) 0))
      = ∑ y, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0) :=
    (Equiv.sum_comp σ (fun y => Complex.normSq (φ₂ (jointIdx h x y) 0))).symm
  rw [h2, ← Finset.sum_sub_distrib]
  -- Off `badY` every summand vanishes, so the whole sum collapses to `badY`.
  have hcollapse : (∑ y, (Complex.normSq (φ₁ (jointIdx h x y) 0)
        - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)))
      = ∑ y ∈ badY, (Complex.normSq (φ₁ (jointIdx h x y) 0)
        - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ badY)
    intro y _ hy
    rw [hrel y hy]; ring
  rw [hcollapse]
  calc |∑ y ∈ badY, (Complex.normSq (φ₁ (jointIdx h x y) 0)
          - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0))|
      ≤ ∑ y ∈ badY, |Complex.normSq (φ₁ (jointIdx h x y) 0)
          - Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ badY, (Complex.normSq (φ₁ (jointIdx h x y) 0)
          + Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)) := by
        apply Finset.sum_le_sum
        intro y _
        rw [abs_le]
        constructor <;>
          nlinarith [Complex.normSq_nonneg (φ₁ (jointIdx h x y) 0),
                     Complex.normSq_nonneg (φ₂ (jointIdx h x (σ y)) 0)]
    _ = (∑ y ∈ badY, Complex.normSq (φ₁ (jointIdx h x y) 0))
          + (∑ y ∈ badY, Complex.normSq (φ₂ (jointIdx h x (σ y)) 0)) :=
        Finset.sum_add_distrib

/-! ## §3. The success-probability transfer — lift §2 through the `r_found`-
       weighted success sum. -/

/-- The Shor full register `2^m·2^n·2^anc` is divisible by the phase register
    `2^m` (data register `= 2^n·2^anc`). -/
theorem shorDvd (m n anc : Nat) : (2 ^ m) ∣ (2 ^ m * 2 ^ n * 2 ^ anc) :=
  ⟨2 ^ n * 2 ^ anc, by ring⟩

/-- **§3 — success transfer under a data-register relabel off a wrap set.**  If
    the coset and ideal final states are related, per phase-outcome `x`, by a
    fixed data permutation `σ` off a per-outcome wrap set `badY x`, then the
    success probabilities differ by at most the total Born weight the two states
    carry on the wrap sets.  (`r_found ≤ 1` drops the indicator; §2 bounds each
    outcome.)  The `σ`-image weight of the ideal state appears because the ideal
    marginal is reindexed by `σ`. -/
theorem prob_of_success_dataPerm_offBad
    (a r N m n anc : Nat) (f_coset f_ideal : Nat → BaseUCom (n + anc))
    (σ : Equiv.Perm (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)))
    (badY : Fin (2 ^ m) → Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m)))
    (hagree : ∀ (x : Fin (2 ^ m)) (y), y ∉ badY x →
        Shor_final_state m n anc f_coset (jointIdx (shorDvd m n anc) x y) 0
          = Shor_final_state m n anc f_ideal (jointIdx (shorDvd m n anc) x (σ y)) 0) :
    |probability_of_success a r N m n anc f_coset
        - probability_of_success a r N m n anc f_ideal|
      ≤ (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
            Complex.normSq (Shor_final_state m n anc f_coset
              (jointIdx (shorDvd m n anc) x y) 0))
        + (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
            Complex.normSq (Shor_final_state m n anc f_ideal
              (jointIdx (shorDvd m n anc) x (σ y)) 0)) := by
  set s₁ := Shor_final_state m n anc f_coset with hs₁
  set s₂ := Shor_final_state m n anc f_ideal with hs₂
  have hdvd := shorDvd m n anc
  -- expand the success-sum difference into one indexed difference
  have hdecomp : probability_of_success a r N m n anc f_coset
      - probability_of_success a r N m n anc f_ideal
      = ∑ x ∈ Finset.range (2 ^ m),
          r_found x m r a N *
            (prob_partial_meas (basis_vector (2 ^ m) x) s₁
              - prob_partial_meas (basis_vector (2 ^ m) x) s₂) := by
    unfold probability_of_success
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hs₁, ← hs₂]; ring
  rw [hdecomp]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun x => |r_found x m r a N *
          (prob_partial_meas (basis_vector (2 ^ m) x) s₁
            - prob_partial_meas (basis_vector (2 ^ m) x) s₂)|) (2 ^ m)]
  -- per-outcome bound (drop `r_found ≤ 1`, then §2), then split the sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [abs_mul, abs_of_nonneg (r_found_nonneg x.val m r a N)]
  calc r_found x.val m r a N *
          |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
            - prob_partial_meas (basis_vector (2 ^ m) x.val) s₂|
      ≤ 1 * |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
            - prob_partial_meas (basis_vector (2 ^ m) x.val) s₂| :=
        mul_le_mul_of_nonneg_right (r_found_le_one _ _ _ _ _) (abs_nonneg _)
    _ = |prob_partial_meas (basis_vector (2 ^ m) x.val) s₁
            - prob_partial_meas (basis_vector (2 ^ m) x.val) s₂| := one_mul _
    _ ≤ _ := prob_partial_meas_basis_dataPerm_offBad hdvd s₁ s₂ x σ (badY x)
              (hagree x)

/-! ## §4. The corrected obligation + the headline coset Shor bound.

`CosetMarginalRelabel` is the SOUND replacement of the discredited
`ApproxCosetShorBound.CosetIdealL1Bound`.  It carries exactly the marginal data
that §3 consumes: a data-register permutation `σ`, a per-outcome wrap set, the
off-wrap relabel agreement, and the two wrap Born-weight bounds.  Crucially its
fields are SATISFIABLE in principle — off wrap the coset state IS a data
permutation of the ideal — unlike the full-state `normSqDist`-to-canonical
obligation, which is `Ω(1)` and unsatisfiable. -/

/-- **The corrected, sound frontier.**  A witness that the coset final state is,
    per phase outcome and off a wrap set, a fixed data-register permutation `σ`
    of the ideal final state, with both states placing Born weight `≤ ε` on the
    wrap set.  The honest replacement for `CosetIdealL1Bound`. -/
structure CosetMarginalRelabel
    (a r N m n anc : Nat) (f_coset f_ideal : Nat → BaseUCom (n + anc)) (ε : ℝ) where
  /-- The data-register relabeling (coset rep ↔ canonical residue). -/
  σ : Equiv.Perm (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m))
  /-- The per-outcome wrap (bad) offsets in the data register. -/
  badY : Fin (2 ^ m) → Finset (Fin ((2 ^ m * 2 ^ n * 2 ^ anc) / 2 ^ m))
  /-- OFF WRAP the coset state is the ideal state with the data register
      relabeled by `σ` (the lift of `WindowedCoset.cosetAdd_correct`, exact off
      wrap, through the QPE orbit). -/
  agree : ∀ (x : Fin (2 ^ m)) (y), y ∉ badY x →
      Shor_final_state m n anc f_coset (jointIdx (shorDvd m n anc) x y) 0
        = Shor_final_state m n anc f_ideal (jointIdx (shorDvd m n anc) x (σ y)) 0
  /-- The coset state's total Born weight on the wrap set is `≤ ε`. -/
  coset_wrap_le :
    (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
        Complex.normSq (Shor_final_state m n anc f_coset
          (jointIdx (shorDvd m n anc) x y) 0)) ≤ ε
  /-- The ideal state's total Born weight on the `σ`-relabeled wrap set is `≤ ε`. -/
  ideal_wrap_le :
    (∑ x : Fin (2 ^ m), ∑ y ∈ badY x,
        Complex.normSq (Shor_final_state m n anc f_ideal
          (jointIdx (shorDvd m n anc) x (σ y)) 0)) ≤ ε

/-- **THE SOUND APPROXIMATE COSET SHOR BOUND (parametric).**  Given the ideal
    family's verified bound `P_success(f_ideal) ≥ P_ideal` and a
    `CosetMarginalRelabel` witness with wrap weight `≤ ε`, the coset gate
    succeeds with probability `≥ P_ideal − 2·ε`.

    Proof: §3 gives `|ΔP_success| ≤ ε + ε`; combine with the ideal bound.  Unlike
    `ApproxCosetShorBound.coset_shor_succeeds_param`, the obligation `R` is the
    SATISFIABLE marginal-relabel fact, not the unsatisfiable full-state
    distance-to-canonical. -/
theorem coset_shor_succeeds_marginal
    (a r N m n anc : Nat) (f_coset f_ideal : Nat → BaseUCom (n + anc))
    (ε P_ideal : ℝ)
    (h_ideal : probability_of_success a r N m n anc f_ideal ≥ P_ideal)
    (R : CosetMarginalRelabel a r N m n anc f_coset f_ideal ε) :
    probability_of_success a r N m n anc f_coset ≥ P_ideal - 2 * ε := by
  have htrans := prob_of_success_dataPerm_offBad a r N m n anc f_coset f_ideal
    R.σ R.badY R.agree
  have hbound : |probability_of_success a r N m n anc f_coset
        - probability_of_success a r N m n anc f_ideal| ≤ 2 * ε := by
    refine le_trans htrans ?_
    have := add_le_add R.coset_wrap_le R.ideal_wrap_le
    linarith
  have hsub := abs_le.mp hbound
  linarith [hsub.1]

end FormalRV.Shor.CosetMarginalShorBound
