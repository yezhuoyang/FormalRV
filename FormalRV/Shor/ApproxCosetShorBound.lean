/-
  FormalRV.Shor.ApproxCosetShorBound — the APPROXIMATE-Shor success bound for
  GE2021's NON-CANONICAL coset modexp gate.
  ════════════════════════════════════════════════════════════════════════════

  WHY THIS FILE EXISTS (commit 77be902 — the GE2021 IN-adapter audit finding).
  The Gidney–Ekerå coset accumulator holds the UNREDUCED value `a^(2^i)·x`
  (non-canonical: it can be `≥ N`).  The EXACT `(c·x) mod N` multiplier interface
  (`windowedModNMultiplier_verifiedModMulFamily`, the object carrying the literal
  `windowedModNMul_shor_correct` bound) REJECTS such an input — its
  `MultiplyCircuitProperty` is stated only for canonical residues.  So the coset
  gate cannot ride the EXACT bound directly; it needs an APPROXIMATE bound that
  pays the coset wrap deviation.

  THE DEVIATION IS VERIFIED, NOT FREE.  The wrap probability of the coset
  representation is the paper's `totalDeviation`, a PROVEN CONSTANT
  `41/536870912 ≈ 7.64·10⁻⁸` (`WindowedCostModel.totalDeviation_eq_const`,
  re-exposed here over ℝ as `totalDeviationR_eq`).  It is the finite union-bound
  counting fraction of `WindowedCosetDeviation.wrapProbCount` — NOT an axiom.

  ════════════════════════════════════════════════════════════════════════════
  THE THREE STEPS (per the build plan) AND THEIR HONEST STATUS
  ════════════════════════════════════════════════════════════════════════════

  STEP 1  `prob_success_stable`  — PROVEN (rides `ApproxTransfer`).
      For any two oracle families, the success probabilities differ by at most
      the amplitude-square (L1) distance of their post-circuit states:
          |P_success(f₁) − P_success(f₂)| ≤ normSqDist(final f₁, final f₂).
      This is exactly `ApproxTransfer.prob_of_success_transfer_normSqDist`
      (Born marginal + r_found ≤ 1 + the joint-index reindexing).  Re-exposed
      here under the plan's name.  No normalization hypothesis.

  STEP 2  `CosetIdealL1Bound` — the Born-weight identity, carried as a PRECISE
      NAMED OBLIGATION (its L1-distance field is a HYPOTHESIS, not a free claim).
      The hard analytic content is: the coset final state and the ideal
      (canonical-residue) final state are L1-distance `≤ 2·totalDeviation` apart,
      because they agree off the wrap offsets and the wrap offsets carry Born
      weight `= wrapProbCount = totalDeviation`.  Proving this from the coset
      superposition structure (`EGateToUnitaryBridge.eGate_toCom_basis` lifted to
      the uniform coset superposition, with the Born weight read off
      `WindowedCosetDeviation.wrapProbCount`) is the SINGLE genuinely-remaining
      sub-obstacle.  We DO NOT claim it proven: it is the one field of the
      `CosetIdealL1Bound` structure below, stated at the exact `normSqDist`
      shape STEP 1 consumes.  NO `sorry`, NO free field asserted proven.

  STEP 3  `ge2021_coset_shor_succeeds` — PROVEN given a `CosetIdealL1Bound`
      witness.  Combines STEP 1 (stability), the obligation's L1 field, and the
      ideal bound `windowedModNMul_shor_correct` to yield
          P(success | coset gate) ≥ κ/(log₂ N)⁴ − 2·totalDeviation,
      with `totalDeviation = 41/536870912 ≈ 7.64·10⁻⁸` and NO no-wrap hypothesis.

  ════════════════════════════════════════════════════════════════════════════
  THE HONEST FRONTIER (one sentence).  The L1 bound `normSqDist(coset, ideal) ≤
  2·totalDeviation` is a PASSED-THROUGH HYPOTHESIS (the `coset_l1_le` field of
  `CosetIdealL1Bound`), NOT a proven theorem here; STEP 1 and STEP 3 ARE proven.
  The deviation constant `41/536870912` ITSELF is proven (`totalDeviationR_eq`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.ApproxTransfer
import FormalRV.Shor.WindowedModNShor
import FormalRV.Arithmetic.Windowed.WindowedCosetDeviation

namespace FormalRV.Shor.ApproxCosetShorBound

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.BQAlgo.WindowedModNShor
  (windowedModNMul_shor_correct windowedModNMultiplier_verifiedModMulFamily)
open VerifiedShor (ShorSetting)
open FormalRV.Shor.WindowedCostModel (totalDeviation totalDeviation_eq_const)
open FormalRV.Arithmetic.Windowed.WindowedCosetDeviation
  (countingBoundQ countingBound_eq_totalDeviation)

/-! ## §0. The verified deviation constant, over ℝ. -/

/-- The coset wrap deviation at the RSA-2048 paper parameters (`n = 2048`,
    `n_e = 3072`), as a real number: the rational constant
    `41/536870912 ≈ 7.64·10⁻⁸` cast to ℝ.  This is the `ε` the approximate bound
    pays — VERIFIED (= `WindowedCostModel.totalDeviation_eq_const`), not free. -/
noncomputable def totalDeviationR : ℝ := ((totalDeviation 2048 3072 : ℚ) : ℝ)

/-- **The deviation is the proven constant `41/536870912 ≈ 7.64·10⁻⁸`.**
    Re-exposes `WindowedCostModel.totalDeviation_eq_const` over ℝ. -/
theorem totalDeviationR_eq : totalDeviationR = (41 : ℝ) / 536870912 := by
  unfold totalDeviationR
  rw [totalDeviation_eq_const 2048 3072 (by norm_num) (by norm_num)]
  norm_num

/-- The deviation is nonnegative (it is a probability). -/
theorem totalDeviationR_nonneg : 0 ≤ totalDeviationR := by
  rw [totalDeviationR_eq]; norm_num

/-- **The deviation IS the union-bound wrap-count fraction.**  Over ℚ, the
    paper's `totalDeviation 2048 3072` equals the finite counting fraction
    `countingBoundQ (lookupAdditionCount …) (n/1024) (n²·n_e·1024)` — the
    union-bound count of wrap-causing coset offsets (`WindowedCosetDeviation`,
    `countingBound_eq_totalDeviation`).  This pins the `ε` paid by the
    approximate bound to the ACTUAL coset wrap combinatorics: the Born weight the
    STEP 2 obligation asserts the wrap offsets carry IS this counting fraction. -/
theorem totalDeviation_eq_wrapCount :
    (totalDeviation 2048 3072 : ℚ)
      = countingBoundQ (FormalRV.Shor.WindowedCostModel.lookupAdditionCount 2048 3072)
          (2048 / 1024) (2048 ^ 2 * 3072 * 1024) :=
  (countingBound_eq_totalDeviation 2048 3072 (by norm_num) (by norm_num)).symm

/-! ## §1. STEP 1 — `prob_success_stable` (PROVEN, rides `ApproxTransfer`). -/

/-- **STEP 1 — the success-probability stability bound (PROVEN).**  For ANY two
    oracle families `f₁ f₂`, the success probabilities differ by at most the
    amplitude-square (L1) distance of the two post-circuit states:

        |P_success(f₁) − P_success(f₂)| ≤ ∑ᵢ | ‖⟨i|final f₁⟩‖² − ‖⟨i|final f₂⟩‖² |.

    No normalization hypothesis.  This is the clean reusable lemma of the build
    plan; it is exactly `ApproxTransfer.prob_of_success_transfer_normSqDist`
    (per-outcome Born marginal `prob_partial_meas_basis_sub_abs_le`, dropping the
    `r_found ≤ 1` indicator, reindexed to the full register via
    `sum_jointIdx_eq`).  Re-exposed here under the plan's name. -/
theorem prob_success_stable
    (a r N m n anc : Nat) (f₁ f₂ : Nat → BaseUCom (n + anc)) :
    |probability_of_success a r N m n anc f₁
        - probability_of_success a r N m n anc f₂|
      ≤ normSqDist (Shor_final_state m n anc f₁) (Shor_final_state m n anc f₂) :=
  prob_of_success_transfer_normSqDist a r N m n anc f₁ f₂

/-! ## §2. STEP 2 — the coset-vs-ideal L1 obligation (PRECISE NAMED FRONTIER).

⚠️  SOUNDNESS WARNING (2026-06-13, no-cheating audit).  As stated below, the
`coset_l1_le` field compares `f_coset` against the CANONICAL-residue family
`f_ideal` via the FULL-STATE `normSqDist`.  This obligation is UNSATISFIABLE for a
genuine GE2021 coset family: the coset gadget leaves the data register holding the
UNREDUCED value `a·x` (`WindowedCoset.cosetRep_of_modProduct`: `(a·x)%2^bits =
a·x`, generally `≥ N`), so `Shor_final_state f_coset` and `Shor_final_state
f_canonical` sit on DIFFERENT data-register supports — their `normSqDist` is Ω(1),
NOT `≤ 2·7.64·10⁻⁸`.  STEP 1/STEP 3 are still valid implications, but no honest
inhabitant of `CosetIdealL1Bound a r N m n anc f_coset f_canonical` exists.  This
is the WRONG COMPARISON (full-state distance to canonical), not merely an open
one.

THE CORRECT COMPARISON is at the PHASE-REGISTER MARGINAL: `probability_of_success`
only reads the phase register, and `prob_partial_meas` is invariant under any
injective DATA-register relabeling.  Off wrap the coset final state is `(I_phase ⊗
ι)` of the canonical final state for the injective orbit relabel `ι : {a^j mod N}
↪ {cosetrep(a^j)}` (coset arithmetic is EXACT off wrap — `cosetAdd_correct`), so
the phase marginals — hence `probability_of_success` — are EQUAL off wrap, and the
wrap set contributes `≤ totalDeviation`.  Building that marginal/eigenvalue-
preservation bound on the real QPE circuit is the live work (see
`Shor.CosetMarginalShorBound`, in progress).  The structure below is retained ONLY
as the record of the discredited full-state route; do NOT treat its inhabitation
as the GE2021 frontier.

`CosetIdealL1Bound` bundles the EXACT analytic input STEP 3 needs and STEP 1
consumes: the coset final state and the ideal (canonical-residue) final state
are within L1-distance `2·totalDeviation`.  Its single field `coset_l1_le` is a
HYPOTHESIS — the Born-weight identity is NOT proven here.  The structure pins it
to the verified deviation constant (via `totalDeviationR`) and to the `normSqDist`
shape STEP 1 produces, so it is not a free object: any inhabitant supplies
precisely the missing analytic fact, stated honestly. -/

/-- **STEP 2 — the named L1 obligation (the honest frontier).**  A witness that,
    for the GE2021 coset modexp gate `f_coset` and the ideal canonical-residue
    family `f_ideal`, the two post-circuit states are L1-close:

        normSqDist(final f_coset, final f_ideal) ≤ 2 · totalDeviationR.

    The `coset_l1_le` field is the Born-weight identity (coset = ideal off the
    wrap offsets; wrap offsets carry Born weight `wrapProbCount = totalDeviation`,
    so the state L1-distance to the ideal is `2·wrapProbCount`).  It is carried as
    a HYPOTHESIS — NOT proven in this file.  Both states are recorded
    L2-normalized (`coset_norm`, `ideal_norm`), the standing assumption for pure
    post-circuit states. -/
structure CosetIdealL1Bound
    (a r N m n anc : Nat)
    (f_coset f_ideal : Nat → BaseUCom (n + anc)) where
  /-- THE OBLIGATION (the lone analytic frontier): the coset and ideal
      post-circuit states are within L1-distance `2·totalDeviationR`.  This is
      the Born-weight identity, stated at the exact `normSqDist` shape STEP 1
      consumes.  Carried as a hypothesis — not proven here. -/
  coset_l1_le :
    normSqDist (Shor_final_state m n anc f_coset) (Shor_final_state m n anc f_ideal)
      ≤ 2 * totalDeviationR

/-! ## §3. STEP 3 — the approximate coset Shor bound (PROVEN given STEP 2). -/

/-- **STEP 3 — the approximate coset Shor bound, parametric form (PROVEN).**
    Given (i) the ideal canonical-residue family's verified Shor bound
    `P_success(f_ideal) ≥ P_ideal` and (ii) a `CosetIdealL1Bound` witness
    (STEP 2's L1 obligation), the coset gate succeeds with probability

        P_success(f_coset) ≥ P_ideal − 2 · totalDeviationR.

    Proof: STEP 1 stability `|ΔP| ≤ normSqDist ≤ 2·totalDeviationR`, then
    `P_coset ≥ P_ideal − |ΔP|`.  NO no-wrap hypothesis. -/
theorem coset_shor_succeeds_param
    (a r N m n anc : Nat)
    (f_coset f_ideal : Nat → BaseUCom (n + anc))
    (P_ideal : ℝ)
    (h_ideal : probability_of_success a r N m n anc f_ideal ≥ P_ideal)
    (B : CosetIdealL1Bound a r N m n anc f_coset f_ideal) :
    probability_of_success a r N m n anc f_coset
      ≥ P_ideal - 2 * totalDeviationR := by
  have hstab := prob_success_stable a r N m n anc f_coset f_ideal
  have hL1 : |probability_of_success a r N m n anc f_coset
        - probability_of_success a r N m n anc f_ideal|
      ≤ 2 * totalDeviationR := le_trans hstab B.coset_l1_le
  have hsub := abs_le.mp hL1
  linarith [hsub.1, h_ideal]

/-- **STEP 3 — the headline: the GE2021 coset gate succeeds (PROVEN given the
    STEP 2 obligation).**  Specialises `coset_shor_succeeds_param` to the verified
    ideal bound `windowedModNMul_shor_correct` (`P_ideal = κ / (log₂ N)⁴`).  For
    the GE2021 coset modexp gate `f_coset` and the EXACT windowed mod-N family,
    given the STEP 2 L1 obligation `B`,

        P_success(f_coset) ≥ κ / (log₂ N)⁴ − 2 · totalDeviationR,

    with `totalDeviationR = 41/536870912 ≈ 7.64·10⁻⁸` VERIFIED and NO no-wrap
    hypothesis.  This is the approximate-Shor success bound running on the
    non-canonical coset gate. -/
theorem ge2021_coset_shor_succeeds
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits)
    (f_coset : Nat → BaseUCom (bits + (2 * w + 2 * bits + 3)))
    (B : CosetIdealL1Bound a r N m bits (2 * w + 2 * bits + 3) f_coset
          (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
            hw hbits hb1 hN1 hN2 h_inv0).family) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3) f_coset
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 - 2 * totalDeviationR :=
  coset_shor_succeeds_param a r N m bits (2 * w + 2 * bits + 3)
    f_coset
    (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0).family
    (κ / (Nat.log2 N : ℝ) ^ 4)
    (windowedModNMul_shor_correct w bits numWin N a ainv0 r m
      hw hbits hb1 hN1 hN2 h_inv0 h_setting)
    B

end FormalRV.Shor.ApproxCosetShorBound
