/-
  FormalRV.Shor.GidneyInPlace.InPlaceE2IdealTrajectory — P1.2 of the coset-Shor
  hybrid route: the per-phase TRAJECTORY INVARIANT for the IDEAL RUNWAY oracle's QPE orbit.
  ════════════════════════════════════════════════════════════════════════════

  WHAT THIS FILE IS (and is NOT).  A naive "full QState equality" route
  (`Shor_final_state_E2coset f = E2shorZ (Shor_final_state f)` via a SELF-commutation
  `hwork_int`) is FALSE and is FORBIDDEN here.  P1.2 proves ONLY the per-phase TRAJECTORY
  INVARIANT for the *ideal RUNWAY oracle* `f_runwayIdeal` — the oracle whose active work
  action realizes the clean two-register coset shift
  `cosetInputVec z 0 ↦ cosetInputVec ((mult k · z)%N) 0` (the matrix-vector form of
  `IdealPermLift.idealShift_cosetInputVec` at the work-factor cast).

  The INVARIANT (`IdealCosetForm`): at every phase branch `x`, the work slice of the state
  is a SCALAR times a single CANONICAL coset column `cosetInputVec z 0` (some `z < N`).  We
  prove this is established at the embedded init (`E2cosetInit`) and PRESERVED by every QPE
  oracle stage `qpeStageMap … f_runwayIdeal k` (`k < m`):
    • INACTIVE phase branch  — the work slice is unchanged (same scalar, same `z`);
    • ACTIVE phase branch    — the work slice's coset base shifts `z ↦ (mult k · z)%N`
      (same scalar), via the realization hypothesis `hf_runway`.

  ⚠ SCOPE.  `f_runwayIdeal` is THIS file's ideal-runway oracle; it is DISTINCT from the
  ordinary residue oracle `f_residueIdeal` of plain Shor (which is NOT used here).  The
  bridge from this trajectory invariant to ordinary residue-oracle Shor success `P_ideal`
  is a SEPARATE later checkpoint (P1.3) and is NOT touched here.

  ⚠ ORACLE-STAGE CAP.  `qpeStage_oracle_jointIdx` needs `k < m`, so the orbit invariant is
  stated for `numIter ≤ m` (the `m` controlled-oracle stages).  The last (`k = m`) `QFTinv`
  stage is OUT OF SCOPE for P1.2 — it is a separate phase-local commute, DEFERRED.

  NO full QState equality, NO self-commutation `hwork_int`, NO `permImg`, NO physical gate
  (`gidneyInPlaceWithSwap`), NO bad sets, NO `pmDist`/marginal/`P_ideal` bridge.

  Kernel-clean target: no `sorry`, no `native_decide`, no axioms beyond the prelude
  `{propext, Classical.choice, Quot.sound}`.
-/
import FormalRV.Shor.GidneyInPlace.Ideal.Def.E2CosetSuccess
import FormalRV.Shor.GidneyInPlace.QPE.Proof.ControlStageBridge
import FormalRV.Shor.GidneyInPlace.Ideal.Def.IdealPermLift

namespace FormalRV.Shor.GidneyInPlace.InPlaceE2IdealTrajectory

open scoped Classical
open FormalRV.SQIRPort
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeInit qpeStageMap)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedCanon (E2shorZ E2shorZ_acts)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq qpeStage_oracle_jointIdx)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (E2cosetInit E2runwayInit E2runwayInit_acts Shor_final_state_E2coset)

/-! ## §0. The form predicate. -/

/-- **(P) The per-phase ideal-coset form.**  Each phase branch `x`'s work slice is the FIXED
    phase scalar `1/√2^m` times a single CANONICAL coset column `cosetInputVec z 0` (some residue
    `z < N`), read at the `E2shor_dim_eq` cast of the work index.  This is the invariant the QPE
    oracle stages preserve along the ideal-runway trajectory.

    ⚠ THE SCALAR IS PINNED to `1/√2^m` (NOT existential).  The base case carries it
    (`E2runwayInit_acts`) and every oracle stage PRESERVES it (the active branch only shifts the
    coset base `z`).  Pinning is what makes the per-phase weight `|1/√2^m|² = 1/2^m` summable —
    `∑_x |1/√2^m|² = 1` — so the H3.2 telescope step's local `pmDist` aggregation is unconditional
    in the scalar (no `pmNorm Φ ≤ 1` side hypothesis).  `IdealCosetForm` has NO external consumers,
    so this refinement is local to this file. -/
def IdealCosetForm (m w bits N cm : Nat)
    (Φ : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits))) : Prop :=
  ∀ (x : Fin (2 ^ m)), ∃ (z : Nat), z < N ∧
    ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
      Φ (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0
        = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
            * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) y) 0

/-! ## §1. The step. -/

/-- **(S) The QPE-oracle step PRESERVES the ideal-coset form** along the ideal-runway
    trajectory.  For `k < m`, run one controlled-oracle stage of `f_runwayIdeal`:
      • INACTIVE (`controlBit … x = false`) — the work slice is unchanged: same `(scalar, z)`;
      • ACTIVE   (`controlBit … x = true`)  — the active work action sends the canonical column
        `z` to the shifted canonical column `(mult k · z) % N` (the realization hypothesis
        `hf_runway`), with the SAME scalar; `(mult k · z) % N < N` by `Nat.mod_lt`.
    The realization hypothesis `hf_runway` is exactly the matrix-vector form of
    `IdealPermLift.idealShift_cosetInputVec` at the work-factor `workDim_eq` cast (the active
    work action on a canonical coset column). -/
theorem idealCosetForm_step (m w bits N cm : Nat) (hN : 0 < N)
    (f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (mult : Nat → Nat)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult k * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (k : Nat) (hk : k < m)
    (Φ : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hΦ : IdealCosetForm m w bits N cm Φ) :
    IdealCosetForm m w bits N cm (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal k Φ) := by
  intro x
  obtain ⟨z, hz, hslice⟩ := hΦ x
  by_cases hcb : controlBit m k hk x
  · -- ACTIVE branch: the coset base shifts z ↦ (mult k · z) % N (the FIXED scalar is preserved).
    refine ⟨(mult k * z) % N, Nat.mod_lt _ hN, fun y => ?_⟩
    rw [qpeStage_oracle_jointIdx m bits (cosetAnc w bits) k hk f_runwayIdeal hwt Φ x y,
        if_pos hcb]
    -- ∑ yp, uc_eval(…)·Φ(jointIdx x yp)  =  ∑ yp, uc_eval(…)·((1/√2^m)·cosetInputVec z 0 (cast yp))
    rw [Finset.sum_congr rfl (fun yp _ => by rw [hslice yp])]
    -- pull the fixed scalar out, then apply hf_runway
    rw [show (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * (((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
                    * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0))
          = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
              * (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun yp _ => by ring)]
    rw [hf_runway k z hz y]
  · -- INACTIVE branch: unchanged (same fixed scalar, same `z`).
    refine ⟨z, hz, fun y => ?_⟩
    rw [qpeStage_oracle_jointIdx m bits (cosetAnc w bits) k hk f_runwayIdeal hwt Φ x y,
        if_neg hcb]
    exact hslice y

/-! ## §2. The orbit invariant (relative to the base case). -/

/-- **(O) The orbit invariant** along the ideal-runway QPE trajectory, for `numIter ≤ m`
    oracle stages, GENERALIZED over an arbitrary init `init`.  Given the base case `hbase` (the
    form at `init`) and the realization hypothesis `hf_runway`, every orbit state after
    `numIter ≤ m` stages of `qpeStageMap … f_runwayIdeal` (started at `init`) satisfies
    `IdealCosetForm`.  Induction on `numIter`: `0 ↦ hbase`; `p+1` (`p < m`) ↦
    `idealCosetForm_step` on the IH.  The last (`k = m`) `QFTinv` stage is out of scope
    (DEFERRED — separate phase-local commute). -/
theorem idealCosetForm_orbit (m w bits N cm : Nat) (hN : 0 < N)
    (f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (mult : Nat → Nat)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult k * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0)
    (init : QState (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)))
    (hbase : IdealCosetForm m w bits N cm init) :
    ∀ numIter, numIter ≤ m →
      IdealCosetForm m w bits N cm
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          init numIter) := by
  intro numIter
  induction numIter with
  | zero => intro _; exact hbase
  | succ p ih =>
      intro hp
      have hpm : p < m := hp
      show IdealCosetForm m w bits N cm
          (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal p
            (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
              init p))
      exact idealCosetForm_step m w bits N cm hN f_runwayIdeal hwt mult hf_runway p hpm
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          init p)
        (ih (Nat.le_of_lt hpm))

/-! ## §3. The base case.

  ⚠ SUPERSEDED.  The `E2cosetInit`-based base case `idealCosetForm_base` below is the OLD,
  degenerate one (residue `z = 2^(cosetAnc w bits)`, side condition `2^(cosetAnc w bits) < N`).
  For real parameters `2^(cosetAnc w bits) ≥ N`, so its side condition `hzc` is UNSATISFIABLE and
  `E2cosetInit = E2shorZ (qpeInit)` is the ZERO state.  The LIVE base case is
  `idealCosetForm_base_direct` (§3′ below), over the corrected DIRECT init `E2runwayInit`, with
  residue `z = 1` and the satisfiable side condition `1 < N`.

  We compute the per-phase work slice of the embedded init `E2cosetInit = E2shorZ (qpeInit)`.
  The ideal Shor init `qpeInit` is the H-prepared `|0⟩_m ⊗ |1⟩_bits ⊗ |0⟩_anc`, so on the work
  register it is the canonical basis vector at value `2^(cosetAnc w bits)` (the value of
  `|1⟩_bits ⊗ |0⟩_anc`), uniformly weighted across phases.  Reading this through `E2shorZ_acts`
  collapses the column sum to the SINGLE canonical coset column at residue
  `z := 2^(cosetAnc w bits)` — provided `2^(cosetAnc w bits) < N` (so the residue is canonical
  and not zeroed by `E2shorZ`).  Hence each phase branch's work slice is `(1/√2^m) ·
  cosetInputVec (2^(cosetAnc w bits)) 0`, establishing `IdealCosetForm` with that `z`.

  ⚠ NOTE on the residue `z`.  Under the standard kron ordering `|1⟩_bits ⊗ |0⟩_anc`, the
  combined work value is `1·2^anc + 0 = 2^(cosetAnc w bits)`, NOT `1`.  (The `z = 1` of an
  informal description would require `cosetAnc w bits = 0`.)  We therefore prove the base case
  with `z = 2^(cosetAnc w bits)`, under the explicit canonicality side-condition `hzc`.

  Requires `0 < m` (for the H-uniform-sum `npar_H_kron_zeros_eq_uniform_sum`). -/

open FormalRV.Framework (kron_vec kron_vec_combine kron_zeros kron_vec_apply_combine kron_vec_high)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp
  (qpeInit_eq qpeRaw shorInitM)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge
  (cast_jointIdx_eq_combine)

/-- The work register of `Shor_initial_state` (= `shorInitM`), factored out by associativity:
    `shorInitM m n anc = kron_vec (kron_zeros m) (kron_vec (basis_vector (2^n) 1) (kron_zeros anc))`.
    Direct from `kron_vec_assoc` (same `Nat.add_assoc` cast as `Shor_initial_state`). -/
theorem shorInitM_eq (m n anc : Nat) :
    shorInitM m n anc
      = kron_vec (kron_zeros m)
          (kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1) (kron_zeros anc)) := by
  show Shor_initial_state m n anc = _
  rw [show Shor_initial_state m n anc
        = QState.cast (by rw [Nat.add_assoc])
            (kron_vec (kron_vec (kron_zeros m) (FormalRV.Framework.basis_vector (2 ^ n) 1))
              (kron_zeros anc)) from rfl]
  exact SQIRPort.kron_vec_assoc (kron_zeros m) (FormalRV.Framework.basis_vector (2 ^ n) 1)
    (kron_zeros anc)

/-- The H-prepared init read at a combined index `kron_vec_combine x w`: only the phase-`x`
    term of the uniform sum survives, leaving `(1/√2^m) · (work register at w)`.  Needs `0 < m`. -/
theorem qpeRaw_combine (m n anc : Nat) (hm : 0 < m)
    (x : Fin (2 ^ m)) (w : Fin (2 ^ (n + anc))) :
    qpeRaw m n anc (kron_vec_combine x w) 0
      = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
          * (kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1) (kron_zeros anc)) w 0 := by
  have hM : qpeRaw m n anc
      = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) •
          ∑ xp : Fin (2 ^ m),
            kron_vec (FormalRV.Framework.basis_vector (2 ^ m) xp.val)
              (kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1) (kron_zeros anc)) := by
    unfold qpeRaw
    rw [shorInitM_eq m n anc]
    exact npar_H_kron_zeros_eq_uniform_sum hm
      (kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1) (kron_zeros anc))
  rw [hM]
  -- read the scaled uniform sum at the combined index
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single x]
  · rw [kron_vec_apply_combine, FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl, one_mul]
  · intro xp _ hxp
    rw [kron_vec_apply_combine, FormalRV.Framework.basis_vector_apply_ne _ _ _ _ (by
      intro h; exact hxp (Fin.ext h.symm)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The work register `|1⟩_n ⊗ |0⟩_anc` read at `w`: `1` iff `w.val = 2^anc`, else `0`. -/
theorem workReg_apply (n anc : Nat) (w : Fin (2 ^ (n + anc))) :
    (kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1) (kron_zeros anc)) w 0
      = (if w.val = 2 ^ anc then 1 else 0) := by
  rw [FormalRV.Framework.kron_vec_apply]
  -- (kron_vec_high w).val = w.val / 2^anc ; (kron_vec_low w).val = w.val % 2^anc
  by_cases hw : w.val = 2 ^ anc
  · have hhigh : (kron_vec_high w : Fin (2 ^ n)).val = 1 := by
      show w.val / 2 ^ anc = 1; rw [hw, Nat.div_self (Nat.two_pow_pos _)]
    have hlow : (FormalRV.Framework.kron_vec_low w : Fin (2 ^ anc)).val = 0 := by
      show w.val % 2 ^ anc = 0; rw [hw, Nat.mod_self]
    rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ hhigh,
        show (FormalRV.Framework.kron_vec_low w : Fin (2 ^ anc))
            = ⟨0, Nat.two_pow_pos anc⟩ from Fin.ext hlow,
        FormalRV.Framework.kron_zeros_apply_zero anc, one_mul, if_pos hw]
  · -- non-canonical: either high ≠ 1 or low ≠ 0, so the product is 0
    rw [if_neg hw]
    by_cases hlow : (FormalRV.Framework.kron_vec_low w : Fin (2 ^ anc)).val = 0
    · -- low = 0, so high ≠ 1 (else w.val = 2^anc)
      have hhigh : (kron_vec_high w : Fin (2 ^ n)).val ≠ 1 := by
        intro h
        apply hw
        -- w.val = high·2^anc + low ; with high = 1, low = 0 ⇒ w.val = 2^anc
        have hdm : 2 ^ anc * (w.val / 2 ^ anc) + w.val % 2 ^ anc = w.val :=
          Nat.div_add_mod w.val (2 ^ anc)
        have hhv : (kron_vec_high w : Fin (2 ^ n)).val = w.val / 2 ^ anc := rfl
        have hlv : (FormalRV.Framework.kron_vec_low w : Fin (2 ^ anc)).val = w.val % 2 ^ anc := rfl
        rw [hhv] at h
        rw [hlv] at hlow
        rw [h, hlow, Nat.mul_one, Nat.add_zero] at hdm
        exact hdm.symm
      rw [FormalRV.Framework.basis_vector_apply_ne _ _ _ _ hhigh, zero_mul]
    · rw [FormalRV.Framework.kron_zeros_apply_ne_zero _ _ _ hlow, mul_zero]

/-- `qpeInit` read at `jointIdx x yp`: `(1/√2^m)` times the work register at `yp`, where the
    work register is `[yp.val = 2^anc]` (the value of `|1⟩_bits ⊗ |0⟩_anc`). -/
theorem qpeInit_jointIdx (m w bits : Nat) (hm : 0 < m)
    (x : Fin (2 ^ m))
    (yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    qpeInit m bits (cosetAnc w bits) (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp) 0
      = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
          * (if yp.val = 2 ^ (cosetAnc w bits) then 1 else 0) := by
  -- bridge qpeInit to qpeRaw at a combined index
  rw [qpeInit_eq]
  show qpeRaw m bits (cosetAnc w bits)
      (Fin.cast (dim_assoc_eq m bits (cosetAnc w bits)).symm
        (jointIdx (shorDvd m bits (cosetAnc w bits)) x yp)) 0 = _
  rw [cast_jointIdx_eq_combine m bits (cosetAnc w bits) x yp,
      qpeRaw_combine m bits (cosetAnc w bits) hm x
        (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp),
      workReg_apply bits (cosetAnc w bits) (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)]
  -- (Fin.cast … yp).val = yp.val
  rfl

/-- **(B) The base case** — the embedded init `E2cosetInit` is in ideal-coset form.  The ideal
    Shor init `qpeInit`'s per-phase work register is the canonical basis vector at the work
    value `2^(cosetAnc w bits)` (the value of `|1⟩_bits ⊗ |0⟩_anc`), uniformly weighted by
    `1/√2^m`.  Threading this through `E2shorZ_acts` collapses the embedding column sum to the
    SINGLE canonical coset column at residue `z := 2^(cosetAnc w bits)` (canonical by `hzc`),
    so each phase branch's work slice is `(1/√2^m) · cosetInputVec (2^(cosetAnc w bits)) 0`.

    ⚠ The residue is `z = 2^(cosetAnc w bits)`, NOT `1` (the standard kron ordering puts the
    work value of `|1⟩_bits ⊗ |0⟩_anc` at `1·2^anc + 0`).  Requires `0 < m` (`hm`, for the
    H-uniform-sum) and the canonicality bound `2^(cosetAnc w bits) < N` (`hzc`). -/
theorem idealCosetForm_base (m w bits N cm : Nat) (hm : 0 < m) (hbits : 0 < bits)
    (hzc : 2 ^ (cosetAnc w bits) < N) :
    IdealCosetForm m w bits N cm (E2cosetInit m w bits N cm) := by
  intro x
  refine ⟨2 ^ (cosetAnc w bits), hzc, fun y => ?_⟩
  -- the work value 2^anc is a valid work-factor index: 2^anc < 2^(bits+anc) = data dim (bits>0)
  have hzlt : 2 ^ (cosetAnc w bits) < (2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m := by
    rw [workDim_eq m bits (cosetAnc w bits)]
    calc 2 ^ (cosetAnc w bits) < 2 ^ (bits + cosetAnc w bits) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 2 ^ (bits + cosetAnc w bits) := rfl
  -- unfold E2cosetInit and use E2shorZ_acts
  show E2shorZ m w bits N cm (qpeInit m bits (cosetAnc w bits))
      (jointIdx (shorDvd m bits (cosetAnc w bits)) x y) 0 = _
  rw [E2shorZ_acts m w bits N cm (qpeInit m bits (cosetAnc w bits)) x y]
  -- substitute qpeInit's value: only yp.val = 2^anc survives
  rw [Finset.sum_congr rfl (fun yp _ => by
        rw [qpeInit_jointIdx m w bits hm x yp])]
  rw [Finset.sum_eq_single (⟨2 ^ (cosetAnc w bits), hzlt⟩ :
        Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))]
  · -- the surviving term
    rw [if_pos hzc, if_pos rfl, mul_one]
    ring
  · -- all other yp vanish (the work register is 0 there)
    intro yp _ hyp
    have : yp.val ≠ 2 ^ (cosetAnc w bits) := fun h => hyp (Fin.ext h)
    rw [if_neg this, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## §4. The fully-discharged orbit invariant (base case closed). -/

/-- **(O′) ⚠ SUPERSEDED — the OLD fully-discharged trajectory invariant** over the DEGENERATE
    embedded init `E2cosetInit = E2shorZ (qpeInit)`.  Its side condition
    `hzc : 2^(cosetAnc w bits) < N` is UNSATISFIABLE for real parameters (so this theorem is
    VACUOUS — `E2cosetInit` is then the zero state).  The LIVE version is
    `idealCosetForm_orbit_runway_direct` (§4′ below), over the corrected DIRECT init
    `E2runwayInit`, with residue `z = 1`, the satisfiable side condition `1 < N`, and NO
    `0 < m`/`0 < bits` base-case obligations.  Kept only as a dead artifact.

    Combines `idealCosetForm_base` (the embedded-init base case, residue
    `2^(cosetAnc w bits) < N`) with `idealCosetForm_orbit` (the step-folded induction).
    Side-conditions: `0 < m`, `0 < bits`, `2^(cosetAnc w bits) < N`, and `hf_runway`. -/
theorem idealCosetForm_orbit_runway (m w bits N cm : Nat) (hN : 0 < N)
    (hm : 0 < m) (hbits : 0 < bits) (hzc : 2 ^ (cosetAnc w bits) < N)
    (f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (mult : Nat → Nat)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult k * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0) :
    ∀ numIter, numIter ≤ m →
      IdealCosetForm m w bits N cm
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2cosetInit m w bits N cm) numIter) :=
  idealCosetForm_orbit m w bits N cm hN f_runwayIdeal hwt mult hf_runway
    (E2cosetInit m w bits N cm) (idealCosetForm_base m w bits N cm hm hbits hzc)

/-! ## §3′. The LIVE base case — the corrected DIRECT runway init `E2runwayInit`.

  The corrected init `E2runwayInit` is, by construction, per phase branch `x` the scalar
  `1/√2^m` times the SINGLE canonical coset column `cosetInputVec 1 0` at residue `z = 1`
  (`E2runwayInit_acts`).  So `IdealCosetForm` holds at `E2runwayInit` directly, with witness
  `(scalar := 1/√2^m, z := 1)`, under the satisfiable side condition `1 < N` — NO H-uniform-sum
  (`0 < m`), NO `0 < bits`, NO `2^(cosetAnc w bits) < N`.  This is the `z = 1` re-anchoring. -/

/-- **(B′) The LIVE base case** — the corrected DIRECT runway init `E2runwayInit` is in
    ideal-coset form, at residue `z = 1`.  Immediate from `E2runwayInit_acts`: each phase branch
    `x`'s work slice is exactly `(1/√2^m) · cosetInputVec 1 0`, so the witness is
    `(scalar := 1/√2^m, z := 1)` with side condition `1 < N` (`hN1`).  No `0 < m`/`0 < bits`
    obligations (the direct init needs neither). -/
theorem idealCosetForm_base_direct (m w bits N cm : Nat) (hN1 : 1 < N) :
    IdealCosetForm m w bits N cm (E2runwayInit m w bits N cm) := by
  intro x
  exact ⟨1, hN1, fun y => E2runwayInit_acts m w bits N cm x y⟩

/-! ## §4′. The LIVE fully-discharged orbit invariant — direct init, `z = 1` base. -/

/-- **(O″) P1.2 — the LIVE fully-discharged trajectory invariant** along the ideal-runway QPE
    orbit, over the corrected DIRECT init `E2runwayInit` (NOT `E2shorZ (qpeInit)`).  Every orbit
    state after `numIter ≤ m` controlled-oracle stages of `qpeStageMap … f_runwayIdeal`, started
    at `E2runwayInit`, is in ideal-coset form.  Combines the generalized `idealCosetForm_orbit`
    (at `init := E2runwayInit`) with the LIVE base case `idealCosetForm_base_direct`
    (residue `z = 1`).

    Side-conditions: `0 < N`, `1 < N` (the base residue `1` is canonical), and the realization
    hypothesis `hf_runway` (the active work action is the clean coset shift — the matrix-vector
    form of `IdealPermLift.idealShift_cosetInputVec`).  NO unsatisfiable `2^(cosetAnc w bits) < N`,
    NO `0 < m`/`0 < bits` (the direct base case needs neither).  The `k = m` QFTinv stage is out
    of scope.  (`f_runwayIdeal` is THIS file's ideal-runway oracle, DISTINCT from the residue
    oracle `f_residueIdeal` of plain Shor.) -/
theorem idealCosetForm_orbit_runway_direct (m w bits N cm : Nat) (hN : 0 < N) (hN1 : 1 < N)
    (f_runwayIdeal : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hwt : ∀ j, FormalRV.Framework.UCom.WellTyped (bits + cosetAnc w bits) (f_runwayIdeal j))
    (mult : Nat → Nat)
    (hf_runway : ∀ (k : Nat) (z : Nat), z < N →
        ∀ (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)),
          (∑ yp : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m),
              FormalRV.Framework.uc_eval (f_runwayIdeal (revIndex m k))
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) y)
                  (Fin.cast (workDim_eq m bits (cosetAnc w bits)) yp)
                * cosetInputVec w bits N cm z 0 (Fin.cast (E2shor_dim_eq m w bits) yp) 0)
            = cosetInputVec w bits N cm ((mult k * z) % N) 0
                (Fin.cast (E2shor_dim_eq m w bits) y) 0) :
    ∀ numIter, numIter ≤ m →
      IdealCosetForm m w bits N cm
        (orbitState (qpeStageMap m bits (cosetAnc w bits) f_runwayIdeal)
          (E2runwayInit m w bits N cm) numIter) :=
  idealCosetForm_orbit m w bits N cm hN f_runwayIdeal hwt mult hf_runway
    (E2runwayInit m w bits N cm) (idealCosetForm_base_direct m w bits N cm hN1)

end FormalRV.Shor.GidneyInPlace.InPlaceE2IdealTrajectory
