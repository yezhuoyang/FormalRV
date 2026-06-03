/-
  FormalRV.PPM.GadgetChannel — GAPS 1–4 (gadget channel), CLOSED for the T gate;
  CCZ all-zeros (000) branch delivered as the analogue.

  ## What this closes

  The measurement-based magic-state gadget (CNOT · Z-measure · feedback) is the
  workhorse of the PPM compilation: a T (resp. CCZ) gate is realized by consuming
  a magic state, performing a destructive Z-measurement on the ancilla, and
  applying an outcome-dependent Pauli/Clifford correction.  Four things must hold
  for this to be a faithful realization of the unitary `U`:

    GAP 1 — *Per-outcome extraction.*  Tracing out the ancilla against outcome
            `⟨b|`, the operator acting on the data register is a scalar times `U`.
    GAP 2 — *Born normalization.*  The per-outcome scalars `c_b` satisfy
            `Σ_b |c_b|² = 1`, so the gadget is trace-preserving.
    GAP 3 — *Magic-injection / ancilla-extraction faithfulness.*  The injection
            `I ⊗ |magic⟩` and extraction `I ⊗ ⟨b|` are the genuine tensor maps,
            so the extracted operator is DERIVED from the gadget theorem, not
            hand-asserted.
    GAP 4 — *Channel equality.*  Summing over outcomes (with the GAP-2 fact),
            the data CHANNEL `Φ(ρ) = Σ_b K_b ρ K_b†` equals the unitary channel
            `U ρ U†`.

  All four are proved here for the T gate (`tChannel_eq_unitaryChannel`,
  refining `tKraus_eq_smul_U` + `tBorn_normSq_sum`).  For CCZ, only the 000
  (all-zeros) measurement branch is delivered (`cczKraus000_eq_smul_U`,
  per-outcome operator extraction); the other 7 outcomes need a CZ-correction
  primitive the repo lacks, so the full CCZ channel is out of scope here.

  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.MagicGadgetInterface
import FormalRV.PPM.CCZGadgetTeleport

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.MagicStateTeleport
open FormalRV.Framework.EightTToCCZ
open FormalRV.PPM.TGadgetTeleport
open FormalRV.PPM.MagicGadgetInterface
open Complex

namespace FormalRV.PPM.GadgetChannel

/-! ## §0-§1. Gadget operator, magic-injection and ancilla-extraction. -/

/-- The full gadget operator on data⊗ancilla (4-dim) for outcome `b`:
    `S-correction · Z-measure · CNOT`. -/
noncomputable def tGadgetOp (b : Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  tCorrection b * tProj b * cnotMatrix

/-- `I_data ⊗ |T⟩` : maps a data state `ψ` to `ψ ⊗ᵥ |T⟩` (data = HIGH qubit). -/
noncomputable def injectMagic : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1 / Real.sqrt 2, 0;
     ω / Real.sqrt 2, 0;
     0, 1 / Real.sqrt 2;
     0, ω / Real.sqrt 2]

/-- `I_data ⊗ ⟨b|` : contracts the ancilla against `⟨b|`. -/
def extractAnc : Bool → Matrix (Fin 2) (Fin 4) ℂ
  | false => !![1, 0, 0, 0;
                0, 0, 1, 0]
  | true  => !![0, 1, 0, 0;
                0, 0, 0, 1]

theorem injectMagic_apply (ψ : StateVec 1) :
    injectMagic * ψ = ψ ⊗ᵥ tKet := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [injectMagic, tKet, Matrix.mul_apply, Fin.sum_univ_two,
          kron_vec_apply, kron_vec_high, kron_vec_low] <;> ring

theorem extractAnc_kron (ψd : StateVec 1) (b : Bool) :
    extractAnc b * (ψd ⊗ᵥ tAnc b) = ψd := by
  funext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [extractAnc, tAnc, basisState, Matrix.mul_apply, Fin.sum_univ_four,
          kron_vec_apply, kron_vec_high, kron_vec_low]

/-! ## §2. (GAPS 1+3) Per-outcome Kraus DATA operator = c_b • U. -/

/-- `Kraus_b := (I ⊗ ⟨b|) · G_b · (I ⊗ |T⟩)`, a 2×2 matrix on the DATA register
    (ancilla discarded, global gadget matrix). -/
noncomputable def tKraus (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  extractAnc b * tGadgetOp b * injectMagic

/-- **GAPS 1+3.** The extracted data operator equals the Born scalar times the
    T-gate matrix: `Kraus_b = tBorn b • tMat`. Derived from `t_gadget_with_feedback`. -/
theorem tKraus_eq_smul_U (b : Bool) :
    tKraus b = tBorn b • tMat := by
  have key : ∀ ψ : StateVec 1, tKraus b * ψ = tBorn b • (tMat * ψ) := by
    intro ψ
    unfold tKraus tGadgetOp
    rw [Matrix.mul_assoc, Matrix.mul_assoc, injectMagic_apply,
        Matrix.mul_assoc, Matrix.mul_assoc, t_gadget_with_feedback ψ b,
        Matrix.mul_smul, extractAnc_kron, tMat_apply]
  funext i j
  fin_cases j
  · show tKraus b i 0 = (tBorn b • tMat) i 0
    have hcol := congrFun (congrFun (key (basisState 0)) i) 0
    have e1 : (tKraus b * (basisState 0 : StateVec 1)) i 0 = tKraus b i 0 := by
      simp [Matrix.mul_apply, basisState]
    have e2 : (tBorn b • (tMat * (basisState 0 : StateVec 1))) i 0
                = (tBorn b • tMat) i 0 := by
      simp [Matrix.smul_apply, Matrix.mul_apply, basisState]
    rw [← e1, hcol, e2]
  · show tKraus b i 1 = (tBorn b • tMat) i 1
    have hcol := congrFun (congrFun (key (basisState 1)) i) 0
    have e1 : (tKraus b * (basisState 1 : StateVec 1)) i 0 = tKraus b i 1 := by
      simp [Matrix.mul_apply, basisState]
    have e2 : (tBorn b • (tMat * (basisState 1 : StateVec 1))) i 0
                = (tBorn b • tMat) i 1 := by
      simp [Matrix.smul_apply, Matrix.mul_apply, basisState]
    rw [← e1, hcol, e2]

/-! ## §3. (GAP 2) Born-scalar normalization Σ_b |c_b|² = 1. -/

theorem normSq_ω : Complex.normSq ω = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm : ‖ω‖ = 1 := by
    unfold ω
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hnorm]; norm_num

/-- **GAP 2.** `Σ_b |c_b|² = |1/√2|² + |ω/√2|² = 1`. -/
theorem tBorn_normSq_sum :
    Complex.normSq (tBorn false) + Complex.normSq (tBorn true) = 1 := by
  have hhalf : Complex.normSq (tBorn false) = 1 / 2 := by
    simp only [tBorn]
    rw [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hhalf2 : Complex.normSq (tBorn true) = 1 / 2 := by
    simp only [tBorn]
    rw [Complex.normSq_div, normSq_ω, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hhalf, hhalf2]; norm_num

/-! ## §4. (GAPS 1–4) The data CHANNEL equals the unitary channel. -/

/-- `Φ(ρ) := Σ_b Kraus_b · ρ · Kraus_b†` (ancilla traced out; outcomes summed). -/
noncomputable def tChannel (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ b : Bool, tKraus b * ρ * (tKraus b)ᴴ

/-- The unitary channel of the T gate: `ρ ↦ U · ρ · U†`. -/
noncomputable def tUnitaryChannel (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  tMat * ρ * tMatᴴ

/-- **GAPS 1–4 combined.** The measurement gadget's data channel IS the unitary
    channel: `Φ(ρ) = Σ_b Kraus_b · ρ · Kraus_b† = U · ρ · U†`. -/
theorem tChannel_eq_unitaryChannel (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    tChannel ρ = tUnitaryChannel ρ := by
  unfold tChannel tUnitaryChannel
  simp only [tKraus_eq_smul_U]
  rw [Fintype.sum_bool]
  have term : ∀ b : Bool,
      (tBorn b • tMat) * ρ * ((tBorn b • tMat)ᴴ)
        = ((Complex.normSq (tBorn b) : ℂ)) • (tMat * ρ * tMatᴴ) := by
    intro b
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_mul, smul_smul]
    congr 1
    simp [Complex.normSq_eq_conj_mul_self, mul_comm]
  rw [term false, term true, ← add_smul]
  rw [show ((Complex.normSq (tBorn true) : ℂ)) + (Complex.normSq (tBorn false) : ℂ)
        = ((Complex.normSq (tBorn false) + Complex.normSq (tBorn true) : ℝ) : ℂ) by
        push_cast; ring,
      tBorn_normSq_sum]
  simp

/-! ## §5. CCZ all-zeros analogue (b = 000 branch). -/
open FormalRV.PPM.CCZGadgetTeleport

noncomputable def cczGadgetOp000 : Matrix (Fin 64) (Fin 64) ℂ :=
  projAnc000 * cnotChain

noncomputable def injectCCZ : Matrix (Fin 64) (Fin 8) ℂ :=
  fun c r => if c.val / 8 = r.val then cczKet ⟨c.val % 8, Nat.mod_lt _ (by norm_num)⟩ 0 else 0

noncomputable def extractCCZ000 : Matrix (Fin 8) (Fin 64) ℂ :=
  fun r c => if c.val = r.val * 8 then 1 else 0

theorem injectCCZ_apply (ψ : StateVec 3) :
    injectCCZ * ψ = ψ ⊗ᵥ cczKet := by
  funext i j
  rw [Matrix.mul_apply, kron_vec_apply, kron_vec_high, kron_vec_low]
  rw [Finset.sum_eq_single ⟨i.val / 8, by have : i.val < 64 := i.isLt; omega⟩]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [injectCCZ, if_true, show (2:Nat)^3 = 8 from rfl]
    ring
  · intro k _ hk
    simp only [injectCCZ]
    rw [if_neg, zero_mul]
    intro hc; apply hk; apply Fin.ext; exact hc.symm
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

theorem extractCCZ000_kron (d : StateVec 3) :
    extractCCZ000 * (d ⊗ᵥ (basisState 0 : StateVec 3)) = d := by
  funext r j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨r.val * 8, by have := r.isLt; omega⟩]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [extractCCZ000, if_true, one_mul, kron_vec_apply, kron_vec_high,
      kron_vec_low, show (2:Nat)^3 = 8 from rfl]
    have hhigh : (r.val * 8) / 8 = r.val := Nat.mul_div_cancel _ (by norm_num)
    have hlow : (r.val * 8) % 8 = 0 := Nat.mul_mod_left _ _
    rw [show (⟨(r.val * 8) / 8, by have := r.isLt; omega⟩ : Fin 8) = r from by
          apply Fin.ext; exact hhigh]
    simp only [basisState, hlow]
    norm_num
  · intro k _ hk
    simp only [extractCCZ000]
    rw [if_neg, zero_mul]
    intro hc; apply hk; apply Fin.ext; exact hc
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

noncomputable def cczKraus000 : Matrix (Fin 8) (Fin 8) ℂ :=
  extractCCZ000 * cczGadgetOp000 * injectCCZ

noncomputable def cczBorn000 : ℂ := 1 / (2 * Real.sqrt 2)

/-- **CCZ analogue (GAPS 1+3, 000 branch).** `Kraus_000 = c_000 • cczMat`. -/
theorem cczKraus000_eq_smul_U :
    cczKraus000 = cczBorn000 • cczMat := by
  have key : ∀ ψ : StateVec 3, cczKraus000 * ψ = cczBorn000 • (cczMat * ψ) := by
    intro ψ
    unfold cczKraus000 cczGadgetOp000 cczBorn000
    rw [Matrix.mul_assoc, Matrix.mul_assoc, injectCCZ_apply, Matrix.mul_assoc,
        ccz_teleport_outcome_000 ψ, Matrix.mul_smul, extractCCZ000_kron,
        CCZdata_eq_cczMat_mul]
  funext i j
  have hcol := congrFun (congrFun (key (basisState j)) i) 0
  have e1 : (cczKraus000 * (basisState j : StateVec 3)) i 0 = cczKraus000 i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [basisState]
    · intro k _ hk; simp [basisState, hk]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have e2 : (cczBorn000 • (cczMat * (basisState j : StateVec 3))) i 0
              = (cczBorn000 • cczMat) i j := by
    rw [Matrix.smul_apply, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [basisState, Matrix.smul_apply]
    · intro k _ hk; simp [basisState, hk]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  rw [← e1, hcol, e2]

end FormalRV.PPM.GadgetChannel
