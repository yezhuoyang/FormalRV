/-
  FormalRV.PPM.PPMDenote — first concrete piece of a state-vector
  denotation ⟦·⟧ for PPM (parallel Pauli-product measurement) programs.

  ## What this delivers

  A *compositional operator semantics* (a genuine denotation, not a stub) for
  measurement-and-correct gadgets at the state-vector level:

    * §1  Primitives.  `pauliProj P b` is the projector onto the `b`-eigenspace
         of a single-qubit Pauli `P` (`b = false ↦ +1`, `b = true ↦ -1`):
         `(I + (-1)^b P)/2`.  `corrOp Q` is the Pauli unitary correction `Q`.
         Both are built from the repo's `FormalRV.BQCode.Pauli.toMatrix`.
    * §2  Projector algebra (the four PVM laws).  `pauliProj` is proved
         idempotent (`Π² = Π`), Hermitian (`Π† = Π`), the two outcome
         projectors resolve the identity (`Π₊ + Π₋ = I`) and are orthogonal
         (`Π₊ Π₋ = 0`) — the four defining laws of a projective measurement.
    * §3  Compositional gadget denotation.  `gadgetDenote U proj corr ψ res`
         = `corr · (proj · (U · (ψ ⊗ res)))`: apply interaction `U`, project the
         ancilla, apply the data correction — operator semantics for the
         measurement-and-correct pipeline, with `gadgetDenote_eq` exposing the
         flattened single-factor form `(corr * proj * U) * (ψ ⊗ res)`
         (compositionality).  Instantiated to the `T`-gadget, REUSING
         `MagicStateTeleport.t_teleport_outcome_0/1` (whose Born amplitudes are
         already proven there), to give the headline `⟦T-gadget⟧ = T|ψ⟩` up to a
         tracked Pauli/Born frame.  `tGadget_outcome1_correction_bridge` makes
         the deferred Pauli/Clifford frame explicit: the raw uncorrected
         outcome-1 branch maps onto the corrected outcome-1 branch exactly by
         left-multiplying the KNOWN correction `Shigh`.
    * §4  Single-qubit Clifford gadget = unitary up to frame (Approach B):
         the `X` correction intertwines the two `Z`-measurement outcomes,
         `X·Π_{Z=-1} = Π_{Z=+1}·X`, the one-qubit deferred-frame principle,
         built purely from the general `pauliProj` / `corrOp` primitives.

  ## Honesty boundary

  * State-vector correctness only (unnormalised post-measurement states).
    Born-rule scalars (`1/√2`, `ω/√2`) are tracked as frame factors, inherited
    from `MagicStateTeleport`; outcome *probabilities* are not re-derived here.
  * `§3` gadgets act on the explicit 2-qubit (data ⊗ ancilla) `Fin 4` space
    using the repo's concrete `projLow0/projLow1/Shigh`.  `§4` uses the GENERAL
    `pauliProj`/`corrOp` 2×2 primitives.  Connecting the general `pauliProj` to
    the concrete `projLow*` via `pad_u`/Kronecker is the natural next step (not
    attempted here).
  * sorry-free; the key theorems depend only on `propext`, `Classical.choice`,
    `Quot.sound` (verified by `#print axioms`).
-/
import FormalRV.PPM.MagicStateTeleport
import FormalRV.PPM.LogicalState

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.MagicStateTeleport
open FormalRV.Framework.EightTToCCZ
open FormalRV.BQCode

namespace FormalRV.PPM.PPMDenote

/-! ## §1. State-vector primitives: measurement projectors and corrections. -/

/-- The projector onto the `b`-eigenspace of a single-qubit Pauli `P`:
    `(I + (-1)^b P)/2`.  `b = false ↦ +1` eigenspace, `b = true ↦ -1`.
    Built from `FormalRV.BQCode.Pauli.toMatrix`. -/
noncomputable def pauliProj (P : Pauli) (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (if b then -P.toMatrix else P.toMatrix))

/-- A Pauli correction operator is the Pauli unitary itself. -/
abbrev corrOp (Q : Pauli) : Matrix (Fin 2) (Fin 2) ℂ := Q.toMatrix

/-! ## §2. Projector algebra: the four PVM laws. -/

/-- Every single-qubit Pauli matrix is Hermitian: `P† = P`. -/
theorem pauli_conjTranspose (P : Pauli) : P.toMatrix.conjTranspose = P.toMatrix := by
  cases P <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Pauli.toMatrix, Matrix.conjTranspose_apply, Complex.conj_I]

/-- The signed Pauli `s = (-1)^b P` squares to `I`, since `P² = I`. -/
theorem signedPauli_sq (P : Pauli) (b : Bool) :
    (if b then -P.toMatrix else P.toMatrix) * (if b then -P.toMatrix else P.toMatrix)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  cases b
  · simp [Pauli.toMatrix_mul_self]
  · rw [if_pos rfl, neg_mul_neg, Pauli.toMatrix_mul_self]

/-- **Idempotency**: `pauliProj P b` is a projector, `Π² = Π`. -/
theorem pauliProj_idem (P : Pauli) (b : Bool) :
    pauliProj P b * pauliProj P b = pauliProj P b := by
  unfold pauliProj
  set s := (if b then -P.toMatrix else P.toMatrix) with hs
  have hsq : s * s = (1 : Matrix (Fin 2) (Fin 2) ℂ) := signedPauli_sq P b
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hsq]
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) + s + (s + 1) = (2 : ℂ) • (1 + s) by
        rw [two_smul]; abel]
  rw [smul_smul]; norm_num

/-- **Hermitian**: `pauliProj P b` is self-adjoint, `Π† = Π`. -/
theorem pauliProj_herm (P : Pauli) (b : Bool) :
    (pauliProj P b).conjTranspose = pauliProj P b := by
  unfold pauliProj
  have hhalf : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num
  cases b
  · simp only [Bool.false_eq_true, if_false, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_add, Matrix.conjTranspose_one, pauli_conjTranspose, hhalf]
  · simp only [if_true, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, Matrix.conjTranspose_neg, pauli_conjTranspose, hhalf]

/-- **Resolution of identity**: the two outcome projectors sum to `I`. -/
theorem pauliProj_resolution (P : Pauli) :
    pauliProj P false + pauliProj P true = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold pauliProj
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [smul_add, smul_add, ← add_assoc]
  rw [show (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1/2 : ℂ) • P.toMatrix
        + (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1/2 : ℂ) • (-P.toMatrix)
        = ((1/2 : ℂ) + (1/2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + ((1/2 : ℂ) • P.toMatrix + (1/2 : ℂ) • (-P.toMatrix)) by
        rw [add_smul]; abel]
  rw [smul_neg, add_neg_cancel, add_zero]; norm_num

/-- **Orthogonality**: the two outcome projectors annihilate, `Π₊ Π₋ = 0`. -/
theorem pauliProj_orthogonal (P : Pauli) :
    pauliProj P false * pauliProj P true = 0 := by
  unfold pauliProj
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_neg, Pauli.toMatrix_mul_self]
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) + -P.toMatrix + (P.toMatrix + -1) = 0 by abel]
  simp

/-! ## §3. Compositional gadget denotation + T-gadget KEY theorem. -/

/-- **Compositional denotation of a measurement-and-correct gadget.**
    Given a 2-qubit (data ⊗ ancilla) interaction unitary `U`, an ancilla
    measurement projector `proj`, and a data-qubit correction `corr`, the
    gadget denotes `corr · (proj · (U · (ψ ⊗ res)))`.  Operator semantics:
    apply `U`, project, correct. -/
noncomputable def gadgetDenote
    (U proj corr : Matrix (Fin 4) (Fin 4) ℂ) (ψ res : StateVec 1) : StateVec 2 :=
  corr * (proj * (U * (ψ ⊗ᵥ res)))

/-- The denotation is **compositional**: each layer is a matrix factor, with
    associativity collapsing them into a single operator `corr * proj * U`. -/
theorem gadgetDenote_eq
    (U proj corr : Matrix (Fin 4) (Fin 4) ℂ) (ψ res : StateVec 1) :
    gadgetDenote U proj corr ψ res = (corr * proj * U) * (ψ ⊗ᵥ res) := by
  unfold gadgetDenote
  rw [Matrix.mul_assoc, Matrix.mul_assoc]

/-- **T-gadget denotation, outcome 0.**  The `T` measurement-teleportation
    gadget (CNOT + Z-measure outcome 0 + no correction) on `ψ ⊗ |T⟩` denotes
    `(1/√2) • (T|ψ⟩ ⊗ |0⟩)`.  Reuses `MagicStateTeleport.t_teleport_outcome_0`. -/
theorem tGadget_denote_outcome_0 (ψ : StateVec 1) :
    gadgetDenote cnotMatrix projLow0 (1 : Matrix (Fin 4) (Fin 4) ℂ) ψ tKet
      = (1 / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)) := by
  unfold gadgetDenote; rw [Matrix.one_mul]; exact t_teleport_outcome_0 ψ

/-- **T-gadget denotation, outcome 1.**  Same gadget, outcome 1, with the
    deferred Clifford correction `S = Shigh` on the data qubit.  Denotes
    `(ω/√2) • (T|ψ⟩ ⊗ |1⟩)`.  Reuses `MagicStateTeleport.t_teleport_outcome_1`. -/
theorem tGadget_denote_outcome_1 (ψ : StateVec 1) :
    gadgetDenote cnotMatrix projLow1 Shigh ψ tKet
      = (ω / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1)) := by
  unfold gadgetDenote; exact t_teleport_outcome_1 ψ

/-- **Deferred-frame correctness (state-vector level).**
    Both measurement outcomes of the `T`-gadget produce the *same* data state
    `Tdata ψ = T|ψ⟩`, differing only by a known frame (scalar `1/√2` vs `ω/√2`,
    ancilla label `|0⟩` vs `|1⟩`, correction `I` vs `S`).  State-vector image of
    the PPM "outcome-independent operation up to a tracked Pauli/phase frame". -/
theorem tGadget_data_outcome_independent (ψ : StateVec 1) :
    (∃ c₀ : ℂ, gadgetDenote cnotMatrix projLow0 (1 : Matrix (Fin 4) (Fin 4) ℂ) ψ tKet
        = c₀ • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)))
    ∧ (∃ c₁ : ℂ, gadgetDenote cnotMatrix projLow1 Shigh ψ tKet
        = c₁ • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1))) :=
  ⟨⟨_, tGadget_denote_outcome_0 ψ⟩, ⟨_, tGadget_denote_outcome_1 ψ⟩⟩

/-- **The deferred Pauli/Clifford frame, explicitly.**  The raw (uncorrected)
    outcome-1 branch — `gadgetDenote` with correction `corr = 1` — is mapped onto
    the corrected outcome-1 branch exactly by left-multiplying the KNOWN
    correction `Shigh`.  Thus the two outcomes' raw states differ by the known
    Clifford correction `Shigh`, the deferred-frame byproduct that classical
    feedforward applies. -/
theorem tGadget_outcome1_correction_bridge (ψ : StateVec 1) :
    Shigh * gadgetDenote cnotMatrix projLow1 (1 : Matrix (Fin 4) (Fin 4) ℂ) ψ tKet
      = gadgetDenote cnotMatrix projLow1 Shigh ψ tKet := by
  unfold gadgetDenote
  rw [Matrix.one_mul]

/-! ## §4. Single-qubit Clifford gadget = unitary up to frame (Approach B). -/

/-- **Single-qubit Clifford gadget = unitary up to frame.**
    The Pauli `X` correction intertwines the two `Z`-measurement outcome
    projectors: `corrOp X * pauliProj Z true = pauliProj Z false * corrOp X`,
    i.e. `X·Π_{Z=-1} = Π_{Z=+1}·X`.  A `Z`-basis measurement gadget whose `-1`
    branch carries the deferred `X` correction lands in the *same* `+1`
    eigenspace as the uncorrected `+1` branch — the one-qubit Clifford instance
    of the deferred-frame principle, built from the general primitives. -/
theorem clifford_gadget_intertwine :
    corrOp Pauli.X * pauliProj Pauli.Z true
      = pauliProj Pauli.Z false * corrOp Pauli.X := by
  unfold pauliProj corrOp
  simp only [Bool.false_eq_true, if_false, if_true]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pauli.toMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
          Matrix.add_apply, Matrix.one_apply]

/-- **State-vector corollary.**  Applying the `X` correction to the `-1`-outcome
    `Z`-measurement gadget on input `ψ` equals running the `+1`-outcome gadget
    on the `X`-flipped input `X|ψ⟩`.  Fully compositional witness that the
    corrected gadget is outcome-independent. -/
theorem clifford_gadget_outcome_independent (ψ : StateVec 1) :
    corrOp Pauli.X * (pauliProj Pauli.Z true * ψ)
      = pauliProj Pauli.Z false * (corrOp Pauli.X * ψ) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, clifford_gadget_intertwine]

end FormalRV.PPM.PPMDenote