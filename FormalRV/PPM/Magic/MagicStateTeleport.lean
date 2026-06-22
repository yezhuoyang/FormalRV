/-
  FormalRV.PPM.Magic.MagicStateTeleport — the measurement-based gate
  teleportation protocol for the `T` gate, proved correct on state
  vectors (Ask 2, item 2).

  ## The protocol

  To apply `T` to a data qubit `|ψ⟩` using one `|T⟩ = (|0⟩+ω|1⟩)/√2`
  magic state (ω = e^{iπ/4}):

    1. prepare `|ψ⟩ ⊗ |T⟩`;
    2. apply `CNOT` (data controls the magic ancilla);
    3. measure the ancilla in the `Z` basis;
       * outcome 0 ⇒ the data qubit is `T|ψ⟩` (no correction);
       * outcome 1 ⇒ apply the Clifford correction `S` ⇒ `T|ψ⟩`.

  This is the canonical *measurement-and-correct* gate teleportation: a
  non-Clifford gate is realised by consuming a magic state, a Clifford
  (CNOT) interaction, a measurement, and a Clifford (S) Pauli/phase
  correction.  Both measurement branches are proved here for an
  arbitrary input `|ψ⟩`, sorry-free.

  ## Honesty boundary

  * This is the **state-vector** correctness of the protocol (unnormalised
    post-measurement states; the `1/√2` / `ω/√2` factors are the Born
    amplitudes).  Outcome probabilities and the renormalisation are the
    Born-rule layer (`prob_outcome`), not re-derived here.
  * The analogous CCZ gate teleportation (Litinski's 6-PPM protocol) acts
    on a 6-qubit register (64×64); its Bell-measurement step is left
    cited.  The `T` protocol here is the fully-proved measurement-
    teleportation instance.
-/
import FormalRV.Core.NDSem
import FormalRV.PPM.Rules.EightTToCCZScheme

namespace FormalRV.Framework.MagicStateTeleport

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.EightTToCCZ
open Complex

/-! ## §1. Ingredients. -/

/-- The `T` magic state `|T⟩ = (|0⟩ + ω|1⟩)/√2`. -/
noncomputable def tKet : StateVec 1 := !![1 / Real.sqrt 2; ω / Real.sqrt 2]

/-- `T|ψ⟩ = ψ₀|0⟩ + ω·ψ₁|1⟩` (the `T` gate is `diag(1, ω)`). -/
noncomputable def Tdata (ψ : StateVec 1) : StateVec 1 := !![ψ 0 0; ω * ψ 1 0]

/-- `Z`-measurement projector for ancilla outcome 0 (keep low bit 0:
    indices 0,2). -/
def projLow0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/-- `Z`-measurement projector for ancilla outcome 1 (keep low bit 1:
    indices 1,3). -/
def projLow1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1]

/-- The `S = diag(1, i)` correction on the data (high) qubit. -/
noncomputable def Shigh : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, I, 0;
     0, 0, 0, I]

/-- `ω² = i`: the T phase squared is the S phase (`e^{iπ/2} = i`). -/
theorem ω_sq : ω ^ 2 = Complex.I := by
  unfold ω
  rw [← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * (Complex.I * ((Real.pi : ℂ) / 4))
            = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ## §2. Outcome 0 — `T|ψ⟩`, no correction. -/

/-- **Measurement-teleportation, outcome 0.**  After CNOT and projecting
    the ancilla onto `|0⟩`, the data qubit carries `T|ψ⟩` (up to the
    `1/√2` Born amplitude). -/
theorem t_teleport_outcome_0 (ψ : StateVec 1) :
    projLow0 * (cnotMatrix * (ψ ⊗ᵥ tKet))
      = (1 / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, kron_vec_apply, kron_vec_high,
          kron_vec_low, projLow0, cnotMatrix, tKet, Tdata, basisState,
          Matrix.smul_apply, Matrix.vecMul, dotProduct] <;>
    ring

/-! ## §3. Outcome 1 — `S`-corrected to `T|ψ⟩`. -/

/-- **Measurement-teleportation, outcome 1.**  After CNOT, projecting the
    ancilla onto `|1⟩`, and applying the Clifford correction `S` on the
    data qubit, the data qubit again carries `T|ψ⟩` (up to the `ω/√2`
    Born amplitude). -/
theorem t_teleport_outcome_1 (ψ : StateVec 1) :
    Shigh * (projLow1 * (cnotMatrix * (ψ ⊗ᵥ tKet)))
      = (ω / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, kron_vec_apply, kron_vec_high,
          kron_vec_low, projLow1, cnotMatrix, tKet, Tdata, basisState, Shigh,
          Matrix.smul_apply, Matrix.vecMul, dotProduct] <;>
    ring_nf <;> (try rw [ω_sq]) <;> ring_nf

/-! ## §4. Both branches deliver `T|ψ⟩`.

    Reading off the data qubit, both measurement outcomes yield the data
    state `Tdata ψ = T|ψ⟩` (the byproduct differs only by the ancilla
    basis label and a global Born phase). -/

theorem t_teleport_data_is_T (ψ : StateVec 1) :
    (projLow0 * (cnotMatrix * (ψ ⊗ᵥ tKet))
        = (1 / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 0 : StateVec 1)))
    ∧ (Shigh * (projLow1 * (cnotMatrix * (ψ ⊗ᵥ tKet)))
        = (ω / Real.sqrt 2 : ℂ) • (Tdata ψ ⊗ᵥ (basisState 1 : StateVec 1))) :=
  ⟨t_teleport_outcome_0 ψ, t_teleport_outcome_1 ψ⟩

end FormalRV.Framework.MagicStateTeleport
