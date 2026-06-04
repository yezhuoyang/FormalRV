/-
  FormalRV.PPM.TGadgetTeleport — the REAL T gate-teleportation gadget.

  The genuine measurement-based T gate (NOT the vacuous `compile := uc_eval`
  baseline):

    * a real magic ancilla `|T⟩ = tKet` (supplied by the factory — the ONE
      assumption: we are given `|T⟩` at the port, ideal here; its error rate is
      the factory parameter),
    * state teleportation: `CNOT` (data controls ancilla) then a `Z`-basis
      measurement of the ancilla (outcome `b`),
    * classically-controlled feedback: apply the Clifford correction `S = Shigh`
      to the data qubit iff `b = 1`.

  The headline `t_gadget_with_feedback` proves that for EVERY outcome `b`, after
  the feedback the DATA qubit deterministically holds `T|ψ⟩` (the ancilla just
  collapses to `|b⟩`, with a Born amplitude).  Built by reusing the already-proven
  amplitudes `MagicStateTeleport.t_teleport_outcome_0/1` — kernel-clean, no sorry,
  no new axiom.

  This is the worked, non-vacuous per-gate gadget that a real
  `PPMGadgetInterface` instance must use for the `T` gate.
-/
import FormalRV.PPM.PPMDenote

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.MagicStateTeleport
open FormalRV.Framework.EightTToCCZ
open Complex

namespace FormalRV.PPM.TGadgetTeleport

/-- The `Z`-measurement projector on the ancilla for outcome `b`. -/
def tProj : Bool → Matrix (Fin 4) (Fin 4) ℂ
  | false => projLow0
  | true  => projLow1

/-- The classically-controlled correction: `S` on the data qubit iff outcome `1`. -/
noncomputable def tCorrection : Bool → Matrix (Fin 4) (Fin 4) ℂ
  | false => 1
  | true  => Shigh

/-- The Born amplitude of outcome `b` (tracked, not normalised away). -/
noncomputable def tBorn : Bool → ℂ
  | false => 1 / Real.sqrt 2
  | true  => ω / Real.sqrt 2

/-- The ancilla's collapsed state after outcome `b`. -/
noncomputable def tAnc : Bool → StateVec 1
  | false => basisState 0
  | true  => basisState 1

/-- **The real T-gadget with classically-controlled feedback.**  For EVERY
    measurement outcome `b`, running `CNOT`, measuring the ancilla (outcome `b`),
    and applying the `S` correction iff `b = 1`, on input `ψ ⊗ |T⟩`, yields
    `(Born amplitude) • (T|ψ⟩ ⊗ |b⟩)`: the data qubit deterministically holds
    `T|ψ⟩` on BOTH branches (the feedback removes the branch dependence on the
    data register).  Reuses `t_teleport_outcome_0/1`. -/
theorem t_gadget_with_feedback (ψ : StateVec 1) (b : Bool) :
    tCorrection b * (tProj b * (cnotMatrix * (ψ ⊗ᵥ tKet)))
      = tBorn b • (Tdata ψ ⊗ᵥ tAnc b) := by
  cases b
  · simp only [tCorrection, tProj, tBorn, tAnc, Matrix.one_mul]
    exact t_teleport_outcome_0 ψ
  · simp only [tCorrection, tProj, tBorn, tAnc]
    exact t_teleport_outcome_1 ψ

/-- **The data register always holds `T|ψ⟩`.**  Outcome-independent correctness of
    the corrected gadget: whatever the measurement outcome, after feedback the data
    state is `T|ψ⟩` (up to the Born amplitude and the ancilla label).  This is the
    real teleportation correctness, deferred-frame discharged by the `S` feedback. -/
theorem t_gadget_data_is_T (ψ : StateVec 1) (b : Bool) :
    ∃ c : ℂ, tCorrection b * (tProj b * (cnotMatrix * (ψ ⊗ᵥ tKet)))
      = c • (Tdata ψ ⊗ᵥ tAnc b) :=
  ⟨tBorn b, t_gadget_with_feedback ψ b⟩

end FormalRV.PPM.TGadgetTeleport
