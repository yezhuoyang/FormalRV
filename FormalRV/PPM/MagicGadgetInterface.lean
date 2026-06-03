/-
  FormalRV.PPM.MagicGadgetInterface — the ANCILLA-CARRYING gadget-realization
  predicate, discharged by the REAL T-gadget (not the `rfl` baseline).

  The operator-level `RealizesUpToFrame op frame U := op = frame * U` in
  `PPMCompilerCorrectness` cannot express a measurement-based gadget, because such
  a gadget consumes a magic ANCILLA and acts on the data only after measurement +
  correction.  The right predicate is therefore on the magic-extended ACTION:

      `MagicRealizes G magic U` :⇔
        ∀ ψ, G · (ψ ⊗ magic) = c • ((U · ψ) ⊗ anc)   for some ancilla `anc`, scalar `c`.

  i.e. running the data state `ψ` together with the magic state `magic` through the
  gadget operator `G` teleports `U · ψ` onto the data register (the ancilla
  collapses, with a Born/frame scalar).

  The headline `tGadget_magic_realizes` discharges this for the T gate using the
  REAL teleportation `TGadgetTeleport.t_gadget_with_feedback` (ancilla `|T⟩`, CNOT,
  Z-measure, classically-controlled `S`).  So the gate realization is the genuine
  gadget theorem — NOT `compile := uc_eval` closing by `rfl`.  Kernel-clean.
-/
import FormalRV.PPM.TGadgetTeleport

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.MagicStateTeleport
open FormalRV.Framework.EightTToCCZ
open FormalRV.PPM.TGadgetTeleport
open Complex

namespace FormalRV.PPM.MagicGadgetInterface

/-- **Ancilla-carrying realization.**  The gadget operator `G` on the
    data⊗ancilla space realizes the gate `U` on the data register, consuming the
    magic state `magic`: for every data input `ψ`, `G · (ψ ⊗ magic)` is
    `(U · ψ) ⊗ anc` up to a scalar.  This is the measurement-based analogue of
    `RealizesUpToFrame`, expressed on the magic-extended action. -/
def MagicRealizes {dD dA : Nat}
    (G : Square (dD + dA)) (magic : StateVec dA) (U : Square dD) : Prop :=
  ∀ ψ : StateVec dD, ∃ (anc : StateVec dA) (c : ℂ),
    G * (ψ ⊗ᵥ magic) = c • ((U * ψ) ⊗ᵥ anc)

/-- The `T`-gate matrix `diag(1, ω)` (`ω = e^{iπ/4}`). -/
noncomputable def tMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, ω]

/-- `tMat` acts as `Tdata`: `tMat · ψ = T|ψ⟩`. -/
theorem tMat_apply (ψ : StateVec 1) : tMat * ψ = Tdata ψ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat, Tdata, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The real T-gadget DISCHARGES `MagicRealizes` for the T gate.**  For each
    measurement outcome `b`, the gadget operator
    `S_feedback · Z-measure · CNOT` realizes the `T`-matrix on the data register
    using the magic state `|T⟩` — witnessed by `t_gadget_with_feedback`.  This is
    a genuine (non-`rfl`) discharge: `realize` IS the proven teleportation, so the
    ancilla-carrying interface is fillable with REAL measurement-based content. -/
theorem tGadget_magic_realizes (b : Bool) :
    MagicRealizes (dD := 1) (dA := 1)
      (tCorrection b * tProj b * cnotMatrix) tKet tMat := by
  intro ψ
  refine ⟨tAnc b, tBorn b, ?_⟩
  rw [tMat_apply, Matrix.mul_assoc, Matrix.mul_assoc]
  exact t_gadget_with_feedback ψ b

end FormalRV.PPM.MagicGadgetInterface
