/-
  FormalRV.PPM.Magic.MagicGadgetInterface — the ANCILLA-CARRYING gadget-realization
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
import FormalRV.PPM.Magic.TGadgetTeleport

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.MagicStateTeleport
open FormalRV.Framework.EightTToCCZ
open FormalRV.PPM.Magic.TGadgetTeleport
open Complex

namespace FormalRV.PPM.Magic.MagicGadgetInterface

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

/-- **Realizations CHAIN on the data register.**  If `G₁` realizes `U₁` (consuming
    magic `m₁`) and `G₂` realizes `U₂` (consuming magic `m₂`), then feeding the
    data output `U₁·ψ` of the first gadget into the second realizes the COMPOSITE
    gate `U₂·U₁` on the data register.  This is the gate-by-gate composition of
    measurement-based gadgets at the effective-data level: each gadget consumes its
    own magic ancilla, and the data-register gate actions compose exactly — the
    property a full circuit's PPM compilation needs.

    (The data-register chaining; assembling the gadgets into a SINGLE operator on
    `data ⊗ anc₁ ⊗ anc₂` is the further tensor-embedding step.) -/
theorem magic_realizes_chain {dD dA1 dA2 : Nat}
    {G1 : Square (dD + dA1)} {m1 : StateVec dA1} {U1 : Square dD}
    {G2 : Square (dD + dA2)} {m2 : StateVec dA2} {U2 : Square dD}
    (h1 : MagicRealizes G1 m1 U1) (h2 : MagicRealizes G2 m2 U2) (ψ : StateVec dD) :
    ∃ (anc1 : StateVec dA1) (anc2 : StateVec dA2) (c1 c2 : ℂ),
      G1 * (ψ ⊗ᵥ m1) = c1 • ((U1 * ψ) ⊗ᵥ anc1)
      ∧ G2 * ((U1 * ψ) ⊗ᵥ m2) = c2 • (((U2 * U1) * ψ) ⊗ᵥ anc2) := by
  obtain ⟨anc1, c1, e1⟩ := h1 ψ
  obtain ⟨anc2, c2, e2⟩ := h2 (U1 * ψ)
  exact ⟨anc1, anc2, c1, c2, e1, by rw [Matrix.mul_assoc]; exact e2⟩

end FormalRV.PPM.Magic.MagicGadgetInterface
