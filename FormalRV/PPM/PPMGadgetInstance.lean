/-
  FormalRV.PPM.PPMGadgetInstance — an inhabitation witness for
  `PPMGadgetInterface`.

  ## READ THIS FIRST — what this module is and is NOT

  This is the TRIVIAL "unitary baseline" instance: `compile := uc_eval` (the
  IDENTITY compiler).  It proves that `PPMGadgetInterface` is satisfiable and
  that the composition + transfer machinery of `PPMCompilerCorrectness` actually
  fires end-to-end — but it does **NOT** model PPM measurement gadgets.  Because
  `compile` is defined to BE `uc_eval`, `realize_gate1`/`realize_cnot` close by
  `rfl`: the instance asserts "compiling a circuit to its own unitary realizes
  that unitary", which is true but vacuous.  Its only non-trivial content is that
  `conj` is the GENUINE Heisenberg conjugation `U · f · U⁻¹` (not the unsound
  identity), so `conj_law` is a real Pauli-frame-update fact.

  It does NOT discharge the real obligation: a measurement-based instance where
  `compile (app1 U_T nq)` is the actual T gate-teleportation gadget operator
  (magic state + CNOT + Z-measure + S-correction), `frame ≠ 1` is the byproduct
  Pauli, and `realize_gate1` is the THEOREM (from `MagicStateTeleport` /
  `CliffordPPMRules`) that the gadget realizes the gate up to that frame.  That
  `frame ≠ 1` measurement-based instance — and the interface rework needed to
  carry the magic/syndrome ancilla qubits — is the genuine open obligation.

  Kept here as: (1) proof the framework is inhabited / non-vacuous; (2) the
  exact-frame discharge of `success_transfer` (free, since `frame = 1`), which
  composes with `ProbabilityTransfer` on the Shor side.  Kernel-clean.
-/
import FormalRV.PPM.PPMCompilerCorrectness

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.CliffordTRotations

namespace FormalRV.PPM.PPMGadgetInstance

open FormalRV.PPM.PPMCompilerCorrectness

/-- The exact-frame (`frame = 1`) instance of `PPMGadgetInterface`: the identity
    compiler `compile := uc_eval`, with GENUINE Heisenberg conjugation
    `conj c f := U · f · U⁻¹`.  `hinv` carries the one physical fact used — every
    compiled circuit unitary is invertible.  TRIVIAL/baseline (see module header):
    it witnesses inhabitation, it does not model measurements. -/
noncomputable def exactFrameInstance (dim : Nat)
    (hinv : ∀ c : BaseUCom dim, Invertible (uc_eval c)) :
    PPMGadgetInterface dim where
  compile := uc_eval
  frame := fun _ => (1 : Square dim)
  conj := fun c f => uc_eval c * f * (letI := hinv c; ⅟(uc_eval c))
  conj_law := by
    intro c f
    letI := hinv c
    show uc_eval c * f = (uc_eval c * f * ⅟(uc_eval c)) * uc_eval c
    rw [Matrix.mul_assoc, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  compile_seq := fun _ _ => rfl
  frame_seq := by
    intro c₁ c₂
    letI := hinv c₂
    show (1 : Square dim)
        = (1 : Square dim) * (uc_eval c₂ * (1 : Square dim) * ⅟(uc_eval c₂))
    rw [Matrix.one_mul, Matrix.mul_one, mul_invOf_self]
  realize_gate1 := by
    intros
    show uc_eval _ = (1 : Square dim) * uc_eval _
    rw [Matrix.one_mul]
  realize_cnot := by
    intros
    show uc_eval _ = (1 : Square dim) * uc_eval _
    rw [Matrix.one_mul]

/-- `compileToPPM_correct` is inhabited (not hypothetical): for any Clifford+T
    `C`, the exact-frame compilation equals the circuit unitary on the nose.
    (Baseline — the compiler here IS `uc_eval`.) -/
theorem exactFrame_compiles_correctly (dim : Nat)
    (hinv : ∀ c : BaseUCom dim, Invertible (uc_eval c))
    {C : BaseUCom dim} (hC : IsCliffordT C) :
    (exactFrameInstance dim hinv).compile C = uc_eval C :=
  realizes_trivial_frame (compileToPPM_correct (exactFrameInstance dim hinv) hC)

/-- Success-probability transfer is FREE for the exact-frame instance: the
    residual frame is `1`, so `success_transfer`'s frame-invariance hypothesis is
    discharged by `Matrix.one_mul`.  Composes with the Shor-side
    `ProbabilityTransfer` lemmas.  (The `frame ≠ 1` case remains open.) -/
theorem exactFrame_success_transfer (dim : Nat)
    (hinv : ∀ c : BaseUCom dim, Invertible (uc_eval c))
    (succ : Square dim → ℝ) {C : BaseUCom dim} (hC : IsCliffordT C) :
    succ ((exactFrameInstance dim hinv).compile C) = succ (uc_eval C) := by
  refine success_transfer succ
    (compileToPPM_correct (exactFrameInstance dim hinv) hC) (fun U => ?_)
  show succ ((1 : Square dim) * U) = succ U
  rw [Matrix.one_mul]

end FormalRV.PPM.PPMGadgetInstance
