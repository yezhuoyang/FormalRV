/-
  FormalRV.PauliRotation.Gadgets.SemanticInstances
  ────────────────────────────────────────────────
  EVERY GADGET, SEMANTICALLY COMPILED: per-gadget instances of the capstone
  `gateRotSchedule_applyNat` — for each compiled rotation program in
  `Gadgets/`, the PARALLELIZED Pauli-rotation program denotes the gadget's
  own Boolean semantics (`Gate.applyNat`), up to the explicit global phase
  `gphase`.  Side conditions (`opsOK` operand distinctness, width) are
  kernel-checked by `decide` at the anchored sizes; the statements use the
  gadget's own `width` so no bound is ever guessed.

  Together with the per-family files this completes, for EVERY existing
  arithmetic gadget: compilation, exact symbolic T-counts, parallelization
  soundness, and end-to-end semantic correctness.
  (`cuccaroRot_applyNat_4`, the n-bit adder instance, lives in
  `Assembly.lean` as the exemplar.)
-/
import FormalRV.PauliRotation.Correctness.Assembly
import FormalRV.PauliRotation.Gadgets

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-! ## §1. Cuccaro constant-arithmetic variants. -/

theorem cuccaroAddConstRot_applyNat :
    RotProg.denote (Resource.width (cuccaro_addConstGate 3 0 5)) (cuccaroAddConstRot 3 0 5)
      = gphase (cuccaro_addConstGate 3 0 5)
          • applyMat _ (cuccaro_addConstGate 3 0 5) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem cuccaroSubConstRot_applyNat :
    RotProg.denote (Resource.width (cuccaro_subConstGate 3 0 5)) (cuccaroSubConstRot 3 0 5)
      = gphase (cuccaro_subConstGate 3 0 5)
          • applyMat _ (cuccaro_subConstGate 3 0 5) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem cuccaroCompareRot_applyNat :
    RotProg.denote (Resource.width (cuccaro_compareConstForwardGate 3 0 5))
        (cuccaroCompareRot 3 0 5)
      = gphase (cuccaro_compareConstForwardGate 3 0 5)
          • applyMat _ (cuccaro_compareConstForwardGate 3 0 5) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem cuccaroSubForwardRot_applyNat :
    RotProg.denote (Resource.width (cuccaro_subConstForwardOnlyGate 3 0 5))
        (cuccaroSubForwardRot 3 0 5)
      = gphase (cuccaro_subConstForwardOnlyGate 3 0 5)
          • applyMat _ (cuccaro_subConstForwardOnlyGate 3 0 5) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem cuccaroSubReverseRot_applyNat :
    RotProg.denote (Resource.width (cuccaro_subConstReverseOnlyGate 3 0 5))
        (cuccaroSubReverseRot 3 0 5)
      = gphase (cuccaro_subConstReverseOnlyGate 3 0 5)
          • applyMat _ (cuccaro_subConstReverseOnlyGate 3 0 5) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

/-! ## §2. The Gidney ripple-carry adders. -/

theorem gidneyRot_applyNat :
    RotProg.denote (Resource.width (gidney_adder 2)) (gidneyRot 2)
      = gphase (gidney_adder 2) • applyMat _ (gidney_adder 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneyPatchedRot_applyNat :
    RotProg.denote (Resource.width (gidney_adder_full_faithful_no_measurement_patched 2))
        (gidneyPatchedRot 2)
      = gphase (gidney_adder_full_faithful_no_measurement_patched 2)
          • applyMat _ (gidney_adder_full_faithful_no_measurement_patched 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneyForwardRevRot_applyNat :
    RotProg.denote (Resource.width (gidney_adder_forward_faithful_full_reverse_patched 2))
        (gidneyForwardRevRot 2)
      = gphase (gidney_adder_forward_faithful_full_reverse_patched 2)
          • applyMat _ (gidney_adder_forward_faithful_full_reverse_patched 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

/-! ## §3. The modular adders (both pipelines). -/

theorem cuccaroModAddRot_applyNat :
    RotProg.denote (Resource.width (sqir_style_modAddConst_clean_gate 3 5 2))
        (cuccaroModAddRot 3 5 2)
      = gphase (sqir_style_modAddConst_clean_gate 3 5 2)
          • applyMat _ (sqir_style_modAddConst_clean_gate 3 5 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem cuccaroCtrlModAddRot_applyNat :
    RotProg.denote (Resource.width (sqir_style_controlledModAddConst_gate 3 2 5 2 1 0))
        (cuccaroCtrlModAddRot 3 2 5 2 1 0)
      = gphase (sqir_style_controlledModAddConst_gate 3 2 5 2 1 0)
          • applyMat _ (sqir_style_controlledModAddConst_gate 3 2 5 2 1 0) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneyAddConstRot_applyNat :
    RotProg.denote (Resource.width (addConstGate 2 1)) (gidneyAddConstRot 2 1)
      = gphase (addConstGate 2 1) • applyMat _ (addConstGate 2 1) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneySubConstRot_applyNat :
    RotProg.denote (Resource.width (subConstGate 2 1)) (gidneySubConstRot 2 1)
      = gphase (subConstGate 2 1) • applyMat _ (subConstGate 2 1) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneyCondAddRot_applyNat :
    RotProg.denote (Resource.width (conditionalAddConstGate 2 1 8))
        (gidneyCondAddRot 2 1 8)
      = gphase (conditionalAddConstGate 2 1 8)
          • applyMat _ (conditionalAddConstGate 2 1 8) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneyModAddRot_applyNat :
    RotProg.denote (Resource.width (modAddConstGate 2 3 1)) (gidneyModAddRot 2 3 1)
      = gphase (modAddConstGate 2 3 1) • applyMat _ (modAddConstGate 2 3 1) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem gidneyCtrlModAddRot_applyNat :
    RotProg.denote (Resource.width (controlledModAddConstGate 2 3 1 9 10))
        (gidneyCtrlModAddRot 2 3 1 9 10)
      = gphase (controlledModAddConstGate 2 3 1 9 10)
          • applyMat _ (controlledModAddConstGate 2 3 1 9 10) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

/-! ## §4. The modular multiplier and the mod-exp chains. -/

theorem modMultConstRot_applyNat :
    RotProg.denote (Resource.width (modmult_const_gate 2 15 7)) (modMultConstRot 2 15 7)
      = gphase (modmult_const_gate 2 15 7)
          • applyMat _ (modmult_const_gate 2 15 7) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem modMultMCPRot_applyNat :
    RotProg.denote (Resource.width (modmult_MCP_gate 2 15 7 13)) (modMultMCPRot 2 15 7 13)
      = gphase (modmult_MCP_gate 2 15 7 13)
          • applyMat _ (modmult_MCP_gate 2 15 7 13) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem shorModExpVerifiedRot_applyNat :
    RotProg.denote (Resource.width (shorModExpVerified 1 15 7 13))
        (shorModExpVerifiedRot 1 15 7 13)
      = gphase (shorModExpVerified 1 15 7 13)
          • applyMat _ (shorModExpVerified 1 15 7 13) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem shorModExpRot_applyNat :
    RotProg.denote (Resource.width (shorModExp 1 15 7)) (shorModExpRot 1 15 7)
      = gphase (shorModExp 1 15 7) • applyMat _ (shorModExp 1 15 7) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

/-! ## §5. The QROM lookups. -/

theorem unaryLookupRot_applyNat :
    RotProg.denote (Resource.width (unary_lookup_multi_iteration 2 [([0], [5])]))
        (unaryLookupRot 2 [([0], [5])])
      = gphase (unary_lookup_multi_iteration 2 [([0], [5])])
          • applyMat _ (unary_lookup_multi_iteration 2 [([0], [5])]) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem grayLookupRot_applyNat :
    RotProg.denote (Resource.width (grayLookupReadAt 2 (fun i => 6 + i) 1 (fun _ => 1)))
        (grayLookupRot 2 (fun i => 6 + i) 1 (fun _ => 1))
      = gphase (grayLookupReadAt 2 (fun i => 6 + i) 1 (fun _ => 1))
          • applyMat _ (grayLookupReadAt 2 (fun i => 6 + i) 1 (fun _ => 1)) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

/-! ## §6. The windowed multipliers. -/

theorem windowedMulRot_applyNat :
    RotProg.denote (Resource.width (windowedMulCircuit 2 4 3 2)) (windowedMulRot 2 4 3 2)
      = gphase (windowedMulCircuit 2 4 3 2)
          • applyMat _ (windowedMulCircuit 2 4 3 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem windowedModNMulRot_applyNat :
    RotProg.denote (Resource.width (windowedModNMulCircuit 2 4 3 7 2))
        (windowedModNMulRot 2 4 3 7 2)
      = gphase (windowedModNMulCircuit 2 4 3 7 2)
          • applyMat _ (windowedModNMulCircuit 2 4 3 7 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem windowedModNInPlaceRot_applyNat :
    RotProg.denote (Resource.width (windowedModNMulGate 2 4 7 2 3 5))
        (windowedModNInPlaceRot 2 4 7 2 3 5)
      = gphase (windowedModNMulGate 2 4 7 2 3 5)
          • applyMat _ (windowedModNMulGate 2 4 7 2 3 5) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

theorem grayWindowedMulRot_applyNat :
    RotProg.denote (Resource.width (grayWindowedMulCircuitOf cuccaroAdder 2 4 3 2))
        (grayWindowedMulRot 2 4 3 2)
      = gphase (grayWindowedMulCircuitOf cuccaroAdder 2 4 3 2)
          • applyMat _ (grayWindowedMulCircuitOf cuccaroAdder 2 4 3 2) :=
  gateRotSchedule_applyNat _ _ (by decide) (Nat.le_refl _)

end FormalRV.PauliRotation
