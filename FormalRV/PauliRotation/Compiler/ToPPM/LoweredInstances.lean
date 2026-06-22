/-
  FormalRV.PauliRotation.Compiler.ToPPM.LoweredInstances
  ─────────────────────────────────────────────
  **EVERY GADGET, FULLY LOWERED TO PPM WITH SEMANTIC CORRECTNESS** — the
  per-gadget instances of `lowerGate_denote`: each compiled arithmetic
  gadget's lowered PPM program implements the gadget's own Boolean
  semantics on every measurement branch (`LoweredOK`), plus the full
  Shor-15 instance through `lowerShorQPE_denote`.

  Together with the per-family compilation files, the symbolic T-counts,
  the scheduler theorems, the dictionary capstone, and the preservation
  theorem, this closes the chain

      Gate-IR ──gateRots──▶ rotations ──schedule──▶ layers ──lower──▶ PPM

  with machine-checked semantics and exact counts at EVERY arrow, for
  EVERY gadget and the complete Shor/QPE circuit.
-/
import FormalRV.PauliRotation.Compiler.ToPPM.GadgetLowering
import FormalRV.PauliRotation.Gadgets

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open Matrix

/-- **The lowered-gadget correctness statement, packaged**: on every
measurement branch, the lowered PPM program of `g` implements
`gphase g • applyMat g` on the data, tensored with the ancilla collapses,
at the explicit branch scalar. -/
def LoweredOK (g : FormalRV.Framework.Gate) : Prop :=
  ∀ (ω : Nat → Bool) (outs : List Bool)
    (ψ : Fin (2 ^ Resource.width g) → ℂ),
    (progDenote (ampsWidth (Resource.width g) (ancAmps (gateRots g))) ω outs
        (lowerFlat (Resource.width g) outs.length (gateRots g))).mulVec
      (stateOver (ancAmps (gateRots g)) (ancAmps (gateRots g))
        (Resource.width g) ψ)
    = (branchScalar ω (gateRots g) outs.length * gphase g)
        • stateOver (ancAmps (gateRots g))
            (ancOutAmps ω (gateRots g) outs.length) (Resource.width g)
            ((applyMat (Resource.width g) g).mulVec ψ)

theorem loweredOK_of (g : FormalRV.Framework.Gate)
    (hops : opsOK g = true) : LoweredOK g :=
  fun ω outs ψ =>
    lowerGate_denote (Resource.width g) g hops (Nat.le_refl _) ω outs ψ

/-! ## §1. The Cuccaro family. -/

theorem cuccaroLowered : LoweredOK (cuccaro_n_bit_adder_full 4 0) :=
  loweredOK_of _ (by decide)

theorem cuccaroAddConstLowered : LoweredOK (cuccaro_addConstGate 3 0 5) :=
  loweredOK_of _ (by decide)

theorem cuccaroSubConstLowered : LoweredOK (cuccaro_subConstGate 3 0 5) :=
  loweredOK_of _ (by decide)

theorem cuccaroCompareLowered :
    LoweredOK (cuccaro_compareConstForwardGate 3 0 5) :=
  loweredOK_of _ (by decide)

theorem cuccaroSubForwardLowered :
    LoweredOK (cuccaro_subConstForwardOnlyGate 3 0 5) :=
  loweredOK_of _ (by decide)

theorem cuccaroSubReverseLowered :
    LoweredOK (cuccaro_subConstReverseOnlyGate 3 0 5) :=
  loweredOK_of _ (by decide)

/-! ## §2. The Gidney adders. -/

theorem gidneyLowered : LoweredOK (gidney_adder 2) :=
  loweredOK_of _ (by decide)

theorem gidneyPatchedLowered :
    LoweredOK (gidney_adder_full_faithful_no_measurement_patched 2) :=
  loweredOK_of _ (by decide)

theorem gidneyForwardRevLowered :
    LoweredOK (gidney_adder_forward_faithful_full_reverse_patched 2) :=
  loweredOK_of _ (by decide)

/-! ## §3. The modular adders (both pipelines). -/

theorem cuccaroModAddLowered :
    LoweredOK (sqir_style_modAddConst_clean_gate 3 5 2) :=
  loweredOK_of _ (by decide)

theorem cuccaroCtrlModAddLowered :
    LoweredOK (sqir_style_controlledModAddConst_gate 3 2 5 2 1 0) :=
  loweredOK_of _ (by decide)

theorem gidneyAddConstLowered : LoweredOK (addConstGate 2 1) :=
  loweredOK_of _ (by decide)

theorem gidneySubConstLowered : LoweredOK (subConstGate 2 1) :=
  loweredOK_of _ (by decide)

theorem gidneyCondAddLowered : LoweredOK (conditionalAddConstGate 2 1 8) :=
  loweredOK_of _ (by decide)

theorem gidneyModAddLowered : LoweredOK (modAddConstGate 2 3 1) :=
  loweredOK_of _ (by decide)

theorem gidneyCtrlModAddLowered :
    LoweredOK (controlledModAddConstGate 2 3 1 9 10) :=
  loweredOK_of _ (by decide)

/-! ## §4. ModMult and the mod-exp chains. -/

theorem modMultConstLowered : LoweredOK (modmult_const_gate 2 15 7) :=
  loweredOK_of _ (by decide)

theorem modMultMCPLowered : LoweredOK (modmult_MCP_gate 2 15 7 13) :=
  loweredOK_of _ (by decide)

theorem shorModExpVerifiedLowered :
    LoweredOK (shorModExpVerified 1 15 7 13) :=
  loweredOK_of _ (by decide)

theorem shorModExpLowered : LoweredOK (shorModExp 1 15 7) :=
  loweredOK_of _ (by decide)

/-! ## §5. The QROM lookups. -/

theorem unaryLookupLowered :
    LoweredOK (unary_lookup_multi_iteration 2 [([0], [5])]) :=
  loweredOK_of _ (by decide)

theorem grayLookupLowered :
    LoweredOK (grayLookupReadAt 2 (fun i => 6 + i) 1 (fun _ => 1)) :=
  loweredOK_of _ (by decide)

/-! ## §6. The windowed multipliers. -/

theorem windowedMulLowered : LoweredOK (windowedMulCircuit 2 4 3 2) :=
  loweredOK_of _ (by decide)

theorem windowedModNMulLowered :
    LoweredOK (windowedModNMulCircuit 2 4 3 7 2) :=
  loweredOK_of _ (by decide)

theorem windowedModNInPlaceLowered :
    LoweredOK (windowedModNMulGate 2 4 7 2 3 5) :=
  loweredOK_of _ (by decide)

theorem grayWindowedMulLowered :
    LoweredOK (grayWindowedMulCircuitOf cuccaroAdder 2 4 3 2) :=
  loweredOK_of _ (by decide)

/-! ## §7. FULL SHOR-15, LOWERED TO PPM. -/

open FormalRV.BQAlgo in
set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2048 in
/-- **The COMPLETE Shor-15 circuit — H-layer, verified modexp oracle,
banded inverse QFT — lowered to a PPM measurement program, with semantic
correctness on every measurement branch**: the lowered program implements
the composed closed form (IQFT block · modexp `applyMat` · H-layer block)
on the data, tensored with the ancilla collapses, at the explicit branch
scalar.  All side conditions kernel-checked. -/
theorem shor15Lowered (ω : Nat → Bool) (outs : List Bool)
    (ψ : Fin (2 ^ 7) → ℂ) :
    (progDenote
        (ampsWidth 7 (ancAmps
          (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13))))) ω outs
        (lowerFlat 7 outs.length
          (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13))))).mulVec
      (stateOver (ancAmps (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13))))
        (ancAmps (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13)))) 7 ψ)
    = (branchScalar ω (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13)))
          outs.length
        * (iqftPhase 2 * gphase (shorModExpVerified 1 15 7 13)
            * ((-Complex.I) * (((Real.sqrt 2 : ℝ) / 2 : ℝ) : ℂ)) ^ 3))
        • stateOver
            (ancAmps (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13))))
            (ancOutAmps ω
              (qpeRots 3 (gateRots (shorModExpVerified 1 15 7 13)))
              outs.length) 7
            ((iqftMat 7 2 * applyMat 7 (shorModExpVerified 1 15 7 13)
                * hLayerMat 7 3).mulVec ψ) :=
  lowerShorQPE_denote 7 2 (shorModExpVerified 1 15 7 13)
    (by decide) (by decide) (by omega) (by decide) ω outs ψ

end FormalRV.PauliRotation
