/-
  FormalRV.PPM.Gadgets.Adder.AdderPPM — per-gadget compiled-PPM semantic
  correctness for ADDERS, proven ONCE for the whole `Adder` interface and
  hence for every instance (Cuccaro, Gidney patched ripple, and any future
  adder), against ANY compiler satisfying `PPMCompilerSpec`.

  ## The statement

  For any compiler `S` and any interface adder `A`: the compiled PPM program
  of `A.circuit n q`, run from any state with the adder's ancilla block
  clean, observes output bits in which

    * the augend register decodes to `(augend + addend) mod 2^n`  (the SUM),
    * the addend register is restored bit-for-bit,
    * the ancilla block is clean again (so adds compose),
    * everything outside the block `[q, q + span n)` is untouched.

  This is the PPM leg of the per-gadget spine (Def / Correctness / Resource /
  PPM).  The arithmetic content is the interface's `sumCorrect` etc.; the
  compiler content is `S.compile_observes`; this file just composes them —
  which is the point: when the Phase-D new-syntax compiler lands, these
  theorems hold for it instantly.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.Adder
import FormalRV.Arithmetic.Adder.Cuccaro
import FormalRV.Arithmetic.Adder.Gidney

namespace FormalRV.PPM.Gadgets.AdderPPM

open FormalRV.Framework
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.BQAlgo

/-! ## §1. The interface-generic theorem (every adder, every compiler). -/

/-- **Any interface adder, compiled by any contract compiler, observes the
    in-place sum** (with addend restored, ancillas clean, frame intact). -/
theorem adder_compiles_to_PPM (S : PPMCompilerSpec) (A : Adder)
    (n q : Nat) (f : Nat → Bool) (h : A.ancClean f n q) :
    ∃ out, S.Observes (S.compile (A.circuit n q)) f out
      ∧ decodeReg (A.augendIdx q) n out
          = (decodeReg (A.augendIdx q) n f + decodeReg (A.addendIdx q) n f) % 2 ^ n
      ∧ (∀ i, i < n → out (A.addendIdx q i) = f (A.addendIdx q i))
      ∧ A.ancClean out n q
      ∧ (∀ p, ¬ inBlock q (A.span n) p → out p = f p) :=
  ⟨Gate.applyNat (A.circuit n q) f,
   S.compile_observes (A.circuit n q) f,
   A.sumCorrect n q f h,
   A.addendRestored n q f h,
   A.ancRestored n q f h,
   A.frame n q f⟩

/-- The compiled adder's magic demand is its Toffoli count (any compiler). -/
theorem adder_ppm_magic_demand (S : PPMCompilerSpec) (A : Adder) (n q : Nat) :
    S.magicDemand (S.compile (A.circuit n q)) = gateCCXCount (A.circuit n q) :=
  S.compile_magicDemand _

/-! ## §2. The named instances (one-liners — the interface did the work). -/

/-- The CUCCARO adder, compiled to PPM by any contract compiler. -/
theorem cuccaroAdder_compiles_to_PPM (S : PPMCompilerSpec)
    (n q : Nat) (f : Nat → Bool) (h : cuccaroAdder.ancClean f n q) :
    ∃ out, S.Observes (S.compile (cuccaroAdder.circuit n q)) f out
      ∧ decodeReg (cuccaroAdder.augendIdx q) n out
          = (decodeReg (cuccaroAdder.augendIdx q) n f
              + decodeReg (cuccaroAdder.addendIdx q) n f) % 2 ^ n
      ∧ (∀ i, i < n → out (cuccaroAdder.addendIdx q i) = f (cuccaroAdder.addendIdx q i))
      ∧ cuccaroAdder.ancClean out n q
      ∧ (∀ p, ¬ inBlock q (cuccaroAdder.span n) p → out p = f p) :=
  adder_compiles_to_PPM S cuccaroAdder n q f h

/-- The GIDNEY patched ripple adder, compiled to PPM by any contract compiler. -/
theorem gidneyAdder_compiles_to_PPM (S : PPMCompilerSpec)
    (n q : Nat) (f : Nat → Bool) (h : gidneyAdder.ancClean f n q) :
    ∃ out, S.Observes (S.compile (gidneyAdder.circuit n q)) f out
      ∧ decodeReg (gidneyAdder.augendIdx q) n out
          = (decodeReg (gidneyAdder.augendIdx q) n f
              + decodeReg (gidneyAdder.addendIdx q) n f) % 2 ^ n
      ∧ (∀ i, i < n → out (gidneyAdder.addendIdx q i) = f (gidneyAdder.addendIdx q i))
      ∧ gidneyAdder.ancClean out n q
      ∧ (∀ p, ¬ inBlock q (gidneyAdder.span n) p → out p = f p) :=
  adder_compiles_to_PPM S gidneyAdder n q f h

/-! ## §3. Factory-grounded corollary (today's concrete compiler, in the
    house E2E shape: run on a provisioned certified-T pool and observe). -/

/-- **The Cuccaro adder compiled to the magic-aware PPM program runs on a
    factory-provisioned certified-T pool and observes the sum.** -/
theorem cuccaroAdder_compiles_to_PPM_with_factory (F : TFactoryContract)
    (n q : Nat) (f : Nat → Bool) (h : cuccaroAdder.ancClean f n q) :
    ∃ σ', MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (cuccaroAdder.circuit n q))
        (encodeWithPool f
          (factoryProvision F (shorMagicDemand (cuccaroAdder.circuit n q)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ'
          (Gate.applyNat (cuccaroAdder.circuit n q) f)
      ∧ decodeReg (cuccaroAdder.augendIdx q) n
            (Gate.applyNat (cuccaroAdder.circuit n q) f)
          = (decodeReg (cuccaroAdder.augendIdx q) n f
              + decodeReg (cuccaroAdder.addendIdx q) n f) % 2 ^ n := by
  obtain ⟨σ', hrun, hobs⟩ :=
    compileToMagicPPM_provisioned_run_observe F (cuccaroAdder.circuit n q) f
  exact ⟨σ', hrun, hobs, cuccaroAdder.sumCorrect n q f h⟩

/-- Same, for the Gidney patched ripple adder. -/
theorem gidneyAdder_compiles_to_PPM_with_factory (F : TFactoryContract)
    (n q : Nat) (f : Nat → Bool) (h : gidneyAdder.ancClean f n q) :
    ∃ σ', MagicPPMProgramRel F
        (compileArithmeticGateToMagicPPM (gidneyAdder.circuit n q))
        (encodeWithPool f
          (factoryProvision F (shorMagicDemand (gidneyAdder.circuit n q)))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ'
          (Gate.applyNat (gidneyAdder.circuit n q) f)
      ∧ decodeReg (gidneyAdder.augendIdx q) n
            (Gate.applyNat (gidneyAdder.circuit n q) f)
          = (decodeReg (gidneyAdder.augendIdx q) n f
              + decodeReg (gidneyAdder.addendIdx q) n f) % 2 ^ n := by
  obtain ⟨σ', hrun, hobs⟩ :=
    compileToMagicPPM_provisioned_run_observe F (gidneyAdder.circuit n q) f
  exact ⟨σ', hrun, hobs, gidneyAdder.sumCorrect n q f h⟩

end FormalRV.PPM.Gadgets.AdderPPM
