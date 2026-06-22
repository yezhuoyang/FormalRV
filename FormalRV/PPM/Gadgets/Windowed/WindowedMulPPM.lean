/-
  FormalRV.PPM.Gadgets.Windowed.WindowedMulPPM — compiled-PPM semantic
  correctness for WINDOWED MULTIPLICATION, generic over BOTH the adder and
  the compiler.

  `windowedMulCircuitOf A w bits a numWin` is the adder-parametric windowed
  multiplier (QROM lookup-add per window, Gidney 1905.07682); its arithmetic
  correctness `windowedMulCircuitOf_correct` holds for ANY interface adder.
  This file lifts it through ANY `PPMCompilerSpec`: the compiled PPM program
  observes the accumulator holding `(a·y) mod 2^bits`.

  Two axes of genericity at once — any adder × any compiler — so the single
  theorem below covers windowed multiplication over Cuccaro, over Gidney,
  and over any future adder, on the old magic-factory IR today and on the
  Phase-D new-syntax IR the day it lands.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect

namespace FormalRV.PPM.Gadgets.WindowedPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-- **Windowed multiplication over ANY adder, compiled by ANY contract
    compiler, observes the product**: the accumulator of the observed
    output decodes to `(a·y) mod 2^bits`. -/
theorem windowedMul_compiles_to_PPM (S : PPMCompilerSpec) (A : Adder)
    (w bits a numWin y : Nat) (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w)) :
    ∃ out, S.Observes (S.compile (windowedMulCircuitOf A w bits a numWin))
        (mulInputOf A w bits numWin y) out
      ∧ decodeAccOf A out (1 + 2 * w) bits = (a * y) % 2 ^ bits :=
  ⟨Gate.applyNat (windowedMulCircuitOf A w bits a numWin)
      (mulInputOf A w bits numWin y),
   S.compile_observes _ _,
   windowedMulCircuitOf_correct A w bits a numWin y hw hy hclean⟩

/-- Magic demand of the compiled windowed multiplier = its Toffoli count. -/
theorem windowedMul_ppm_magic_demand (S : PPMCompilerSpec) (A : Adder)
    (w bits a numWin : Nat) :
    S.magicDemand (S.compile (windowedMulCircuitOf A w bits a numWin))
      = FormalRV.Framework.CircuitToPPMFactoryProvision.gateCCXCount
          (windowedMulCircuitOf A w bits a numWin) :=
  S.compile_magicDemand _

end FormalRV.PPM.Gadgets.WindowedPPM
