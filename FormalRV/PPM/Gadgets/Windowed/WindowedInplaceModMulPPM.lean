/-
  FormalRV.PPM.Gadgets.Windowed.WindowedInplaceModMulPPM — compiled-PPM
  semantic correctness for the composed WINDOWED IN-PLACE modular
  multiplier `windowedInplaceModMulGate` (windowed-forward · swap ·
  selected-add cascade · swap-unload), against ANY `PPMCompilerSpec`.

  This is the spec-parametric form of the existing factory E2E
  `Shor/WindowedShorPPMFactoryE2E.windowed_compiles_to_PPM_with_factory`
  (which stays as-is — it IS the `magicFactoryCompiler` instance of this
  theorem).  Arithmetic content: `windowedInplaceModMulGate_roundTrip`.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Shor.WindowedShorConnection

namespace FormalRV.PPM.Gadgets.WindowedPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedShorConnection

/-- **The windowed in-place modular multiplier, compiled by any contract
    compiler, observes `x ↦ (c·x) mod N`** on the encoded data register
    with clean ancillas. -/
theorem windowedInplaceModMul_compiles_to_PPM (S : PPMCompilerSpec)
    (c N ainv bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (hx : x < N) (h_ainv_le : ainv ≤ N) (h_inv : (c * ainv) % N = 1) :
    S.Observes (S.compile (windowedInplaceModMulGate c N ainv bits))
      (encodeDataZeroAnc bits anc x)
      (encodeDataZeroAnc bits anc ((c * x) % N)) := by
  have h := S.compile_observes (windowedInplaceModMulGate c N ainv bits)
      (encodeDataZeroAnc bits anc x)
  rwa [windowedInplaceModMulGate_roundTrip c N ainv bits anc x
        hbits h_even hN_pos hN hN2 h_anc_pos hx h_ainv_le h_inv] at h

end FormalRV.PPM.Gadgets.WindowedPPM
