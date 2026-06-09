/-
  FormalRV.Shor.WindowedCapstone — the logical-level verification of Gidney's windowed
  modular multiplier, bundled.

  This ties together, for ARBITRARY window size `w`, the three faces of "fully verified
  at the logical level", with interfaces consistent with the rest of FormalRV:

    1. VALUE   — the windowed multiplier computes `a·x mod N` (the value the Shor oracle
                 contract `MultiplyCircuitProperty a N` requires);
    2. RESOURCE— its Toffoli (CCX) count is the closed form `numWin·(4·w·2^w + 2·bits)`,
                 which compares to Gidney–Ekerå's `0.3 n³` (the gap being exactly the
                 Gray-code + measurement-uncompute optimizations deferred to PPM —
                 see `WindowedCircuit`'s comparison note);
    3. PPM     — compiling the circuit through the PPM magic-state compiler demands
                 EXACTLY that Toffoli count of magic states (`shorMagicDemand`), so the
                 logical circuit descends to the magic-factory / lattice-surgery layer
                 with a proven budget.

  All three are kernel-clean and hold for every `(w, bits, a, numWin, N, x)`.  The
  concrete circuit (`windowedMulCircuit`, a `Gate`) is executed on genuinely
  qubit-encoded integers at two window sizes in `WindowedCircuitExec`.
-/
import FormalRV.Arithmetic.Windowed.WindowedArith
import FormalRV.Shor.WindowedPPM

namespace FormalRV.Shor.WindowedCapstone

open FormalRV.Framework.CircuitToPPMFactoryProvision
open FormalRV.Shor.WindowedArith
open FormalRV.Shor.WindowedCircuit

/-- **Logical-level verification of the windowed modular multiplier (any window size).**
    For all parameters, the windowed multiplier (a) computes the modular product
    `a·x mod N` that the Shor oracle contract requires, (b) has the verified closed-form
    Toffoli count, and (c) demands exactly that many magic states when compiled to PPM —
    one statement carrying the value-correctness, the resource number, and the
    lower-level hand-off. -/
theorem windowedMultiplier_verified
    (w bits a numWin N x : Nat) (hN : 0 < N) (hx : x < (2 ^ w) ^ numWin) :
    windowedLookupFold a N w (window w x) numWin 0 = (a * x) % N
    ∧ toffoliCount (windowedMulCircuit w bits a numWin) = numWin * (4 * w * 2 ^ w + 2 * bits)
    ∧ shorMagicDemand (windowedMulCircuit w bits a numWin) = numWin * (4 * w * 2 ^ w + 2 * bits) :=
  ⟨windowedLookupFold_eq_modmul a N w numWin x hN hx,
   windowedMulCircuit_toffoli w bits a numWin,
   FormalRV.Shor.WindowedPPM.windowedMulCircuit_magicDemand w bits a numWin⟩

end FormalRV.Shor.WindowedCapstone
