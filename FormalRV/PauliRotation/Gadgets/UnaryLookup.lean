/-
  FormalRV.PauliRotation.Gadgets.UnaryLookup
  ──────────────────────────────────────────
  THE BABBUSH-STYLE QROM LOOKUPS, compiled to Pauli rotations
  (`GateBridge.lean`):

    • `unary_lookup_multi_iteration` — the faithful unary-iteration lookup
      (per-address prefix-AND compute/uncompute): `14·n_addr` T per
      iteration, `14·n_addr·|iters|` total;
    • `grayLookupReadAt` — the Gray-code/sawtooth read: `14·(2^w − 1)` T,
      the factor-`w` saving over the faithful read (selection contract
      proven identical in `UnaryLookupGrayCode.lean`).

  Both compile exactly (Toffoli-class).  NB the Gray-code module lives in
  namespace `FormalRV.Shor.WindowedCircuit`, not `BQAlgo`.
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGateDerivations
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGrayCode

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. The faithful unary-iteration lookup. -/

/-- The faithful multi-iteration QROM lookup as a rotation program. -/
def unaryLookupRot (n_addr : Nat) (iters : List (List Nat × List Nat)) : RotProg :=
  gateRotSchedule (unary_lookup_multi_iteration n_addr iters)

/-- **Rotation T-count = `14·n_addr·|iters|`** — the faithful (no
measurement, no Gray-code) QROM cost, for every table. -/
theorem unaryLookupRot_countPi8 (n_addr : Nat)
    (iters : List (List Nat × List Nat)) :
    countPi8 (unaryLookupRot n_addr iters) = 14 * n_addr * iters.length := by
  rw [unaryLookupRot, gateRotSchedule_countPi8,
      tcount_unary_lookup_multi_iteration]

/-! ## §2. The Gray-code (sawtooth) read. -/

open FormalRV.Shor.WindowedCircuit in
/-- The Gray-code QROM read as a rotation program. -/
def grayLookupRot (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) : RotProg :=
  gateRotSchedule (grayLookupReadAt w pos W T)

open FormalRV.Shor.WindowedCircuit in
/-- **Rotation T-count = `14·(2^w − 1)`** — the Gray-code saving, for every
window size, position map, and table. -/
theorem grayLookupRot_countPi8 (w : Nat) (pos : Nat → Nat) (W : Nat)
    (T : Nat → Nat) :
    countPi8 (grayLookupRot w pos W T) = 14 * (2 ^ w - 1) := by
  rw [grayLookupRot, gateRotSchedule_countPi8, tcount_grayLookupReadAt]

end FormalRV.PauliRotation
