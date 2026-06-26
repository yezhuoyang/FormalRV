/- WindowedShorConnection — Â§1-3 multiplier interface obligation + reduction + headline connection.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.VerifiedShor
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.RelaxedSetting
import FormalRV.Arithmetic.ModExp

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §1. The residual obligation: an `encodeDataZeroAnc`-layout
       modular multiplier family.

    This is the SINGLE interface the windowed (or any) circuit must
    meet to plug into the headline Shor theorem.  `gate c` is the
    compiled multiply-by-`c`-mod-`N` circuit in the canonical
    data+ancilla layout; `roundTrip` is its Boolean
    `Gate.applyNat` correctness in that layout, for every constant `c`
    that is invertible mod `N` (witnessed by some `d` with
    `(c*d) % N = 1`).  The invertibility guard is NOT a weakening of
    the intended contract but a soundness necessity: well-typed gates
    act injectively on basis states (X/CX/CCX on distinct wires are
    permutations), while `x ↦ (c*x) % N` is non-injective on `[0,N)`
    for non-invertible `c` (e.g. `c = 0` collapses `0` and `1`), so an
    unguarded round-trip would make the structure uninhabitable for
    every composite `N ≥ 2`.  Shor only ever instantiates `c := a^(2^i)`
    with `a` invertible mod `N`, so the guard is free at the use site
    (see `toVerifiedModMulFamily`). -/
structure EncodeRoundTripModMul (N bits anc : Nat) where
  /-- The multiply-by-`c` gate, indexed by the multiplier constant. -/
  gate : Nat → Gate
  /-- Each gate is well-typed at the total dimension `bits + anc`. -/
  wellTyped : ∀ c, Gate.WellTyped (bits + anc) (gate c)
  /-- Boolean correctness in the `encodeDataZeroAnc` layout:
      `|x⟩|0⟩ ↦ |(c*x) % N⟩|0⟩` for every `x < N` and every constant
      `c` invertible mod `N`. -/
  roundTrip : ∀ c x, x < N → (∃ d, (c * d) % N = 1) →
    Gate.applyNat (gate c) (encodeDataZeroAnc bits anc x)
      = encodeDataZeroAnc bits anc ((c * x) % N)

/-! ## §2. Reduction: obligation ⟹ `VerifiedModMulFamily`.

    For QPE iterate `i` the family must multiply by `a^(2^i)`; we
    instantiate `gate` at the raw constant `a^(2^i)` so the
    round-trip target `((a^(2^i)) * x) % N` matches
    `MultiplyCircuitProperty (a^(2^i)) …` on the nose.  The
    invertibility guard at iterate `i` is discharged by the witness
    `ainv0^(2^i)` from the base inverse `a · ainv0 ≡ 1 (mod N)` via
    `mul_pow_mod_one` — the same per-power-inverse pattern as
    `windowedModMulFamily` (§9). -/
noncomputable def EncodeRoundTripModMul.toVerifiedModMulFamily
    {N bits anc : Nat} (W : EncodeRoundTripModMul N bits anc)
    (a : Nat) (hN : N ≤ 2 ^ bits)
    (ainv0 : Nat) (hN1 : 1 < N) (h_inv0 : a * ainv0 % N = 1) :
    VerifiedModMulFamily a N bits anc where
  family := fun i => Gate.toUCom (bits + anc) (W.gate (a ^ (2 ^ i)))
  mmi := by
    intro i
    exact toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
      (W.wellTyped (a ^ (2 ^ i))) hN
      (fun x hx => W.roundTrip (a ^ (2 ^ i)) x hx
        ⟨ainv0 ^ (2 ^ i), by
          rw [Nat.mul_mod]
          exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩)
  wellTyped := by
    intro i
    exact uc_well_typed_toUCom_of_Gate_WellTyped (bits + anc)
      (W.gate (a ^ (2 ^ i))) (W.wellTyped (a ^ (2 ^ i)))

/-! ## §3. The headline connection. -/

/-- **Connection theorem.** Any `encodeDataZeroAnc`-round-trip
    modular multiplier family yields the canonical Shor
    success-probability bound `≥ κ / (log₂ N)^4`.

    This is the wiring the windowed pipeline needs: it shows that
    *everything above the round-trip is already done*, so the
    windowed multiplier's only remaining job is to inhabit
    `EncodeRoundTripModMul`. -/
theorem shor_correct_of_encodeRoundTrip
    {N bits anc : Nat} (W : EncodeRoundTripModMul N bits anc)
    (a r m : Nat) (hN : N ≤ 2 ^ bits)
    (ainv0 : Nat) (hN1 : 1 < N) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc
        (W.toVerifiedModMulFamily a hN ainv0 hN1 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (W.toVerifiedModMulFamily a hN ainv0 hN1 h_inv0).shorCorrect r m h_setting


end FormalRV.BQAlgo.WindowedShorConnection
