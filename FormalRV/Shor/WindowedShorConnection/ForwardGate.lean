/- WindowedShorConnection — Â§4 concrete windowed layout + proven forward gate.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.Obligation

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §4. Concrete windowed layout + the PROVEN forward gate.

    We pin the windowed circuit to a concrete ancilla layout so the
    proven apex
    `VerifiedShor.Windowed.windowedSwapLoadAdapter_then_selectedAdd_apply_clean`
    instantiates with all ~20 layout/distinctness hypotheses
    discharged.  This turns the windowed forward half into a
    standalone *proven* lemma `windowedForwardGate_apply`, narrowing
    the residual from "wire windowed arithmetic into Shor" to a
    single in-place completion gate. -/

/-- Number of windowSize-2 windows for a `bits`-wide register. -/
def wnumWin (bits : Nat) : Nat := bits / 2

/-- `b0` (even) window-register index for window `k`: placed just
    above the Cuccaro workspace `[0, 2*bits+3)`. -/
def wb0Idx (bits : Nat) : Nat → Nat := fun k => 2 * bits + 3 + 2 * k

/-- `b1` (odd) window-register index for window `k`. -/
def wb1Idx (bits : Nat) : Nat → Nat := fun k => 2 * bits + 4 + 2 * k

/-- The PROVEN windowed forward gate for multiplier constant `c`:
    SWAP-load `x` into the window registers, then run the
    multi-window selected-add.  Output is in `windowed2Input`
    layout. -/
noncomputable def windowedForwardGate (c N bits : Nat) : Gate :=
  Gate.seq
    (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
    (windowed2SelectedAddGate
      (toyWindow2SelectedAddStateSpecImpl c N).toSelectedAddSpec
      bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits))

/-- **Forward half — PROVEN.** At the concrete layout above, the
    windowed forward gate maps `encodeDataZeroAnc bits anc x` to the
    `windowed2Input` state with accumulator `(c*x) % N` and the
    window registers still holding `x`'s bits.  This is the apex
    `windowedSwapLoadAdapter_then_selectedAdd_apply_clean` with every
    layout/distinctness hypothesis discharged by `omega` (flag at 0,
    `b0Idx k = 2·bits+3+2k`, `b1Idx k = 2·bits+4+2k`,
    `numWin = bits/2`).

    Requires `bits` even (`2 ∣ bits`) for exact window coverage
    `2·numWin = bits`. -/
theorem windowedForwardGate_apply
    (c N bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_anc_pos : 0 < anc) (hx : x < N) :
    Gate.applyNat (windowedForwardGate c N bits) (encodeDataZeroAnc bits anc x)
      = windowed2Input ((c * x) % N) (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) (wnumWin bits) := by
  have hx_pow : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_numWin : 2 * wnumWin bits = bits := by
    unfold wnumWin; exact Nat.mul_div_cancel' h_even
  unfold windowedForwardGate
  rw [windowedSwapLoadAdapter_then_selectedAdd_apply_clean
        bits anc (wnumWin bits) x N c 0 (wb0Idx bits) (wb1Idx bits)
        hx_pow h_anc_pos h_numWin hbits hN_pos hN hN2
        (by decide) (by decide)
        (by unfold sqir_modmult_rev_anc; omega)
        (by intro k _; unfold wb0Idx; omega)
        (by intro k _; unfold wb1Idx; omega)
        (by intro k _; unfold wb0Idx wb1Idx; omega)
        (by intro k _; unfold wb0Idx; omega)
        (by intro k _; unfold wb1Idx; omega)
        (by intro i j _ _ hij; unfold wb0Idx; omega)
        (by intro i j _ _ _; unfold wb0Idx wb1Idx; omega)
        (by intro i j _ _ _; unfold wb1Idx wb0Idx; omega)
        (by intro i j _ _ hij; unfold wb1Idx; omega)]
  rw [Nat.mod_eq_of_lt hx_pow]


end FormalRV.BQAlgo.WindowedShorConnection
