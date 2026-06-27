/- WindowedShorConnection — Â§9 windowed multiplier family + HEADLINE Shor bound.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.Multiplier

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §9. The windowed multiplier family and the HEADLINE Shor bound — UNCONDITIONAL.

    All gate-level facts now proven, we package the windowed multiplier as a
    `VerifiedModMulFamily` and derive the headline success-probability bound
    `≥ κ / (log₂ N)^4` with **no remaining obligations**: the in-place
    round-trip (§5b–§7) and full well-typedness (§8/§8b) are both proven, and
    the modular-inverse side is discharged — at QPE iterate `i` the inverse is
    `ainv0^(2^i) % N` with `(a^(2^i) · (ainv0^(2^i)%N)) % N = 1` via
    `mul_pow_mod_one`; `ainv0` is `Order`'s modular inverse
    (`Order_modinv_correct`).  Requires `anc ≥ 2·bits+11` so the SQIR-Cuccaro
    workspace (`3·bits+11`) fits the dimension. -/

/-- Well-typedness of the full windowed in-place gate at `bits + anc`.
    The two SWAP cascades are discharged by §8 and the window selected-add by
    §8b (`windowedSelectedAdd_wellTyped_concrete`); `anc ≥ 2·bits+11` keeps
    every position (window registers `≤ 3·bits+2`, mod-add workspace
    `3·bits+11`) inside the dimension. -/
theorem windowedInplaceModMulGate_wellTyped
    (c N ainv bits anc : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc) :
    Gate.WellTyped (bits + anc) (windowedInplaceModMulGate c N ainv bits) := by
  have h_sel : ∀ c', Gate.WellTyped (bits + anc)
      (windowed2SelectedAddGate (toyWindow2SelectedAddStateSpecImpl c' N).toSelectedAddSpec
        bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
    fun c' => windowedSelectedAdd_wellTyped_concrete bits N anc hbits h_even hN_pos hN hN2 h_anc c'
  have h_load : Gate.WellTyped (bits + anc)
      (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
    windowedSwapLoadAdapter_wellTyped bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits) (bits + anc)
      (by omega)
      (fun k _ => by omega)
      (fun k _ => by omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb1Idx; omega)
      (fun k _ => by unfold wb0Idx; omega)
      (fun k _ => by unfold wb1Idx; omega)
  have h_swap : Gate.WellTyped (bits + anc)
      (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
    swapTargetWindows_wellTyped (bits + anc) (wb0Idx bits) (wb1Idx bits) (wnumWin bits)
      (by omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb1Idx; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
      (fun k _ => by unfold wb1Idx; omega)
  unfold windowedInplaceModMulGate windowedForwardGate
  exact ⟨⟨h_load, h_sel c⟩, h_swap, h_sel ((N - ainv) % N), h_load⟩

/-- **The windowed modular-multiplier QPE family.**  At iterate `i` it
    multiplies by `a^(2^i) mod N` using the in-place windowed gate with
    per-power inverse `ainv0^(2^i) % N`.  Both family contracts (`mmi`
    matrix semantics, `wellTyped`) are discharged via the universal
    bridges, the proven round-trip, and `mul_pow_mod_one`. -/
noncomputable def windowedModMulFamily
    (a N bits anc ainv0 : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc)
    (h_inv0 : a * ainv0 % N = 1) :
    VerifiedModMulFamily a N bits anc where
  family := fun i => Gate.toUCom (bits + anc)
      (windowedInplaceModMulGate (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits)
  mmi := by
    intro i
    have h_wt := windowedInplaceModMulGate_wellTyped (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits anc
      hbits h_even hN_pos hN hN2 h_anc
    refine toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc h_wt hN ?_
    intro x hx
    have h_ainv_le : ainv0 ^ (2 ^ i) % N ≤ N := (Nat.mod_lt _ hN_pos).le
    have h_inv_i : (a ^ (2 ^ i) * (ainv0 ^ (2 ^ i) % N)) % N = 1 := by
      rw [Nat.mul_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hN_pos)]
      exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0
    exact windowedInplaceModMulGate_roundTrip (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits anc x
      hbits h_even hN_pos hN hN2 (by omega) hx h_ainv_le h_inv_i
  wellTyped := by
    intro i
    exact uc_well_typed_toUCom_of_Gate_WellTyped (bits + anc) _
      (windowedInplaceModMulGate_wellTyped (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits anc
        hbits h_even hN_pos hN hN2 h_anc)

/-- **HEADLINE — windowed multiplier ⟹ Shor success bound (UNCONDITIONAL).**
    The windowed (Pipeline C) modular multiplier achieves the canonical Shor
    success-probability bound `≥ κ / (log₂ N)^4`, with no remaining circuit
    obligations.  Every ingredient — the `h_tw` target↔windows SWAP, the
    in-place round-trip, the full gate well-typedness (SWAP cascades + window
    selected-add), and the modular-inverse arithmetic — is proven and
    kernel-clean.  The only hypotheses are the standard Shor sizing/setting
    facts plus the base modular inverse `a · ainv0 % N = 1` (obtainable from
    `Order_modinv_correct`) and `anc ≥ 2·bits+11`. -/
theorem windowed_shor_correct
    (a r N m bits anc ainv0 : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc
        (windowedModMulFamily a N bits anc ainv0 hbits h_even hN_pos hN1 hN hN2 h_anc
          h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (windowedModMulFamily a N bits anc ainv0 hbits h_even hN_pos hN1 hN hN2 h_anc
    h_inv0).shorCorrect r m h_setting


end FormalRV.BQAlgo.WindowedShorConnection
