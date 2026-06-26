/- WindowedShorConnection — Â§7-8b windowed in-place mod-mul (unconditional) + well-typedness.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.Parity

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §7. The windowed in-place modular multiplier — UNCONDITIONAL.

    With `h_tw` (`swapTargetWindows_h_tw`) and `h_unload`
    (`windowed_unload_concrete`) both now proven, the 5-stage in-place
    composition `windowedInplaceModMul_roundTrip` becomes an
    UNCONDITIONAL Boolean round-trip of the canonical `encodeDataZeroAnc`
    layout: `|x⟩|0⟩ ↦ |(c·x) % N⟩|0⟩`.  This is the windowed (Pipeline C)
    analogue of `modmult_inplace_candidate`, and the exact
    `EncodeRoundTripModMul.roundTrip` obligation for the windowed
    multiplier (for any constant `c` equipped with a modular inverse
    `ainv`). -/

/-- The windowed in-place multiply-by-`c`-mod-`N` gate at the concrete
    layout: forward (load+selected-add) ; SWAP target↔windows ; clear `x`
    via selected-add by `(N-ainv)%N` ; unload.  `ainv` is `c`'s modular
    inverse. -/
noncomputable def windowedInplaceModMulGate (c N ainv bits : Nat) : Gate :=
  Gate.seq (windowedForwardGate c N bits)
    (Gate.seq (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
      (Gate.seq
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl ((N - ainv) % N) N).toSelectedAddSpec
          bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
        (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))))

/-- **The windowed in-place modular multiplier is correct — UNCONDITIONAL.**
    Discharges the two swap obligations of `windowedInplaceModMul_roundTrip`
    with the now-proven `swapTargetWindows_h_tw` and
    `windowed_unload_concrete`. -/
theorem windowedInplaceModMulGate_roundTrip
    (c N ainv bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (hx : x < N) (h_ainv_le : ainv ≤ N) (h_inv : (c * ainv) % N = 1) :
    Gate.applyNat (windowedInplaceModMulGate c N ainv bits) (encodeDataZeroAnc bits anc x)
      = encodeDataZeroAnc bits anc ((c * x) % N) := by
  unfold windowedInplaceModMulGate
  exact windowedInplaceModMul_roundTrip
    (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
    c N ainv bits anc x hbits h_even hN_pos hN hN2 h_anc_pos hx h_ainv_le h_inv
    (fun acc w hacc hw => swapTargetWindows_h_tw bits acc w h_even hacc hw)
    (fun y hy => windowed_unload_concrete bits anc y h_even h_anc_pos hy)

/-! ## §8. Structural well-typedness of the windowed gates.

    The headline `VerifiedModMulFamily` needs each iterate well-typed at
    the total dimension `bits + anc`.  The two SWAP cascades
    (`windowedSwapLoadAdapter`, `swapTargetWindows`) are products of
    `qubit_swap`s, so their well-typedness follows by induction from
    `qubit_swap_wellTyped`.  These reduce the well-typedness of the full
    in-place gate to the single remaining structural obligation
    `windowed2SelectedAddGate_wellTyped`. -/

/-- The target↔windows SWAP cascade is well-typed when every source
    `4k+3`/`4k+5` and window `b0Idx k`/`b1Idx k` is below `dim` and each
    swap pair is distinct. -/
theorem swapTargetWindows_wellTyped
    (dim : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (h_dim_pos : 0 < dim)
    (h_t0 : ∀ k, k < numWin → 4 * k + 3 < dim)
    (h_t1 : ∀ k, k < numWin → 4 * k + 5 < dim)
    (h_b0 : ∀ k, k < numWin → b0Idx k < dim)
    (h_b1 : ∀ k, k < numWin → b1Idx k < dim)
    (h_t0_ne_b0 : ∀ k, k < numWin → 4 * k + 3 ≠ b0Idx k)
    (h_t1_ne_b1 : ∀ k, k < numWin → 4 * k + 5 ≠ b1Idx k) :
    Gate.WellTyped dim (swapTargetWindows b0Idx b1Idx numWin) := by
  induction numWin with
  | zero => exact h_dim_pos
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ]
    exact ⟨ih (fun k hk => h_t0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_t1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_t0_ne_b0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_t1_ne_b1 k (Nat.lt_succ_of_lt hk)),
           qubit_swap_wellTyped dim _ _ (h_t0 n hlt) (h_b0 n hlt) (h_t0_ne_b0 n hlt),
           qubit_swap_wellTyped dim _ _ (h_t1 n hlt) (h_b1 n hlt) (h_t1_ne_b1 n hlt)⟩

/-- The SWAP loader cascade is well-typed when every data source
    `bits-1-2k`/`bits-1-(2k+1)` and window `b0Idx k`/`b1Idx k` is below
    `dim` and each swap pair is distinct. -/
theorem windowedSwapLoadAdapter_wellTyped
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin dim : Nat)
    (h_dim_pos : 0 < dim)
    (h_src0 : ∀ k, k < numWin → bits - 1 - 2 * k < dim)
    (h_src1 : ∀ k, k < numWin → bits - 1 - (2 * k + 1) < dim)
    (h_b0 : ∀ k, k < numWin → b0Idx k < dim)
    (h_b1 : ∀ k, k < numWin → b1Idx k < dim)
    (h_src0_ne : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_src1_ne : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k) :
    Gate.WellTyped dim (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) := by
  induction numWin with
  | zero => exact h_dim_pos
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [windowedSwapLoadAdapter_succ]
    exact ⟨ih (fun k hk => h_src0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_src1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_src0_ne k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_src1_ne k (Nat.lt_succ_of_lt hk)),
           qubit_swap_wellTyped dim _ _ (h_src0 n hlt) (h_b0 n hlt) (h_src0_ne n hlt),
           qubit_swap_wellTyped dim _ _ (h_src1 n hlt) (h_b1 n hlt) (h_src1_ne n hlt)⟩

/-! ## §8b. Well-typedness of the window selected-add (discharges `h_sel_wt`).

    The window selected-add cascade is well-typed at `bits + anc` for
    `anc ≥ 2·bits+11`.  Each window step `toyWindow2SelectedAddGate` is
    `Case1 ; Case2 ; Case3`, each a `[X] ; CCX ; controlled-mod-add ; CCX ; [X]`.
    The CCX/X positions (`flagIdx=0`, `wb0Idx`, `wb1Idx`) are bounded by
    `omega`; the controlled-mod-add `sqirCuccaroImpl.gate` is well-typed at
    `sqir_modmult_rev_anc bits = 3·bits+11` by `clean_wellTyped` (control
    `0 < 2`, `0 ≠ flagPos=1`, `tableValue < N`) and lifted to `bits+anc`
    by `Gate.WellTyped.mono`. -/

/-- One window's selected-add gate is well-typed: `Case1 ; Case2 ; Case3`,
    each a CCX-sandwiched controlled-mod-add. -/
theorem toyWindow2SelectedAddGate_wellTyped
    (dim bits N a k flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ctrl_lo : flagIdx < 2) (h_ctrl_ne1 : flagIdx ≠ 1)
    (h_anc_le : sqir_modmult_rev_anc bits ≤ dim)
    (h_flag_lt : flagIdx < dim) (h_b0_lt : b0Idx < dim) (h_b1_lt : b1Idx < dim)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx) (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.WellTyped dim (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx) := by
  have h_ctrl_lt_anc : flagIdx < sqir_modmult_rev_anc bits := by
    unfold sqir_modmult_rev_anc; omega
  have hccx : Gate.WellTyped dim (Gate.CCX b0Idx b1Idx flagIdx) :=
    ⟨h_b0_lt, h_b1_lt, h_flag_lt, h_b0_ne_b1, h_b0_ne_flag, h_b1_ne_flag⟩
  have h_modadd : ∀ v, Gate.WellTyped dim
      (ControlledModAdd.sqirCuccaroImpl.gate bits N (tableValue a N 2 k v) flagIdx) := fun v =>
    Gate.WellTyped.mono
      (ControlledModAdd.clean_wellTyped ControlledModAdd.sqirCuccaroImpl bits N
        (tableValue a N 2 k v) 0 flagIdx false hbits hN_pos hN hN2
        (tableValue_lt_N a N 2 k v hN_pos) hN_pos (Or.inl h_ctrl_lo) h_ctrl_ne1 h_ctrl_lt_anc)
      h_anc_le
  unfold toyWindow2SelectedAddGate toyWindow2Case1Gate toyWindow2Case2Gate toyWindow2Case3Gate
  exact ⟨⟨h_b1_lt, hccx, h_modadd 1, hccx, h_b1_lt⟩,
         ⟨h_b0_lt, hccx, h_modadd 2, hccx, h_b0_lt⟩,
         hccx, h_modadd 3, hccx⟩

/-- The multi-window selected-add cascade is well-typed (induction over
    `numWin`, each step by `toyWindow2SelectedAddGate_wellTyped`). -/
theorem windowed2SelectedAddGate_wellTyped
    (dim bits N a flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ctrl_lo : flagIdx < 2) (h_ctrl_ne1 : flagIdx ≠ 1)
    (h_anc_le : sqir_modmult_rev_anc bits ≤ dim) (h_flag_lt : flagIdx < dim)
    (h_b0_lt : ∀ k, k < numWin → b0Idx k < dim)
    (h_b1_lt : ∀ k, k < numWin → b1Idx k < dim)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_b0_ne_flag : ∀ k, k < numWin → b0Idx k ≠ flagIdx)
    (h_b1_ne_flag : ∀ k, k < numWin → b1Idx k ≠ flagIdx) :
    Gate.WellTyped dim
      (windowed2SelectedAddGate (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
        bits flagIdx b0Idx b1Idx numWin) := by
  induction numWin with
  | zero =>
    rw [windowed2SelectedAddGate_zero]
    show 0 < dim
    exact lt_of_lt_of_le (show 0 < sqir_modmult_rev_anc bits by unfold sqir_modmult_rev_anc; omega) h_anc_le
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [windowed2SelectedAddGate_succ]
    exact ⟨ih (fun k hk => h_b0_lt k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1_lt k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0_ne_b1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0_ne_flag k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1_ne_flag k (Nat.lt_succ_of_lt hk)),
           toyWindow2SelectedAddGate_wellTyped dim bits N a n flagIdx (b0Idx n) (b1Idx n)
             hbits hN_pos hN hN2 h_ctrl_lo h_ctrl_ne1 h_anc_le h_flag_lt
             (h_b0_lt n hlt) (h_b1_lt n hlt) (h_b0_ne_b1 n hlt)
             (h_b0_ne_flag n hlt) (h_b1_ne_flag n hlt)⟩

/-- **`h_sel_wt` — CLOSED at the concrete layout.**  The window
    selected-add gate is well-typed at `bits + anc` for `anc ≥ 2·bits+11`,
    discharging the obligation the headline previously carried. -/
theorem windowedSelectedAdd_wellTyped_concrete
    (bits N anc : Nat) (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc) (c' : Nat) :
    Gate.WellTyped (bits + anc)
      (windowed2SelectedAddGate (toyWindow2SelectedAddStateSpecImpl c' N).toSelectedAddSpec
        bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
  windowed2SelectedAddGate_wellTyped (bits + anc) bits N c' 0 (wb0Idx bits) (wb1Idx bits)
    (wnumWin bits) hbits hN_pos hN hN2 (by omega) (by omega)
    (by show sqir_modmult_rev_anc bits ≤ bits + anc; unfold sqir_modmult_rev_anc; omega)
    (by omega)
    (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
    (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb1Idx; omega)
    (fun k _ => by unfold wb0Idx wb1Idx; omega)
    (fun k _ => by unfold wb0Idx; omega)
    (fun k _ => by unfold wb1Idx; omega)


end FormalRV.BQAlgo.WindowedShorConnection
