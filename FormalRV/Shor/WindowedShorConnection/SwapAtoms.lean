/- WindowedShorConnection — Â§5d foundational atoms for swap involutivity.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.Residual

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §5d. Foundational atoms for `windowedSwapLoadAdapter_involutive`.

    `windowedSwapLoadAdapter` is a product of disjoint transpositions,
    so it is self-inverse — the involution `h_invol` that §5c needs.
    The two lemmas here are the verified building blocks of that proof
    (the remaining assembly — an update-frame induction, the
    swap/loader commutation, and the involution induction — follows
    the established `reverse_register_swap_involution_general`
    template and is the next dedicated step). -/

/-- A single `qubit_swap` is an involution (its own inverse). -/
theorem qubit_swap_involutive (a b : Nat) (f : Nat → Bool) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) (Gate.applyNat (qubit_swap a b) f) = f := by
  rw [qubit_swap_correct a b f hab, qubit_swap_correct a b _ hab]
  funext r
  by_cases hrb : r = b <;> by_cases hra : r = a <;>
    simp_all [FormalRV.Framework.update_eq, FormalRV.Framework.update_neq]

/-- A `qubit_swap` commutes with an `update` at a position disjoint
    from both swapped qubits.  This is the frame property that lets
    the loader's swaps slide past updates on data/window registers —
    the inductive engine of the loader involution. -/
theorem qubit_swap_update_comm (a b p : Nat) (v : Bool) (h : Nat → Bool)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) (FormalRV.Framework.update h p v)
      = FormalRV.Framework.update (Gate.applyNat (qubit_swap a b) h) p v := by
  rw [qubit_swap_correct a b _ hab, qubit_swap_correct a b h hab]
  have hap := hpa.symm; have hbp := hpb.symm
  funext x
  by_cases hxp : x = p <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [FormalRV.Framework.update_eq, FormalRV.Framework.update_neq]

/-- **Update-frame for the SWAP loader.** `windowedSwapLoadAdapter`
    commutes with an `update` at a position `p` disjoint from all of
    its source/window positions.  This is the inductive engine of the
    loader involution: it lets a disjoint update slide through the
    whole swap cascade.  Proven by induction on `numWin` using
    `qubit_swap_update_comm`. -/
theorem windowedSwapLoadAdapter_update_frame
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin p : Nat) (v : Bool) (g : Nat → Bool)
    (h_src0_ne_b0 : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_src1_ne_b1 : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k)
    (h_p_ne_src0 : ∀ k, k < numWin → p ≠ bits - 1 - 2 * k)
    (h_p_ne_src1 : ∀ k, k < numWin → p ≠ bits - 1 - (2 * k + 1))
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (FormalRV.Framework.update g p v)
      = FormalRV.Framework.update
          (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) g) p v := by
  revert h_src0_ne_b0 h_src1_ne_b1 h_p_ne_src0 h_p_ne_src1 h_p_ne_b0 h_p_ne_b1 g
  induction numWin with
  | zero => intro g _ _ _ _ _ _; rfl
  | succ n ih =>
    intro g h_src0_ne_b0 h_src1_ne_b1 h_p_ne_src0 h_p_ne_src1 h_p_ne_b0 h_p_ne_b1
    have hlt : n < n + 1 := Nat.lt_succ_self n
    simp only [windowedSwapLoadAdapter_succ, Gate.applyNat_seq]
    rw [ih g (fun k hk => h_src0_ne_b0 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_src1_ne_b1 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_src0 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_src1 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))]
    rw [qubit_swap_update_comm (bits - 1 - 2 * n) (b0Idx n) p v _
          (h_p_ne_src0 n hlt) (h_p_ne_b0 n hlt) (h_src0_ne_b0 n hlt)]
    rw [qubit_swap_update_comm (bits - 1 - (2 * n + 1)) (b1Idx n) p v _
          (h_p_ne_src1 n hlt) (h_p_ne_b1 n hlt) (h_src1_ne_b1 n hlt)]

/-- **Loader commutes with a disjoint swap.** `windowedSwapLoadAdapter`
    (over windows `0..numWin-1`) commutes with `qubit_swap a b` when
    `a, b` are disjoint from all of the loader's source/window
    positions.  Proven from the update-frame (both swapped values
    slide through the loader) plus `preserves_disjoint` (the loader
    leaves `a, b` fixed).  This is the step that lets each new
    window's swap block move past the recursive loader in the
    involution induction. -/
theorem windowedSwapLoadAdapter_comm_swap
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin a b : Nat) (g : Nat → Bool)
    (hab : a ≠ b)
    (h_src0_ne_b0 : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_src1_ne_b1 : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k)
    (ha_src0 : ∀ k, k < numWin → a ≠ bits - 1 - 2 * k)
    (ha_src1 : ∀ k, k < numWin → a ≠ bits - 1 - (2 * k + 1))
    (ha_b0 : ∀ k, k < numWin → a ≠ b0Idx k)
    (ha_b1 : ∀ k, k < numWin → a ≠ b1Idx k)
    (hb_src0 : ∀ k, k < numWin → b ≠ bits - 1 - 2 * k)
    (hb_src1 : ∀ k, k < numWin → b ≠ bits - 1 - (2 * k + 1))
    (hb_b0 : ∀ k, k < numWin → b ≠ b0Idx k)
    (hb_b1 : ∀ k, k < numWin → b ≠ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (Gate.applyNat (qubit_swap a b) g)
      = Gate.applyNat (qubit_swap a b)
          (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) g) := by
  rw [qubit_swap_correct a b g hab]
  rw [windowedSwapLoadAdapter_update_frame bits b0Idx b1Idx numWin b (g a) _
        h_src0_ne_b0 h_src1_ne_b1 hb_src0 hb_src1 hb_b0 hb_b1]
  rw [windowedSwapLoadAdapter_update_frame bits b0Idx b1Idx numWin a (g b) _
        h_src0_ne_b0 h_src1_ne_b1 ha_src0 ha_src1 ha_b0 ha_b1]
  rw [qubit_swap_correct a b
        (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) g) hab]
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx a numWin g
        h_src0_ne_b0 h_src1_ne_b1 ha_src0 ha_src1 ha_b0 ha_b1]
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx b numWin g
        h_src0_ne_b0 h_src1_ne_b1 hb_src0 hb_src1 hb_b0 hb_b1]

/-- Two `qubit_swap`s on four pairwise-distinct positions commute. -/
theorem qubit_swap_comm (a b c d : Nat) (g : Nat → Bool)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Gate.applyNat (qubit_swap a b) (Gate.applyNat (qubit_swap c d) g)
      = Gate.applyNat (qubit_swap c d) (Gate.applyNat (qubit_swap a b) g) := by
  rw [qubit_swap_correct c d g hcd, qubit_swap_correct a b g hab,
      qubit_swap_correct a b _ hab, qubit_swap_correct c d _ hcd]
  have hba := hab.symm; have hdc := hcd.symm; have hca := hac.symm
  have hda := had.symm; have hcb := hbc.symm; have hdb := hbd.symm
  funext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    by_cases hxd : x = d <;>
    simp_all [FormalRV.Framework.update_eq, FormalRV.Framework.update_neq]

/-- **The SWAP loader is an involution (self-inverse).** Applying
    `windowedSwapLoadAdapter` twice is the identity, because it is a
    product of pairwise-disjoint transpositions.  Proven by induction
    on `numWin`: the new window's swap block commutes past the
    recursive loader (`windowedSwapLoadAdapter_comm_swap`), the
    recursive call cancels by the induction hypothesis, and the two
    window swaps cancel via `qubit_swap_comm` + `qubit_swap_involutive`.

    This is the `h_invol` hypothesis required by
    `windowedUnload_of_involutive` (§5c), and hence — at the concrete
    layout — discharges the gap-1 `h_unload` obligation. -/
theorem windowedSwapLoadAdapter_involutive
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (h_2numWin : 2 * numWin ≤ bits)
    (h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j)
    (f : Nat → Bool) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
      (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) f) = f := by
  revert h_2numWin h_b0_above h_b1_above h_b0_ne_b1
    h_dist_b0b0 h_dist_b0b1 h_dist_b1b0 h_dist_b1b1 f
  induction numWin with
  | zero => intro _ _ _ _ _ _ _ _ f; rfl
  | succ n ih =>
    intro h_2numWin h_b0_above h_b1_above h_b0_ne_b1
      h_dist_b0b0 h_dist_b0b1 h_dist_b1b0 h_dist_b1b1 f
    have hlt : n < n + 1 := Nat.lt_succ_self n
    have ihn := ih (by omega)
      (fun k hk => h_b0_above k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b1_above k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b0_ne_b1 k (Nat.lt_succ_of_lt hk))
      (fun i j hi hj hij => h_dist_b0b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      (fun i j hi hj hij => h_dist_b0b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      (fun i j hi hj hij => h_dist_b1b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      (fun i j hi hj hij => h_dist_b1b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      f
    simp only [windowedSwapLoadAdapter_succ, Gate.applyNat_seq]
    rw [windowedSwapLoadAdapter_comm_swap bits b0Idx b1Idx n (bits - 1 - (2 * n + 1)) (b1Idx n) _
          (by have := h_b1_above n hlt; omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by omega)
          (fun k hk => by omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above n hlt; omega)
          (fun k hk => by have := h_b1_above n hlt; omega)
          (fun k hk => h_dist_b1b0 n k hlt (Nat.lt_succ_of_lt hk) (by omega))
          (fun k hk => h_dist_b1b1 n k hlt (Nat.lt_succ_of_lt hk) (by omega))]
    rw [windowedSwapLoadAdapter_comm_swap bits b0Idx b1Idx n (bits - 1 - 2 * n) (b0Idx n) _
          (by have := h_b0_above n hlt; omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by omega)
          (fun k hk => by omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b0_above n hlt; omega)
          (fun k hk => by have := h_b0_above n hlt; omega)
          (fun k hk => h_dist_b0b0 n k hlt (Nat.lt_succ_of_lt hk) (by omega))
          (fun k hk => h_dist_b0b1 n k hlt (Nat.lt_succ_of_lt hk) (by omega))]
    rw [ihn]
    rw [qubit_swap_comm (bits - 1 - 2 * n) (b0Idx n) (bits - 1 - (2 * n + 1)) (b1Idx n) _
          (by have := h_b0_above n hlt; omega)
          (by have := h_b1_above n hlt; omega)
          (by omega)
          (by have := h_b1_above n hlt; omega)
          (by have := h_b0_above n hlt; omega)
          (h_b0_ne_b1 n hlt)]
    rw [qubit_swap_involutive (bits - 1 - 2 * n) (b0Idx n) _ (by have := h_b0_above n hlt; omega)]
    rw [qubit_swap_involutive (bits - 1 - (2 * n + 1)) (b1Idx n) _
          (by have := h_b1_above n hlt; omega)]

/-- **gap-1 `h_unload` — CLOSED at the concrete layout.** Combining
    `windowedUnload_of_involutive` (§5c) with the now-proven loader
    involution, with every disjointness/bound hypothesis discharged by
    `omega` at the layout `wb0Idx k = 2·bits+3+2k`,
    `wb1Idx k = 2·bits+4+2k`, `wnumWin = bits/2`.  Requires `2 ∣ bits`. -/
theorem windowed_unload_concrete (bits anc y : Nat)
    (h_even : 2 ∣ bits) (h_anc_pos : 0 < anc) (hy : y < 2 ^ bits) :
    Gate.applyNat (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
        (windowed2Input 0 (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x y) (windowed2_b1_of_x y) (wnumWin bits))
      = encodeDataZeroAnc bits anc y := by
  have h_numWin : 2 * wnumWin bits = bits := by unfold wnumWin; exact Nat.mul_div_cancel' h_even
  exact windowedUnload_of_involutive bits anc (wnumWin bits) y (wb0Idx bits) (wb1Idx bits)
    hy h_anc_pos h_numWin
    (fun k _ => by unfold wb0Idx; omega)
    (fun k _ => by unfold wb1Idx; omega)
    (fun k _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ hij => by unfold wb0Idx; omega)
    (fun i j _ _ _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ _ => by unfold wb1Idx wb0Idx; omega)
    (fun i j _ _ hij => by unfold wb1Idx; omega)
    (fun g => windowedSwapLoadAdapter_involutive bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits)
      (by unfold wnumWin; omega)
      (fun k _ => by unfold wb0Idx; omega)
      (fun k _ => by unfold wb1Idx; omega)
      (fun k _ => by unfold wb0Idx wb1Idx; omega)
      (fun i j _ _ hij => by unfold wb0Idx; omega)
      (fun i j _ _ _ => by unfold wb0Idx wb1Idx; omega)
      (fun i j _ _ _ => by unfold wb1Idx wb0Idx; omega)
      (fun i j _ _ hij => by unfold wb1Idx; omega)
      g)


end FormalRV.BQAlgo.WindowedShorConnection
