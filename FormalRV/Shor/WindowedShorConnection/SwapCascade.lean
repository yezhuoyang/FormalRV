/- WindowedShorConnection — Â§5e the target<->windows SWAP cascade (h_tw).
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.SwapAtoms

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §5e. Gap-1 `h_tw` — the target↔windows SWAP cascade.

    `swapTargetWindows` swaps each accumulator b-position with the
    matching window register: acc-bit `2k` (Cuccaro b-position `4k+3`)
    ↔ window-b0 `k`, and acc-bit `2k+1` (b-position `4k+5`) ↔
    window-b1 `k`, for `k < numWin`.  All `2·numWin` transpositions are
    pairwise disjoint (b-positions `< 4·numWin+2 ≤` window positions),
    so the cascade is a clean product of disjoint swaps — the windowed
    analogue of Gidney's `fig:multiply` final SWAP.  Proven by the same
    funext + read-lemma pattern as
    `windowedSwapLoadAdapter_apply_encodeDataZeroAnc`. -/

/-- The target↔windows SWAP cascade over windows `0..numWin-1`.  Each
    step swaps the two Cuccaro b-positions `4n+3 = 2·(2n)+3` and
    `4n+5 = 2·(2n+1)+3` (holding accumulator bits `2n`, `2n+1`) with the
    window registers `b0Idx n`, `b1Idx n`. -/
noncomputable def swapTargetWindows
    (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (swapTargetWindows b0Idx b1Idx n)
        (Gate.seq
          (qubit_swap (4 * n + 3) (b0Idx n))
          (qubit_swap (4 * n + 5) (b1Idx n)))

@[simp] theorem swapTargetWindows_succ
    (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    swapTargetWindows b0Idx b1Idx (n + 1)
      = Gate.seq
          (swapTargetWindows b0Idx b1Idx n)
          (Gate.seq
            (qubit_swap (4 * n + 3) (b0Idx n))
            (qubit_swap (4 * n + 5) (b1Idx n))) := rfl

/-- **Frame property for the SWAP cascade.**  A position `p` disjoint
    from every source (`4k+3`, `4k+5`) and every window (`b0Idx k`,
    `b1Idx k`) passes through the cascade unchanged.  The window-above
    bounds make each swap well-formed.  Mirrors
    `windowedSwapLoadAdapter_preserves_disjoint`. -/
theorem swapTargetWindows_preserves_disjoint
    (b0Idx b1Idx : Nat → Nat) (numWin p : Nat) (f : Nat → Bool)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_p_ne_t0 : ∀ k, k < numWin → p ≠ 4 * k + 3)
    (h_p_ne_t1 : ∀ k, k < numWin → p ≠ 4 * k + 5)
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f p = f p := by
  induction numWin generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have hlt : n < n + 1 := Nat.lt_succ_self n
    have h_t1_ne_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_t0_ne_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_t1_ne_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_b1 n hlt)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_t1 n hlt)]
    rw [qubit_swap_correct _ _ _ h_t0_ne_b0n]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_b0 n hlt)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_t0 n hlt)]
    exact ih f
      (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
      (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
      (fun k hk => h_p_ne_t0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_t1 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-- At a position `q` disjoint from all window registers, `windowed2Input`
    agrees with its Cuccaro base `cuccaro_input_F 2 false 0 acc`.  (The
    window updates all slide off via `update_neq`.) -/
theorem windowed2Input_at_window_disjoint
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (numWin q : Nat)
    (h_b0_disj : ∀ k, k < numWin → q ≠ b0Idx k)
    (h_b1_disj : ∀ k, k < numWin → q ≠ b1Idx k) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin q = cuccaro_input_F 2 false 0 acc q := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_disj n (Nat.lt_succ_self n))]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_disj n (Nat.lt_succ_self n))]
    exact ih (fun k hk => h_b0_disj k (Nat.lt_succ_of_lt hk))
             (fun k hk => h_b1_disj k (Nat.lt_succ_of_lt hk))

/-- The Cuccaro base `cuccaro_input_F 2 false 0 v` is `false` at any `q`
    that is not a low b-position `2t+3` (`t < bits`): the only non-false
    branch is the b-register, and an `acc < 2^bits` has no set bit at
    index `≥ bits`. -/
theorem cuccaro_base_false (bits v q : Nat) (hv : v < 2 ^ bits)
    (h_not_b : ∀ t, t < bits → q ≠ 2 * t + 3) :
    cuccaro_input_F 2 false 0 v q = false := by
  simp only [cuccaro_input_F]
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · -- odd offset: b-register, index `(q-2-1)/2`
    have ht : q = 2 * ((q - 2 - 1) / 2) + 3 := by omega
    have hge : bits ≤ (q - 2 - 1) / 2 := by
      by_contra hlt
      push_neg at hlt
      exact h_not_b _ hlt ht
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hge))
  · -- even offset: a-register is `0`
    exact Nat.zero_testBit _

/-- **Read at source `4k+3`.**  The cascade carries the value at the
    window register `b0Idx k` to the accumulator b-position `4k+3`. -/
theorem swapTargetWindows_read_t0
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (4 * k + 3) = f (b0Idx k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ b1Idx n by have := h_b1_above n hlt; omega)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ 4 * n + 5 by omega)]
    rw [qubit_swap_correct _ _ _ h_b0n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 3 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_eq]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (b0Idx n) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b0_above n hlt; omega)
        (fun j hj => by have := h_b0_above n hlt; omega)
        (fun j hj => h_dist_b0b0 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
        (fun j hj => h_dist_b0b1 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ 4 * n + 3 by omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun i j hi hj hij => h_dist_b0b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b0b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Read at source `4k+5`.**  The cascade carries the value at the
    window register `b1Idx k` to the accumulator b-position `4k+5`. -/
theorem swapTargetWindows_read_t1
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (4 * k + 5) = f (b1Idx k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 5 ≠ b1Idx n by have := h_b1_above n hlt; omega)]
      rw [FormalRV.Framework.update_eq]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ ((h_b0_ne_b1 n hlt).symm)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b1Idx n ≠ 4 * n + 3 by have := h_b1_above n hlt; omega)]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (b1Idx n) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above n hlt; omega)
        (fun j hj => by have := h_b1_above n hlt; omega)
        (fun j hj => h_dist_b1b0 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
        (fun j hj => h_dist_b1b1 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ b1Idx n by have := h_b1_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ 4 * n + 5 by omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ 4 * n + 3 by omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij => h_dist_b1b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b1b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Read at window `b0Idx k`.**  The cascade carries the accumulator
    b-position `4k+3` to the window register `b0Idx k`. -/
theorem swapTargetWindows_read_b0
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (b0Idx k) = f (4 * k + 3) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_ne_b1 n hlt)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b0Idx n ≠ 4 * n + 5 by have := h_b0_above n hlt; omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_eq]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (4 * n + 3) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by omega)
        (fun j hj => by omega)
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b0b1 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b0Idx k ≠ 4 * n + 5 by have := h_b0_above k (Nat.lt_succ_of_lt hkn'); omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b0b0 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b0Idx k ≠ 4 * n + 3 by have := h_b0_above k (Nat.lt_succ_of_lt hkn'); omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij => h_dist_b0b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b0b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Read at window `b1Idx k`.**  The cascade carries the accumulator
    b-position `4k+5` to the window register `b1Idx k`. -/
theorem swapTargetWindows_read_b1
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (b1Idx k) = f (4 * k + 5) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_eq]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 5 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 5 ≠ 4 * n + 3 by omega)]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (4 * n + 5) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by omega)
        (fun j hj => by omega)
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b1b1 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b1Idx k ≠ 4 * n + 5 by have := h_b1_above k (Nat.lt_succ_of_lt hkn'); omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b1b0 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b1Idx k ≠ 4 * n + 3 by have := h_b1_above k (Nat.lt_succ_of_lt hkn'); omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun i j hi hj hij => h_dist_b1b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b1b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **The target↔windows SWAP — PROVEN.**  Applying `swapTargetWindows`
    to a `windowed2Input` whose accumulator is `acc` and whose windows
    carry `w`'s bits yields the `windowed2Input` whose accumulator is `w`
    and whose windows carry `acc`'s bits.  This is the open `h_tw`
    hypothesis of `windowedInplaceModMul_roundTrip`, discharged at the
    abstract layout (window indices above all `4·numWin+1` sources,
    pairwise distinct).  Proven by funext + the read/frame lemmas. -/
theorem swapTargetWindows_apply
    (bits acc w : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (h_numWin : 2 * numWin = bits)
    (hacc : acc < 2 ^ bits) (hw : w < 2 ^ bits)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin)
        (windowed2Input acc b0Idx b1Idx (windowed2_b0_of_x w) (windowed2_b1_of_x w) numWin)
      = windowed2Input w b0Idx b1Idx (windowed2_b0_of_x acc) (windowed2_b1_of_x acc) numWin := by
  have hbpos0 : ∀ (v i : Nat), cuccaro_input_F 2 false 0 v (4 * i + 3) = v.testBit (2 * i) := by
    intro v i
    rw [show 4 * i + 3 = 2 + 2 * (2 * i) + 1 by ring]
    exact cuccaro_input_F_at_b 2 (2 * i) false 0 v
  have hbpos1 : ∀ (v i : Nat), cuccaro_input_F 2 false 0 v (4 * i + 5) = v.testBit (2 * i + 1) := by
    intro v i
    rw [show 4 * i + 5 = 2 + 2 * (2 * i + 1) + 1 by ring]
    exact cuccaro_input_F_at_b 2 (2 * i + 1) false 0 v
  have h_not_b : ∀ q, (∀ k, k < numWin → q ≠ 4 * k + 3) → (∀ k, k < numWin → q ≠ 4 * k + 5) →
      ∀ j, j < bits → q ≠ 2 * j + 3 := by
    intro q ht0 ht1 j hj
    rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · have htw : t < numWin := by omega
      have := ht0 t htw; omega
    · have htw : t < numWin := by omega
      have := ht1 t htw; omega
  funext q
  by_cases hb0 : ∃ k, k < numWin ∧ q = b0Idx k
  · obtain ⟨k, hk, rfl⟩ := hb0
    rw [swapTargetWindows_read_b0 b0Idx b1Idx numWin k _ hk
          h_b0_above h_b1_above h_b0_ne_b1 h_dist_b0b0 h_dist_b0b1]
    rw [windowed2Input_at_window_disjoint acc b0Idx b1Idx _ _ numWin (4 * k + 3)
          (fun j hj => by have := h_b0_above j hj; omega)
          (fun j hj => by have := h_b1_above j hj; omega)]
    rw [hbpos0 acc k]
    rw [windowed2Input_read_b0_bounded w b0Idx b1Idx (windowed2_b0_of_x acc) (windowed2_b1_of_x acc)
          numWin k hk h_b0_ne_b1 h_dist_b0b0 h_dist_b0b1]
    rfl
  · push_neg at hb0
    by_cases hb1 : ∃ k, k < numWin ∧ q = b1Idx k
    · obtain ⟨k, hk, rfl⟩ := hb1
      rw [swapTargetWindows_read_b1 b0Idx b1Idx numWin k _ hk
            h_b0_above h_b1_above h_dist_b1b0 h_dist_b1b1]
      rw [windowed2Input_at_window_disjoint acc b0Idx b1Idx _ _ numWin (4 * k + 5)
            (fun j hj => by have := h_b0_above j hj; omega)
            (fun j hj => by have := h_b1_above j hj; omega)]
      rw [hbpos1 acc k]
      rw [windowed2Input_read_b1_bounded w b0Idx b1Idx (windowed2_b0_of_x acc) (windowed2_b1_of_x acc)
            numWin k hk h_dist_b0b1 h_dist_b1b1]
      rfl
    · push_neg at hb1
      by_cases ht0 : ∃ k, k < numWin ∧ q = 4 * k + 3
      · obtain ⟨k, hk, rfl⟩ := ht0
        rw [swapTargetWindows_read_t0 b0Idx b1Idx numWin k _ hk
              h_b0_above h_b1_above h_dist_b0b0 h_dist_b0b1]
        rw [windowed2Input_read_b0_bounded acc b0Idx b1Idx (windowed2_b0_of_x w) (windowed2_b1_of_x w)
              numWin k hk h_b0_ne_b1 h_dist_b0b0 h_dist_b0b1]
        rw [windowed2Input_at_window_disjoint w b0Idx b1Idx _ _ numWin (4 * k + 3)
              (fun j hj => by have := h_b0_above j hj; omega)
              (fun j hj => by have := h_b1_above j hj; omega)]
        rw [hbpos0 w k]
        rfl
      · push_neg at ht0
        by_cases ht1 : ∃ k, k < numWin ∧ q = 4 * k + 5
        · obtain ⟨k, hk, rfl⟩ := ht1
          rw [swapTargetWindows_read_t1 b0Idx b1Idx numWin k _ hk
                h_b0_above h_b1_above h_b0_ne_b1 h_dist_b1b0 h_dist_b1b1]
          rw [windowed2Input_read_b1_bounded acc b0Idx b1Idx (windowed2_b0_of_x w) (windowed2_b1_of_x w)
                numWin k hk h_dist_b0b1 h_dist_b1b1]
          rw [windowed2Input_at_window_disjoint w b0Idx b1Idx _ _ numWin (4 * k + 5)
                (fun j hj => by have := h_b0_above j hj; omega)
                (fun j hj => by have := h_b1_above j hj; omega)]
          rw [hbpos1 w k]
          rfl
        · push_neg at ht1
          rw [swapTargetWindows_preserves_disjoint b0Idx b1Idx numWin q _
                h_b0_above h_b1_above ht0 ht1 hb0 hb1]
          rw [windowed2Input_at_window_disjoint acc b0Idx b1Idx _ _ numWin q hb0 hb1]
          rw [windowed2Input_at_window_disjoint w b0Idx b1Idx _ _ numWin q hb0 hb1]
          rw [cuccaro_base_false bits acc q hacc (h_not_b q ht0 ht1)]
          rw [cuccaro_base_false bits w q hw (h_not_b q ht0 ht1)]

/-- **`h_tw` at the concrete windowed layout — CLOSED.**  Instantiates
    `swapTargetWindows_apply` at `wb0Idx`/`wb1Idx`/`wnumWin`, discharging
    every layout hypothesis by `omega` (using `2 ∣ bits` for
    `2·wnumWin = bits`).  This is exactly the open `h_tw` hypothesis of
    `windowedInplaceModMul_roundTrip` with
    `tw := swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits)`. -/
theorem swapTargetWindows_h_tw (bits acc w : Nat)
    (h_even : 2 ∣ bits) (hacc : acc < 2 ^ bits) (hw : w < 2 ^ bits) :
    Gate.applyNat (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
        (windowed2Input acc (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x w) (windowed2_b1_of_x w) (wnumWin bits))
      = windowed2Input w (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x acc) (windowed2_b1_of_x acc) (wnumWin bits) := by
  have h_numWin : 2 * wnumWin bits = bits := by unfold wnumWin; exact Nat.mul_div_cancel' h_even
  exact swapTargetWindows_apply bits acc w (wb0Idx bits) (wb1Idx bits) (wnumWin bits)
    h_numWin hacc hw
    (fun k _ => by unfold wb0Idx; omega)
    (fun k _ => by unfold wb1Idx; omega)
    (fun k _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ hij => by unfold wb0Idx; omega)
    (fun i j _ _ _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ _ => by unfold wb1Idx wb0Idx; omega)
    (fun i j _ _ hij => by unfold wb1Idx; omega)


end FormalRV.BQAlgo.WindowedShorConnection
