/- WindowedLoaderBitExtraction — Part5 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedLoaderBitExtraction.Part4

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xxv — per-window selected-add on multi-window input

Closes the per-window theorem `toyWindow2SelectedAddGate_on_windowed2Input`
using the frame helper from R7d^xxiv.

Strategy:
- Auxiliary `toyWindow2SelectedAddGate_active_extended` handles the
  "active gate applied to a Case3Input-like state extended by an
  inactive prefix". Proven by induction on the prefix size with
  `update_comm` swaps + frame helper + IH.
- Main theorem handles arbitrary `numWin` by outer induction:
  - Active newest (k = n): reduce to the auxiliary at m = n, k = n.
  - Inactive newest (k < n): apply frame helper twice + IH on the
    inner `windowed2Input ... n`. -/

/-- **Active-extended auxiliary.** The selected-add gate at fixed
active window index `k` applied to an inactive prefix of size `m`
(with `m ≤ k`) plus the active layer produces the same shape with
the accumulator updated per `windowedStepSpec`.

Proven by induction on `m`. The base case (`m = 0`) is the pure
`Case3Input` shape and applies the spec directly. The inductive case
uses 4 `update_comm` swaps to bring the inactive m-th layer outside
the active layer, applies the frame helper twice to push it past the
gate, then applies the IH on the smaller prefix. -/
theorem toyWindow2SelectedAddGate_active_extended
    (bits N a acc flagIdx k : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i ≤ k → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i ≤ k → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i ≤ k → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b1Idx j) :
    ∀ (m : Nat), m ≤ k →
      Gate.applyNat
          (toyWindow2SelectedAddGate bits N a k flagIdx (b0Idx k) (b1Idx k))
          (update (update (windowed2Input acc b0Idx b1Idx b0 b1 m)
                     (b0Idx k) (b0 k)) (b1Idx k) (b1 k))
        = update (update (windowed2Input
            (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
            b0Idx b1Idx b0 b1 m) (b0Idx k) (b0 k)) (b1Idx k) (b1 k) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [windowed2Input_zero, windowed2Input_zero]
    have h_k_le_k : k ≤ k := Nat.le_refl k
    show Gate.applyNat _ (toyWindow2Case3Input acc (b0Idx k) (b1Idx k) (b0 k) (b1 k))
       = toyWindow2Case3Input
           (windowedStepSpec a N 2 k acc (windowBits2_to_v (b0 k) (b1 k)))
           (b0Idx k) (b1Idx k) (b0 k) (b1 k)
    exact toyWindow2SelectedAddGate_state_eq_spec bits N a k acc flagIdx
      (b0Idx k) (b1Idx k) (b0 k) (b1 k)
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      (h_hi0 k h_k_le_k) (h_hi1 k h_k_le_k) (h_b0_ne_b1 k h_k_le_k)
      (h_b0_ne_flag k h_k_le_k) (h_b1_ne_flag k h_k_le_k)
  | succ j ih =>
    intro hmk
    have hjk : j ≤ k :=
      Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hmk)
    have hjk_ne : j ≠ k :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hmk)
    have h_k_le_k : k ≤ k := Nat.le_refl k
    have h_b0j_ne_b0k : b0Idx j ≠ b0Idx k :=
      h_distinct_b0_b0 j k hjk h_k_le_k hjk_ne
    have h_b0j_ne_b1k : b0Idx j ≠ b1Idx k :=
      h_distinct_b0_b1 j k hjk h_k_le_k hjk_ne
    have h_b1j_ne_b0k : b1Idx j ≠ b0Idx k :=
      h_distinct_b1_b0 j k hjk h_k_le_k hjk_ne
    have h_b1j_ne_b1k : b1Idx j ≠ b1Idx k :=
      h_distinct_b1_b1 j k hjk h_k_le_k hjk_ne
    have h_b0j_hi : 2 + 2 * bits + 1 ≤ b0Idx j := h_hi0 j hjk
    have h_b1j_hi : 2 + 2 * bits + 1 ≤ b1Idx j := h_hi1 j hjk
    have h_b0j_ne_flag : b0Idx j ≠ flagIdx := h_b0_ne_flag j hjk
    have h_b1j_ne_flag : b1Idx j ≠ flagIdx := h_b1_ne_flag j hjk
    -- Generic swap lemma: 4 update_comm reorderings.
    have swap : ∀ (W : Nat → Bool),
        update (update (update (update W (b0Idx j) (b0 j)) (b1Idx j) (b1 j))
            (b0Idx k) (b0 k)) (b1Idx k) (b1 k)
      = update (update (update (update W (b0Idx k) (b0 k)) (b1Idx k) (b1 k))
            (b0Idx j) (b0 j)) (b1Idx j) (b1 j) := by
      intro W
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1j_ne_b0k]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0j_ne_b0k]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1j_ne_b1k]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0j_ne_b1k]
    -- Unfold `windowed2Input ... (j+1)` on both sides via simp on the
    -- @[simp] succ unfold (covers both LHS acc and RHS acc' instances).
    simp only [windowed2Input_succ]
    -- Swap the active layer past the inactive m-th layer (both sides).
    rw [swap (windowed2Input acc b0Idx b1Idx b0 b1 j)]
    rw [swap (windowed2Input
              (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
              b0Idx b1Idx b0 b1 j)]
    -- Push the inactive layer past the gate via frame helper.
    rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
          (b0Idx k) (b1Idx k) (b1Idx j) (b1 j) _
          h_b1j_hi h_b1j_ne_b0k h_b1j_ne_b1k h_b1j_ne_flag]
    rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
          (b0Idx k) (b1Idx k) (b0Idx j) (b0 j) _
          h_b0j_hi h_b0j_ne_b0k h_b0j_ne_b1k h_b0j_ne_flag]
    -- Apply IH on the smaller prefix.
    rw [ih hjk]

/-- **Per-window selected-add correctness on the multi-window
input encoding.** The selected-add gate at active window `k` (with
`k < numWin`) applied to the `windowed2Input` state produces the
same state with the accumulator advanced by `windowedStepSpec` at
the encoded window value.

Proof by induction on `numWin`:
- `k = n` (active newest): reduce to the active-extended auxiliary
  at `m = n`, `k = n`.
- `k < n` (inactive newest): apply the frame helper twice to push
  the two newest inactive updates past the gate, then apply the IH
  on the inner `windowed2Input ... n`, then reassemble. -/
theorem toyWindow2SelectedAddGate_on_windowed2Input
    (bits N a k acc flagIdx numWin : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (hk : k < numWin)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < numWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < numWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < numWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (toyWindow2SelectedAddGate bits N a k flagIdx (b0Idx k) (b1Idx k))
        (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = windowed2Input
          (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
          b0Idx b1Idx b0 b1 numWin := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · -- Active newest case: apply the auxiliary at m = n, k = n.
      subst hkn
      have h_k_le_k : k ≤ k := Nat.le_refl k
      -- Convert bounded hypotheses from i < k+1 to i ≤ k.
      have h_hi0' : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b0Idx i :=
        fun i hi => h_hi0 i (Nat.lt_succ_of_le hi)
      have h_hi1' : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b1Idx i :=
        fun i hi => h_hi1 i (Nat.lt_succ_of_le hi)
      have h_b0_ne_b1' : ∀ i, i ≤ k → b0Idx i ≠ b1Idx i :=
        fun i hi => h_b0_ne_b1 i (Nat.lt_succ_of_le hi)
      have h_b0_ne_flag' : ∀ i, i ≤ k → b0Idx i ≠ flagIdx :=
        fun i hi => h_b0_ne_flag i (Nat.lt_succ_of_le hi)
      have h_b1_ne_flag' : ∀ i, i ≤ k → b1Idx i ≠ flagIdx :=
        fun i hi => h_b1_ne_flag i (Nat.lt_succ_of_le hi)
      have h_distinct_b0_b0' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b0Idx j :=
        fun i j hi hj hij => h_distinct_b0_b0 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      have h_distinct_b0_b1' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b1Idx j :=
        fun i j hi hj hij => h_distinct_b0_b1 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      have h_distinct_b1_b0' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b0Idx j :=
        fun i j hi hj hij => h_distinct_b1_b0 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      have h_distinct_b1_b1' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b1Idx j :=
        fun i j hi hj hij => h_distinct_b1_b1 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      rw [show windowed2Input acc b0Idx b1Idx b0 b1 (k + 1) =
              update (update (windowed2Input acc b0Idx b1Idx b0 b1 k)
                (b0Idx k) (b0 k)) (b1Idx k) (b1 k) from rfl]
      rw [show windowed2Input
              (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
              b0Idx b1Idx b0 b1 (k + 1) =
              update (update (windowed2Input
                  (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
                  b0Idx b1Idx b0 b1 k)
                (b0Idx k) (b0 k)) (b1Idx k) (b1 k) from rfl]
      exact toyWindow2SelectedAddGate_active_extended bits N a acc flagIdx k
        b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_hi0' h_hi1' h_b0_ne_b1' h_b0_ne_flag' h_b1_ne_flag'
        h_distinct_b0_b0' h_distinct_b0_b1' h_distinct_b1_b0' h_distinct_b1_b1'
        k h_k_le_k
    · -- Inactive newest case (k < n): push outer two updates past gate via
      -- frame helper, apply IH on inner prefix.
      have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have hn_lt_succ : n < n + 1 := Nat.lt_succ_self n
      have h_n_ne_k : n ≠ k := fun h => hkn h.symm
      -- Frame helper hypotheses for the n-th window updates.
      have h_b0n_hi : 2 + 2 * bits + 1 ≤ b0Idx n := h_hi0 n hn_lt_succ
      have h_b1n_hi : 2 + 2 * bits + 1 ≤ b1Idx n := h_hi1 n hn_lt_succ
      have h_b0n_ne_b0k : b0Idx n ≠ b0Idx k :=
        h_distinct_b0_b0 n k hn_lt_succ hk h_n_ne_k
      have h_b0n_ne_b1k : b0Idx n ≠ b1Idx k :=
        h_distinct_b0_b1 n k hn_lt_succ hk h_n_ne_k
      have h_b1n_ne_b0k : b1Idx n ≠ b0Idx k :=
        h_distinct_b1_b0 n k hn_lt_succ hk h_n_ne_k
      have h_b1n_ne_b1k : b1Idx n ≠ b1Idx k :=
        h_distinct_b1_b1 n k hn_lt_succ hk h_n_ne_k
      have h_b0n_ne_flag : b0Idx n ≠ flagIdx := h_b0_ne_flag n hn_lt_succ
      have h_b1n_ne_flag : b1Idx n ≠ flagIdx := h_b1_ne_flag n hn_lt_succ
      -- Unfold windowed2Input ... (n+1) on both sides.
      simp only [windowed2Input_succ]
      -- Push outer two updates past gate via frame helper.
      rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
            (b0Idx k) (b1Idx k) (b1Idx n) (b1 n) _
            h_b1n_hi h_b1n_ne_b0k h_b1n_ne_b1k h_b1n_ne_flag]
      rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
            (b0Idx k) (b1Idx k) (b0Idx n) (b0 n) _
            h_b0n_hi h_b0n_ne_b0k h_b0n_ne_b1k h_b0n_ne_flag]
      -- Restrict hypotheses to numWin = n for IH.
      rw [ih hk_lt_n
            (fun i hi => h_hi0 i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_hi1 i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_b0_ne_b1 i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_b0_ne_flag i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_b1_ne_flag i (Nat.lt_succ_of_lt hi))
            (fun i j hi hj hij =>
              h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
            (fun i j hi hj hij =>
              h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
            (fun i j hi hj hij =>
              h_distinct_b1_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
            (fun i j hi hj hij =>
              h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)]


end Windowed
end VerifiedShor
