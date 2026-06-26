/- WindowedLoaderBitExtraction — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.WindowedMultiplyAddSpecification

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-- **q_start-parametric base-false at disjoint positions.** If `q`
is not any `b0Idx k` / `b1Idx k` for `k < numWin`, and the
zero-accumulator Cuccaro base reads `false` at `q`, then the full
parametric encoding reads `false` at `q`. Caller supplies the
base-false fact (preserves generality across q_start values).

Mirrors `windowed2Input_zero_at_disjoint` for the q_start-parametric
encoding. -/
theorem windowed2Input_qstart_zero_at_disjoint
    (q_start : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin q : Nat)
    (h_base : cuccaro_input_F q_start false 0 0 q = false)
    (h_b0_disj : ∀ k, k < numWin → q ≠ b0Idx k)
    (h_b1_disj : ∀ k, k < numWin → q ≠ b1Idx k) :
    windowed2Input_qstart q_start 0 b0Idx b1Idx b0 b1 numWin q = false := by
  induction numWin with
  | zero =>
    rw [windowed2Input_qstart_zero]
    exact h_base
  | succ n ih =>
    rw [windowed2Input_qstart_succ]
    have h_b0_n : q ≠ b0Idx n := h_b0_disj n (Nat.lt_succ_self n)
    have h_b1_n : q ≠ b1Idx n := h_b1_disj n (Nat.lt_succ_self n)
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_n]
    exact ih
      (fun k hk => h_b0_disj k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b1_disj k (Nat.lt_succ_of_lt hk))

/-- **Bounded q_start-parametric b0 readback.** For any installed
window `k < numWin`, the parametric encoding reads back the latest
write at `b0Idx k`. Hypotheses restricted to `< numWin`. -/
theorem windowed2Input_qstart_read_b0_bounded
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 numWin (b0Idx k)
      = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_qstart_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _
            (h_b0_ne_b1 k (Nat.lt_succ_self k))]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0k_ne_b1n : b0Idx k ≠ b1Idx n :=
        h_distinct_b0_b1 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      have h_b0k_ne_b0n : b0Idx k ≠ b0Idx n :=
        h_distinct_b0_b0 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b0n]
      exact ih hk_lt_n
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)

/-- **Bounded q_start-parametric b1 readback.** -/
theorem windowed2Input_qstart_read_b1_bounded
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 numWin (b1Idx k)
      = b1 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_qstart_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b1k_ne_b1n : b1Idx k ≠ b1Idx n :=
        h_distinct_b1_b1 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      have h_b1k_ne_b0n : b1Idx k ≠ b0Idx n := by
        have := h_distinct_b0_b1 n k (Nat.lt_succ_self n) hk
          (Ne.symm (Nat.ne_of_lt hk_lt_n))
        exact Ne.symm this
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0n]
      exact ih hk_lt_n
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)

/-! ### Shifted-layout disjointness arithmetic

For the shifted Cuccaro layout (q_start = bits), the accumulator
b-bit positions live at `bits + 2*k + 1`. These are strictly above
any official data position `q < bits`, ensuring the disjointness
needed by the (forthcoming) Cuccaro→Data SWAP cascade. -/

/-- **Accumulator b-bit position is at least `bits + 1`.** Direct
arithmetic from `q_start + 2*k + 1` with `q_start = bits`. -/
theorem shifted_cuccaro_b_pos_ge
    (bits k : Nat) :
    bits + 1 ≤ bits + 2 * k + 1 := by
  omega

/-- **Accumulator b-bit position lies strictly above the data
register.** -/
theorem shifted_cuccaro_b_above_data
    (bits k : Nat) :
    bits ≤ bits + 2 * k + 1 := by
  omega

/-- **Accumulator b-bit position differs from any data position.**
For the shifted layout (`q_start = bits`), the accumulator b-bit at
position `bits + 2*k + 1` cannot equal a data position `q < bits`. -/
theorem shifted_cuccaro_b_ne_data
    (bits k q : Nat) (h_q : q < bits) :
    bits + 2 * k + 1 ≠ q := by
  omega

/-- **Data position differs from any accumulator b-bit position.**
Symmetric form of `shifted_cuccaro_b_ne_data`. -/
theorem data_ne_shifted_cuccaro_b
    (bits k q : Nat) (h_q : q < bits) :
    q ≠ bits + 2 * k + 1 := by
  omega

/-- **Cuccaro→Data SWAP source/destination disjointness** (shifted
layout). The Cuccaro b-bit at `bits + 2*k + 1` (source) and the data
position `bits - 1 - k` (destination) are distinct for any `k`. The
data range `q < bits` is strictly below the accumulator range
`q ≥ bits + 1`. -/
theorem shifted_swap_src_ne_dst
    (bits k : Nat) (h_k : k < bits) :
    bits + 2 * k + 1 ≠ bits - 1 - k := by
  omega

/-! ### End of R7d^xxix-L-1 q_start-parametric layout

What landed in L-1:
- `windowed2Input_qstart` def + simp unfolds.
- `windowed2Input_eq_qstart_2` bridge to old layout.
- `windowed2Input_qstart_zero_at_disjoint` (private).
- `windowed2Input_qstart_read_b0_bounded` /
  `windowed2Input_qstart_read_b1_bounded` (bounded readbacks).
- Shifted-layout arithmetic (b_pos_ge, b_above_data, b_ne_data,
  data_ne_b, swap_src_ne_dst).

Deferred to L-2 / L-3:
- q_start-parametric selected-add gate + frame lemma.
- K-stage at q_start = bits.
- target-decode for the q_start-parametric layout (not strictly
  needed by L-2; can be deferred indefinitely if not used
  downstream). -/


end Windowed
end VerifiedShor
