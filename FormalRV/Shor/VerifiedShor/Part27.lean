import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.Part26

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)

/-- **Data-position source classification.** Under exact coverage
`2 * numWin = bits`, every data-register position `q < bits`
corresponds to either the even or odd source of some window
`k < numWin`. -/
theorem data_position_is_source
    (bits numWin q : Nat)
    (h_exact : 2 * numWin = bits)
    (hq : q < bits) :
    (∃ k, k < numWin ∧ q = bits - 1 - 2 * k) ∨
    (∃ k, k < numWin ∧ q = bits - 1 - (2 * k + 1)) := by
  set i := bits - 1 - q with hi_def
  have hi_lt : i < bits := by omega
  rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
  · left
    refine ⟨i / 2, ?_, ?_⟩
    · omega
    · omega
  · right
    refine ⟨i / 2, ?_, ?_⟩
    · omega
    · omega

/-- `cuccaro_input_F 2 false 0 0 q = false` for any `q`. The Cuccaro
input layout with zero carry-in / zero a / zero b is uniformly false:
positions `< 2` return false directly; the c_in slot at i = 0 is
false; alternating a/b positions read `Nat.testBit 0 _ = false`. -/
theorem cuccaro_input_F_zero_acc_eq_false (q : Nat) :
    cuccaro_input_F 2 false 0 0 q = false := by
  unfold cuccaro_input_F
  split_ifs <;> simp

/-- `windowed2Input 0 ...` is `false` at any position disjoint from
all window-bit indices. The zero-accumulator base is uniformly false
(from `cuccaro_input_F_zero_acc_eq_false`), and the recursive updates
only affect window-target positions. -/
theorem windowed2Input_zero_at_disjoint
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin q : Nat)
    (h_b0_disj : ∀ k, k < numWin → q ≠ b0Idx k)
    (h_b1_disj : ∀ k, k < numWin → q ≠ b1Idx k) :
    windowed2Input 0 b0Idx b1Idx b0 b1 numWin q = false := by
  induction numWin with
  | zero => exact cuccaro_input_F_zero_acc_eq_false q
  | succ n ih =>
    rw [windowed2Input_succ]
    have h_b0_n : q ≠ b0Idx n := h_b0_disj n (Nat.lt_succ_self n)
    have h_b1_n : q ≠ b1Idx n := h_b1_disj n (Nat.lt_succ_self n)
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_n]
    exact ih
      (fun k hk => h_b0_disj k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b1_disj k (Nat.lt_succ_of_lt hk))

/-- Bounded-distinctness variant of `windowed2Input_read_b0`. Same
result but the distinctness hypotheses are restricted to indices
`< numWin`, matching the apply theorem's signature. -/
theorem windowed2Input_read_b0_bounded
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b0Idx k) = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
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
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- Bounded-distinctness variant of `windowed2Input_read_b1`. -/
theorem windowed2Input_read_b1_bounded
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b1Idx k) = b1 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
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
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Full SWAP loader apply theorem.** Under exact coverage
`2 * numWin = bits` and above-data + distinctness hypotheses, the
SWAP loader applied to `encodeDataZeroAnc bits anc x` produces
exactly the `windowed2Input 0 ... numWin` state expected by the
verified multi-window selected-add pipeline.

Proven by `funext q` + 4-way case analysis:
- q is a `b0Idx` window target: readback + windowed2Input_read.
- q is a `b1Idx` window target: readback + windowed2Input_read.
- q is a data position (q < bits): clearing + disjoint zero base.
- q is above the data register, not a window target: frame +
  encodeDataZeroAnc_above + disjoint zero base. -/
theorem windowedSwapLoadAdapter_apply_encodeDataZeroAnc
    (bits anc numWin x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_anc_pos : 0 < anc)
    (h_numWin_exact : 2 * numWin = bits)
    (h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x)
      = windowed2Input 0 b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin := by
  funext q
  have h_2numWin_le : 2 * numWin ≤ bits := by omega
  by_cases hA : ∃ k, k < numWin ∧ q = b0Idx k
  · obtain ⟨k, hk, hq_eq⟩ := hA
    subst hq_eq
    rw [windowedSwapLoadAdapter_read_b0 bits anc x b0Idx b1Idx numWin k hx hk
          h_2numWin_le h_b0_above h_b1_above h_b0_ne_b1
          h_distinct_b0_b0 h_distinct_b0_b1]
    rw [windowed2Input_read_b0_bounded 0 b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin k hk
          h_b0_ne_b1 h_distinct_b0_b0 h_distinct_b0_b1]
    rfl
  · push_neg at hA
    have hA' : ∀ k, k < numWin → q ≠ b0Idx k := fun k hk h => hA k hk h
    by_cases hB : ∃ k, k < numWin ∧ q = b1Idx k
    · obtain ⟨k, hk, hq_eq⟩ := hB
      subst hq_eq
      rw [windowedSwapLoadAdapter_read_b1 bits anc x b0Idx b1Idx numWin k hx hk
            h_2numWin_le h_b0_above h_b1_above
            h_distinct_b1_b0 h_distinct_b1_b1]
      rw [windowed2Input_read_b1_bounded 0 b0Idx b1Idx
            (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin k hk
            h_distinct_b0_b1 h_distinct_b1_b1]
      rfl
    · push_neg at hB
      have hB' : ∀ k, k < numWin → q ≠ b1Idx k := fun k hk h => hB k hk h
      -- RHS: windowed2Input 0 at q (not a target) = false.
      have h_rhs : windowed2Input 0 b0Idx b1Idx
                     (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin q = false :=
        windowed2Input_zero_at_disjoint b0Idx b1Idx _ _ numWin q hA' hB'
      by_cases hq_lt : q < bits
      · -- Case C: q < bits. Classify as even/odd source.
        rcases data_position_is_source bits numWin q h_numWin_exact hq_lt with
          ⟨k, hk, hq_eq⟩ | ⟨k, hk, hq_eq⟩
        · subst hq_eq
          rw [windowedSwapLoadAdapter_clears_data_even bits anc x b0Idx b1Idx
                numWin k hx hk h_anc_pos h_2numWin_le
                h_b0_above h_b1_above h_distinct_b0_b0 h_distinct_b0_b1]
          rw [h_rhs]
        · subst hq_eq
          rw [windowedSwapLoadAdapter_clears_data_odd bits anc x b0Idx b1Idx
                numWin k hx hk h_anc_pos h_2numWin_le
                h_b0_above h_b1_above h_b0_ne_b1
                h_distinct_b1_b0 h_distinct_b1_b1]
          rw [h_rhs]
      · -- Case D: bits ≤ q, not a window target.
        push_neg at hq_lt
        -- LHS via frame property: q disjoint from all sources and targets.
        have h_prefix_swap0_ne : ∀ j, j < numWin → bits - 1 - 2 * j ≠ b0Idx j :=
          fun j hj => src0_ne_above bits j _ (by omega) (h_b0_above j hj)
        have h_prefix_swap1_ne : ∀ j, j < numWin → bits - 1 - (2 * j + 1) ≠ b1Idx j :=
          fun j hj => src1_ne_above bits j _ (by omega) (h_b1_above j hj)
        have h_q_disj_src0 : ∀ j, j < numWin → q ≠ bits - 1 - 2 * j :=
          fun j hj => by omega
        have h_q_disj_src1 : ∀ j, j < numWin → q ≠ bits - 1 - (2 * j + 1) :=
          fun j hj => by omega
        rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx q numWin
              (encodeDataZeroAnc bits anc x)
              h_prefix_swap0_ne h_prefix_swap1_ne
              h_q_disj_src0 h_q_disj_src1 hA' hB']
        rw [encodeDataZeroAnc_above bits anc x q hx hq_lt h_anc_pos]
        rw [h_rhs]

/-! ## Phase R7d^xxix-K — SWAP loader + selected-add composition

Composes the SWAP loader's full apply theorem (R7d^xxix-J) with the
verified multi-window selected-add full-state correctness
(`toyWindowed2SelectedAddGate_state_mul_correct`).

The intermediate output is still in `windowed2Input` layout (the
reverse/output adapter is R7d^xxix-L's scope). -/

/-- **SWAP loader + selected-add composition (raw form).** Applying
the SWAP loader followed by the multi-window selected-add to
`encodeDataZeroAnc` produces the windowed input state with the
accumulator advanced by `a * windowed2Value (b0_of_x x) (b1_of_x x)
numWin` modulo `N`. -/
theorem windowedSwapLoadAdapter_then_selectedAdd_apply
    (bits anc numWin x N a flagIdx : Nat)
    (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_anc_pos : 0 < anc)
    (h_numWin_exact : 2 * numWin = bits)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_b1_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_b0_ne_flag : ∀ k, k < numWin → b0Idx k ≠ flagIdx)
    (h_b1_ne_flag : ∀ k, k < numWin → b1Idx k ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (Gate.seq
          (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
          (windowed2SelectedAddGate
            (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
            bits flagIdx b0Idx b1Idx numWin))
        (encodeDataZeroAnc bits anc x)
      = windowed2Input
          ((0 + a * windowed2Value
              (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin) % N)
          b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin := by
  rw [Gate.applyNat_seq]
  -- Derive bits ≤ b0Idx, bits ≤ b1Idx from the stricter selected-add hypotheses.
  have h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k :=
    fun k hk => by have := h_b0_hi k hk; omega
  have h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k :=
    fun k hk => by have := h_b1_hi k hk; omega
  rw [windowedSwapLoadAdapter_apply_encodeDataZeroAnc bits anc numWin x b0Idx b1Idx
        hx h_anc_pos h_numWin_exact h_b0_above h_b1_above h_b0_ne_b1
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  exact toyWindowed2SelectedAddGate_state_mul_correct bits N a flagIdx numWin 0
    b0Idx b1Idx (windowed2_b0_of_x x) (windowed2_b1_of_x x)
    hbits hN_pos hN hN2 hN_pos
    h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1

/-- **SWAP loader + selected-add composition (cleaned form).** Same
as the raw theorem but with the windowed multiplier value collapsed
to `x % 2^bits` (using `windowed2Value_of_x_mod` and the exact-coverage
hypothesis) and the `0 + ...` simplified away. -/
theorem windowedSwapLoadAdapter_then_selectedAdd_apply_clean
    (bits anc numWin x N a flagIdx : Nat)
    (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_anc_pos : 0 < anc)
    (h_numWin_exact : 2 * numWin = bits)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_b1_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_b0_ne_flag : ∀ k, k < numWin → b0Idx k ≠ flagIdx)
    (h_b1_ne_flag : ∀ k, k < numWin → b1Idx k ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (Gate.seq
          (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
          (windowed2SelectedAddGate
            (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
            bits flagIdx b0Idx b1Idx numWin))
        (encodeDataZeroAnc bits anc x)
      = windowed2Input
          ((a * (x % 2^bits)) % N)
          b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin := by
  rw [windowedSwapLoadAdapter_then_selectedAdd_apply bits anc numWin x N a flagIdx
        b0Idx b1Idx hx h_anc_pos h_numWin_exact hbits hN_pos hN hN2
        h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  rw [windowed2Value_of_x_mod, h_numWin_exact, Nat.zero_add]

/-! ### Status: SWAP loader behavior fully proven (R7d^xxix-J)

The remaining proofs require composing the helpers above with
`encodeDataZeroAnc_data` (data-position value lookup) and a Boolean
identity `nat_to_funbool n x i = x.testBit (n - 1 - i)` (which
itself follows from `Nat.toNat_testBit`).

**R7d^xxix-F (next tick)** should:
1. Prove the per-window readback lemmas:
   - `windowedSwapLoadAdapter_succ_read_b1`: latest-window b1 readback
     returning `x.testBit (2*n + 1)`. ~50-80 lines using
     `qubit_swap_correct` ×2 + `windowedSwapLoadAdapter_preserves_disjoint`
     + `encodeDataZeroAnc_data` + a `nat_to_funbool ↔ testBit` bridge.
   - `windowedSwapLoadAdapter_succ_read_b0`: similar.
   - General-k versions via induction.
2. Prove the data-clearing lemmas at moved positions
   (the swap target was initially 0 from `encodeDataZeroAnc_anc` /
   `encodeDataZeroAnc_oob`, so the source becomes 0 after swap).
3. Compose into the full apply theorem under
   `2 * numWin = bits`:
   ```
   Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
       (encodeDataZeroAnc bits anc x)
     = windowed2Input 0 b0Idx b1Idx
         (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin
   ```
   Proof by `funext q` with case analysis on whether `q` is a
   window target, a moved source, or disjoint.

Estimated 150-250 lines total. The arithmetic helpers landed here
remove a significant fraction of that bookkeeping noise. -/

/-! ## Phase R7d^xiii — composed selected-add: status partial

The composed `toyWindow2SelectedAddGate` correctness theorem requires
**unified case-N state_eq theorems** that cover all four `(b0, b1)`
inputs (not just the firing case). For non-firing inputs, the gate
should act as the identity on `toyWindow2Case3Input acc ... b0 b1`.

The existing state_eq theorems (R7d^x, R7d^xi^d, R7d^xii) only handle
the firing input:
- `toyWindow2Case3Gate_state_eq` for `(b0=true, b1=true)`.
- `toyWindow2Case1Gate_state_eq` for `(b0=true, b1=false)`.
- `toyWindow2Case2Gate_state_eq` for `(b0=false, b1=true)`.

For the composition, each non-firing application produces an
intermediate state. The case-N _correct theorem gives target_val
for general `(b0, b1)`, but the target_val alone does not let the
next case-N _correct apply, since the latter requires the input
to be in `toyWindow2Case3Input` shape. Thus, we need 9 no-op
state_eq lemmas (or equivalently 3 unified case-N state_eq
theorems covering all 4 `(b0, b1)`).

Each no-op state_eq is roughly the size of an existing firing
state_eq (~300 lines). Total for full composition:
- 3 unified case state_eq (each ~600 lines covering 4 (b0,b1)
  values): ~1800 lines.
- Composition theorem proper: ~100 lines.

This exceeds a single tick budget. Deferred to R7d^xiv. The
remainder of this tick documents the gap and verifies that the
existing state_eq theorems remain intact. -/

/-! ### R7d''' status: composition theorem deferred to follow-up tick

**What is verified now**:
* All three case gates (`toyWindow2Case1Gate`, `_Case2Gate`,
  `_Case3Gate`) have proven correctness theorems for their
  respective firing conditions (b0 && !b1, !b0 && b1, b0 && b1).
* The composed gate `toyWindow2SelectedAddGate` is now concretely
  defined as the sequence of the three case gates.
* All four windowSize=2 arithmetic-spec helpers (v=0, v=1, v=2, v=3)
  are landed and rfl/Nat-mod-eq-of-lt-provable.

**What is deferred** (`toyWindow2SelectedAddGate_correct`):
The composed gate's target-decode correctness theorem requires
state-equality proofs for each case gate:

```
theorem toyWindow2CaseV_state_eq :
  Gate.applyNat (caseV_gate ...) (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
    = toyWindow2Case3Input (newAccV acc b0 b1) b0Idx b1Idx b0 b1
```

where `newAccV` selects the case-fired accumulator update.

These state-equality theorems require funext + per-position case
splits (~60-90 lines per case), analogous to
`sqir_modmult_step_state_eq` (SQIRModMult.lean:1156).  The proof
infrastructure is in place (`cuccaro_target_val_eq_implies_bits_match`,
`cuccaro_read_val_eq_implies_bits_match`, R4b clean conjuncts, the
above-layout commute lemmas, `sqir_style_controlledModAddConst_gate_carry_in_restored`),
but the per-case-per-position bookkeeping is substantial.

Once the three case_state_eq theorems land, the composition theorem
becomes a 4-way `by_cases` on `(b0, b1)` plus straightforward
applications of the case-correctness theorems:

```
theorem toyWindow2SelectedAddGate_correct
    ...
    (v : Nat) (hv : v < 4)
    (h_window : v = ...windowValue from b0, b1...) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2SelectedAddGate ...) (Input acc b0 b1))
      = windowedStepSpec a N 2 k acc v
```

* v=0 (b0=F, b1=F): all three case_state_eq give acc' = acc; finish with `windowedStepSpec_window2_v0`.
* v=1 (b0=T, b1=F): case1_state_eq gives acc' = (acc + tv1) % N; cases 2 and 3 don't fire; finish with `windowedStepSpec_window2_v1`.
* v=2 (b0=F, b1=T): case2 fires; finish with `windowedStepSpec_window2_v2`.
* v=3 (b0=T, b1=T): case3 fires; finish with `windowedStepSpec_window2_v3`.

**Next tick**: prove the three `_state_eq` theorems (mirroring
`sqir_modmult_step_state_eq` proof structure), then add the composition
theorem with the 4-way case split above. -/

/-! ## Phase R7d^xxix-L-REVIEW — diagnostic on the reverse-SWAP unloader

The K-state (post selected-add) is:

  windowed2Input ((a * (x % 2^bits)) % N) b0Idx b1Idx
    (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin

with the following position-by-position content:

* Cuccaro workspace (positions `q < q_start = 2`): false.
* Cuccaro carry-in (position 2): false.
* Cuccaro `b`-bit positions `q_start + 2*k + 1 = 2*k + 3`: bit `k`
  of the accumulator `y := (a * (x % 2^bits)) % N`.
* Cuccaro `a`-bit positions `q_start + 2*k + 2 = 2*k + 4`: false
  (the `a`-register input was 0 because the windowed adder is
  constant-shift modular addition).
* `b0Idx k`, `b1Idx k` (above-workspace window positions):
  `windowed2_b0_of_x x k = x.testBit (2*k)` and
  `windowed2_b1_of_x x k = x.testBit (2*k + 1)`.

The `encodeDataZeroAnc bits anc y` target shape, by contrast, demands:

* Data positions `0..bits-1`: bit `bits-1-i` of `y` at position `i`
  (big-endian decoding via `nat_to_funbool`).
* Ancilla positions `bits..bits+anc-1`: all false.

These two layouts overlap: position `bits-1` is simultaneously
the LSB of the encodeDataZeroAnc shape AND the LSB of the
Cuccaro accumulator (when `bits - 1 = q_start + 1 = 3`, i.e.
`bits = 4`). More generally, the SWAP loader's "data even
position" `bits - 1 - 2*k` is below `q_start = 2` for the highest
windows.

This review proves that a literal inverse-SWAP unloader (applying the
same swaps as the loader in reverse order) restores the **original `x`
window bits** into the data positions and moves the accumulator bits
into the ancilla `b0Idx/b1Idx` positions. That is the wrong direction
for the `encodeDataZeroAnc` shape — it requires `y` at data positions
and `false` at ancilla positions.

The diagnostic theorem below proves this for the simplest non-trivial
case (`numWin = 1`, position `bits - 1`): the inverse-SWAP unloader
produces `windowed2_b0_of_x x 0` at position `bits - 1`, regardless of
the accumulator value `y`. This is sufficient evidence to redesign the
R7d^xxix-L reverse adapter as reversible cleanup rather than reverse
SWAP. -/

/-- **Candidate reverse-SWAP unloader (diagnostic only).** Same swap
operations as `windowedSwapLoadAdapter`, but applied in reverse order:
for `n + 1`, first apply the window-`n` swaps, then recurse on `n`.
Since `qubit_swap` is involutive, applying both loader and unloader
sequentially to disjoint swap positions gives identity. However, the
unloader applied to the post-K state does NOT clean back to
`encodeDataZeroAnc y` — see the diagnostic theorem below. -/
noncomputable def windowedSwapUnloadAdapterDiag
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * n) (b0Idx n))
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - (2 * n + 1)) (b1Idx n)))
        (windowedSwapUnloadAdapterDiag bits b0Idx b1Idx n)

/-- **DIAGNOSTIC — reverse-SWAP unloader pulls `x` bit back into data
position.** For `numWin = 1`, applying the candidate reverse-SWAP
unloader to the post-K windowed input state (with arbitrary accumulator
`y`) gives at the data position `bits - 1` the original `x` bit
`windowed2_b0_of_x x 0 = x.testBit 0`, NOT a bit of the accumulator
`y`. The accumulator's bit 0 (which was at position `bits - 1` in the
specific case `bits = 4` since `q_start + 1 = 3`) is lost — it gets
moved to position `b0Idx 0` (the ancilla position that
`encodeDataZeroAnc` requires to be false).

This shows the inverse-SWAP approach is INVALID for projecting back to
the `encodeDataZeroAnc y` shape required by `gateMCP_apply_encode`. -/
theorem unloadDiag_data_msb_reads_old_x_at_numWin_1
    (bits y x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hbits : 2 ≤ bits)
    (h_b0_above : bits ≤ b0Idx 0)
    (h_b1_above : bits ≤ b1Idx 0)
    (h_b0_ne_b1 : b0Idx 0 ≠ b1Idx 0) :
    Gate.applyNat (windowedSwapUnloadAdapterDiag bits b0Idx b1Idx 1)
        (windowed2Input y b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) 1)
        (bits - 1)
      = windowed2_b0_of_x x 0 := by
  -- Unfold unload at numWin = 1 and compute through the SWAP applies.
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * 0) (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - (2 * 0 + 1)) (b1Idx 0)))
        (windowedSwapUnloadAdapterDiag bits b0Idx b1Idx 0))
      _ (bits - 1) = _
  -- Normalize indices.
  have hidx0 : bits - 1 - 2 * 0 = bits - 1 := by omega
  have hidx1 : bits - 1 - (2 * 0 + 1) = bits - 2 := by omega
  rw [hidx0, hidx1]
  -- Unfold the recursion base.
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1) (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap (bits - 2) (b1Idx 0)))
        Gate.I)
      _ (bits - 1) = _
  -- Apply Gate.applyNat_seq three times.
  simp only [Gate.applyNat_seq, Gate.applyNat_I]
  -- Now we have:
  --   applyNat (swap (bits-2) (b1Idx 0))
  --     (applyNat (swap (bits-1) (b0Idx 0)) s) (bits - 1)
  -- where s is the windowed2Input state.
  -- Disjointness facts:
  have h_b0_ne_msb : b0Idx 0 ≠ bits - 1 := by omega
  have h_b1_ne_msb : b1Idx 0 ≠ bits - 1 := by omega
  have h_msb_ne_msb2 : bits - 1 ≠ bits - 2 := by omega
  have h_msb_ne_b0 : bits - 1 ≠ b0Idx 0 := fun h => h_b0_ne_msb h.symm
  have h_msb_ne_b1 : bits - 1 ≠ b1Idx 0 := fun h => h_b1_ne_msb h.symm
  have h_msb2_ne_b1 : bits - 2 ≠ b1Idx 0 := by omega
  -- Step 1: rewrite the inner swap.
  rw [FormalRV.BQAlgo.qubit_swap_correct (bits - 1) (b0Idx 0) _ h_msb_ne_b0]
  -- Step 2: rewrite the outer swap.
  rw [FormalRV.BQAlgo.qubit_swap_correct (bits - 2) (b1Idx 0) _ h_msb2_ne_b1]
  -- Read at position bits - 1.
  -- The outermost update is at b1Idx 0; skip via h_msb_ne_b1.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_msb_ne_b1]
  -- The middle update is at (bits - 2); skip via h_msb_ne_msb2.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_msb_ne_msb2]
  -- The next update is at b0Idx 0; skip via h_msb_ne_b0.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_msb_ne_b0]
  -- The innermost update is at (bits - 1); take its assigned value
  -- which is s (b0Idx 0).
  rw [FormalRV.Framework.update_eq _ _ _]
  -- Now reduce the windowed2Input read at b0Idx 0.
  rw [windowed2Input_succ_read_b0 y b0Idx b1Idx
        (windowed2_b0_of_x x) (windowed2_b1_of_x x) 0 h_b0_ne_b1]

/-- **DIAGNOSTIC corollary — accumulator bit lost.** The inverse-SWAP
unloader on the post-K state places the accumulator's LSB at position
`b0Idx 0` (an ancilla position required to be false in
`encodeDataZeroAnc` form). This is the symmetric witness: the data
position is wrong AND the ancilla position is dirty. Stated for
`numWin = 1` and the specific case `bits = 4` where the accumulator
bit 0 lives at position `bits - 1 = 3`. -/
theorem unloadDiag_ancilla_receives_acc_at_numWin_1_bits_4
    (y x : Nat) (b0Idx b1Idx : Nat → Nat)
    (h_b0_above : 4 ≤ b0Idx 0)
    (h_b1_above : 4 ≤ b1Idx 0)
    (h_b0_ne_b1 : b0Idx 0 ≠ b1Idx 0) :
    Gate.applyNat (windowedSwapUnloadAdapterDiag 4 b0Idx b1Idx 1)
        (windowed2Input y b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) 1)
        (b0Idx 0)
      = y.testBit 0 := by
  -- Unfold unload at numWin = 1 with bits = 4.
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (4 - 1 - 2 * 0) (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap (4 - 1 - (2 * 0 + 1)) (b1Idx 0)))
        (windowedSwapUnloadAdapterDiag 4 b0Idx b1Idx 0))
      _ (b0Idx 0) = _
  -- Normalize indices: bits - 1 = 3, bits - 2 = 2.
  have hidx0 : (4 : Nat) - 1 - 2 * 0 = 3 := by decide
  have hidx1 : (4 : Nat) - 1 - (2 * 0 + 1) = 2 := by decide
  rw [hidx0, hidx1]
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap 3 (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap 2 (b1Idx 0)))
        Gate.I)
      _ (b0Idx 0) = _
  simp only [Gate.applyNat_seq, Gate.applyNat_I]
  have h_3_ne_b0 : (3 : Nat) ≠ b0Idx 0 := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx 0 := by omega
  have h_b0_ne_3 : b0Idx 0 ≠ 3 := fun h => h_3_ne_b0 h.symm
  have h_b0_ne_2 : b0Idx 0 ≠ 2 := by omega
  have h_b0_ne_b1' : b0Idx 0 ≠ b1Idx 0 := h_b0_ne_b1
  -- Step 1: rewrite the inner swap (3 ↔ b0Idx 0).
  rw [FormalRV.BQAlgo.qubit_swap_correct 3 (b0Idx 0) _ h_3_ne_b0]
  -- Step 2: rewrite the outer swap (2 ↔ b1Idx 0).
  rw [FormalRV.BQAlgo.qubit_swap_correct 2 (b1Idx 0) _ h_2_ne_b1]
  -- Read at position b0Idx 0:
  -- Outermost update at b1Idx 0; skip via h_b0_ne_b1.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1']
  -- Next update at 2; skip via h_b0_ne_2.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_2]
  -- Next update at b0Idx 0; take its value via update_eq.
  rw [FormalRV.Framework.update_eq _ _ _]
  -- Now the value is s (bits - 1) where the original swap read it from
  -- position bits - 1 = 3 in s.
  -- s at position 3: cuccaro accumulator bit 0 since
  --   q_start = 2, q - q_start = 1, b.testBit 0 = y.testBit 0.
  -- We use windowed2Input_succ to strip the two ancilla updates,
  -- then cuccaro_input_F_at_b for the accumulator readout.
  -- The state is windowed2Input y b0Idx b1Idx ... 1, expand:
  rw [windowed2Input_succ]
  -- Outer update at b1Idx 0 ≠ 3.
  have h_3_ne_b1 : (3 : Nat) ≠ b1Idx 0 := by omega
  rw [FormalRV.Framework.update_neq _ _ _ _ h_3_ne_b1]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_3_ne_b0]
  -- Inner: windowed2Input y _ _ _ _ 0 = cuccaro_input_F 2 false 0 y.
  rw [windowed2Input_zero]
  -- cuccaro_input_F 2 false 0 y 3 = y.testBit 0 since 3 = q_start + 2*0 + 1.
  have h_b : cuccaro_input_F 2 false 0 y 3 = y.testBit 0 := by
    rw [show (3 : Nat) = 2 + 2 * 0 + 1 from by rfl]
    exact cuccaro_input_F_at_b 2 0 false 0 y
  exact h_b

/-! ## Phase R7d^xxix-L-DESIGN-LOCK — overlap diagnostics for the
naive cuccaroBitsToDataSwap proposal

After R7d^xxix-L-REVIEW showed the reverse-SWAP unloader is invalid,
the proposed next architecture was Option C: K-stage + a separate
"Cuccaro→Data SWAP" cascade swapping accumulator bits at Cuccaro
b-bit positions `2*n + 3` into official data positions `bits - 1 - n`.

This section proves the proposed independent SWAP cascade is ALSO
invalid in its naive form — the source-position set
`{2*n + 3 : n < bits}` and destination-position set
`{bits - 1 - n : n < bits}` are NOT disjoint, so a sequential
independent SWAP cascade would either (a) include `qubit_swap p p`
calls (violating the well-typed precondition `a ≠ b`) or (b) overwrite
earlier swaps' outputs.

The key facts: at `bits = 4`, the very first swap `qubit_swap 3 3` is
malformed; at `bits = 10`, there are multiple cross-index overlaps. -/

/-- Cuccaro b-bit (accumulator) position for window index `n`. -/
def cuccaroBPos (n : Nat) : Nat := 2 * n + 3

/-- Official `encodeDataZeroAnc` data position for window index `n`
(under the `bits - 1 - n` big-endian mapping). -/
def dataPos (bits n : Nat) : Nat := bits - 1 - n

/-- **Coincidence characterization (key arithmetic fact).** The
Cuccaro accumulator's `n`-th b-bit position coincides with the official
data register's `n`-th big-endian position exactly when `bits = 3*n + 4`.
Proof: `omega` on the Nat subtractions. -/
theorem cuccaroBPos_dataPos_eq_iff (bits n : Nat) :
    cuccaroBPos n = dataPos bits n ↔ bits = 3 * n + 4 := by
  unfold cuccaroBPos dataPos
  omega

/-- **`bits = 4` diagnostic.** At the smallest interesting width
(`bits = 4`, satisfying `2 * numWin = bits` with `numWin = 2`), the
window-0 source `cuccaroBPos 0 = 3` and window-0 destination
`dataPos 4 0 = 3` are EQUAL. A `qubit_swap 3 3` is malformed because
`qubit_swap_correct` requires `a ≠ b`. -/
theorem cuccaroBitsToDataSwap_invalid_at_bits_4 :
    cuccaroBPos 0 = dataPos 4 0 := by
  rfl

/-- **`bits = 10` cross-index overlap diagnostic.** Even when window-0
source and destination are distinct (e.g., for `bits = 10`,
`cuccaroBPos 0 = 3` vs `dataPos 10 0 = 9`), other window indices
create cross-collisions: window-1 source coincides with window-4
destination, and window-2 source coincides with window-2 destination
(the diagonal case `bits = 3*n + 4` at `n = 2`, `bits = 10`).
A naive sequential cascade would produce either malformed swaps or
incorrect overwrites. -/
theorem cuccaroBitsToDataSwap_overlap_bits10 :
    cuccaroBPos 1 = dataPos 10 4 ∧
    cuccaroBPos 2 = dataPos 10 2 := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- **Verdict: Cuccaro accumulator positions overlap data positions in
general.** The set `{cuccaroBPos n : n < bits}` (positions
`{3, 5, 7, …, 2*bits + 1}`) and the set `{dataPos bits n : n < bits}`
(positions `{0, 1, 2, …, bits - 1}`) share all odd integers in
`[3, bits - 1]` — i.e., for every `bits ≥ 4`, there is at least one
shared position.

Specifically, for `bits = 4`: shared = `{3}`; for `bits = 6`: shared
= `{3, 5}`; for `bits = 10`: shared = `{3, 5, 7, 9}`.

The "Cuccaro→Data SWAP" cascade therefore cannot be specified as a
naive sequence of independent SWAPs. The fix requires either:
- a permutation network (multiple non-independent swap chains), or
- shifting the Cuccaro workspace ABOVE the official data register
  (Option C2 in the design note). -/
theorem cuccaroBPos_in_data_range (n bits : Nat)
    (h : 2 * n + 3 < bits) :
    cuccaroBPos n < bits := by
  unfold cuccaroBPos
  omega

end Windowed
end VerifiedShor
