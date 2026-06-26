/- WindowedSwapLoaderWithDataClear — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.WindowedLoaderBitExtraction

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xxvi — multi-window selected-add fold correctness

Closes the multi-window correctness theorem: the sequence of
`windowed2SelectedAddGate` applications implements the iterated
`windowedStepSpecIter2`.

Strategy: prove a **prefix theorem** with separate parameters `m`
(number of gates applied) and `totalWin` (size of the input window
encoding), then specialize `m = totalWin = numWin`. -/

/-- **Prefix theorem.** Applying the first `m` selected-add gates of
the windowSize=2 toy implementation to a `totalWin`-window input
encoding produces the same input shape with the accumulator advanced
by `windowedStepSpecIter2 ... m acc`.

Proven by induction on `m`. Base case uses `Gate.applyNat_I`. Step
case applies the IH to expose the intermediate accumulator, derives
its `< N` bound via `windowedStepSpecIter2_lt_N`, then applies
`toyWindow2SelectedAddGate_on_windowed2Input` at `k = n` and
reduces via `windowedStepSpecIter2_succ`. -/
theorem toyWindowed2SelectedAddGate_correct_prefix
    (bits N a flagIdx m totalWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (hm_le : m ≤ totalWin)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < totalWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < totalWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < totalWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < totalWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < totalWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
          bits flagIdx b0Idx b1Idx m)
        (windowed2Input acc b0Idx b1Idx b0 b1 totalWin)
      = windowed2Input
          (windowedStepSpecIter2 a N b0 b1 m acc)
          b0Idx b1Idx b0 b1 totalWin := by
  induction m with
  | zero =>
    rw [windowed2SelectedAddGate_zero, windowedStepSpecIter2_zero]
    exact Gate.applyNat_I _
  | succ n ih =>
    have hn_lt : n < totalWin :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hm_le
    have hn_le : n ≤ totalWin := Nat.le_of_lt hn_lt
    rw [windowed2SelectedAddGate_succ, Gate.applyNat_seq, ih hn_le]
    -- After IH: goal is
    --   Gate.applyNat ((toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec.gate
    --                    bits n flagIdx (b0Idx n) (b1Idx n))
    --       (windowed2Input (windowedStepSpecIter2 ... n acc) b0Idx b1Idx b0 b1 totalWin)
    --     = windowed2Input (windowedStepSpecIter2 ... (n+1) acc) b0Idx b1Idx b0 b1 totalWin
    -- The spec's gate is definitionally toyWindow2SelectedAddGate (via the
    -- toSelectedAddSpec conversion and the impl's gate field).
    have hacc_n : windowedStepSpecIter2 a N b0 b1 n acc < N :=
      windowedStepSpecIter2_lt_N a N b0 b1 n acc hN_pos hacc
    show Gate.applyNat
            (toyWindow2SelectedAddGate bits N a n flagIdx (b0Idx n) (b1Idx n))
            (windowed2Input (windowedStepSpecIter2 a N b0 b1 n acc)
              b0Idx b1Idx b0 b1 totalWin)
       = windowed2Input (windowedStepSpecIter2 a N b0 b1 (n + 1) acc)
           b0Idx b1Idx b0 b1 totalWin
    rw [toyWindow2SelectedAddGate_on_windowed2Input bits N a n
          (windowedStepSpecIter2 a N b0 b1 n acc) flagIdx totalWin
          b0Idx b1Idx b0 b1
          hbits hN_pos hN hN2 hacc_n hn_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
    rw [windowedStepSpecIter2_succ]

/-- **R7d^xxvi — toy multi-window selected-add correctness.**

The full `numWin`-window selected-add fold (applying the toy
implementation's selected-add gate at each window index `0, …, numWin
- 1`) on an input of the same window size produces the input shape
with the accumulator advanced by `windowedStepSpecIter2`.

Specialization of the prefix theorem at `m = totalWin = numWin`. -/
theorem toyWindowed2SelectedAddGate_correct
    (bits N a flagIdx numWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
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
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
          bits flagIdx b0Idx b1Idx numWin)
        (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = windowed2Input
          (windowedStepSpecIter2 a N b0 b1 numWin acc)
          b0Idx b1Idx b0 b1 numWin :=
  toyWindowed2SelectedAddGate_correct_prefix bits N a flagIdx numWin numWin acc
    b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc (Nat.le_refl numWin)
    h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1

/-! ## Phase R7d^xxvii — arithmetic aggregation

Pure arithmetic stack connecting `windowedStepSpecIter2` to modular
multiplication semantics:
- Stage 1: `windowed2Value` decodes the multiplier value from
  window bits.
- Stage 2: `windowed2TableSum` is the running sum of per-window
  `tableValue`s.
- Stage 3: `windowedStepSpecIter2 ... = (acc + windowed2TableSum ...) % N`.
- Stage 4: `windowed2TableSum ... ≡ a * windowed2Value ... (mod N)`.
- Stage 5: `windowedStepSpecIter2 ... = (acc + a * windowed2Value ...) % N`.
- Stretch: `cuccaro_target_val ∘ Gate.applyNat ... = (acc + a * x) % N`. -/

/-- **Decoded multiplier value.** Sums `windowBits2_at b0 b1 k * 4^k`
over windows `k = 0, …, numWin - 1`. This is the integer encoded by
the per-window bits in the natural window-size-2 binary decoding. -/
def windowed2Value (b0 b1 : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => windowed2Value b0 b1 n + windowBits2_at b0 b1 n * 2^(n * 2)

@[simp] theorem windowed2Value_zero (b0 b1 : Nat → Bool) :
    windowed2Value b0 b1 0 = 0 := rfl

@[simp] theorem windowed2Value_succ (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Value b0 b1 (n + 1)
      = windowed2Value b0 b1 n + windowBits2_at b0 b1 n * 2^(n * 2) := rfl

/-- **Running sum of per-window `tableValue`s.** Matches the
recursion of `windowedStepSpecIter2`. -/
def windowed2TableSum
    (a N : Nat) (b0 b1 : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      windowed2TableSum a N b0 b1 n + tableValue a N 2 n (windowBits2_at b0 b1 n)

@[simp] theorem windowed2TableSum_zero (a N : Nat) (b0 b1 : Nat → Bool) :
    windowed2TableSum a N b0 b1 0 = 0 := rfl

@[simp] theorem windowed2TableSum_succ
    (a N : Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2TableSum a N b0 b1 (n + 1)
      = windowed2TableSum a N b0 b1 n
        + tableValue a N 2 n (windowBits2_at b0 b1 n) := rfl

/-- **Stage 3.** The iterated step spec aggregates to the running
table sum modulo N. Requires `acc < N` for the base case (so that
`acc % N = acc`). -/
theorem windowedStepSpecIter2_eq_acc_plus_tableSum_mod
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc
      = (acc + windowed2TableSum a N b0 b1 numWin) % N := by
  induction numWin with
  | zero =>
    rw [windowedStepSpecIter2_zero, windowed2TableSum_zero, Nat.add_zero]
    exact (Nat.mod_eq_of_lt hacc).symm
  | succ n ih =>
    rw [windowedStepSpecIter2_succ]
    show (windowedStepSpecIter2 a N b0 b1 n acc
            + tableValue a N 2 n (windowBits2_at b0 b1 n)) % N
       = (acc + windowed2TableSum a N b0 b1 (n + 1)) % N
    rw [ih, windowed2TableSum_succ]
    -- Goal: ((acc + ws_n) % N + tv) % N
    --     = (acc + (ws_n + tv)) % N
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_assoc]

/-- **Stage 4.** The running table sum is congruent to
`a * windowed2Value` modulo `N`. -/
theorem windowed2TableSum_mod_eq_mul_windowed2Value_mod
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin : Nat) :
    windowed2TableSum a N b0 b1 numWin % N
      = (a * windowed2Value b0 b1 numWin) % N := by
  induction numWin with
  | zero => simp
  | succ n ih =>
    rw [windowed2TableSum_succ, windowed2Value_succ]
    -- LHS: (windowed2TableSum n + tableValue) % N
    -- RHS: (a * (windowed2Value n + v_n * 2^(n*2))) % N
    conv_lhs => rw [Nat.add_mod, ih, ← Nat.add_mod]
    rw [Nat.mul_add]
    -- LHS: (a * windowed2Value n + tableValue) % N
    -- RHS: (a * windowed2Value n + a * (v_n * 2^(n*2))) % N
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    -- Need: tableValue % N = (a * (v_n * 2^(n*2))) % N
    congr 1
    congr 1
    unfold tableValue
    rw [Nat.mod_mod]
    -- Goal: (a * 2^(n*2) * v_n) % N = (a * (v_n * 2^(n*2))) % N
    -- Up to multiplication commutativity / associativity.
    rw [Nat.mul_assoc, Nat.mul_comm (2^(n * 2))]

/-- **Stage 5.** The iterated step spec equals `acc + a * x` modulo
`N`, where `x = windowed2Value b0 b1 numWin` is the multiplier value
decoded from the window bits. -/
theorem windowedStepSpecIter2_eq_mul_mod
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc
      = (acc + a * windowed2Value b0 b1 numWin) % N := by
  rw [windowedStepSpecIter2_eq_acc_plus_tableSum_mod a N b0 b1 numWin acc
        hN_pos hacc]
  conv_lhs => rw [Nat.add_mod, windowed2TableSum_mod_eq_mul_windowed2Value_mod,
                  ← Nat.add_mod]

/-- **Bounded target extraction.** Variant of
`cuccaro_target_val_windowed2Input` where the high-index hypotheses
are bounded by `i < numWin` rather than universal. Required for the
circuit-facing corollary below — the main theorem's hypotheses are
bounded. -/
theorem cuccaro_target_val_windowed2Input_bounded
    (bits acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (numWin : Nat)
    (hacc_bits : acc < 2^bits)
    (h_hi0 : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b1Idx k) :
    cuccaro_target_val bits 2 (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = acc := by
  induction numWin with
  | zero =>
    rw [windowed2Input_zero]
    exact cuccaro_target_val_input bits 2 0 acc false hacc_bits
  | succ n ih =>
    have hn_lt : n < n + 1 := Nat.lt_succ_self n
    rw [windowed2Input_succ]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b1Idx n) (b1 n) _
          (Or.inr (h_hi1 n hn_lt))]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b0Idx n) (b0 n) _
          (Or.inr (h_hi0 n hn_lt))]
    exact ih
      (fun k hk => h_hi0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_hi1 k (Nat.lt_succ_of_lt hk))

/-- **Circuit-facing corollary.** The full multi-window selected-add
target accumulator implements `(acc + a * x) % N` where `x` is the
window-encoded multiplier. Composes the per-tick R7d^xxvi correctness
with the arithmetic aggregation. -/
theorem toyWindowed2SelectedAddGate_target_mul_correct
    (bits N a flagIdx numWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
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
    cuccaro_target_val bits 2
        (Gate.applyNat
          (windowed2SelectedAddGate
            (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
            bits flagIdx b0Idx b1Idx numWin)
          (windowed2Input acc b0Idx b1Idx b0 b1 numWin))
      = (acc + a * windowed2Value b0 b1 numWin) % N := by
  rw [toyWindowed2SelectedAddGate_correct bits N a flagIdx numWin acc
        b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc
        h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  have h_iter_lt : windowedStepSpecIter2 a N b0 b1 numWin acc < N :=
    windowedStepSpecIter2_lt_N a N b0 b1 numWin acc hN_pos hacc
  have h_iter_lt_pow : windowedStepSpecIter2 a N b0 b1 numWin acc < 2^bits :=
    Nat.lt_of_lt_of_le h_iter_lt hN
  rw [cuccaro_target_val_windowed2Input_bounded bits
        (windowedStepSpecIter2 a N b0 b1 numWin acc)
        b0Idx b1Idx b0 b1 numWin h_iter_lt_pow h_hi0 h_hi1]
  exact windowedStepSpecIter2_eq_mul_mod a N b0 b1 numWin acc hN_pos hacc


end Windowed
end VerifiedShor
