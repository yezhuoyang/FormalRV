import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.WindowedLoaderBitExtraction

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

/-! ## Phase R7d^xxviii — multi-window multiply-add spec interface

Packages the verified window-size-2 multi-window multiply-add
primitive into a reusable spec record. Defines a stronger state-level
correctness theorem (combining R7d^xxvi's
`toyWindowed2SelectedAddGate_correct` with R7d^xxvii's
`windowedStepSpecIter2_eq_mul_mod`) and provides a concrete toy
implementation.

**Interface inspection summary** (for next-tick wiring):

| Existing interface | Level | Suitable here? |
| --- | --- | --- |
| `Window2SelectedAddSpec` | per-window gate spec | too narrow (single window) |
| `Window2SelectedAddStateSpec` | per-window gate state-eq spec | too narrow (single window) |
| `WindowedLookupModMulSpec` | pure arithmetic, no gate field | doesn't capture circuit-level result |
| `ControlledModAddImpl` | single mod-add gate | wrong abstraction (no window decoding) |
| `ModMulImpl` (SQIRPort) | full QState/BaseUCom | too high-level — Shor oracle, not Gate IR |
| `VerifiedModMulFamily` | full oracle family + QPE wiring | far too high-level |

None of the existing records cleanly captures the **Gate-level
multi-window multiply-add** primitive we've verified. The new
`Window2MulAddSpec` (below) sits between `Window2SelectedAddStateSpec`
(per-window) and `WindowedLookupModMulSpec` (pure arithmetic), and is
the natural composition target for both. -/

/-- **Full-state multiply-add correctness.** Composes
`toyWindowed2SelectedAddGate_correct` (R7d^xxvi) with
`windowedStepSpecIter2_eq_mul_mod` (R7d^xxvii) to give the gate's
output as a `windowed2Input` with the accumulator advanced by
`(acc + a * x) % N`, where `x` is the window-encoded multiplier.

This is the state-level analog of
`toyWindowed2SelectedAddGate_target_mul_correct`. -/
theorem toyWindowed2SelectedAddGate_state_mul_correct
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
          ((acc + a * windowed2Value b0 b1 numWin) % N)
          b0Idx b1Idx b0 b1 numWin := by
  rw [toyWindowed2SelectedAddGate_correct bits N a flagIdx numWin acc
        b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc
        h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  rw [windowedStepSpecIter2_eq_mul_mod a N b0 b1 numWin acc hN_pos hacc]

/-- **`Window2MulAddSpec`**: a spec contract for a Gate-level
windowSize=2 multi-window multiply-add primitive.

An implementation provides:
- `gate`: the composed multi-window gate.
- `input`: the input state encoding (accumulator + window bits).
- `decodeX`: the multiplier decoded from window bits.
- `stateCorrect`: full-state correctness — gate(input(acc)) =
  input((acc + a*x) % N).
- `targetCorrect`: target-decode correctness —
  cuccaro_target_val ∘ gate ∘ input = (acc + a*x) % N.

This is the natural composition target for downstream multi-step
multiplier/exponentiator constructions. -/
structure Window2MulAddSpec (a N : Nat) where
  /-- The composed multi-window multiply-add gate. -/
  gate :
    (bits flagIdx numWin : Nat) →
    (b0Idx b1Idx : Nat → Nat) →
    Gate
  /-- The input state encoding (accumulator + window bits installed). -/
  input :
    (acc : Nat) →
    (b0Idx b1Idx : Nat → Nat) →
    (b0 b1 : Nat → Bool) →
    Nat → (Nat → Bool)
  /-- The multiplier value decoded from the window bits. -/
  decodeX : (b0 b1 : Nat → Bool) → Nat → Nat
  /-- **State-level correctness.** Gate transforms `input(acc)` to
  `input((acc + a * decodeX) % N)`. -/
  stateCorrect :
    ∀ (bits flagIdx numWin acc : Nat)
      (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i) →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ flagIdx) →
      (∀ i, i < numWin → b1Idx i ≠ flagIdx) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) →
      Gate.applyNat (gate bits flagIdx numWin b0Idx b1Idx)
          (input acc b0Idx b1Idx b0 b1 numWin)
        = input ((acc + a * decodeX b0 b1 numWin) % N)
            b0Idx b1Idx b0 b1 numWin
  /-- **Target-decode correctness.** `cuccaro_target_val` extracts
  `(acc + a * decodeX) % N` from the gate's output. -/
  targetCorrect :
    ∀ (bits flagIdx numWin acc : Nat)
      (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i) →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ flagIdx) →
      (∀ i, i < numWin → b1Idx i ≠ flagIdx) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) →
      cuccaro_target_val bits 2
          (Gate.applyNat (gate bits flagIdx numWin b0Idx b1Idx)
            (input acc b0Idx b1Idx b0 b1 numWin))
        = (acc + a * decodeX b0 b1 numWin) % N

/-- **Toy multi-window multiply-add spec implementation.** Wraps the
windowSize=2 CCX-based multi-window selected-add stack as a concrete
`Window2MulAddSpec` instance. -/
noncomputable def toyWindow2MulAddSpecImpl (a N : Nat) :
    Window2MulAddSpec a N where
  gate := fun bits flagIdx numWin b0Idx b1Idx =>
            windowed2SelectedAddGate
              (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
              bits flagIdx b0Idx b1Idx numWin
  input := windowed2Input
  decodeX := windowed2Value
  stateCorrect := fun bits flagIdx numWin acc b0Idx b1Idx b0 b1
                      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                      h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag
                      h_b1_ne_flag h_distinct_b0_b0 h_distinct_b0_b1
                      h_distinct_b1_b0 h_distinct_b1_b1 =>
    toyWindowed2SelectedAddGate_state_mul_correct bits N a flagIdx numWin acc
      b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
      h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
      h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1
  targetCorrect := fun bits flagIdx numWin acc b0Idx b1Idx b0 b1
                       hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                       h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag
                       h_b1_ne_flag h_distinct_b0_b0 h_distinct_b0_b1
                       h_distinct_b1_b0 h_distinct_b1_b1 =>
    toyWindowed2SelectedAddGate_target_mul_correct bits N a flagIdx numWin acc
      b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
      h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
      h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1

/-! ## Phase R7d^xxix-B — windowed loader adapter (bit extraction + gate)

First sub-step toward bridging the windowed multiply-add primitive
to the `encodeDataZeroAnc` shape consumed by the existing
`gateMCP_apply_encode` seam (R7d^xxix-A map).

Adds:
- Per-window bit-extraction functions `windowed2_b0_of_x`,
  `windowed2_b1_of_x` (LSB-first decoding of `x`).
- Arithmetic decoding theorem `windowed2Value_of_x_mod`.
- The loader gate `windowedLoadAdapter` (recursive on `numWin`).
- Loader zero/succ unfold simp lemmas.
- The frame property `windowedLoadAdapter_preserves_disjoint` (loader
  preserves any position disjoint from all `b0Idx(k)`, `b1Idx(k)`).

The full apply-to-`encodeDataZeroAnc` theorem (which reads x out of
the data register and writes window bits) is deferred to R7d^xxix-C
because it requires careful big-endian / little-endian bit-position
bookkeeping. -/

/-- The `k`-th LSB-first window-bit decoder for `b0`: returns bit
`2 * k` of `x`. -/
def windowed2_b0_of_x (x : Nat) : Nat → Bool :=
  fun k => x.testBit (2 * k)

/-- The `k`-th LSB-first window-bit decoder for `b1`: returns bit
`2 * k + 1` of `x`. -/
def windowed2_b1_of_x (x : Nat) : Nat → Bool :=
  fun k => x.testBit (2 * k + 1)

/-- Arithmetic helper: `2^(2*k) = 4^k`. -/
theorem two_pow_two_mul (k : Nat) : 2^(2 * k) = 4^k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, ih]
    rfl

/-- The decoded 2-bit window value at window `k` extracted from `x`. -/
theorem windowBits2_at_of_x (x k : Nat) :
    windowBits2_at (windowed2_b0_of_x x) (windowed2_b1_of_x x) k
      = (x / 4^k) % 4 := by
  unfold windowBits2_at windowBits2_to_v
    windowed2_b0_of_x windowed2_b1_of_x
  rw [Nat.toNat_testBit, Nat.toNat_testBit]
  -- Goal: x / 2^(2*k) % 2 + 2 * (x / 2^(2*k+1) % 2) = x / 4^k % 4
  have h4k : 2^(2 * k) = 4^k := two_pow_two_mul k
  have h4k1 : 2^(2 * k + 1) = 2 * 4^k := by
    rw [pow_succ, h4k]; ring
  rw [h4k, h4k1]
  -- Goal: x / 4^k % 2 + 2 * (x / (2 * 4^k) % 2) = x / 4^k % 4
  have h_div : x / (2 * 4^k) = (x / 4^k) / 2 := by
    rw [Nat.div_div_eq_div_mul]; congr 1; ring
  rw [h_div]
  -- Goal: y % 2 + 2 * (y / 2 % 2) = y % 4 where y = x / 4^k
  omega

/-- **Arithmetic decoding theorem.** The multi-window value decoded
from `x`'s bits via `windowed2_b0_of_x` / `windowed2_b1_of_x` is
`x mod 2^(2 * numWin)`. When `x < 2^(2 * numWin)`, this equals `x`
itself. -/
theorem windowed2Value_of_x_mod (x numWin : Nat) :
    windowed2Value (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin
      = x % 2^(2 * numWin) := by
  induction numWin with
  | zero =>
    rw [windowed2Value]
    rw [show 2 * 0 = 0 from rfl, pow_zero]
    exact (Nat.mod_one x).symm
  | succ n ih =>
    rw [windowed2Value_succ, ih, windowBits2_at_of_x]
    have h_4n : 2^(2 * n) = 4^n := two_pow_two_mul n
    have h_n2 : 2^(n * 2) = 4^n := by rw [Nat.mul_comm n 2]; exact two_pow_two_mul n
    have h_4n1 : 2^(2 * (n + 1)) = 4^n * 4 := by
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, h_4n]
      norm_num
    rw [h_4n, h_n2, h_4n1, Nat.mod_mul]
    -- Goal: x % 4^n + (x / 4^n) % 4 * 4^n = x % 4^n + 4^n * ((x / 4^n) % 4)
    ring

/-- **Loader gate** (recursive on `numWin`). Installs window `n`'s
b0/b1 bits at positions `b0Idx n`, `b1Idx n` by `CX`-copying from the
big-endian data register positions `bits - 1 - 2*n` and `bits - 2 - 2*n`.

Definition is parameterized by `bits` (data register width) and
`b0Idx`, `b1Idx` (window-bit ancilla position functions). Base case
is `Gate.I`; step case appends two `CX` gates to install the n-th
window's bits. -/
noncomputable def windowedLoadAdapter
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (windowedLoadAdapter bits b0Idx b1Idx n)
        (Gate.seq
          (Gate.CX (bits - 1 - 2 * n) (b0Idx n))
          (Gate.CX (bits - 1 - (2 * n + 1)) (b1Idx n)))

/-- Zero-window loader is the identity. -/
@[simp] theorem windowedLoadAdapter_zero
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowedLoadAdapter bits b0Idx b1Idx 0 = Gate.I := rfl

/-- Successor-window loader appends two `CX` gates to the prefix. -/
@[simp] theorem windowedLoadAdapter_succ
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowedLoadAdapter bits b0Idx b1Idx (n + 1)
      = Gate.seq
          (windowedLoadAdapter bits b0Idx b1Idx n)
          (Gate.seq
            (Gate.CX (bits - 1 - 2 * n) (b0Idx n))
            (Gate.CX (bits - 1 - (2 * n + 1)) (b1Idx n))) := rfl

/-- **Frame property (preserves disjoint positions).** The loader
preserves any position `p` that's not a target of any of its CX gates
(i.e., `p ≠ b0Idx(k)` and `p ≠ b1Idx(k)` for all `k < numWin`).

In particular, this proves the loader preserves all data-register
bits and any ancilla outside the window-bit region. -/
theorem windowedLoadAdapter_preserves_disjoint
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (p : Nat) (numWin : Nat)
    (f : Nat → Bool)
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (windowedLoadAdapter bits b0Idx b1Idx numWin) f p = f p := by
  induction numWin generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [windowedLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_p_ne_b0n : p ≠ b0Idx n := h_p_ne_b0 n (Nat.lt_succ_self n)
    have h_p_ne_b1n : p ≠ b1Idx n := h_p_ne_b1 n (Nat.lt_succ_self n)
    rw [Gate.applyNat_CX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b1n]
    rw [Gate.applyNat_CX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b0n]
    -- Apply IH on the prefix.
    exact ih f
      (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-! ## Phase R7d^xxix-C — windowed loaded-state encoding

**Critical layout finding**: the windowed selected-add gate's Cuccaro
workspace (positions `[2, 2 + 2*bits + 1]`) OVERLAPS with the
`encodeDataZeroAnc` data register (positions `[0, bits)`) whenever
`bits ≥ 3`. Specifically, positions `[2, bits)` are simultaneously
data-register bits (containing `x`) AND Cuccaro workspace bits
(expected to be `c_in`/`a`/`b` initialization).

**Consequence for the bridge**: a CX-based copy loader leaves `x`'s
bits in the data register (positions `[0, bits)`). When the selected-add
gate then runs, it reads stale `x`-bits as Cuccaro workspace,
corrupting the multiply-add. So copy-based loading CANNOT bridge to
the existing `windowed2SelectedAddGate` correctness.

**The correct bridge** requires a SWAP-based adapter (analogous to the
existing `sqir_encode_to_mult_adapter`) that MOVES `x`'s bits from
data positions to window-bit positions, leaving the data register zero.
This is the natural continuation of the R7d^xxix-D work.

This phase still defines the loaded-state encoding produced by the
current CX loader (with `x` preserved in the data register) so that
the loader's apply theorem can be documented, and provides the readback
lemmas. The bridge to selected-add is deferred to the SWAP loader. -/

/-- **Windowed loaded-state encoding.** The state produced by the
CX-based loader: starts from `encodeDataZeroAnc bits anc x` (data
register holds `x`; ancillas are zero), then installs window bits
`x.testBit (2*k)` at `b0Idx k` and `x.testBit (2*k+1)` at `b1Idx k`
for `k < numWin`. Recursive on `numWin` to match the loader's
recursion structure. -/
def windowed2LoadedInput
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) :
    Nat → (Nat → Bool)
  | 0 => encodeDataZeroAnc bits anc x
  | n + 1 =>
      update
        (update (windowed2LoadedInput bits anc x b0Idx b1Idx n)
          (b0Idx n) (x.testBit (2 * n)))
        (b1Idx n) (x.testBit (2 * n + 1))

/-- Zero-window loaded state is the raw `encodeDataZeroAnc`. -/
@[simp] theorem windowed2LoadedInput_zero
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2LoadedInput bits anc x b0Idx b1Idx 0
      = encodeDataZeroAnc bits anc x := rfl

/-- Successor-window loaded state appends two updates installing
the n-th window's bits. -/
@[simp] theorem windowed2LoadedInput_succ
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowed2LoadedInput bits anc x b0Idx b1Idx (n + 1)
      = update
          (update (windowed2LoadedInput bits anc x b0Idx b1Idx n)
            (b0Idx n) (x.testBit (2 * n)))
          (b1Idx n) (x.testBit (2 * n + 1)) := rfl

/-- Latest-window readback for `b1Idx n`: returns
`x.testBit (2 * n + 1)`. -/
theorem windowed2LoadedInput_succ_read_b1
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowed2LoadedInput bits anc x b0Idx b1Idx (n + 1) (b1Idx n)
      = x.testBit (2 * n + 1) := by
  rw [windowed2LoadedInput_succ]
  exact FormalRV.Framework.update_eq _ _ _

/-- Latest-window readback for `b0Idx n`: returns `x.testBit (2 * n)`. -/
theorem windowed2LoadedInput_succ_read_b0
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat)
    (h_ne : b0Idx n ≠ b1Idx n) :
    windowed2LoadedInput bits anc x b0Idx b1Idx (n + 1) (b0Idx n)
      = x.testBit (2 * n) := by
  rw [windowed2LoadedInput_succ]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_ne]
  exact FormalRV.Framework.update_eq _ _ _

/-- **General `b0` readback.** For any window `k < numWin`, the
loaded state at `b0Idx k` returns `x.testBit (2 * k)`. -/
theorem windowed2LoadedInput_read_b0
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_distinct : ∀ i j, i ≠ j → b0Idx i ≠ b0Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2LoadedInput bits anc x b0Idx b1Idx numWin (b0Idx k)
      = x.testBit (2 * k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2LoadedInput_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k k)]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k n)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_distinct k n hkn)]
      exact ih hk_lt_n

/-- **General `b1` readback.** For any window `k < numWin`, the
loaded state at `b1Idx k` returns `x.testBit (2 * k + 1)`. -/
theorem windowed2LoadedInput_read_b1
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat) (hk : k < numWin)
    (h_b1_distinct : ∀ i j, i ≠ j → b1Idx i ≠ b1Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2LoadedInput bits anc x b0Idx b1Idx numWin (b1Idx k)
      = x.testBit (2 * k + 1) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2LoadedInput_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_distinct k n hkn)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm (h_b0_b1 n k))]
      exact ih hk_lt_n

/-- **Data-position preservation.** At any position `p` distinct from
all window-bit indices `b0Idx(k)`, `b1Idx(k)` (k < numWin), the loaded
state equals the underlying `encodeDataZeroAnc bits anc x`. In
particular, all data-register positions `[0, bits)` are preserved
when window indices are disjoint from data positions. -/
theorem windowed2LoadedInput_at_disjoint
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin p : Nat)
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    windowed2LoadedInput bits anc x b0Idx b1Idx numWin p
      = encodeDataZeroAnc bits anc x p := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2LoadedInput_succ]
    have h_p_ne_b0n : p ≠ b0Idx n := h_p_ne_b0 n (Nat.lt_succ_self n)
    have h_p_ne_b1n : p ≠ b1Idx n := h_p_ne_b1 n (Nat.lt_succ_self n)
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b0n]
    exact ih (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
             (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-! ### Layout conflict: bridge to selected-add NOT YET CLOSED

The selected-add gate's Cuccaro workspace `[2, 2 + 2*bits + 1]`
includes positions `[2, bits)` (when `bits ≥ 3`), which are also
data-register positions in `encodeDataZeroAnc`. After the CX-based
copy loader, those positions still hold `x`'s bits — NOT the
`cuccaro_input_F`-formatted workspace expected by the selected-add.

**This means the simple frame argument fails**:
`Gate.applyNat (selectedAdd) (windowed2LoadedInput ...) ≠
 windowed2LoadedInput ((acc + a*x) % N) ...`
because the selected-add reads stale `x`-bits as `c_in`/`a`/`b`,
producing incorrect output.

**Required for the bridge** (next ticks):
- **R7d^xxix-D**: Build a SWAP-based loader
  `windowedSwapLoadAdapter bits b0Idx b1Idx numWin` that MOVES
  `x`'s bits from `encodeDataZeroAnc` data positions to window-bit
  ancilla positions, leaving the data register zero.
- **R7d^xxix-E**: Prove the SWAP loader's apply theorem:
  `Gate.applyNat (windowedSwapLoadAdapter ...)
   (encodeDataZeroAnc bits anc x)
   = windowed2Input 0 b0Idx b1Idx (windowed2_b0_of_x x)
     (windowed2_b1_of_x x) numWin`.
  The output IS `windowed2Input`-shaped — so the existing selected-add
  correctness (`toyWindowed2SelectedAddGate_state_mul_correct`) chains
  directly.

The current `windowed2LoadedInput` + readback lemmas remain useful as
documentation of what the CX-loader produces, and may be reused as
building blocks for the SWAP loader's invariants. -/

/-! ## Phase R7d^xxix-D — SWAP-based loader construction

Reuses the existing `FormalRV.BQAlgo.qubit_swap` primitive (CX×3)
from `ModularAdder.lean`. The loader sequences per-window SWAPs that
move data bits from `encodeDataZeroAnc` positions to window-bit
ancillas, leaving the data positions cleared (to whatever the
window-bit ancilla initially held — typically 0).

This is the analog of `sqir_encode_to_mult_adapter` /
`reverse_register_swap` but targets the windowed b0Idx/b1Idx ancilla
positions rather than the SQIR multiplier-shifted layout. -/

/-- **SWAP-based loader gate** (recursive on `numWin`). Per window
`n`, performs two `qubit_swap`s:
- swap (data position `bits - 1 - 2*n`) ↔ `b0Idx n`,
- swap (data position `bits - 1 - (2*n + 1)`) ↔ `b1Idx n`.

Source positions follow `encodeDataZeroAnc`'s big-endian convention,
matching the same indexing used by `windowedLoadAdapter` (the
deprecated CX copy loader).

Unlike the CX loader, the data positions are CLEARED after the swap
(they hold whatever the ancilla positions held before, typically 0). -/
noncomputable def windowedSwapLoadAdapter
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (windowedSwapLoadAdapter bits b0Idx b1Idx n)
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * n) (b0Idx n))
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - (2 * n + 1)) (b1Idx n)))

/-- Zero-window SWAP loader is the identity. -/
@[simp] theorem windowedSwapLoadAdapter_zero
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowedSwapLoadAdapter bits b0Idx b1Idx 0 = Gate.I := rfl

/-- Successor-window SWAP loader appends two `qubit_swap`s. -/
@[simp] theorem windowedSwapLoadAdapter_succ
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowedSwapLoadAdapter bits b0Idx b1Idx (n + 1)
      = Gate.seq
          (windowedSwapLoadAdapter bits b0Idx b1Idx n)
          (Gate.seq
            (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * n) (b0Idx n))
            (FormalRV.BQAlgo.qubit_swap
              (bits - 1 - (2 * n + 1)) (b1Idx n))) := rfl

/-- **Frame property: preserves positions disjoint from all sources
and targets.** The SWAP loader preserves any position `p` that's not
any source data position `bits - 1 - 2*k` / `bits - 1 - (2*k+1)` and
not any target window position `b0Idx(k)` / `b1Idx(k)` for `k < numWin`.

Side conditions `h_swap0_ne`, `h_swap1_ne` ensure each `qubit_swap`'s
two positions are distinct (required by `qubit_swap_correct`). -/
theorem windowedSwapLoadAdapter_preserves_disjoint
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (p : Nat) (numWin : Nat)
    (f : Nat → Bool)
    (h_swap0_ne : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_swap1_ne : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k)
    (h_p_ne_src0 : ∀ k, k < numWin → p ≠ bits - 1 - 2 * k)
    (h_p_ne_src1 : ∀ k, k < numWin → p ≠ bits - 1 - (2 * k + 1))
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) f p
      = f p := by
  induction numWin generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_swap0_n : bits - 1 - 2 * n ≠ b0Idx n :=
      h_swap0_ne n (Nat.lt_succ_self n)
    have h_swap1_n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
      h_swap1_ne n (Nat.lt_succ_self n)
    have h_p_ne_src0n : p ≠ bits - 1 - 2 * n :=
      h_p_ne_src0 n (Nat.lt_succ_self n)
    have h_p_ne_src1n : p ≠ bits - 1 - (2 * n + 1) :=
      h_p_ne_src1 n (Nat.lt_succ_self n)
    have h_p_ne_b0n : p ≠ b0Idx n := h_p_ne_b0 n (Nat.lt_succ_self n)
    have h_p_ne_b1n : p ≠ b1Idx n := h_p_ne_b1 n (Nat.lt_succ_self n)
    -- Outer qubit_swap.
    rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_swap1_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_src1n]
    -- Inner qubit_swap.
    rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_swap0_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b0n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_src0n]
    -- Apply IH on the prefix.
    exact ih f
      (fun k hk => h_swap0_ne k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_swap1_ne k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_src0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_src1 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-! ### Source-index arithmetic helpers (R7d^xxix-E foundations)

Small kernel-clean helpers establishing that data-source positions
`bits - 1 - 2*k` and `bits - 1 - (2*k + 1)` (i) lie within the data
register `[0, bits)` and (ii) differ from any window-bit ancilla
position satisfying `bits ≤ b_idx k`. These are the foundational
arithmetic lemmas the full readback / apply theorem will compose with
`qubit_swap_correct` and `windowedSwapLoadAdapter_preserves_disjoint`. -/

/-- Data source for the b0 bit of window `k` is strictly below `bits`
when `2 * k < bits`. -/
theorem src0_lt_bits (bits k : Nat) (h : 2 * k < bits) :
    bits - 1 - 2 * k < bits := by omega

/-- Data source for the b1 bit of window `k` is strictly below `bits`
when `2 * k + 1 < bits`. -/
theorem src1_lt_bits (bits k : Nat) (h : 2 * k + 1 < bits) :
    bits - 1 - (2 * k + 1) < bits := by omega

/-- Data source for window `k`'s b0 bit differs from any
"above-data" ancilla index. -/
theorem src0_ne_above (bits k b : Nat)
    (h_src : 2 * k < bits) (h_above : bits ≤ b) :
    bits - 1 - 2 * k ≠ b := by omega

/-- Data source for window `k`'s b1 bit differs from any
"above-data" ancilla index. -/
theorem src1_ne_above (bits k b : Nat)
    (h_src : 2 * k + 1 < bits) (h_above : bits ≤ b) :
    bits - 1 - (2 * k + 1) ≠ b := by omega

/-- The two source positions within a single window differ. -/
theorem src0_ne_src1 (bits k : Nat)
    (h : 2 * k + 1 < bits) :
    bits - 1 - 2 * k ≠ bits - 1 - (2 * k + 1) := by omega

/-- Boolean bridge: `x.testBit k = decide (x / 2^k % 2 = 1)`. Proved
by case analysis on the Bool value of `testBit`, using
`Nat.toNat_testBit` to bridge to the Nat form. -/
theorem testBit_eq_decide (x k : Nat) :
    x.testBit k = decide (x / 2^k % 2 = 1) := by
  have h := Nat.toNat_testBit x k
  cases hb : x.testBit k with
  | false =>
    rw [hb] at h
    simp at h
    have h_ne : x / 2^k % 2 ≠ 1 := by omega
    simp [h_ne]
  | true =>
    rw [hb] at h
    simp at h
    have h_eq : x / 2^k % 2 = 1 := h.symm
    simp [h_eq]

/-- **Boolean bridge from `nat_to_funbool` to `Nat.testBit`.**
For any `n, x, i`, the big-endian bit-extractor `nat_to_funbool n x i`
returns `x.testBit (n - 1 - i)`. -/
theorem nat_to_funbool_eq_testBit
    (n x i : Nat) :
    FormalRV.Framework.nat_to_funbool n x i = x.testBit (n - 1 - i) := by
  unfold FormalRV.Framework.nat_to_funbool
  rw [testBit_eq_decide]

/-- **Latest-window readback for `b1`.** The SWAP loader at
`numWin = n + 1`, applied to `encodeDataZeroAnc`, reads
`x.testBit (2 * n + 1)` at position `b1Idx n`. -/
theorem windowedSwapLoadAdapter_succ_read_b1
    (bits anc n x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_2n1_lt : 2 * n + 1 < bits)
    (h_b0n_above : bits ≤ b0Idx n)
    (h_b1n_above : bits ≤ b1Idx n)
    (h_prefix_b0_above : ∀ k, k < n → bits ≤ b0Idx k)
    (h_prefix_b1_above : ∀ k, k < n → bits ≤ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx (n + 1))
        (encodeDataZeroAnc bits anc x) (b1Idx n)
      = x.testBit (2 * n + 1) := by
  have h_src1n_lt : bits - 1 - (2 * n + 1) < bits := src1_lt_bits bits n h_2n1_lt
  have h_2n_lt : 2 * n < bits := by omega
  have h_src0n_lt : bits - 1 - 2 * n < bits := src0_lt_bits bits n h_2n_lt
  have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
    src0_ne_above bits n _ h_2n_lt h_b0n_above
  have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
    src1_ne_above bits n _ h_2n1_lt h_b1n_above
  have h_b0n_ne_src1n : b0Idx n ≠ bits - 1 - (2 * n + 1) := by omega
  have h_src0n_ne_src1n : bits - 1 - 2 * n ≠ bits - 1 - (2 * n + 1) :=
    src0_ne_src1 bits n h_2n1_lt
  rw [windowedSwapLoadAdapter_succ]
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
  rw [FormalRV.Framework.update_eq]
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0n_ne_src1n)]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_src0n_ne_src1n)]
  -- Apply frame property of prefix loader at src1n
  have h_prefix_swap0_ne : ∀ k, k < n → bits - 1 - 2 * k ≠ b0Idx k :=
    fun k hk => src0_ne_above bits k _ (by omega) (h_prefix_b0_above k hk)
  have h_prefix_swap1_ne : ∀ k, k < n → bits - 1 - (2 * k + 1) ≠ b1Idx k :=
    fun k hk => src1_ne_above bits k _ (by omega) (h_prefix_b1_above k hk)
  have h_src1n_disj_src0_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ bits - 1 - 2 * k :=
    fun k hk => by omega
  have h_src1n_disj_src1_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ bits - 1 - (2 * k + 1) :=
    fun k hk => by omega
  have h_src1n_disj_b0_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ b0Idx k :=
    fun k hk => by
      have := h_prefix_b0_above k hk
      omega
  have h_src1n_disj_b1_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ b1Idx k :=
    fun k hk => by
      have := h_prefix_b1_above k hk
      omega
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
        (bits - 1 - (2 * n + 1)) n
        (encodeDataZeroAnc bits anc x)
        h_prefix_swap0_ne h_prefix_swap1_ne
        h_src1n_disj_src0_prefix h_src1n_disj_src1_prefix
        h_src1n_disj_b0_prefix h_src1n_disj_b1_prefix]
  rw [encodeDataZeroAnc_data hx h_src1n_lt]
  rw [nat_to_funbool_eq_testBit]
  congr 1
  omega

/-- **Latest-window readback for `b0`.** The SWAP loader at
`numWin = n + 1`, applied to `encodeDataZeroAnc`, reads
`x.testBit (2 * n)` at position `b0Idx n`. -/
theorem windowedSwapLoadAdapter_succ_read_b0
    (bits anc n x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_2n_lt : 2 * n < bits)
    (h_2n1_lt : 2 * n + 1 < bits)
    (h_b0n_above : bits ≤ b0Idx n)
    (h_b1n_above : bits ≤ b1Idx n)
    (h_b0n_ne_b1n : b0Idx n ≠ b1Idx n)
    (h_prefix_b0_above : ∀ k, k < n → bits ≤ b0Idx k)
    (h_prefix_b1_above : ∀ k, k < n → bits ≤ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx (n + 1))
        (encodeDataZeroAnc bits anc x) (b0Idx n)
      = x.testBit (2 * n) := by
  have h_src0n_lt : bits - 1 - 2 * n < bits := src0_lt_bits bits n h_2n_lt
  have h_src1n_lt : bits - 1 - (2 * n + 1) < bits := src1_lt_bits bits n h_2n1_lt
  have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
    src0_ne_above bits n _ h_2n_lt h_b0n_above
  have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
    src1_ne_above bits n _ h_2n1_lt h_b1n_above
  have h_b0n_ne_b1n_swap : b0Idx n ≠ b1Idx n := h_b0n_ne_b1n
  have h_b1n_ne_b0n : b1Idx n ≠ b0Idx n := Ne.symm h_b0n_ne_b1n
  have h_b0n_ne_src1n : b0Idx n ≠ bits - 1 - (2 * n + 1) := by omega
  have h_src1n_ne_b0n : bits - 1 - (2 * n + 1) ≠ b0Idx n := Ne.symm h_b0n_ne_src1n
  rw [windowedSwapLoadAdapter_succ]
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Outer qubit_swap at (src1n, b1Idx n).
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
  -- update at b1Idx n (≠ b0Idx n).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0n_ne_b1n_swap]
  -- update at src1n (≠ b0Idx n).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0n_ne_src1n]
  -- Inner qubit_swap at (src0n, b0Idx n).
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
  -- update at b0Idx n: use update_eq.
  rw [FormalRV.Framework.update_eq]
  -- Goal: (applyNat prefix encode) src0n = x.testBit (2*n)
  have h_prefix_swap0_ne : ∀ k, k < n → bits - 1 - 2 * k ≠ b0Idx k :=
    fun k hk => src0_ne_above bits k _ (by omega) (h_prefix_b0_above k hk)
  have h_prefix_swap1_ne : ∀ k, k < n → bits - 1 - (2 * k + 1) ≠ b1Idx k :=
    fun k hk => src1_ne_above bits k _ (by omega) (h_prefix_b1_above k hk)
  have h_src0n_disj_src0_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ bits - 1 - 2 * k :=
    fun k hk => by omega
  have h_src0n_disj_src1_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ bits - 1 - (2 * k + 1) :=
    fun k hk => by omega
  have h_src0n_disj_b0_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ b0Idx k :=
    fun k hk => by
      have := h_prefix_b0_above k hk
      omega
  have h_src0n_disj_b1_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ b1Idx k :=
    fun k hk => by
      have := h_prefix_b1_above k hk
      omega
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
        (bits - 1 - 2 * n) n
        (encodeDataZeroAnc bits anc x)
        h_prefix_swap0_ne h_prefix_swap1_ne
        h_src0n_disj_src0_prefix h_src0n_disj_src1_prefix
        h_src0n_disj_b0_prefix h_src0n_disj_b1_prefix]
  rw [encodeDataZeroAnc_data hx h_src0n_lt]
  rw [nat_to_funbool_eq_testBit]
  congr 1
  omega

/-- **General-k readback for `b1`.** For any window `k < numWin`, the
SWAP loader applied to `encodeDataZeroAnc` reads `x.testBit (2*k+1)`
at position `b1Idx k`. Proven by induction on `numWin`.

Uses `h_2numWin_le : 2 * numWin ≤ bits` (rather than the exact-coverage
`2 * numWin = bits`) because the induction hypothesis at `n` requires
`2 * n ≤ bits` (derivable from outer `2 * (n+1) ≤ bits`). -/
theorem windowedSwapLoadAdapter_read_b1
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (b1Idx k)
      = x.testBit (2 * k + 1) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      exact windowedSwapLoadAdapter_succ_read_b1 bits anc k x b0Idx b1Idx hx
        h_2k1_lt
        (h_b0_above k (Nat.lt_succ_self k))
        (h_b1_above k (Nat.lt_succ_self k))
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b1k_above : bits ≤ b1Idx k := h_b1_above k hk
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_b1k_ne_b1n : b1Idx k ≠ b1Idx n :=
        h_distinct_b1_b1 k n hk (Nat.lt_succ_self n) hkn
      have h_b1k_ne_b0n : b1Idx k ≠ b0Idx n :=
        h_distinct_b1_b0 k n hk (Nat.lt_succ_self n) hkn
      have h_b1k_ne_src0n : b1Idx k ≠ bits - 1 - 2 * n := by omega
      have h_b1k_ne_src1n : b1Idx k ≠ bits - 1 - (2 * n + 1) := by omega
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      rw [windowedSwapLoadAdapter_succ]
      rw [Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b1_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **General-k readback for `b0`.** For any window `k < numWin`, the
SWAP loader applied to `encodeDataZeroAnc` reads `x.testBit (2*k)`
at position `b0Idx k`. -/
theorem windowedSwapLoadAdapter_read_b0
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (b0Idx k)
      = x.testBit (2 * k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k_lt : 2 * k < bits := by omega
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      exact windowedSwapLoadAdapter_succ_read_b0 bits anc k x b0Idx b1Idx hx
        h_2k_lt h_2k1_lt
        (h_b0_above k (Nat.lt_succ_self k))
        (h_b1_above k (Nat.lt_succ_self k))
        (h_b0_ne_b1 k (Nat.lt_succ_self k))
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0k_above : bits ≤ b0Idx k := h_b0_above k hk
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_b0k_ne_b0n : b0Idx k ≠ b0Idx n :=
        h_distinct_b0_b0 k n hk (Nat.lt_succ_self n) hkn
      have h_b0k_ne_b1n : b0Idx k ≠ b1Idx n :=
        h_distinct_b0_b1 k n hk (Nat.lt_succ_self n) hkn
      have h_b0k_ne_src0n : b0Idx k ≠ bits - 1 - 2 * n := by omega
      have h_b0k_ne_src1n : b0Idx k ≠ bits - 1 - (2 * n + 1) := by omega
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      rw [windowedSwapLoadAdapter_succ]
      rw [Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **`encodeDataZeroAnc` above-data value.** For any position `q ≥ bits`,
the encoding's value is `false` — either it's in the ancilla range
`[bits, bits + anc)` (use `encodeDataZeroAnc_anc`) or out of range
`[bits + anc, ∞)` (use `encodeDataZeroAnc_oob`). Requires `0 < anc`. -/
theorem encodeDataZeroAnc_above
    (bits anc x q : Nat) (hx : x < 2^bits) (hq : bits ≤ q) (hanc_pos : 0 < anc) :
    encodeDataZeroAnc bits anc x q = false := by
  by_cases h : q < bits + anc
  · have h_offset : q - bits < anc := by omega
    have h_eq : q = bits + (q - bits) := by omega
    rw [h_eq]
    exact encodeDataZeroAnc_anc hx h_offset
  · push_neg at h
    exact encodeDataZeroAnc_oob hanc_pos h

/-- **Data-clearing at b0 source positions.** For any window
`k < numWin`, the SWAP loader applied to `encodeDataZeroAnc` clears
the data position `bits - 1 - 2 * k` to `false`.

Proven by induction on `numWin`. Latest-window case: the new
`qubit_swap` moves the (initially-zero) window-bit ancilla value
into the data position. Older windows: IH says the position was
already cleared, and the new swaps don't touch this position. -/
theorem windowedSwapLoadAdapter_clears_data_even
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_anc_pos : 0 < anc)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (bits - 1 - 2 * k)
      = false := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k_lt : 2 * k < bits := by omega
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      have h_b0k_above : bits ≤ b0Idx k := h_b0_above k (Nat.lt_succ_self k)
      have h_b1k_above : bits ≤ b1Idx k := h_b1_above k (Nat.lt_succ_self k)
      have h_src0k_ne_b0k : bits - 1 - 2 * k ≠ b0Idx k :=
        src0_ne_above bits k _ h_2k_lt h_b0k_above
      have h_src1k_ne_b1k : bits - 1 - (2 * k + 1) ≠ b1Idx k :=
        src1_ne_above bits k _ h_2k1_lt h_b1k_above
      have h_src0k_ne_src1k : bits - 1 - 2 * k ≠ bits - 1 - (2 * k + 1) :=
        src0_ne_src1 bits k h_2k1_lt
      have h_src0k_ne_b1k : bits - 1 - 2 * k ≠ b1Idx k := by omega
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1k_ne_b1k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b1k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_src1k]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0k_ne_b0k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b0k]
      rw [FormalRV.Framework.update_eq]
      -- Goal: applyNat prefix encode (b0Idx k) = false
      have h_prefix_swap0_ne : ∀ j, j < k → bits - 1 - 2 * j ≠ b0Idx j :=
        fun j hj => src0_ne_above bits j _ (by omega) (h_b0_above j (by omega))
      have h_prefix_swap1_ne : ∀ j, j < k → bits - 1 - (2 * j + 1) ≠ b1Idx j :=
        fun j hj => src1_ne_above bits j _ (by omega) (h_b1_above j (by omega))
      have h_b0k_disj_src0_prefix :
          ∀ j, j < k → b0Idx k ≠ bits - 1 - 2 * j :=
        fun j hj => by
          have := h_b0_above k (Nat.lt_succ_self k); omega
      have h_b0k_disj_src1_prefix :
          ∀ j, j < k → b0Idx k ≠ bits - 1 - (2 * j + 1) :=
        fun j hj => by
          have := h_b0_above k (Nat.lt_succ_self k); omega
      have h_b0k_disj_b0_prefix : ∀ j, j < k → b0Idx k ≠ b0Idx j :=
        fun j hj => h_distinct_b0_b0 k j (Nat.lt_succ_self k) (by omega) (by omega)
      have h_b0k_disj_b1_prefix : ∀ j, j < k → b0Idx k ≠ b1Idx j :=
        fun j hj => h_distinct_b0_b1 k j (Nat.lt_succ_self k) (by omega) (by omega)
      rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
            (b0Idx k) k (encodeDataZeroAnc bits anc x)
            h_prefix_swap0_ne h_prefix_swap1_ne
            h_b0k_disj_src0_prefix h_b0k_disj_src1_prefix
            h_b0k_disj_b0_prefix h_b0k_disj_b1_prefix]
      exact encodeDataZeroAnc_above bits anc x (b0Idx k) hx h_b0k_above h_anc_pos
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_2k_lt : 2 * k < bits := by omega
      have h_src0k_ne_b0n : bits - 1 - 2 * k ≠ b0Idx n := by omega
      have h_src0k_ne_b1n : bits - 1 - 2 * k ≠ b1Idx n := by omega
      have h_src0k_ne_src0n : bits - 1 - 2 * k ≠ bits - 1 - 2 * n := by omega
      have h_src0k_ne_src1n : bits - 1 - 2 * k ≠ bits - 1 - (2 * n + 1) := by omega
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Data-clearing at b1 source positions.** For any window
`k < numWin`, the SWAP loader applied to `encodeDataZeroAnc` clears
the data position `bits - 1 - (2 * k + 1)` to `false`.

Latest-window case: outer `qubit_swap (src1k) (b1Idx k)` swaps;
inner swap doesn't touch `b1Idx k` (requires `b0Idx k ≠ b1Idx k`).
Older window: outer two swaps don't touch src1k. -/
theorem windowedSwapLoadAdapter_clears_data_odd
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_anc_pos : 0 < anc)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (bits - 1 - (2 * k + 1))
      = false := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k_lt : 2 * k < bits := by omega
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      have h_b0k_above : bits ≤ b0Idx k := h_b0_above k (Nat.lt_succ_self k)
      have h_b1k_above : bits ≤ b1Idx k := h_b1_above k (Nat.lt_succ_self k)
      have h_b0k_ne_b1k : b0Idx k ≠ b1Idx k := h_b0_ne_b1 k (Nat.lt_succ_self k)
      have h_src1k_ne_b1k : bits - 1 - (2 * k + 1) ≠ b1Idx k :=
        src1_ne_above bits k _ h_2k1_lt h_b1k_above
      have h_src0k_ne_b0k : bits - 1 - 2 * k ≠ b0Idx k :=
        src0_ne_above bits k _ h_2k_lt h_b0k_above
      have h_b1k_ne_src0k : b1Idx k ≠ bits - 1 - 2 * k := by omega
      have h_b1k_ne_b0k : b1Idx k ≠ b0Idx k := Ne.symm h_b0k_ne_b1k
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1k_ne_b1k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_b1k]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0k_ne_b0k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_src0k]
      have h_prefix_swap0_ne : ∀ j, j < k → bits - 1 - 2 * j ≠ b0Idx j :=
        fun j hj => src0_ne_above bits j _ (by omega) (h_b0_above j (by omega))
      have h_prefix_swap1_ne : ∀ j, j < k → bits - 1 - (2 * j + 1) ≠ b1Idx j :=
        fun j hj => src1_ne_above bits j _ (by omega) (h_b1_above j (by omega))
      have h_b1k_disj_src0_prefix :
          ∀ j, j < k → b1Idx k ≠ bits - 1 - 2 * j :=
        fun j hj => by
          have := h_b1_above k (Nat.lt_succ_self k); omega
      have h_b1k_disj_src1_prefix :
          ∀ j, j < k → b1Idx k ≠ bits - 1 - (2 * j + 1) :=
        fun j hj => by
          have := h_b1_above k (Nat.lt_succ_self k); omega
      have h_b1k_disj_b0_prefix : ∀ j, j < k → b1Idx k ≠ b0Idx j :=
        fun j hj => h_distinct_b1_b0 k j (Nat.lt_succ_self k) (by omega) (by omega)
      have h_b1k_disj_b1_prefix : ∀ j, j < k → b1Idx k ≠ b1Idx j :=
        fun j hj => h_distinct_b1_b1 k j (Nat.lt_succ_self k) (by omega) (by omega)
      rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
            (b1Idx k) k (encodeDataZeroAnc bits anc x)
            h_prefix_swap0_ne h_prefix_swap1_ne
            h_b1k_disj_src0_prefix h_b1k_disj_src1_prefix
            h_b1k_disj_b0_prefix h_b1k_disj_b1_prefix]
      exact encodeDataZeroAnc_above bits anc x (b1Idx k) hx h_b1k_above h_anc_pos
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      have h_src1k_ne_b0n : bits - 1 - (2 * k + 1) ≠ b0Idx n := by omega
      have h_src1k_ne_b1n : bits - 1 - (2 * k + 1) ≠ b1Idx n := by omega
      have h_src1k_ne_src0n : bits - 1 - (2 * k + 1) ≠ bits - 1 - 2 * n := by omega
      have h_src1k_ne_src1n :
          bits - 1 - (2 * k + 1) ≠ bits - 1 - (2 * n + 1) := by omega
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b1_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

end Windowed
end VerifiedShor
