/- WindowedSwapLoaderWithDataClear — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedSwapLoaderWithDataClear.Part1

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

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


end Windowed
end VerifiedShor
