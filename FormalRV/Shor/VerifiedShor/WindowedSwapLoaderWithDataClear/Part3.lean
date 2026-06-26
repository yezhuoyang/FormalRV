/- WindowedSwapLoaderWithDataClear — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedSwapLoaderWithDataClear.Part2

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

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
existing `encode_to_mult_adapter`) that MOVES `x`'s bits from
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

This is the analog of `encode_to_mult_adapter` /
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


end Windowed
end VerifiedShor
