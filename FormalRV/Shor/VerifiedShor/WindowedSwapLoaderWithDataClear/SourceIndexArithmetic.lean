/- WindowedSwapLoaderWithDataClear — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedSwapLoaderWithDataClear.LoadedStateEncoding

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

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
