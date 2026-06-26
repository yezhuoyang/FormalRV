/- WindowedMultiplyAddSpecification — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedMultiplyAddSpecification.Part3

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xxi — multi-window spec scaffold

Pure spec-level layer for iterating `windowedStepSpec` over multiple
windows. Defines a windowed-bit accessor, an iterated step function,
and the basic unfold/boundedness lemmas needed by the future
multi-window circuit correctness theorem. No circuit-level reasoning
yet — this layer is purely arithmetic. -/

/-- Per-window bit accessor: extracts the window value at window
index `k` from a pair of bit functions `b0 : Nat → Bool` (LSB) and
`b1 : Nat → Bool` (MSB). The window value lives in `[0, 4)`. -/
def windowBits2_at (b0 b1 : Nat → Bool) (k : Nat) : Nat :=
  windowBits2_to_v (b0 k) (b1 k)

/-- The boolean-pair window encoding always fits in `[0, 4)`. -/
theorem windowBits2_to_v_lt_4 (b0 b1 : Bool) :
    windowBits2_to_v b0 b1 < 4 := by
  unfold windowBits2_to_v
  cases b0 <;> cases b1 <;> simp [Bool.toNat]

/-- Multi-window analog: every window value extracted via
`windowBits2_at` is bounded above by `4 = 2^2`. -/
theorem windowBits2_at_lt_4 (b0 b1 : Nat → Bool) (k : Nat) :
    windowBits2_at b0 b1 k < 4 := windowBits2_to_v_lt_4 (b0 k) (b1 k)

/-- **Iterated windowed step** at window size 2: applies
`windowedStepSpec a N 2 k` for `k = 0, …, numWin - 1` starting from
`acc`, with the `k`-th step using window value
`windowBits2_at b0 b1 k`. Recursive on `numWin` for clean induction. -/
def windowedStepSpecIter2
    (a N : Nat) (b0 b1 : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc =>
      windowedStepSpec a N 2 n
        (windowedStepSpecIter2 a N b0 b1 n acc)
        (windowBits2_at b0 b1 n)

/-- Base unfold: 0 windows leaves the accumulator unchanged. -/
@[simp] theorem windowedStepSpecIter2_zero
    (a N acc : Nat) (b0 b1 : Nat → Bool) :
    windowedStepSpecIter2 a N b0 b1 0 acc = acc := rfl

/-- Step unfold: `numWin + 1` windows compose as `numWin` windows
followed by the `numWin`-th selected-add. -/
@[simp] theorem windowedStepSpecIter2_succ
    (a N numWin acc : Nat) (b0 b1 : Nat → Bool) :
    windowedStepSpecIter2 a N b0 b1 (numWin + 1) acc
      = windowedStepSpec a N 2 numWin
          (windowedStepSpecIter2 a N b0 b1 numWin acc)
          (windowBits2_at b0 b1 numWin) := rfl

/-- **Iterated boundedness.** Every intermediate accumulator stays
in `[0, N)`. The base case uses the initial bound `acc < N`; the
inductive case uses `windowedStepSpec_lt_N` (the modular reduction
guarantees output `< N` unconditionally). -/
theorem windowedStepSpecIter2_lt_N
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc < N := by
  induction numWin with
  | zero => exact hacc
  | succ n _ =>
    rw [windowedStepSpecIter2_succ]
    exact windowedStepSpec_lt_N a N 2 n _ _ hN_pos

/-- **Circuit skeleton: multi-window selected-add gate sequence.**

Given a `Window2SelectedAddSpec` implementation, sequences `numWin`
applications of its `gate` constructor over windows `k = 0, …,
numWin - 1`, with `b0Idx k` / `b1Idx k` supplying the per-window
bit positions. Recursion on `numWin` mirrors `windowedStepSpecIter2`.

This is the gate-level analog of `windowedStepSpecIter2`; proving its
correctness theorem (gate output's `cuccaro_target_val` matches
`windowedStepSpecIter2`) is the next major milestone (deferred). -/
noncomputable def windowed2SelectedAddGate
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq (windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx n)
        (impl.gate bits n flagIdx (b0Idx n) (b1Idx n))

/-- Base unfold for the gate skeleton: 0 windows is the identity. -/
@[simp] theorem windowed2SelectedAddGate_zero
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx 0 = Gate.I := rfl

/-- Step unfold for the gate skeleton: `numWin + 1` windows compose
as `numWin` windows followed by the `numWin`-th selected-add. -/
@[simp] theorem windowed2SelectedAddGate_succ
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx numWin : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx (numWin + 1)
      = Gate.seq (windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx numWin)
                 (impl.gate bits numWin flagIdx (b0Idx numWin) (b1Idx numWin)) :=
  rfl

/-! ## Phase R7d^xxii — full-state selected-add spec

Strengthens the selected-add spec from target-decode (R7d^xx) to
full-state correctness. The composed gate maps a `Case3Input`
state to a `Case3Input` state with the accumulator updated
according to `windowedStepSpec` — preserving the input shape so
the next selected-add gate (at the next window) can chain.

This is the prerequisite for the multi-window circuit correctness
theorem: without preserved state shape, sequential `selectedAdd`
applications can't be composed via the spec interface. -/

/-- **Full-state selected-add correctness.** The composed
windowSize=2 selected-add gate produces a `Case3Input` state with
the accumulator advanced by `windowedStepSpec a N 2 k acc
(windowBits2_to_v b0 b1)`, leaving all other bit positions intact
in the `Case3Input` shape.

Proof mirrors `toyWindow2SelectedAddGate_correct` (R7d^xix) but
stops at the state level — no `cuccaro_target_val` extraction. -/
theorem toyWindow2SelectedAddGate_state_eq_spec
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1))
          b0Idx b1Idx b0 b1 := by
  unfold toyWindow2SelectedAddGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Apply Case 1 unified.
  rw [toyWindow2Case1Gate_state_eq_unified bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc1 := if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc
    with h_acc1_def
  have h_acc1_lt : acc1 < N := by
    rw [h_acc1_def]; split
    · exact Nat.mod_lt _ hN_pos
    · exact hacc
  -- Apply Case 2 unified at acc1.
  rw [toyWindow2Case2Gate_state_eq_unified bits N a k acc1 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc1_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc2 := if !b0 && b1 then (acc1 + tableValue a N 2 k 2) % N else acc1
    with h_acc2_def
  have h_acc2_lt : acc2 < N := by
    rw [h_acc2_def]; split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc1_lt
  -- Apply Case 3 unified at acc2.
  rw [toyWindow2Case3Gate_state_eq_unified bits N a k acc2 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc2_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc3 := if b0 && b1 then (acc2 + tableValue a N 2 k 3) % N else acc2
    with h_acc3_def
  -- Show acc3 = windowedStepSpec ... by unfolding + bool-bridge + cases.
  have h_acc3_eq : acc3 = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) := by
    rw [h_acc3_def, h_acc2_def, h_acc1_def,
        windowedStepSpec_window2_bool a N k acc b0 b1 hN_pos hacc]
    cases b0 <;> cases b1 <;> simp
  rw [h_acc3_eq]

/-- **`Window2SelectedAddStateSpec`**: stronger spec contract for a
composed windowSize=2 selected-add component, exposing the full-state
correctness theorem instead of just target-decode correctness.

The state-level field is required for multi-window composition:
without it, two consecutive selected-add gates can't be chained
through the spec interface (target-decode alone leaves the
intermediate state's shape unknown).

Strictly stronger than `Window2SelectedAddSpec` — instances of
this structure imply `Window2SelectedAddSpec` instances (see
`Window2SelectedAddStateSpec.toSelectedAddSpec`). -/
structure Window2SelectedAddStateSpec (a N : Nat) where
  /-- The composed selected-add gate constructor. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Full-state correctness: the gate transforms a `Case3Input`
  state to a `Case3Input` state with the accumulator updated per
  `windowedStepSpec`. All other bit positions are preserved. -/
  selectedAddStateEq :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
        = toyWindow2Case3Input
            (windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1))
            b0Idx b1Idx b0 b1

/-- A `Window2SelectedAddStateSpec` instance yields a
`Window2SelectedAddSpec` instance by composing the state-eq theorem
with `cuccaro_target_val_Case3Input`. The conversion is uniform
in the implementation. -/
noncomputable def Window2SelectedAddStateSpec.toSelectedAddSpec
    {a N : Nat} (impl : Window2SelectedAddStateSpec a N) :
    Window2SelectedAddSpec a N where
  gate := impl.gate
  selectedAddCorrect := by
    intro bits k acc flagIdx b0Idx b1Idx b0 b1
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
    have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
    have h_step_lt : windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) < N :=
      windowedStepSpec_lt_N a N 2 k acc _ hN_pos
    rw [impl.selectedAddStateEq bits k acc flagIdx b0Idx b1Idx b0 b1
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact cuccaro_target_val_Case3Input bits _ b0Idx b1Idx b0 b1
      h_b0_out h_b1_out (Nat.lt_of_lt_of_le h_step_lt hN)

/-- **Toy windowSize=2 selected-add full-state spec implementation.**

Wraps the CCX-based `toyWindow2SelectedAddGate` as a
`Window2SelectedAddStateSpec a N` instance via
`toyWindow2SelectedAddGate_state_eq_spec`. -/
noncomputable def toyWindow2SelectedAddStateSpecImpl (a N : Nat) :
    Window2SelectedAddStateSpec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx
  selectedAddStateEq := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                            hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                            h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                            h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2SelectedAddGate_state_eq_spec bits N a k acc flagIdx b0Idx b1Idx
      b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xxiii — multi-window input encoding

All-windows-at-once input encoding for the windowSize=2 selected-add
pipeline. Installs every window's b0/b1 bits simultaneously over the
Cuccaro accumulator base. Recursive on `numWin` for clean induction;
proves basic readback lemmas (for an arbitrary installed window),
target-extraction (cuccaro_target_val ignores the high window bits),
and workspace preservation (a frame-style lemma for any low-position
query). -/

/-- **Multi-window input encoding.** Installs the b0/b1 bits for
windows `0, …, numWin - 1` on top of a Cuccaro-formatted accumulator
encoding. Recursive on `numWin`. -/
def windowed2Input
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) :
    Nat → (Nat → Bool)
  | 0 => cuccaro_input_F 2 false 0 acc
  | n + 1 =>
      update
        (update (windowed2Input acc b0Idx b1Idx b0 b1 n) (b0Idx n) (b0 n))
        (b1Idx n) (b1 n)

/-- Zero windows: the encoding is just the Cuccaro accumulator base. -/
@[simp] theorem windowed2Input_zero
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) :
    windowed2Input acc b0Idx b1Idx b0 b1 0
      = cuccaro_input_F 2 false 0 acc := rfl

/-- Successor unfold: install window `n`'s bits on top of windows
`0 … n - 1`. -/
@[simp] theorem windowed2Input_succ
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1)
      = update
          (update (windowed2Input acc b0Idx b1Idx b0 b1 n) (b0Idx n) (b0 n))
          (b1Idx n) (b1 n) := rfl

/-- Latest-window readback for `b1`: just the outermost update. -/
theorem windowed2Input_succ_read_b1
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1) (b1Idx n) = b1 n := by
  rw [windowed2Input_succ]
  exact FormalRV.Framework.update_eq _ _ _

/-- Latest-window readback for `b0`: strip the outer `update` at
`b1Idx n` (requires `b0Idx n ≠ b1Idx n`), then read the inner one. -/
theorem windowed2Input_succ_read_b0
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat)
    (h_ne : b0Idx n ≠ b1Idx n) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1) (b0Idx n) = b0 n := by
  rw [windowed2Input_succ]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_ne]
  exact FormalRV.Framework.update_eq _ _ _

/-- **General `b0` readback** for any installed window `k < numWin`,
under universal index-disjointness. -/
theorem windowed2Input_read_b0
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_distinct : ∀ i j, i ≠ j → b0Idx i ≠ b0Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b0Idx k) = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k k)]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k n)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_distinct k n hkn)]
      exact ih hk_lt_n

/-- **General `b1` readback** for any installed window `k < numWin`. -/
theorem windowed2Input_read_b1
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b1_distinct : ∀ i j, i ≠ j → b1Idx i ≠ b1Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
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
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_distinct k n hkn)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm (h_b0_b1 n k))]
      exact ih hk_lt_n

/-- **Target extraction.** The Cuccaro target decoder ignores all
window bits (they live above the workspace), recovering the input
accumulator. -/
theorem cuccaro_target_val_windowed2Input
    (bits acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (numWin : Nat)
    (hacc_bits : acc < 2^bits)
    (h_hi0 : ∀ k, 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, 2 + 2 * bits + 1 ≤ b1Idx k) :
    cuccaro_target_val bits 2 (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = acc := by
  induction numWin with
  | zero =>
    rw [windowed2Input_zero]
    exact cuccaro_target_val_input bits 2 0 acc false hacc_bits
  | succ n ih =>
    rw [windowed2Input_succ]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b1Idx n) (b1 n) _
          (Or.inr (h_hi1 n))]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b0Idx n) (b0 n) _
          (Or.inr (h_hi0 n))]
    exact ih

/-- **Workspace preservation (frame-style).** At any position `q` in
the Cuccaro workspace (`q < 2 + 2 * bits`), the multi-window encoding
agrees with the base accumulator encoding. Useful for proving that
gates operating only on the workspace + flag + active window bits
preserve `cuccaro_target_val` / `cuccaro_read_val` semantics. -/
theorem windowed2Input_at_low
    (acc bits q : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin : Nat) (h_q_low : q < 2 + 2 * bits + 1)
    (h_hi0 : ∀ k, 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, 2 + 2 * bits + 1 ≤ b1Idx k) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin q
      = cuccaro_input_F 2 false 0 acc q := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ]
    have h_q_ne_b1 : q ≠ b1Idx n := by
      have := h_hi1 n; omega
    have h_q_ne_b0 : q ≠ b0Idx n := by
      have := h_hi0 n; omega
    rw [FormalRV.Framework.update_neq _ _ _ _ h_q_ne_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_q_ne_b0]
    exact ih

/-! ## Phase R7d^xxix-L-1 — q_start-parametric windowed input layout

R7d^xxix-L-DESIGN-LOCK selected Option C2: shift the Cuccaro
workspace above the official data register so that the official data
register `q < bits` is disjoint from the arithmetic accumulator /
workspace.

This section introduces the q_start-parametric counterpart of
`windowed2Input`, bridges it to the old `q_start = 2` layout, and
proves the readback / zero-base / shifted-layout disjointness lemmas
needed by the (forthcoming L-2 / L-3) parametric K-stage.

**Exact accumulator-bit formula (from `cuccaro_input_F`):** the
accumulator's `k`-th bit lives at position `q_start + 2*k + 1`.
(With `q_start = 2`, this gives the old positions `2*k + 3 = 3, 5,
7, ...`; with `q_start = bits`, this gives the shifted positions
`bits + 1, bits + 3, ...`.) -/

/-- **q_start-parametric multi-window input encoding.** Same recursive
structure as `windowed2Input`, but the underlying Cuccaro base allows
an arbitrary `q_start`. The old `windowed2Input` is the
`q_start = 2` specialization (see `windowed2Input_eq_qstart_2`). -/
def windowed2Input_qstart
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) : Nat → (Nat → Bool)
  | 0 => cuccaro_input_F q_start false 0 acc
  | n + 1 =>
      update
        (update
          (windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 n)
          (b0Idx n) (b0 n))
        (b1Idx n) (b1 n)

/-- Zero-window unfold for the q_start-parametric encoding. -/
@[simp] theorem windowed2Input_qstart_zero
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 0
      = cuccaro_input_F q_start false 0 acc := rfl

/-- Successor unfold for the q_start-parametric encoding. -/
@[simp] theorem windowed2Input_qstart_succ
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 (n + 1)
      = update
          (update
            (windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 n)
            (b0Idx n) (b0 n))
          (b1Idx n) (b1 n) := rfl

/-- **Bridge to the old q_start = 2 layout.** The original
`windowed2Input` is the `q_start = 2` specialization of
`windowed2Input_qstart`. Proven by induction on `numWin`, with both
recursive defs unfolding identically. -/
theorem windowed2Input_eq_qstart_2
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin
      = windowed2Input_qstart 2 acc b0Idx b1Idx b0 b1 numWin := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ, windowed2Input_qstart_succ, ih]


end Windowed
end VerifiedShor
