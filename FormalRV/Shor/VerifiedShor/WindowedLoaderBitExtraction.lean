import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.WindowedMultiplyAddSpecification

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

/-! ## Phase R7d^xxix-L-2′ — q_start-parametric selected-add frame

For Architecture D (Gidney style, see
`GIDNEY_WINDOWED_ARITHMETIC_REVIEW.md`), the selected-add gate must
admit window control bits at positions **below** the Cuccaro
workspace — specifically at data positions `[0, bits)` when the
workspace starts at `q_start = bits`.

This section:
1. Generalizes `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`
   to arbitrary `q_start` and `flagPos`.
2. Defines q_start-parametric versions of the three case gates and
   the composed selected-add gate.
3. Proves the q_start-parametric frame property for the composed
   selected-add gate: it commutes with updates at any position `p`
   that is disjoint from its support (workspace, b0Idx, b1Idx,
   flagIdx).

Critically, the frame disjointness hypothesis allows
`p < q_start` (data positions) as well as
`q_start + 2*bits + 1 ≤ p` (high ancilla). The old q_start = 2
version only allowed `p < 2` (degenerate, just the prefix) plus
high ancilla. -/

/-- **q_start-parametric controlled-mod-add frame lemma.** The
underlying gate `sqir_style_controlledModAddConst_gate bits q_start
N c controlIdx flagPos` commutes with an `update _ updateIdx v`
when `updateIdx` is disjoint from the Cuccaro workspace
(`< q_start` or `≥ q_start + 2*bits + 1`), distinct from `flagPos`,
and distinct from `controlIdx`. -/
theorem sqir_modAdd_qstart_commute_update_disjoint
    (bits q_start N c controlIdx flagPos updateIdx : Nat) (v : Bool)
    (f : Nat → Bool)
    (hupdate_out :
      updateIdx < q_start ∨ q_start + 2 * bits + 1 ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ flagPos)
    (hupdate_ne_control : updateIdx ≠ controlIdx) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
        (update f updateIdx v)
      = update (Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          f) updateIdx v := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc : c = 0
  · simp [hc, Gate.applyNat_I]
  · simp only [hc, if_false]
    unfold sqir_style_controlledModAddConst_candidate
    simp only [Gate.applyNat_seq]
    rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start c
          controlIdx updateIdx v f hupdate_out hupdate_ne_control]
    rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start N
          flagPos updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits q_start N
          flagPos updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_controlledCompareConst_commute_update_outside_fun bits q_start c
          controlIdx flagPos updateIdx v _
          hupdate_out hupdate_ne_flag hupdate_ne_control]
    rw [Gate.applyNat_CX_commute_update_outside_fun controlIdx flagPos updateIdx v _
          hupdate_ne_control hupdate_ne_flag]

/-- **q_start-parametric case-3 selected-add gate** (binary 11).
Same structure as `toyWindow2Case3Gate` but operating at parametric
`q_start` and `flagPos`. -/
noncomputable def toyWindow2Case3Gate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 3
  Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
    (Gate.seq (sqir_style_controlledModAddConst_gate bits q_start N c flagIdx flagPos)
              (Gate.CCX b0Idx b1Idx flagIdx))

/-- **q_start-parametric case-1 selected-add gate** (binary 01).
X-normalizes b1 before/after the CCX cascade. -/
noncomputable def toyWindow2Case1Gate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 1
  Gate.seq (Gate.X b1Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (sqir_style_controlledModAddConst_gate bits q_start N c flagIdx flagPos)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b1Idx))))

/-- **q_start-parametric case-2 selected-add gate** (binary 10).
X-normalizes b0 before/after the CCX cascade. -/
noncomputable def toyWindow2Case2Gate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 2
  Gate.seq (Gate.X b0Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (sqir_style_controlledModAddConst_gate bits q_start N c flagIdx flagPos)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b0Idx))))

/-- **q_start-parametric composed selected-add gate.** Runs the
three nonzero-case gates in sequence. -/
noncomputable def toyWindow2SelectedAddGate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  Gate.seq (toyWindow2Case1Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
    (Gate.seq (toyWindow2Case2Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
              (toyWindow2Case3Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx))

/-- **Frame property of a single case gate.** Any `toyWindow2CaseN`
gate (N ∈ {1, 2, 3}) commutes with an `update _ p v` whose position
`p` is disjoint from the Cuccaro workspace, distinct from `b0Idx`,
`b1Idx`, `flagIdx`, and `flagPos`. -/
theorem toyWindow2Case3Gate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2Case3Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2Case3Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2Case3Gate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx f p v
      hp_ne_b0 hp_ne_b1 hp_ne_flag
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact sqir_modAdd_qstart_commute_update_disjoint bits q_start N
        (tableValue a N 2 k 3) flagIdx flagPos p v g
        hp_disj_workspace hp_ne_flagPos hp_ne_flag
    · intro g
      exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx g p v
        hp_ne_b0 hp_ne_b1 hp_ne_flag

theorem toyWindow2Case1Gate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2Case1Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2Case1Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2Case1Gate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact Gate.applyNat_X_commute_update_outside_fun b1Idx p v f hp_ne_b1
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx g p v
        hp_ne_b0 hp_ne_b1 hp_ne_flag
    · intro g
      refine applyNat_seq_commute_update _ _ g p v ?_ ?_
      · intro h
        exact sqir_modAdd_qstart_commute_update_disjoint bits q_start N
          (tableValue a N 2 k 1) flagIdx flagPos p v h
          hp_disj_workspace hp_ne_flagPos hp_ne_flag
      · intro h
        refine applyNat_seq_commute_update _ _ h p v ?_ ?_
        · intro i
          exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx i p v
            hp_ne_b0 hp_ne_b1 hp_ne_flag
        · intro i
          exact Gate.applyNat_X_commute_update_outside_fun b1Idx p v i hp_ne_b1

theorem toyWindow2Case2Gate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2Case2Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2Case2Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2Case2Gate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact Gate.applyNat_X_commute_update_outside_fun b0Idx p v f hp_ne_b0
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx g p v
        hp_ne_b0 hp_ne_b1 hp_ne_flag
    · intro g
      refine applyNat_seq_commute_update _ _ g p v ?_ ?_
      · intro h
        exact sqir_modAdd_qstart_commute_update_disjoint bits q_start N
          (tableValue a N 2 k 2) flagIdx flagPos p v h
          hp_disj_workspace hp_ne_flagPos hp_ne_flag
      · intro h
        refine applyNat_seq_commute_update _ _ h p v ?_ ?_
        · intro i
          exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx i p v
            hp_ne_b0 hp_ne_b1 hp_ne_flag
        · intro i
          exact Gate.applyNat_X_commute_update_outside_fun b0Idx p v i hp_ne_b0

/-- **PRIMARY L-2′ THEOREM: q_start-parametric selected-add frame.**

The composed `toyWindow2SelectedAddGate_qstart` commutes with any
`update _ p v` where `p` is disjoint from:
- the Cuccaro workspace at `[q_start, q_start + 2*bits + 1)`,
- the case gate's CCX-control positions `b0Idx`, `b1Idx`,
- the CCX-target `flagIdx`,
- the inner mod-add's flag position `flagPos`.

The workspace disjointness is given as a disjunction
(`p < q_start ∨ q_start + 2*bits + 1 ≤ p`), so `p` can be **below**
the workspace (e.g., at official data positions in Architecture D)
as well as above.

This is the architectural-correctness frame property needed by the
Gidney-style two-register pipeline. -/
theorem toyWindow2SelectedAddGate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2SelectedAddGate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2SelectedAddGate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact toyWindow2Case1Gate_qstart_commute_update_disjoint bits q_start N a k
      flagIdx flagPos b0Idx b1Idx p v f
      hp_disj_workspace hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact toyWindow2Case2Gate_qstart_commute_update_disjoint bits q_start N a k
        flagIdx flagPos b0Idx b1Idx p v g
        hp_disj_workspace hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1
    · intro g
      exact toyWindow2Case3Gate_qstart_commute_update_disjoint bits q_start N a k
        flagIdx flagPos b0Idx b1Idx p v g
        hp_disj_workspace hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1

/-- **Data-position corollary** for the shifted layout `q_start = bits`.
At any data position `p < bits` distinct from the active window
control positions and flag positions, the selected-add gate
preserves the value at `p`. This is the form directly consumed by
Architecture D's compute step. -/
theorem toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint
    (bits N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_data : p < bits)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2SelectedAddGate_qstart bits bits N a k flagIdx flagPos b0Idx b1Idx)
          s) p v :=
  toyWindow2SelectedAddGate_qstart_commute_update_disjoint
    bits bits N a k flagIdx flagPos b0Idx b1Idx p v s
    (Or.inl hp_data) hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1

/-! ## Phase R7d^xxix-L-3′ — Architecture D state-builder + data preservation

For Gidney-style Architecture D, the input state has:
- official data register at positions `[0, bits)` holding bits of `x`
  (big-endian, matching `encodeDataZeroAnc`);
- shifted Cuccaro workspace at `q_start = bits` holding the
  accumulator `acc`;
- flag position above the workspace (the first free qubit, here
  taken as `bits + 2*bits + 1`).

Window control positions are slice-aliases into the data register:
- `gidneyB0Idx bits k := bits - 1 - 2*k` (bit `2*k` of `x` in
  big-endian).
- `gidneyB1Idx bits k := bits - 1 - (2*k + 1)` (bit `2*k + 1` of `x`).

This phase introduces the Architecture D state-builder
`gidneyComputeInput`, basic readback / disjointness lemmas, and the
**data-preservation theorem** showing the q_start-parametric
selected-add gate preserves all data positions other than the active
window controls.

Full single-window arithmetic correctness on `gidneyComputeInput`
(an actual `acc → (acc + a * windowValue) % N` advance) is deferred
to follow-up sub-ticks; it requires q_start-parametric versions of
the Cuccaro internal helpers (`mod_add_state_eq_when_control_false`,
`mod_add_above_layout_noop_on_F`, etc.) that the existing
`toyWindow2CaseN_state_eq_*` proofs depend on. Those helpers
unfold the Cuccaro adder internals and require careful porting. -/

/-- **Architecture D window-0 control position.** Bit `2*k` of `x`
lives at this position in the big-endian data register. -/
def gidneyB0Idx (bits k : Nat) : Nat := bits - 1 - 2 * k

/-- **Architecture D window-1 control position.** Bit `2*k + 1` of
`x` lives at this position in the big-endian data register. -/
def gidneyB1Idx (bits k : Nat) : Nat := bits - 1 - (2 * k + 1)

/-- **Architecture D flag position.** First free qubit above the
shifted Cuccaro workspace, available as scratch for the case-gate
CCX target. -/
def gidneyFlagPos (bits : Nat) : Nat := bits + 2 * bits + 1

/-- **Architecture D compute input state.** Data positions `[0, bits)`
encode `x` (big-endian, matching `encodeDataZeroAnc`); the shifted
Cuccaro workspace at `q_start = bits` encodes `acc`; positions
outside both regions fall through to the Cuccaro `false` base. -/
def gidneyComputeInput (bits x acc : Nat) : Nat → Bool :=
  fun q =>
    if q < bits then x.testBit (bits - 1 - q)
    else cuccaro_input_F bits false 0 acc q

/-- **Data-position readback.** At any data position `q < bits`, the
state stores `x.testBit (bits - 1 - q)`. -/
theorem gidneyComputeInput_data (bits x acc q : Nat) (hq : q < bits) :
    gidneyComputeInput bits x acc q = x.testBit (bits - 1 - q) := by
  unfold gidneyComputeInput
  rw [if_pos hq]

/-- **Window-0 readback.** At `gidneyB0Idx bits k`, the state holds
bit `2*k` of `x`. -/
theorem gidneyComputeInput_b0 (bits x acc k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyComputeInput bits x acc (gidneyB0Idx bits k) = x.testBit (2 * k) := by
  show gidneyComputeInput bits x acc (bits - 1 - 2 * k) = x.testBit (2 * k)
  have h_lt : bits - 1 - 2 * k < bits := by omega
  rw [gidneyComputeInput_data bits x acc _ h_lt]
  congr 1
  omega

/-- **Window-1 readback.** At `gidneyB1Idx bits k`, the state holds
bit `2*k + 1` of `x`. -/
theorem gidneyComputeInput_b1 (bits x acc k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyComputeInput bits x acc (gidneyB1Idx bits k) = x.testBit (2 * k + 1) := by
  show gidneyComputeInput bits x acc (bits - 1 - (2 * k + 1)) = x.testBit (2 * k + 1)
  have h_lt : bits - 1 - (2 * k + 1) < bits := by omega
  rw [gidneyComputeInput_data bits x acc _ h_lt]
  congr 1
  omega

/-- **Flag position readback (zero).** At `gidneyFlagPos bits`, the
state holds `false` whenever `acc < 2^bits` (so `acc.testBit bits =
false`). The position is `bits + 2*bits + 1` which, relative to the
shifted Cuccaro at `q_start = bits`, sits at offset `2*bits + 1` —
the first odd offset above the workspace, decoding to
`acc.testBit bits`. -/
theorem gidneyComputeInput_at_flagPos (bits x acc : Nat)
    (hbits : 1 ≤ bits) (hacc_lt : acc < 2^bits) :
    gidneyComputeInput bits x acc (gidneyFlagPos bits) = false := by
  unfold gidneyComputeInput gidneyFlagPos
  have h_ge : ¬ bits + 2 * bits + 1 < bits := by omega
  rw [if_neg h_ge]
  unfold cuccaro_input_F
  have h_not_lt : ¬ (bits + 2 * bits + 1 < bits) := by omega
  rw [if_neg h_not_lt]
  have h_idx : bits + 2 * bits + 1 - bits = 2 * bits + 1 := by omega
  rw [h_idx]
  have h_ne_zero : ¬ (2 * bits + 1 = 0) := by omega
  rw [if_neg h_ne_zero]
  have h_odd : (2 * bits + 1) % 2 = 1 := by omega
  rw [if_pos h_odd]
  have h_div : (2 * bits + 1 - 1) / 2 = bits := by omega
  rw [h_div]
  exact Nat.testBit_eq_false_of_lt hacc_lt

/-! ### Shifted-layout arithmetic helpers -/

/-- `gidneyB0Idx k` is a data position when the window fits. -/
theorem gidneyB0_lt_bits (bits k : Nat) (hwin : 2 * k + 1 < bits) :
    gidneyB0Idx bits k < bits := by
  unfold gidneyB0Idx; omega

/-- `gidneyB1Idx k` is a data position when the window fits. -/
theorem gidneyB1_lt_bits (bits k : Nat) (hwin : 2 * k + 1 < bits) :
    gidneyB1Idx bits k < bits := by
  unfold gidneyB1Idx; omega

/-- The two window control positions for a single window are
distinct. -/
theorem gidneyB0_ne_gidneyB1 (bits k : Nat) (hwin : 2 * k + 1 < bits) :
    gidneyB0Idx bits k ≠ gidneyB1Idx bits k := by
  unfold gidneyB0Idx gidneyB1Idx; omega

/-- `gidneyFlagPos` is above the shifted Cuccaro workspace. -/
theorem gidneyFlag_above_workspace (bits : Nat) :
    bits + 2 * bits + 1 ≤ gidneyFlagPos bits := by
  unfold gidneyFlagPos; omega

/-- Any data position is distinct from `gidneyFlagPos`. -/
theorem gidneyFlag_ne_data (bits q : Nat) (hq : q < bits) :
    q ≠ gidneyFlagPos bits := by
  unfold gidneyFlagPos; omega

/-- `gidneyFlagPos` is distinct from the window-0 control. -/
theorem gidneyFlagPos_ne_gidneyB0 (bits k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyFlagPos bits ≠ gidneyB0Idx bits k := by
  unfold gidneyFlagPos gidneyB0Idx; omega

/-- `gidneyFlagPos` is distinct from the window-1 control. -/
theorem gidneyFlagPos_ne_gidneyB1 (bits k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyFlagPos bits ≠ gidneyB1Idx bits k := by
  unfold gidneyFlagPos gidneyB1Idx; omega

/-! ### State-builder reconstruction lemma

The data-preservation theorem uses the observation that updating a
state at position `p` and then applying the gate is the same as
applying the gate first and then updating at `p`, provided `p` is
disjoint from the gate's support. This is exactly the L-2′ frame
theorem. The state-builder reconstruction shows we can express
`gidneyComputeInput bits x acc` as the underlying `cuccaro_input_F`
base with successive data-position updates — but we don't actually
need this; the direct evaluation at q for the gate's output state
follows from a single application of L-2′. -/

/-- **PRIMARY L-3′ THEOREM: data-position preservation under the
shifted-workspace selected-add gate.**

At any data position `q < bits` other than the active window
controls `gidneyB0Idx bits k` and `gidneyB1Idx bits k`, the gate
preserves the value of `gidneyComputeInput bits x acc q`.

The proof is a single application of the L-2′ data-position frame
theorem (`toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint`)
applied to the difference between the input state and a "zeroed at
q" state. -/
theorem toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint
    (bits N a k acc x q : Nat)
    (hwin : 2 * k + 1 < bits)
    (hq : q < bits)
    (hq_ne_b0 : q ≠ gidneyB0Idx bits k)
    (hq_ne_b1 : q ≠ gidneyB1Idx bits k) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k
          (gidneyFlagPos bits) (gidneyFlagPos bits)
          (gidneyB0Idx bits k) (gidneyB1Idx bits k))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  -- Strategy: express gidneyComputeInput as
  --   update (substateWithQReplaced) q (gidneyComputeInput bits x acc q)
  -- Then apply L-2′ to commute the gate past the outer update, since
  -- q is disjoint from b0Idx, b1Idx, flagPos.
  -- The update commutes through the gate; reading at q gives the
  -- assigned value, which is the original gidneyComputeInput value at q.
  set f := gidneyComputeInput bits x acc with hf_def
  have h_self : update f q (f q) = f := FormalRV.Framework.update_self f q
  have h_qne_flag : q ≠ gidneyFlagPos bits := gidneyFlag_ne_data bits q hq
  have h_commute := toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint
    bits N a k (gidneyFlagPos bits) (gidneyFlagPos bits)
    (gidneyB0Idx bits k) (gidneyB1Idx bits k) q (f q) f
    hq h_qne_flag h_qne_flag hq_ne_b0 hq_ne_b1
  -- h_commute : applyNat gate (update f q (f q)) = update (applyNat gate f) q (f q)
  rw [h_self] at h_commute
  -- h_commute : applyNat gate f = update (applyNat gate f) q (f q)
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Corollary: data-position preservation at non-window positions.**
For data positions `q < bits` that fall OUTSIDE the active window
(`q < gidneyB1Idx bits k ∨ q > gidneyB0Idx bits k`), the gate
preserves the value. Useful when iterating over multi-window
products. -/
theorem toyWindow2SelectedAddGate_qstart_preserves_data_outside_window
    (bits N a k acc x q : Nat)
    (hwin : 2 * k + 1 < bits)
    (hq : q < bits)
    (h_outside : q < bits - 1 - (2 * k + 1) ∨ bits - 1 - 2 * k < q) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k
          (gidneyFlagPos bits) (gidneyFlagPos bits)
          (gidneyB0Idx bits k) (gidneyB1Idx bits k))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have hq_ne_b0 : q ≠ gidneyB0Idx bits k := by
    unfold gidneyB0Idx
    rcases h_outside with h | h <;> omega
  have hq_ne_b1 : q ≠ gidneyB1Idx bits k := by
    unfold gidneyB1Idx
    rcases h_outside with h | h <;> omega
  exact toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint
    bits N a k acc x q hwin hq hq_ne_b0 hq_ne_b1

/-! ### Status: R7d^xxix-L-3′ partial deliverable

What landed:
- Architecture D layout primitives:
  `gidneyB0Idx`, `gidneyB1Idx`, `gidneyFlagPos`, `gidneyComputeInput`.
- Readback lemmas: `_data`, `_b0`, `_b1`, `_at_flagPos`.
- Shifted-layout arithmetic helpers (B0_lt_bits, B1_lt_bits,
  B0_ne_B1, flag_above_workspace, flag_ne_data, flagPos_ne_b0/b1).
- Primary deliverable: **data-position preservation theorem**
  `toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint`
  showing all non-active data positions are preserved.
- Outside-window corollary
  `toyWindow2SelectedAddGate_qstart_preserves_data_outside_window`.

What is deferred to follow-up ticks (full single-window arithmetic
correctness):
- q_start-parametric versions of the Cuccaro internal helpers:
  - `mod_add_state_eq_when_control_false_on_qstart_input`.
  - `mod_add_above_layout_noop_on_F` at q_start.
- q_start-parametric per-case state-eq theorems
  (Case1/2/3 FF/FT/TF/TT no-op or fire branches).
- The composed q_start selected-add state-equation theorem
  `toyWindow2SelectedAddGate_qstart_state_eq_on_gidneyComputeInput`.

Why deferred: the existing q_start = 2 state-eq theorems
(`toyWindow2Case3Gate_state_eq_FF_noop`, etc.) span ~200 lines each
because they unfold the Cuccaro adder internals at the specific
positions of the q_start = 2 layout. A clean port to q_start
requires ~6-8 helper lemmas to be ported first, each ~100-200
lines. This is a multi-tick effort that should follow its own
dedicated planning. -/

/-! ## Phase R7d^xxix-L-3.5′ — q_start controlled-mod-add preservation

This phase closes the q_start-parametric **frame-based**
preservation theorem for the controlled mod-add gate
`sqir_style_controlledModAddConst_gate bits q_start N c controlIdx
flagPos`.

**Scope**: positions OUTSIDE the gate's working set are proven
preserved (a strict subset of "full no-op when control is false",
but the workspace/control/flagPos preservation requires the FULL
clean theorem at q_start which is multi-tick effort).

**Why the FULL state preservation is deferred**:
- The q_start = 2 clean theorem
  (`sqir_style_controlledModAddConst_gate_clean`) bakes in
  q_start = 2 AND flagPos = 1 throughout its multi-stage proof
  (deliverables A through G, each ~50-200 lines, in
  `CuccaroSQIRDirtyFlag.lean`).
- The `ControlledModAdd.clean_*` projections used by
  `mod_add_state_eq_when_control_false_on_Case3Input` extract from
  the q_start = 2 clean bundle; they do NOT generalize to q_start =
  bits without a parallel clean theorem.
- Porting clean to parametric q_start requires touching the entire
  `sqir_style_controlledModAddConst_gate_clean` proof chain,
  redoing each deliverable.

**What L-3.5′ achieves**: the FRAME-based preservation gives us
"the gate preserves any state at positions outside the workspace
and outside control/flag positions". This is a clean, useful
result that survives any future clean-theorem port. -/

/-- **q_start frame preservation: gate preserves state at any single
position disjoint from its working set.** Direct consequence of the
L-2′ `sqir_modAdd_qstart_commute_update_disjoint` via
`update_self`. -/
theorem sqir_modAdd_qstart_preserves_at_outside
    (bits q_start N c controlIdx flagPos q : Nat) (s : Nat → Bool)
    (h_q_outside :
      q < q_start ∨ q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos)
    (h_q_ne_control : q ≠ controlIdx) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos) s q
      = s q := by
  have h_self : update s q (s q) = s := FormalRV.Framework.update_self s q
  have h_commute := sqir_modAdd_qstart_commute_update_disjoint
    bits q_start N c controlIdx flagPos q (s q) s
    h_q_outside h_q_ne_flag h_q_ne_control
  rw [h_self] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Above-layout no-op specialization** (matches the prompt's
Step 2 fallback shape). On the zero-accumulator Cuccaro base
`cuccaro_input_F q_start false 0 acc`, at any position above the
workspace + ≠ flagPos, the gate yields `false`. -/
theorem mod_add_above_layout_noop_on_F_qstart
    (bits q_start N c flagPos acc q : Nat)
    (hacc : acc < 2^bits)
    (h_q_above : q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c flagPos flagPos)
        (cuccaro_input_F q_start false 0 acc) q
      = false := by
  rw [sqir_modAdd_qstart_preserves_at_outside bits q_start N c
        flagPos flagPos q _ (Or.inr h_q_above) h_q_ne_flag h_q_ne_flag]
  exact cuccaro_input_F_above_eq_false q_start bits acc q h_q_above hacc

/-- **Architecture D mod-add preservation at data positions.** For
any data position `q < bits`, the q_start = bits controlled
mod-add gate (with control = flag = gidneyFlagPos) preserves the
value of `gidneyComputeInput bits x acc` at `q`.

This holds because data positions `q < bits = q_start` are below
the shifted workspace, and `gidneyFlagPos = 3*bits + 1 > bits >
q`. -/
theorem sqir_modAdd_qstart_preserves_data_on_gidneyComputeInput
    (bits N c x acc q : Nat)
    (hq : q < bits) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate
          bits bits N c (gidneyFlagPos bits) (gidneyFlagPos bits))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have h_q_outside : q < bits ∨ bits + 2 * bits + 1 ≤ q := Or.inl hq
  have h_q_ne_flag : q ≠ gidneyFlagPos bits := gidneyFlag_ne_data bits q hq
  exact sqir_modAdd_qstart_preserves_at_outside bits bits N c
    (gidneyFlagPos bits) (gidneyFlagPos bits) q _ h_q_outside
    h_q_ne_flag h_q_ne_flag

/-- **Architecture D mod-add preservation above the flag.** For
any position `q > gidneyFlagPos bits`, the q_start = bits
controlled mod-add gate preserves the value of `gidneyComputeInput
bits x acc` at `q`. -/
theorem sqir_modAdd_qstart_preserves_above_flag_on_gidneyComputeInput
    (bits N c x acc q : Nat)
    (h_q_above : gidneyFlagPos bits < q) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate
          bits bits N c (gidneyFlagPos bits) (gidneyFlagPos bits))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have h_q_workspace_above : bits + 2 * bits + 1 ≤ q := by
    have : bits + 2 * bits + 1 = gidneyFlagPos bits := by unfold gidneyFlagPos; rfl
    omega
  have h_q_outside : q < bits ∨ bits + 2 * bits + 1 ≤ q := Or.inr h_q_workspace_above
  have h_q_ne_flag : q ≠ gidneyFlagPos bits := by
    intro h_eq; rw [h_eq] at h_q_above; exact absurd h_q_above (Nat.lt_irrefl _)
  exact sqir_modAdd_qstart_preserves_at_outside bits bits N c
    (gidneyFlagPos bits) (gidneyFlagPos bits) q _ h_q_outside
    h_q_ne_flag h_q_ne_flag

/-- **c = 0 trivial no-op.** When the constant being added is 0,
the controlled mod-add gate is literally `Gate.I`. -/
theorem sqir_style_controlledModAddConst_gate_qstart_zero_noop
    (bits q_start N controlIdx flagPos : Nat) (s : Nat → Bool) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos) s
      = s := by
  unfold sqir_style_controlledModAddConst_gate
  rw [if_pos rfl]
  exact Gate.applyNat_I s

/-! ## Phase R7d^xxix-L-3.6′ — Architecture D control=false target-decode

The L-3.6′ tick ported the control=false target-decode of the
controlled mod-add candidate from q_start = 2 + flagPos = 1 to
parametric q_start + flagPos (see `BQAlgo/CuccaroSQIRDirtyFlag.lean`
for the chain of five ports).

This section specializes the new ported theorem to Architecture D
(q_start = bits, flagPos = gidneyFlagPos bits). The specialization
is the FIRST architectural-correctness theorem for the Gidney-style
layout: it shows that when the control bit is false, the mod-add
gate's target decode equals the original `x`. -/

/-- **Architecture D second ancilla position.** Allocated just above
`gidneyFlagPos bits` so the controlled mod-add can use two distinct
above-workspace positions for its external control and internal
flag. -/
def gidneyFlagPos' (bits : Nat) : Nat := gidneyFlagPos bits + 1

/-- `gidneyFlagPos' bits` is distinct from `gidneyFlagPos bits`. -/
theorem gidneyFlagPos'_ne_gidneyFlagPos (bits : Nat) :
    gidneyFlagPos' bits ≠ gidneyFlagPos bits := by
  unfold gidneyFlagPos' gidneyFlagPos; omega

/-- `gidneyFlagPos' bits` is also above the shifted workspace. -/
theorem gidneyFlagPos'_above_workspace (bits : Nat) :
    bits + 2 * bits + 1 ≤ gidneyFlagPos' bits := by
  unfold gidneyFlagPos' gidneyFlagPos; omega

/-- **Architecture D control=false target-decode.** When the
external control at `gidneyFlagPos' bits` is `false`, the controlled
mod-add candidate (with `q_start = bits`, controlIdx = `gidneyFlagPos'
bits`, internal flagPos = `gidneyFlagPos bits`) preserves the
target's decoded value at `x`. -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false_gidney
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_target_val bits bits
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
      = x := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
    bits bits N c x (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)

/-- **R7d^xxix-L-3.7′ Gidney specialization (workspace bundle,
control=false).**  The Architecture-D controlled mod-add (external
control = `gidneyFlagPos' bits`, internal flagPos = `gidneyFlagPos
bits`) preserves the four workspace conjuncts after applying to the
shifted-workspace `cuccaro_input_F` base with control=false. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false_gidney
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_read_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (bits + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos' bits)
        = false := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
    bits bits N c x (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)

/-- **R7d^xxix-L-3.8′ Gidney specialization (clean bundle,
control=false).**  The Architecture-D controlled mod-add (q_start =
`bits`, internal flagPos = `gidneyFlagPos bits`, external controlIdx =
`gidneyFlagPos' bits`) clean bundle for the control=false branch.

Parametric in `dim` with the three standard dimension hypotheses:
- the shifted Cuccaro workspace fits: `bits + 2 * bits + 1 ≤ dim`;
- `gidneyFlagPos' bits < dim`;
- `gidneyFlagPos bits < dim`.

Trivial wrapper over
`sqir_style_controlledModAddConst_candidate_clean_control_false_qstart`. -/
theorem sqir_style_controlledModAddConst_candidate_clean_control_false_gidney
    (bits N c x dim : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (h_workspace : bits + 2 * bits + 1 ≤ dim)
    (h_flagPos'_lt_dim : gidneyFlagPos' bits < dim)
    (h_flagPos_lt_dim  : gidneyFlagPos bits  < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_candidate bits bits N c
          (gidneyFlagPos' bits) (gidneyFlagPos bits))
    ∧ cuccaro_target_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = x
    ∧ cuccaro_read_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (bits + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos' bits)
        = false := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
    bits bits N c x dim (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)
    h_workspace h_flagPos'_lt_dim h_flagPos_lt_dim

/-! ### Status: R7d^xxix-L-3.5′ partial deliverable

**Closed** (kernel-clean):
- `sqir_modAdd_qstart_preserves_at_outside` (generic single-position
  frame preservation).
- `mod_add_above_layout_noop_on_F_qstart` (above-layout no-op on
  cuccaro_input_F base, the prompt's Step 2 fallback shape).
- `sqir_modAdd_qstart_preserves_data_on_gidneyComputeInput`
  (Architecture D specialization at data positions).
- `sqir_modAdd_qstart_preserves_above_flag_on_gidneyComputeInput`
  (Architecture D specialization above flag).
- `sqir_style_controlledModAddConst_gate_qstart_zero_noop` (c = 0
  trivial no-op).

**Deferred** (require q_start clean theorem port, multi-tick):
- `sqir_style_controlledModAddConst_gate_qstart_noop_of_control_false`:
  full-state no-op when the control bit is false. Requires the
  q_start-parametric versions of
  `ControlledModAdd.clean_controlPreserved`,
  `ControlledModAdd.clean_flagFalse`,
  `ControlledModAdd.clean_targetDecode` (with control = false),
  and `ControlledModAdd.clean_readZero`. These all factor through
  `sqir_style_controlledModAddConst_gate_clean` which is q_start
  = 2 hard-coded.
- `sqir_style_controlledModAddConst_gate_qstart_noop_on_gidneyComputeInput`
  (the full Architecture-D specialization).
- `toyWindow2SelectedAddGate_qstart_FF_noop_on_gidneyComputeInput`
  (depends on the above).

The deferred theorems are NOT structural — they're proof-engineering
liabilities. The roadmap for porting them is:
1. Port `sqir_style_controlledModAddConst_gate_clean` to parametric
   q_start AND parametric flagPos (the latter being the harder
   change). ~6 subordinate clean lemmas, each ~50-200 lines.
2. Build q_start-parametric `ControlledModAddImpl` instance for
   q_start = bits and the gidneyFlagPos convention.
3. Extract `clean_*` projections.
4. Port `mod_add_state_eq_when_control_false_on_Case3Input` to
   parametric layout.
5. Use to build FF / FT / TF / TT case state_eq theorems for
   `toyWindow2CaseN_qstart`.
6. Compose into full `toyWindow2SelectedAddGate_qstart_state_eq`. -/

/-! ## Phase R7d^xxiv — per-window selected-add frame helper

The frame helper for the toy windowSize=2 selected-add gate. Says that
the gate commutes with an `update _ p v` whenever `p` is "inactive":
above the Cuccaro workspace, distinct from the gate's active window
positions, and distinct from `flagIdx`.

This is the key bridge for proving the full multi-window correctness
theorem `toyWindow2SelectedAddGate_on_windowed2Input` (see the docstring
of that theorem stub below for the proof strategy). -/

/-- **Frame helper for the selected-add gate.**

`toyWindow2SelectedAddGate` at active window positions `(b0Idx, b1Idx,
flagIdx)` commutes with any `update _ p v` where `p` is disjoint from
the gate's support. Specifically:
- `p` is above the Cuccaro workspace (`p ≥ 2 + 2*bits + 1`),
- `p` is not the active b0 / b1 positions,
- `p` is not `flagIdx`.

The proof composes primitive frame lemmas (`Gate.applyNat_X_commute
_update_outside_fun`, `applyNat_CCX_commute_update_disjoint`,
`sqir_style_controlledModAddConst_gate_commute_update_outside_fun`)
through `applyNat_seq_commute_update` per case gate (Case 1, 2, 3), then
chains the three case gates via two more `applyNat_seq_commute_update`. -/
theorem toyWindow2SelectedAddGate_commute_update_inactive
    (bits N a k flagIdx b0Idx b1Idx p : Nat) (v : Bool) (s : Nat → Bool)
    (hp_hi : 2 + 2 * bits + 1 ≤ p)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx)
    (hp_ne_flag : p ≠ flagIdx) :
    Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
        (update s p v)
      = update
          (Gate.applyNat
            (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx) s)
          p v := by
  have hp_out : p < 2 ∨ 2 + (2 * bits + 1) ≤ p := Or.inr (by omega)
  have hp_ne_one : p ≠ 1 := by omega
  -- Primitive commute proofs (universally quantified over inner state).
  have hX_b0 : ∀ f', Gate.applyNat (Gate.X b0Idx) (update f' p v)
                    = update (Gate.applyNat (Gate.X b0Idx) f') p v :=
    fun f' => Gate.applyNat_X_commute_update_outside_fun b0Idx p v f' hp_ne_b0
  have hX_b1 : ∀ f', Gate.applyNat (Gate.X b1Idx) (update f' p v)
                    = update (Gate.applyNat (Gate.X b1Idx) f') p v :=
    fun f' => Gate.applyNat_X_commute_update_outside_fun b1Idx p v f' hp_ne_b1
  have hCCX : ∀ f', Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                       (update f' p v)
                  = update (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx) f') p v :=
    fun f' => applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx f' p v
                hp_ne_b0 hp_ne_b1 hp_ne_flag
  have hM1 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1) f') p v :=
    fun f' => sqir_style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 1) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  have hM2 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1) f') p v :=
    fun f' => sqir_style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 2) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  have hM3 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1) f') p v :=
    fun f' => sqir_style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 3) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  -- Case-1 gate commute (5-layer seq X-CCX-M-CCX-X).
  have hCase1 : ∀ f', Gate.applyNat
                        (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hX_b1
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCCX
              (fun f''' => applyNat_seq_commute_update _ _ f''' p v hM1
                (fun f'''' => applyNat_seq_commute_update _ _ f'''' p v hCCX hX_b1)))
  -- Case-2 gate commute (5-layer seq X-CCX-M-CCX-X).
  have hCase2 : ∀ f', Gate.applyNat
                        (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.X b0Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 2) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
          (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hX_b0
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCCX
              (fun f''' => applyNat_seq_commute_update _ _ f''' p v hM2
                (fun f'''' => applyNat_seq_commute_update _ _ f'''' p v hCCX hX_b0)))
  -- Case-3 gate commute (3-layer seq CCX-M-CCX).
  have hCase3 : ∀ f', Gate.applyNat
                        (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 3) flagIdx 1)
              (Gate.CCX b0Idx b1Idx flagIdx))) (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hCCX
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hM3 hCCX)
  -- Compose: toyWindow2SelectedAddGate = Case1Gate ; Case2Gate ; Case3Gate.
  show Gate.applyNat (Gate.seq (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (Gate.seq (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
                    (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)))
        (update s p v) = _
  exact applyNat_seq_commute_update _ _ s p v hCase1
          (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCase2 hCase3)

/-! ### Documentation: main multi-window theorem strategy

The full main theorem
```
toyWindow2SelectedAddGate_on_windowed2Input : ∀ ... ,
  Gate.applyNat (toyWindow2SelectedAddGate ... k ... (b0Idx k) (b1Idx k))
      (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
    = windowed2Input
        (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
        b0Idx b1Idx b0 b1 numWin
```
is proved by induction on `numWin`. Two cases per step (`numWin = n + 1`):

**Case B (k < n, inactive newest):** The two outermost updates of
`windowed2Input ... (n+1)` are at the inactive positions
`(b0Idx n, b1Idx n)`. By cross-window distinctness, these positions
satisfy the frame helper's "inactive" predicate
(`p ≠ b0Idx k`, `p ≠ b1Idx k`, `p ≠ flagIdx`, `p ≥ 2 + 2*bits + 1`).
Apply `toyWindow2SelectedAddGate_commute_update_inactive` twice to push
the two outer updates outside the gate, then apply the inductive
hypothesis on the inner `windowed2Input ... n`, then re-apply
`windowed2Input_succ` to reconstruct the result.

**Case A (k = n, active newest):** The outer two updates ARE the
active layer `(b0Idx n, b1Idx n) = (b0Idx k, b1Idx k)`. Inside is
`windowed2Input ... n` containing `n` inactive prefix layers. To apply
`toyWindow2SelectedAddGate_state_eq_spec`, we need the inner state to
be `cuccaro_input_F 2 false 0 acc` (i.e., no inactive prefix).
Strategy: inner induction on `n` (the inactive prefix size).
- Inner base `n = 0`: inner state IS `cuccaro_input_F`. State is a
  literal `toyWindow2Case3Input`. Apply spec directly.
- Inner step `n = j + 1`: the inner state has outer layer `(b0Idx j,
  b1Idx j)`. Use `update_comm` (four times) to swap this layer past
  the active `(b0Idx k, b1Idx k)` updates, bringing the inactive layer
  outermost. Use the frame helper to commute the inactive layer through
  the gate. Use inner IH on the stripped state. Then `update_comm` back.

Hypotheses required: cross-window distinctness `b0Idx i ≠ b0Idx j`,
`b1Idx i ≠ b1Idx j`, `b0Idx i ≠ b1Idx j` (for any i, j with i ≠ j),
plus the existing single-window hypotheses. The four `update_comm`
swaps need each pair (`b0Idx k`, `b1Idx k`) × (`b0Idx j`, `b1Idx j`)
to be distinct — which is exactly the cross-window distinctness.

This proof structure is mechanically clear but verbose (~150–200 lines
total). Deferred to a follow-up tick to keep this commit focused on
the reusable frame infrastructure. -/

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
