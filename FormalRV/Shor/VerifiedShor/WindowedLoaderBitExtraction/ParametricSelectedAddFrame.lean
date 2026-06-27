/- WindowedLoaderBitExtraction — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Shor.VerifiedShor.WindowedLoaderBitExtraction.ShiftedLayoutDisjointness

namespace VerifiedShor
namespace Windowed
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.Framework (Gate update)

/-! ## Phase R7d^xxix-L-2′ — q_start-parametric selected-add frame

For Architecture D (Gidney style, see
`GIDNEY_WINDOWED_ARITHMETIC_REVIEW.md`), the selected-add gate must
admit window control bits at positions **below** the Cuccaro
workspace — specifically at data positions `[0, bits)` when the
workspace starts at `q_start = bits`.

This section:
1. Generalizes `style_controlledModAddConst_gate_commute_update_outside_fun`
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
    rw [controlledCompareConst_commute_update_outside_fun bits q_start c
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


end Windowed
end VerifiedShor
