/-
  FormalRV.BQAlgo.CuccaroCompare — exact-budget comparator from
  the Cuccaro MAJ-chain forward pass.

  Tick 47: build the first exact-budget comparison primitive by
  reading the top carry of the Cuccaro MAJ chain BEFORE the reverse
  UMA chain uncomputes it.

  Mathematical idea: to compare `x` with `N`, add the two's-complement
  constant `K := 2^bits - N` to `x` and read the (bits)-th carry bit:
    carry_out_bit = decide (N ≤ x).
  The reverse UMA chain in `cuccaro_n_bit_adder_full` erases this
  carry; the forward-only gate retains it at position `q_start + 2*bits`.

  This file proves:
  - the arithmetic helper relating `Adder.carry false bits` to
    `(a + b).testBit bits` for a, b < 2^bits;
  - the comparator's top-carry value = `decide (N ≤ x)` (and its
    negation = `decide (x < N)`).

  IMPORTANT: this is a FORWARD-ONLY gate. It leaves the workspace
  in a "dirty" state — the MAJ chain has propagated XOR'd values
  through every register position. A separate reverse pass is needed
  to uncompute the workspace, which destroys the flag. Tick 48+
  will address how to use this flag before uncomputation (a future
  decision-point flagged in QUESTIONS.md). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst
import FormalRV.Arithmetic.Cuccaro.CuccaroSubConst

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Arithmetic helper: top carry of n-bit addition = `decide (a + b ≥ 2^bits)`. -/

/-- **Top-bit-of-sum lemma** (private helper).  For `a, b < 2^bits`,
the `bits`-th bit of `a + b` equals `decide (2^bits ≤ a + b)`. -/
private theorem testBit_top_of_sum_eq_decide_ge
    (bits a b : Nat) (ha : a < 2^bits) (hb : b < 2^bits) :
    (a + b).testBit bits = decide (2^bits ≤ a + b) := by
  by_cases h : 2^bits ≤ a + b
  · -- a + b ∈ [2^bits, 2 * 2^bits).
    have h_eq : a + b = 2^bits + (a + b - 2^bits) := by omega
    have h_diff_lt : a + b - 2^bits < 2^bits := by
      -- a + b ≤ 2*2^bits - 2 < 2*2^bits.
      have hpow : 2 * 2^bits = 2^(bits + 1) := by rw [pow_succ]; ring
      omega
    rw [h_eq, Nat.testBit_two_pow_add_eq]
    rw [Nat.testBit_lt_two_pow h_diff_lt]
    simp [h]
  · push_neg at h
    rw [Nat.testBit_lt_two_pow h]
    simp [Nat.not_le.mpr h]

/-- **Carry-out via top bit of sum** (private helper).  For
`a, b < 2^bits`, the carry-out of an n-bit addition equals the
`bits`-th bit of `a + b`. -/
private theorem Adder_carry_top_eq_testBit_sum
    (bits a b : Nat) (ha : a < 2^bits) (hb : b < 2^bits) :
    Adder.carry false bits (fun i => a.testBit i) (fun i => b.testBit i)
      = (a + b).testBit bits := by
  -- Via Adder.sumfb_eq_testBit_add_gen at index `bits`:
  -- sumfb false a.testBit b.testBit bits = (a + b + 0).testBit bits.
  have h_sumfb := Adder.sumfb_eq_testBit_add_gen false a b bits
  have ha_top : a.testBit bits = false := Nat.testBit_lt_two_pow ha
  have hb_top : b.testBit bits = false := Nat.testBit_lt_two_pow hb
  simp only [Adder.sumfb, ha_top, hb_top, Bool.toNat, Nat.add_zero] at h_sumfb
  simpa using h_sumfb

/-! ## Deliverable D — arithmetic carry-out helper. -/

/-- **HEADLINE arithmetic helper**: the carry-out of adding the
two's-complement constant `2^bits - N` to `x` equals `decide (N ≤ x)`. -/
theorem add_twos_complement_carry_out_eq
    (bits N x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Adder.carry false bits
        (fun i => (2^bits - N).testBit i)
        (fun i => x.testBit i)
      = decide (N ≤ x) := by
  have hK_lt : 2^bits - N < 2^bits := by omega
  rw [Adder_carry_top_eq_testBit_sum bits (2^bits - N) x hK_lt hx]
  rw [testBit_top_of_sum_eq_decide_ge bits (2^bits - N) x hK_lt hx]
  -- Goal: decide (2^bits ≤ 2^bits - N + x) = decide (N ≤ x).
  by_cases h : N ≤ x
  · have hge : 2^bits ≤ 2^bits - N + x := by omega
    simp [h, hge]
  · push_neg at h
    have hlt : 2^bits - N + x < 2^bits := by omega
    simp [Nat.not_le.mpr h, Nat.not_le.mpr hlt]

/-! ## Deliverable A — comparison-forward gate definition. -/

/-- **Forward-only Cuccaro comparison gate.**  Prepares the
two's-complement constant `K := 2^bits - N` in the read register,
then runs the MAJ chain.  The top carry at position `q_start + 2*bits`
holds `decide (N ≤ x)`.

This gate does NOT uncompute the workspace.  Subsequent positions
hold XOR'd intermediate values from the MAJ chain.  This is by
design — uncomputing would erase the flag. -/
def cuccaro_compareConstForwardGate (bits q_start N : Nat) : Gate :=
  seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
      (cuccaro_maj_chain bits q_start)

/-! ## Deliverable B — top-carry theorem. -/

/-- **HEADLINE — top-carry of the forward comparator = `decide (N ≤ x)`.**
After running `cuccaro_compareConstForwardGate bits q_start N` on
`cuccaro_input_F q_start false 0 x`, the qubit at position
`q_start + 2*bits` holds the comparison flag `decide (N ≤ x)`. -/
theorem cuccaro_compareConstForward_top_carry
    (bits q_start N x : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (cuccaro_compareConstForwardGate bits q_start N)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits)
      = decide (N ≤ x) := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (cuccaro_maj_chain bits q_start))
      (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits) = _
  simp only [Gate.applyNat_seq]
  -- After MAJ chain at top position: cuccaro_carry of the prepared state.
  rw [cuccaro_maj_chain_at_top_carry bits q_start
      (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
        (cuccaro_input_F q_start false 0 x))]
  -- Bridge cuccaro_carry to Adder.carry.
  rw [cuccaro_carry_eq_Adder_carry]
  -- The prepared state's relevant bits.
  have hK_lt : 2^bits - N < 2^bits := by omega
  -- Carry-in qubit: prepare doesn't touch q_start (it's not a read position).
  have h_carry_in : (Gate.applyNat
        (cuccaro_prepareConstRead bits q_start (2^bits - N))
        (cuccaro_input_F q_start false 0 x)) q_start = false := by
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) q_start
        (by intros j _ h; omega)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  rw [h_carry_in]
  -- b-stream: prepare doesn't touch target positions; input is x.
  have h_b_stream : ∀ k, (Gate.applyNat
        (cuccaro_prepareConstRead bits q_start (2^bits - N))
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * k + 1) = x.testBit k := by
    intro k
    rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) _
        (by intros j _ h; omega)]
    exact cuccaro_input_F_at_b q_start k false 0 x
  -- a-stream: prepare XOR's read positions with K.testBit; input a = 0.
  have h_a_stream : ∀ k, (Gate.applyNat
        (cuccaro_prepareConstRead bits q_start (2^bits - N))
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * k + 2)
        = (2^bits - N).testBit k := by
    intro k
    by_cases hk : k < bits
    · rw [cuccaro_prepareConstRead_at_read bits q_start (2^bits - N) k hk]
      rw [cuccaro_input_F_at_a q_start k false 0 x]
      simp [Nat.zero_testBit]
    · push_neg at hk
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) _
          (by intros j hj h; omega)]
      rw [cuccaro_input_F_at_a q_start k false 0 x]
      simp [Nat.zero_testBit]
      -- (2^bits - N).testBit k = false for k ≥ bits (since 2^bits - N < 2^bits).
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hK_lt (Nat.pow_le_pow_right (by omega) hk))
  rw [show (fun j => (Gate.applyNat
        (cuccaro_prepareConstRead bits q_start (2^bits - N))
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * j + 1))
        = (fun j => x.testBit j) from funext h_b_stream]
  rw [show (fun j => (Gate.applyNat
        (cuccaro_prepareConstRead bits q_start (2^bits - N))
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * j + 2))
        = (fun j => (2^bits - N).testBit j) from funext h_a_stream]
  -- Now: Adder.carry false bits x.testBit (2^bits - N).testBit = decide (N ≤ x).
  -- Adder.carry is symmetric in its two streams.
  rw [Adder.carry_sym]
  -- Apply the arithmetic helper.
  exact add_twos_complement_carry_out_eq bits N x hN_pos hN hx

/-! ## Deliverable C — underflow (negated) version. -/

/-- **Underflow version**: the negation of the top carry equals
`decide (x < N)`. -/
theorem cuccaro_compareConstForward_underflow
    (bits q_start N x : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    !(Gate.applyNat (cuccaro_compareConstForwardGate bits q_start N)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits))
      = decide (x < N) := by
  rw [cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx]
  by_cases h : N ≤ x
  · simp [h, Nat.not_lt.mpr h]
  · push_neg at h
    simp [h.le, h, Nat.not_le.mpr h]

/-! ## Deliverable B — WellTyped for the forward comparator. -/

/-- **WellTyped: the forward comparator fits in `q_start + 2*bits + 1`
qubits.** -/
theorem cuccaro_compareConstForwardGate_wellTyped
    (bits q_start N dim : Nat) (h : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_compareConstForwardGate bits q_start N) := by
  refine ⟨?_, ?_⟩
  · exact cuccaro_prepareConstRead_wellTyped bits q_start (2^bits - N) dim h
  · exact cuccaro_maj_chain_wellTyped bits q_start dim h

/-! ## Deliverable E — analysis of exact-budget flag-use strategy.

We now have:
- `cuccaro_compareConstForward_top_carry`: the flag IS at position
  `q_start + 2 * bits` of the forward comparator's output state, in
  the exact-budget `2*bits + 1` qubits.
- Caveat: the workspace BELOW this position is in a "dirty"
  intermediate state (XOR'd values from the MAJ chain).

**Tick-47 conclusion (exact-budget flag-use viability)**:

Within the exact `2*bits + 1` budget, the forward comparator's top
qubit DOES hold the comparison flag. However:

(i) The flag's position coincides with what would be the top a-bit
    in the layout. Using this flag as a control for a subsequent
    operation is straightforward in principle (e.g., as a control
    for a CCX gate).

(ii) After the forward comparator runs, the rest of the workspace
    holds intermediate XOR'd values. Any subsequent operation must
    eventually uncompute these to return to a clean state.

(iii) The standard "reversible computation" trick: use the flag,
    then run the REVERSE of the forward MAJ chain (the "uncompute"
    pass) to restore the input state. The flag itself remains in
    the top qubit after uncomputation.

This gives a viable exact-budget design:
  forward-MAJ ; copy-flag-to-flagPos ; reverse-MAJ
But "copy-flag-to-flagPos" requires an EXTRA qubit `flagPos`. Without
one, the flag and the workspace are entangled and any uncompute will
either destroy the flag or leave residual workspace.

Therefore the exact-budget forward comparator's top carry is a USABLE
flag ONLY IF:
- it's consumed (used as a control) BEFORE any uncompute pass, AND
- the subsequent uncompute is carefully designed to restore the
  workspace without destroying the flag-using operation's net effect.

This matches strategy (a) from QUESTIONS.md: a temporary in-place
use of the flag before any external "borrow a qubit" step.

The next-tick deliverable (Tick 48+) is to design such a usage:
the controlled-modular-add-back step that uses this flag as a
control directly (without copying it to another qubit), then runs
the appropriate uncompute. -/

/-- **Packaged exact-budget comparator forward gate.** -/
theorem cuccaro_compareConstForwardGate_primitive
    (bits q_start N x : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (q_start + (2 * bits + 1))
        (cuccaro_compareConstForwardGate bits q_start N)
    ∧ Gate.applyNat (cuccaro_compareConstForwardGate bits q_start N)
          (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits)
        = decide (N ≤ x) := by
  refine ⟨?_, ?_⟩
  · apply cuccaro_compareConstForwardGate_wellTyped bits q_start N
    omega
  · exact cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx

end FormalRV.BQAlgo
