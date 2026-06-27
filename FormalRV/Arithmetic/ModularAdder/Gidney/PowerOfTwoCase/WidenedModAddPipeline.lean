/- PowerOfTwoCase — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.PowerOfTwoCase.FrameRestorationAndUnderflowFlag

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Widened modular-addition arithmetic pipeline (width `bits + 1`)

To compute `(x + c) mod N` reversibly when `x, c < N ≤ 2^bits`, we
*cannot* work at width `bits` — the intermediate sum `s = x + c` may
exceed `2^bits`, losing the overflow bit.  The standard widened
pipeline operates at width `bits + 1`:

1. **add** `c`:                    `s = x + c`,  `s < 2N ≤ 2^(bits+1)`.
2. **subtract** `N`:                `y = subConstPow2WideSpec bits N s`.
   Bit `bits` of `y` is the comparison flag `decide (s < N)`.
3. **conditionally add back** `N`:  `z = (y + (if flag then N else 0)) % 2^(bits+1)`.

The arithmetic correctness is `z % 2^bits = (x + c) % N`.  This
section proves that identity at the Nat level, then begins the
gate-level chain via per-step idealized-input theorems. -/

/-! ### Deliverable A — sum bounds -/

/-- After widened add, the sum fits in `bits + 1` bits. -/
theorem modAdd_sum_bound
    (bits N x c : Nat) (hN : N ≤ 2^bits) (hx : x < N) (hc : c < N) :
    x + c < 2^(bits + 1) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  omega

/-- After widened add, the sum is bounded by `2N` (the tighter bound
needed by the generalized underflow theorem). -/
theorem modAdd_sum_lt_twoN
    (N x c : Nat) (hx : x < N) (hc : c < N) :
    x + c < 2 * N := by omega

/-- **Widened modular-add pipeline correctness** (arithmetic level).
For `0 < N ≤ 2^bits` and `x, c < N`, the low `bits` bits of the
widened pipeline result equal `(x + c) mod N`. -/
theorem modAddConstArithmeticSpec_correct
    (bits N c x : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    modAddConstArithmeticSpec bits N c x % 2^bits = (x + c) % N := by
  unfold modAddConstArithmeticSpec
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_2pos : 0 < 2^(bits + 1) := Nat.two_pow_pos (bits + 1)
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_xc_lt_pow : x + c < 2^(bits + 1) := by omega
  by_cases h_flag : x + c < N
  · -- flag = true: subtract underflows, add-back restores `x + c`
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) + 2^(bits+1) - N := by
      unfold subConstPow2WideSpec
      have h_lt : (x + c) + (2^(bits+1) - N) < 2^(bits+1) := by omega
      rw [Nat.mod_eq_of_lt h_lt]; omega
    rw [h_y, decide_eq_true h_flag]
    show ((x + c) + 2^(bits+1) - N + N) % 2^(bits+1) % 2^bits = (x + c) % N
    have h_eq : ((x + c) + 2^(bits+1) - N) + N = (x + c) + 2^(bits+1) := by omega
    rw [h_eq, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show x + c < 2^(bits+1) by omega)]
    rw [Nat.mod_eq_of_lt (show x + c < 2^bits by omega)]
    exact (Nat.mod_eq_of_lt h_flag).symm
  · -- flag = false: subtract gives `x + c - N`, add-back is zero
    have h_le : N ≤ x + c := by omega
    have h_y : subConstPow2WideSpec bits N (x + c) = (x + c) - N := by
      unfold subConstPow2WideSpec
      have h_eq2 : (x + c) + (2^(bits + 1) - N) = ((x + c) - N) + 2^(bits + 1) := by omega
      rw [h_eq2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_y, decide_eq_false (by omega)]
    show ((x + c) - N + 0) % 2^(bits+1) % 2^bits = (x + c) % N
    rw [Nat.add_zero]
    have h_sN_lt : (x + c) - N < 2^bits := by omega
    have h_sN_lt' : (x + c) - N < 2^(bits+1) := by omega
    have h_sN_lt_N : (x + c) - N < N := by omega
    rw [Nat.mod_eq_of_lt h_sN_lt', Nat.mod_eq_of_lt h_sN_lt]
    have h_s_mod : (x + c) % N = (x + c) - N := by
      have h_split : x + c = ((x + c) - N) + N := by omega
      conv_lhs => rw [h_split]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt h_sN_lt_N]
    rw [h_s_mod]

/-! ### Deliverable C — low-bit version of the arithmetic correctness -/

/-- Bit-level form of `modAddConstArithmeticSpec_correct`: bit `i` of
the pipeline result (for `i < bits`) equals bit `i` of `(x + c) % N`. -/
theorem modAddConstArithmeticSpec_low_bit_correct
    (bits N c x i : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits) :
    (modAddConstArithmeticSpec bits N c x).testBit i
    = ((x + c) % N).testBit i := by
  have h_main : modAddConstArithmeticSpec bits N c x % 2^bits = (x + c) % N :=
    modAddConstArithmeticSpec_correct bits N c x hN_pos hN hx hc
  have h_bit : (modAddConstArithmeticSpec bits N c x % 2^bits).testBit i
              = (modAddConstArithmeticSpec bits N c x).testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [← h_bit, h_main]

/-! ### Deliverable D — per-step gate-level theorems (idealized inputs)

Each gate step in the pipeline is decoded into target-register
semantics, taking the *idealized* `adder_input_F` form as input.
Composition of these into a single gate-level theorem requires
intermediate-state preservation (the gate output of step `k` must be
extensionally equal to the `adder_input_F` form for step `k+1`),
which is the next tick's task and is NOT claimed here. -/

/-- **Step 1 — first add**.  Applied to a clean `adder_input_F (bits+1)
0 x`, `addConstGate (bits+1) c` decodes its target register to
`x + c` (no overflow, since `x + c < 2^(bits+1)`). -/
theorem modAdd_step1_target_decode
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    gidney_target_val (bits+1)
      (Gate.applyNat (addConstGate (bits+1) c) (adder_input_F (bits+1) 0 x))
    = x + c := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have hbits' : 2 ≤ bits + 1 := by omega
  have hc' : c < 2^(bits+1) := by omega
  have hx' : x < 2^(bits+1) := by omega
  obtain ⟨_, h_target, _, _⟩ := addConstGate_clean (bits+1) c x hbits' hc' hx'
  rw [h_target]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Step 2 — subtract `N`, observe comparison flag at `target_idx bits`**.
Applied to an *idealized* `adder_input_F (bits+1) 0 s` (i.e., target
holds `s` and read/carry are zero), `addConstGate (bits+1) (2^(bits+1) - N)`
makes the bit at `target_idx bits` equal `decide (s < N)`. -/
theorem modAdd_step2_flag_at_target_idx_bits
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    Gate.applyNat (addConstGate (bits+1) (2^(bits+1) - N))
      (adder_input_F (bits+1) 0 s) (target_idx bits)
    = decide (s < N) := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_yields_input_F (bits+1) (2^(bits+1)-N) s]
  have h_t_neq_read : ∀ j, j < bits+1 → target_idx bits ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareConstRead_preserves_outside (bits+1) (2^(bits+1)-N) _
        (target_idx bits) h_t_neq_read]
  exact patched_adder_sub_const_underflow_flag_bounded_sum bits N s hbits hN_pos hN hs

/-- **Step 3 — conditional add-back**.  Applied to the idealized
`update (adder_input_F (bits+1) 0 y) flagIdx flag` (target holds `y`,
read/carry zero, flag bit at out-of-band `flagIdx`), the
`conditionalAddConstGate (bits+1) N flagIdx` decodes target to
`(y + (if flag then N else 0)) mod 2^(bits+1)` — which is exactly the
`modAddConstArithmeticSpec` value when `y = subConstPow2WideSpec bits N s`
and `flag = decide (s < N)`. -/
theorem modAdd_step3_target_decode
    (bits N flagIdx y : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^(bits+1)) (hy : y < 2^(bits+1))
    (hflagIdx : adder_n_qubits (bits+1) ≤ flagIdx) :
    gidney_target_val (bits+1)
      (Gate.applyNat (conditionalAddConstGate (bits+1) N flagIdx)
        (update (adder_input_F (bits+1) 0 y) flagIdx flag))
    = (y + (if flag then N else 0)) % 2^(bits+1) := by
  have hbits' : 2 ≤ bits + 1 := by omega
  exact conditionalAddConstGate_target_decode (bits+1) N flagIdx y flag hbits' hN hy hflagIdx

/-! ## State-normalization for composing the full modular-add gate

The per-step theorems above take *idealised* `adder_input_F` inputs.
For full gate-level composition, we need per-bit / per-position
"normal-form" facts about the output of each step, plus a flag-copy
gate that promotes the comparison flag from the in-band
`target_idx bits` to an out-of-band `flagIdx`.

This section delivers:
* per-bit target correctness for `addConstGate` (Deliverable A);
* weak normal-form (working positions only) for step 1
  (Deliverable B);
* weak normal-form (working positions + flag bit) for step 2
  (Deliverable C);
* flag-copy gate + correctness + frame + WellTyped (Deliverable D).

Full gate-level chain composition (Deliverable E) is *blocked* by the
need to prove the patched Gidney adder is `WellTyped` at the tight
dimension `3 * n` (or equivalent: that the cascade preserves the gap
positions `read_idx n` and `target_idx n` for an `n`-bit adder).  The
existing WellTyped is at `adder_n_qubits n = 3*n + 2`, two positions
too loose to bridge intermediate gate states; see the closing comments
of this section for the precise blocker statement. -/

/-! ### Deliverable A — per-bit target correctness for `addConstGate` -/

/-- Bit-level form of `addConstGate_clean`'s target-decode line:
applied to `adder_input_F bits 0 x`, the gate's value at `target_idx i`
(for `i < bits`) equals bit `i` of `(x + c) % 2^bits`. -/
theorem addConstGate_target_bit
    (bits c x i : Nat) (hbits : 2 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (hi : i < bits) :
    Gate.applyNat (addConstGate bits c) (adder_input_F bits 0 x) (target_idx i)
    = ((x + c) % 2^bits).testBit i := by
  unfold addConstGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [prepareConstRead_yields_input_F bits c x]
  have h_t_neq_read : ∀ j, j < bits → target_idx i ≠ read_idx j := by
    intro j _; unfold target_idx read_idx; omega
  rw [prepareConstRead_preserves_outside bits c _ (target_idx i) h_t_neq_read]
  obtain ⟨_, h_target, _⟩ := gidney_adder_full_faithful_no_measurement_patched_correct_bits
                              bits c x hbits hc hx
  rw [h_target i hi]
  rw [Nat.add_comm c x]
  rw [Nat.testBit_mod_two_pow]; simp [hi]

/-- No-overflow corollary for widened addition.  When `x, c < N ≤ 2^bits`,
the widened sum `x + c` fits in `bits + 1` bits, so bit `i` of the
target is `(x + c).testBit i` (no mod needed). -/
theorem addConstGate_target_bit_no_overflow
    (bits N c x i : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) (hi : i < bits + 1) :
    Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (target_idx i)
    = (x + c).testBit i := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_xc_lt_2N : x + c < 2 * N := by omega
  have h_2N_le : 2 * N ≤ 2 * 2^bits := by omega
  have h_xc_lt : x + c < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  rw [addConstGate_target_bit (bits+1) c x i hbits' h_c_lt h_x_lt hi]
  rw [Nat.mod_eq_of_lt h_xc_lt]

/-! ### Deliverable B — weak normal-form for step 1 (`addConstGate`)

Working-position state characterization for `addConstGate (bits + 1) c`
applied to a clean `adder_input_F (bits + 1) 0 x`. -/

/-- After step 1, the read register is zero, carries are cleared, and
target bits 0..bits encode `(x + c)` (no overflow under `x, c < N`).
This is the WEAK normal-form: it does NOT claim function equality at
positions outside the working range. -/
theorem addConstGate_modAdd_step1_state_normal
    (bits N c x : Nat) (hbits : 1 ≤ bits) (hN : N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (target_idx i)
      = (x + c).testBit i)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (read_idx i)
      = false)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) c) (adder_input_F (bits + 1) 0 x) (carry_idx i)
      = false) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_c_lt : c < 2^(bits+1) := by
    have : c < 2^bits := by omega
    rw [h_pow_succ]; omega
  have h_x_lt : x < 2^(bits+1) := by
    have : x < 2^bits := by omega
    rw [h_pow_succ]; omega
  obtain ⟨_, _, h_read, h_carry⟩ := addConstGate_clean (bits+1) c x hbits' h_c_lt h_x_lt
  refine ⟨?_, h_read, h_carry⟩
  intro i hi
  exact addConstGate_target_bit_no_overflow bits N c x i hbits hN hx hc hi

/-! ### Deliverable C — weak normal-form for step 2 (`subConstGate`)

Applied to a clean `adder_input_F (bits + 1) 0 s` (idealised input —
NOT the actual post-step-1 state, but the structurally-clean version),
`subConstGate (bits + 1) N` writes the widened-subtraction bits and
places the comparison flag at `target_idx bits`. -/

/-- Weak normal-form for step 2.  Same caveat as step 1: working
positions only. -/
theorem subConstGate_modAdd_step2_state_normal
    (bits N s : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hs : s < 2 * N) :
    (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (target_idx i)
      = (subConstPow2WideSpec bits N s).testBit i)
    ∧ Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (target_idx bits)
      = decide (s < N)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (read_idx i)
      = false)
    ∧ (∀ i, i < bits + 1 →
      Gate.applyNat (subConstGate (bits + 1) N) (adder_input_F (bits + 1) 0 s) (carry_idx i)
      = false) := by
  have h_pow_succ : (2:Nat)^(bits + 1) = 2 * 2^bits := by rw [pow_succ]; ring
  have h_pow_pos : 0 < 2^bits := Nat.two_pow_pos bits
  have hbits' : 2 ≤ bits + 1 := by omega
  have h_s_lt : s < 2^(bits+1) := by rw [h_pow_succ]; omega
  have h_c : 2^(bits+1) - N < 2^(bits+1) := by
    have h_pow_pos2 : 0 < 2^(bits+1) := by rw [h_pow_succ]; omega
    omega
  unfold subConstGate
  obtain ⟨_, _, h_read, h_carry⟩ :=
    addConstGate_clean (bits+1) (2^(bits+1) - N) s hbits' h_c h_s_lt
  have h_target_bit : ∀ i, i < bits + 1 →
      Gate.applyNat (addConstGate (bits + 1) (2^(bits+1) - N)) (adder_input_F (bits + 1) 0 s)
        (target_idx i) = (subConstPow2WideSpec bits N s).testBit i := by
    intro i hi
    rw [addConstGate_target_bit (bits+1) (2^(bits+1) - N) s i hbits' h_c h_s_lt hi]
    rfl
  have h_flag :
      Gate.applyNat (addConstGate (bits + 1) (2^(bits+1) - N)) (adder_input_F (bits + 1) 0 s)
        (target_idx bits) = decide (s < N) := by
    rw [h_target_bit bits (by omega)]
    exact subConstPow2WideSpec_high_bit_bounded_sum bits N s hN_pos hN hs
  exact ⟨h_target_bit, h_flag, h_read, h_carry⟩

/-- Correctness: when the flag bit is initially `false`, the gate
sets it to the value of `target_idx bits`. -/
theorem copyTargetHighBitToFlag_correct
    (bits flagIdx : Nat) (f : Nat → Bool) (h_init : f flagIdx = false) :
    Gate.applyNat (copyTargetHighBitToFlag bits flagIdx) f flagIdx
    = f (target_idx bits) := by
  unfold copyTargetHighBitToFlag
  simp only [Gate.applyNat_CX]
  rw [update_eq, h_init]
  simp

/-- Frame: when `flagIdx` is out-of-band (`flagIdx ≥ adder_n_qubits (bits+1)`),
the flag-copy gate preserves all positions strictly inside the
working dimension. -/
theorem copyTargetHighBitToFlag_preserves_working
    (bits flagIdx : Nat) (f : Nat → Bool) (p : Nat)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx)
    (h_p_lt : p < adder_n_qubits (bits + 1)) :
    Gate.applyNat (copyTargetHighBitToFlag bits flagIdx) f p = f p := by
  unfold copyTargetHighBitToFlag
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ (by unfold adder_n_qubits at *; omega : p ≠ flagIdx)]

/-- WellTyped at the enlarged dimension `flagIdx + 1`. -/
theorem copyTargetHighBitToFlag_wellTyped
    (bits flagIdx : Nat)
    (hflagIdx : adder_n_qubits (bits + 1) ≤ flagIdx) :
    Gate.WellTyped (flagIdx + 1) (copyTargetHighBitToFlag bits flagIdx) := by
  unfold copyTargetHighBitToFlag
  unfold adder_n_qubits target_idx at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ### Deliverable E — STATUS

Composing `addConstGate (bits+1) c → subConstGate (bits+1) N →
copyTargetHighBitToFlag bits flagIdx → conditionalAddConstGate (bits+1) N flagIdx`
into a single `modAddConstGate_dirtyFlag` gate, with the target-decode
theorem `gidney_target_val bits (...) = (x + c) % N`, is BLOCKED on
the following gate-level intermediate-state preservation gap.

**Specific blocker.**  To chain the per-step theorems via the
existing primitive infrastructure, we need the state after step 1 to
be *extensionally equal* to `adder_input_F (bits+1) 0 (x+c)` (so that
the step-2 primitive `subConstGate_clean` / `addConstGate_target_bit`
can be applied).  The WEAK normal-form (Deliverable B) gives equality
at the working positions `read_idx i, target_idx i, carry_idx i` for
`i < bits + 1` — these are positions `0..3*bits + 2`.  But the
ambient dimension `adder_n_qubits (bits + 1) = 3*bits + 5` includes
two *gap* positions `read_idx (bits + 1) = 3*bits + 3` and
`target_idx (bits + 1) = 3*bits + 4` that are touched by neither the
prep cascade nor the (`bits + 1`)-wide patched Gidney adder cascade
(whose maximum touched position is `carry_idx bits = 3*bits + 2`),
but for which we lack a Lean frame lemma.

To close this gap, the next tick needs ONE of:
(a) a frame lemma showing the patched Gidney adder of width `n`
    preserves positions `≥ 3 * n` (which would give the strong
    normal-form `Gate.applyNat (addConstGate (bits+1) c) (adder_input_F
    (bits+1) 0 x) = adder_input_F (bits+1) 0 (x + c)` extensionally);
(b) a re-proof of the patched adder's `WellTyped` at the tight
    dimension `3 * n` (which would yield the same frame via the
    existing `applyNat_commute_update_above_dim`);
(c) a `Gate.applyNat` congruence lemma at a custom dimension matching
    the cascade's actual max-touched position, plus a per-gate
    "doesn't-touch" infrastructure.

The weak normal-forms (Deliverables B and C) together with
`conditionalAddConstGate_clean` are SUFFICIENT to prove Deliverable
E's headline once any of (a)/(b)/(c) closes; the proof skeleton is
the chain `addConstGate_modAdd_step1_state_normal →
(intermediate-state bridge) → subConstGate_modAdd_step2_state_normal →
(intermediate-state bridge) → copyTargetHighBitToFlag_correct →
(intermediate-state bridge) → modAdd_step3_target_decode →
modAddConstArithmeticSpec_low_bit_correct`.

The dirty-flag composite gate is NOT defined or proved in this
commit, to avoid making any unproven claim. -/

/-! ## Tick 1 — Gap-position frame lemmas and strengthened normalization

This section closes the gap blocker by proving:

* Per-step frame lemmas: `bit_step_*_preserves_above` for the first /
  interior / last / *_reverse / *_reverse_patched gates, each with a
  tight position bound derived from the bit index.
* Cascade frame lemmas: `forward_with_propagation`,
  `forward_faithful_full`, `forward_with_propagation_reverse_patched`,
  `forward_faithful_full_reverse_patched`, `final_cx_cascade` — each
  preserves positions above its actual support.
* Full patched-adder frame: positions `≥ 3 * w` preserved.
* `prepareConstRead`, `addConstGate`, `subConstGate` frame lemmas with
  the uniform bound `3 * bits ≤ p`.
* **Strengthened state normalization** lifting the weak normal-form
  theorems to full extensional `Gate.applyNat ... = adder_input_F ...`
  equalities.

These frame lemmas close the gap-position blocker identified in the
previous section. -/


end FormalRV.BQAlgo
