/- CuccaroDirtyFlagStageCorrectness — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroDirtyFlagStageCorrectness.Part2

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 61 — SQIR-exact-layout specializations.

`q_start = 2`, `flagPos = 1`, dimension `sqir_modmult_rev_anc bits =
3 * bits + 11`. -/

/-- **Deliverable A — SQIR-layout comparator flag-copy.** -/
theorem sqir_style_compareConst_candidate_flag_sqir_layout
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x) 1
      = decide (N ≤ x) :=
  sqir_style_compareConst_candidate_flag_general bits 2 N x 1
    hN_pos hN hx (Or.inl (by omega))

/-- **Deliverable B — SQIR-layout clean comparator bundle.** -/
theorem sqir_style_compareConst_candidate_clean_sqir_layout
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_compareConst_candidate bits 2 N 1)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) 1
        = decide (N ≤ x)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) (2 + 2 * i + 2)
          = false)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) (2 + 2 * i + 1)
          = x.testBit i)
    ∧ Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
          (cuccaro_input_F 2 false 0 x) (2 + 2 * bits) = false := by
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- WellTyped at SQIR dim.
    apply sqir_style_compareConst_candidate_wellTyped bits 2 N 1
      (sqir_modmult_rev_anc bits)
    · unfold sqir_modmult_rev_anc; omega
    · unfold sqir_modmult_rev_anc; omega
    · omega
  · exact sqir_style_compareConst_candidate_flag_sqir_layout bits N x hbits hN_pos hN hx
  · -- read register restored: at (2 + 2*i + 2), workspace_restored_at_general gives input,
    -- and cuccaro_input_F at a-position with a=0 is false.
    intro i hi
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        (cuccaro_input_F 2 false 0 x) hflag_out (2 + 2 * i + 2) (by omega) (by omega)]
    rw [cuccaro_input_F_at_a 2 i false 0 x]
    simp [Nat.zero_testBit]
  · -- target register restored: at (2 + 2*i + 1), workspace + input bit.
    intro i hi
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        (cuccaro_input_F 2 false 0 x) hflag_out (2 + 2 * i + 1) (by omega) (by omega)]
    exact cuccaro_input_F_at_b 2 i false 0 x
  · -- top carry restored: 2 + 2*bits is q_start + 2*(bits-1) + 2 → a.testBit (bits-1) = 0.
    rw [sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        (cuccaro_input_F 2 false 0 x) hflag_out (2 + 2 * bits) (by omega) (by omega)]
    have h_eq : 2 + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    simp [Nat.zero_testBit]

/-- **Deliverable C — SQIR-layout dirty-flag mod-N add target decode.** -/
theorem sqir_style_modAddConst_dirtyFlag_target_decode_sqir_layout
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false))
      = (x + c) % N :=
  sqir_style_modAddConst_dirtyFlag_target_decode_general bits 2 N c x 1
    hbits hN_pos hN hN2 hx hc (by intros i _; omega) (Or.inl (by omega))

/-- **Deliverable D — SQIR-layout dirty-flag mod-N add clean-except-flag bundle.** -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag_sqir_layout
    (bits N c x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hx : x < N) (hc : c < N) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 2
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate bits 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = decide (N ≤ x + c) := by
  apply sqir_style_modAddConst_dirtyFlag_clean_except_flag_general bits 2 N c x 1
      (sqir_modmult_rev_anc bits) hbits hN_pos hN hN2 hx hc
  · unfold sqir_modmult_rev_anc; omega
  · unfold sqir_modmult_rev_anc; omega
  · intros i _; omega
  · exact Or.inl (by omega)

/-- **Deliverable E — BasicSetting-based SQIR-layout corollary.**
Combines the SQIR-layout bundle with the sizing relation from
`BasicSetting`.  Instantiates `bits := n + 1` as the canonical
workspace width per `BasicSetting_twoN_le_pow_succ`. -/
theorem sqir_style_modAddConst_dirtyFlag_clean_except_flag_from_BasicSetting
    (a r N m n c x : Nat)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (hx : x < N) (hc : c < N) :
    Gate.WellTyped (sqir_modmult_rev_anc (n + 1))
        (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
    ∧ cuccaro_target_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = (x + c) % N
    ∧ cuccaro_read_val (n + 1) 2
          (Gate.applyNat
            (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
            (update (cuccaro_input_F 2 false 0 x) 1 false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 2
        = false
    ∧ Gate.applyNat
          (sqir_style_modAddConst_dirtyFlag_candidate (n + 1) 2 N c 1)
          (update (cuccaro_input_F 2 false 0 x) 1 false) 1
        = decide (N ≤ x + c) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN_le : N ≤ 2 ^ (n + 1) := by
    have : N ≤ 2 * N := by omega
    omega
  exact sqir_style_modAddConst_dirtyFlag_clean_except_flag_sqir_layout (n + 1) N c x
    (by omega) hN_pos hN_le hN2 hx hc

/-! ## Tick 62 — Flag-uncomputation infrastructure.

The Tick 61 SQIR-layout bundle exposes a dirty flag holding
`decide (N ≤ x + c)`.  To clean it, we observe an arithmetic identity:

  For `0 < c`, `x < N`, `c < N`, `0 < N`:
    `decide (c ≤ (x + c) % N) = ! decide (N ≤ x + c)`.

So running `compareConst(c)` on the post-dirty-flag state would XOR
`decide (c ≤ (x+c) % N) = ! decide (N ≤ x+c)` into the flag, giving
`decide (N ≤ x+c) XOR ! decide (N ≤ x+c) = true`.  A subsequent
`X(flagPos)` flips this to `false`, restoring the flag.

We prove (Task 1) the comparator's general flag-XOR semantics, the
arithmetic identity, and define the clean candidate.  Full flag
restoration is deferred to Tick 63 because composing the XOR semantics
with the dirty-flag bundle requires a function-level state equality
that we don't yet have (the existing dirty-flag bundle only exposes
DECODED workspace properties, not bit-level state equality).

The c = 0 case is special: the dirty flag is already `false` after
`dirtyFlag(c=0)`, so cleanup is trivially identity — but the current
clean candidate over-cleans it.  We carry the precondition `0 < c`
for the clean candidate. -/

/-- Helper for the XOR flag theorem: the inner `(prepare; maj)` block
at `q_start + 2*bits` (top carry) equals `decide (N ≤ x)` even when
the input has an outside `update` at `flagPos`. -/
lemma prepareMaj_at_top_eq_after_update
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (update (cuccaro_input_F q_start false 0 x) flagPos flag))
        (q_start + 2 * bits)
      = decide (N ≤ x) := by
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start (2^bits - N)
        flagPos flag _ hflag_out]
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start flagPos flag _ hflag_out]
  have h_ne : q_start + 2 * bits ≠ flagPos := by
    rcases hflag_out with hl | hr
    · omega
    · omega
  rw [update_neq _ _ _ _ h_ne]
  have h_carry := cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx
  unfold cuccaro_compareConstForwardGate at h_carry
  simp only [Gate.applyNat_seq] at h_carry
  exact h_carry

/-- **HEADLINE Task 1 — comparator flag-XOR semantics.**  For any
initial flag value `flag`, the SQIR-style comparator at `flagPos`
returns `flag XOR decide (N ≤ x)`.  This is the key polarity result
needed for any flag-uncomputation construction. -/
theorem sqir_style_compareConst_candidate_flag_xor
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_compareConst_candidate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos flag) flagPos
      = xor flag (decide (N ≤ x)) := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (cuccaro_prepareConstRead bits q_start (2^bits - N))))))
      (update (cuccaro_input_F q_start false 0 x) flagPos flag) flagPos = _
  simp only [Gate.applyNat_seq]
  have h_flagPos_not_read : ∀ j, j < bits → flagPos ≠ q_start + 2 * j + 2 := by
    intros j _ heq; rcases hflag_out with hl | hr <;> omega
  rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
  -- The "state at flagPos" (before CX, through maj_chain ∘ prepare₁) is `flag`.
  have h_flag_state :
      Gate.applyNat (cuccaro_maj_chain bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - N))
          (update (cuccaro_input_F q_start false 0 x) flagPos flag)) flagPos = flag := by
    rcases hflag_out with h_below | h_above
    · rw [cuccaro_maj_chain_frame_below bits q_start _ flagPos h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
      exact update_eq _ _ _
    · rw [cuccaro_maj_chain_frame_above bits q_start _ flagPos h_above]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - N) flagPos h_flagPos_not_read]
      exact update_eq _ _ _
  -- Top-carry value (= state at q_start + 2*bits) before CX = decide (N ≤ x).
  have h_top_state := prepareMaj_at_top_eq_after_update bits q_start N x flagPos flag
    hN_pos hN hx hflag_out
  -- Strip maj_inv (frame at flagPos), then CX.
  rcases hflag_out with h_below | h_above
  · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ flagPos h_below]
    simp only [Gate.applyNat_CX, update_eq]
    rw [h_flag_state, h_top_state]
  · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ flagPos h_above]
    simp only [Gate.applyNat_CX, update_eq]
    rw [h_flag_state, h_top_state]

/-- **SQIR-layout corollary of Task 1.** -/
theorem sqir_style_compareConst_candidate_flag_xor_sqir_layout
    (bits N x : Nat) (flag : Bool) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (update (cuccaro_input_F 2 false 0 x) 1 flag) 1
      = xor flag (decide (N ≤ x)) :=
  sqir_style_compareConst_candidate_flag_xor bits 2 N x 1 flag
    hN_pos hN hx (Or.inl (by omega))

/-! ## Tick 62 — Arithmetic identity for flag uncomputation. -/

/-- **HEADLINE — arithmetic identity for clean candidate.**  For
`0 < c`, `x < N`, `c < N`, the comparator's result on the reduced
target `(x+c) % N` is precisely the negation of the dirty flag. -/
theorem decide_c_le_xc_mod_N_eq_not_decide_N_le_xc
    (N x c : Nat) (hN_pos : 0 < N) (hc_pos : 0 < c)
    (hx : x < N) (hc : c < N) :
    decide (c ≤ (x + c) % N) = ! decide (N ≤ x + c) := by
  by_cases h : N ≤ x + c
  · -- Case x + c ≥ N: (x+c) % N = x + c - N, and x+c-N < c iff x < N (true).
    have h_lt : x + c < 2 * N := by omega
    have h_xc_lt_2N : x + c - N < N := by omega
    have h_mod : (x + c) % N = x + c - N := by
      rw [Nat.mod_eq_sub_mod h]
      exact Nat.mod_eq_of_lt h_xc_lt_2N
    rw [h_mod]
    -- c ≤ x+c-N iff N ≤ x.  But x < N, so c ≤ x+c-N is FALSE.
    have h_xc_sub_lt_c : x + c - N < c := by omega
    simp [h, Nat.not_le.mpr h_xc_sub_lt_c]
  · -- Case x + c < N: (x+c) % N = x + c, and c ≤ x+c is TRUE.
    push_neg at h
    have h_mod : (x + c) % N = x + c := Nat.mod_eq_of_lt h
    rw [h_mod]
    have h_c_le_xc : c ≤ x + c := by omega
    simp [Nat.not_le.mpr h, h_c_le_xc]

/-! ## Status note (Tick 62).

Landed (all kernel-clean):
- `sqir_style_compareConst_candidate_flag_xor` — comparator
  flag-XOR semantics for arbitrary initial flag.
- `sqir_style_compareConst_candidate_flag_xor_sqir_layout` —
  SQIR-layout corollary.
- `decide_c_le_xc_mod_N_eq_not_decide_N_le_xc` — the arithmetic
  identity making the cleanup XOR cancel.
- `sqir_style_modAddConst_clean_candidate` — clean-candidate
  definition for `0 < c < N`.

Empirical validation (Python, `scripts/check_sqir_modadder21_flag_uncompute.py`):
clean candidate passes target/read/carry/flag tests for all
`(bits, N, c, x)` with `bits ∈ {1..5}, 0 < N, 2N ≤ 2^bits, 0 < c < N,
x < N`.  Fails (as expected) for `c = 0` because
`compareConst(0)` is not implementable in the `bits` register.

**Not yet landed (deferred to Tick 63 — Phase 2 finalization):**
- `sqir_style_modAddConst_clean_candidate_flag_restored` (full flag
  restoration).  Blocker: composing the XOR semantics with the
  dirty-flag stage requires a function-level state equality
  `applyNat dirtyFlag (update cuccaro_input_F flagPos false)
  = update (cuccaro_input_F false 0 ((x+c)%N)) flagPos (decide(N ≤ x+c))`.
  The existing dirty-flag bundle exposes DECODED workspace properties
  only (cuccaro_read_val = 0, cuccaro_target_val = (x+c)%N), not
  per-position bit values.  Closing this requires bit-level workspace
  theorems for the dirty-flag candidate.

**SQIR `modadder21` faithfulness:** the Coq sequence uses
`bcx 1 ; swapper02 ; bcinv comparator01 ; swapper02` instead of our
`compareConst(c) ; X`.  Empirically the two cleanup mechanisms
agree for all tested cases (`0 < c < N`).  Full Coq-faithful port
including `swapper02` and `bcinv` is deferred unless it becomes
necessary for the next layer.

**Original SQIR placeholder axioms NOT YET CLOSED.**  This tick
makes incremental progress toward Phase 2 finalization.  The
clean-flag mod-N add is the immediate next milestone.

### Next tick should
1. **Bit-level workspace theorems for `sqir_style_modAddConst_dirtyFlag_candidate`** —
   per-position bit values at target/read/carry positions.
2. **Post-dirtyFlag state equality** — combine with bit-level
   workspace + frame_outside to get the full function-level state.
3. **Flag restoration for `sqir_style_modAddConst_clean_candidate`** —
   compose Task 1's XOR theorem with the state equality and the
   arithmetic identity.
4. **Workspace restoration for the clean candidate** — show
   compareConst's workspace-restored property holds after the
   composition, so target/read/carry stay at the dirty-flag values.
5. **Clean modular add bundle** — WellTyped + target = (x+c)%N
   + workspace restored + flag = false.
6. **Optional**: c = 0 wrapper. -/


end FormalRV.BQAlgo
