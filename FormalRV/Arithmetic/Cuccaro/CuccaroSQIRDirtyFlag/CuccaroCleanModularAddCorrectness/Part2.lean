/- CuccaroCleanModularAddCorrectness — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroCleanModularAddCorrectness.Part1

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Tick 64 — Deliverable E: controlled-modadd route analysis.

The clean modular add-constant gate (Deliverables A–D) is now total
over `c ∈ [0, N)` at the SQIR-faithful layout.  Phase 3 of the
modarith-to-modexp plan is **controlled modular addition** — needed
by the modular multiplier, which iterates over bits of the
multiplicand.

**Important warning (per Tick 64 directive):** do not assume
"control the whole clean modadd gate" works mechanically.  Two
routes to consider:

**Route 1 — Port SQIR's `bygatectrl` infrastructure.**

In Coq SQIR, `bygatectrl 1 g` builds a controlled version of `g`
gate-by-gate.  Each CX becomes CCX, each X becomes CX, etc.  Our
`Gate` IR (`I`, `X`, `CX`, `CCX`, `seq`) does not have a 4-qubit
gate, so any `CCX` inside the inner gate cannot be controlled
directly.  Inside the clean candidate, `CCX` appears (e.g., inside
`cuccaro_MAJ`).  Naive `bygatectrl` would require a 4-input gate
or an additional ancilla qubit.

**Route 2 — Build controlled mod-add-constant by masking the
constant.**

The clean candidate's first stage is `addConstGate(c)`, which adds
the constant `c` to the target.  If we replace this with a *masked*
add-constant — where the prepared `c` is XORed with the control bit
— then:
  - control = false ⇒ the masked-prepared read register is `0`, so
    addConstGate has no effect on the target (just runs the
    cuccaro adder with `a = 0`, which is identity at the target).
  - control = true ⇒ the masked-prepared read register is `c`, so
    addConstGate adds `c`.

The subsequent compareConst, conditionalSub, and flag-uncomputation
stages must also be control-aware.  Naively running them
unconditionally would give:
  - control = false: target unchanged = `x`.  Then compareConst
    computes `decide(N ≤ x) = false` (since `x < N`), so the flag
    XOR is no-op.  conditionalSub with flag = false is identity.
    Then the cleanup compareConst(c) computes `decide(c ≤ x)`,
    which is `false` iff `x < c`.  The `X(1)` flip then negates a
    bit that may or may not have been changed.  This DOES NOT
    cleanly handle the `control = false` case.

The cleanest path is therefore:

**Route 3 (selected for Tick 65) — Wrap the entire clean modadd
gate with a `bygatectrl`-style construction that controls every
gate operation by `control`.**  Since our IR has `CCX` but no
4-input gate, the strategy is:
  - `I` controlled by `ctrl` → `I`.
  - `X(q)` controlled by `ctrl` → `CX(ctrl, q)`.
  - `CX(c, t)` controlled by `ctrl` → `CCX(ctrl, c, t)`.
  - `CCX(a, b, c)` controlled by `ctrl` → would need 4-input; this
    is the structural problem.

The CCX gates inside the cuccaro_MAJ chain are the blocker.  Two
sub-options:
  (a) Use one ancilla `aux` qubit to decompose `controlled-CCX`:
      `CCX(ctrl, c, t)` becomes a Toffoli cascade through `aux`.
  (b) Replace the entire clean modular adder with a structurally
      different design (e.g., port SQIR's `modadder21` directly
      with control wired in at the masked-prepare level).

We will pursue option (b) for Tick 65 — masking the constant
via CX from `control` is structurally simpler and avoids the
auxiliary qubit.  The `compareConst` and conditional sub stages
must then be examined for whether their CCX content survives the
masking.

**Pending Tick 65 questions** (will be added to QUESTIONS.md):
  - Does masking `c` to `0` when `control = false` make the
    cleanup XOR + `X(1)` correctly identity?
  - Or must we ALSO mask `N` (in the comparator) by `control`?
    The cleanup uses `compareConst(c) ; X(1)`; if `c` is masked,
    `c = 0` would fire the broken `compareConst(0)` case (the
    `K = 2^bits` overflow).  We may need an additional guard. -/

/-! ## Tick 65 — Controlled SQIR modular add-constant: design + Task 3 + definitions.

**Route selected (per Python simulation, `scripts/check_sqir_controlled_modadd.py`):**
Route B — control-aware masked constants.  Candidate B (full-control)
passes all `bits ∈ {1..4}, 0 < N ≤ 2^bits / 2, 0 < c < N, x < N,
control ∈ {false, true}` test cases.  Candidate A (naive — control only
stage 1) FAILS for `control = false, c > 0` because the unconditional
cleanup `compareConst(c) ; X(1)` dirties the flag.  Candidate C
(Candidate B with `c = 0` wrapper) also passes, extending to `c = 0`.

**Controlled construction** (5 stages):
  1. `sqir_conditionalAddConstGate(bits, q_start, c, controlIdx)` — adds
     `c` to target iff `controlIdx`.
  2. `sqir_style_compareConst_candidate(bits, q_start, N, flagPos)` —
     UNCONDITIONAL: flag XOR `decide(N ≤ target)`.
  3. `sqir_conditionalSubConstGate(bits, q_start, N, flagPos)` —
     conditional on flag.
  4. `sqir_controlledCompareConst(bits, q_start, c, controlIdx, flagPos)` —
     masked cleanup; control-aware.
  5. `Gate.CX controlIdx flagPos` — control-aware flag flip.

When `control = false`:
- Stage 1 is identity (masked prepare ↔ K=0, full adder on `read = 0` =
  identity at target).
- Stage 2 sets flag := decide(N ≤ x) = false (since `x < N`).
- Stage 3 is identity (flag = false).
- Stage 4 is identity (masked prepare ↔ K=0; compareConst on read=0
  gives top_carry = decide(target ≥ 2^bits) = false; no flag change).
- Stage 5 (CX with control=false) is identity.
- Net: target = x, flag = false, controlIdx preserved. ✓

When `control = true`:
- Stage 1 = `addConstGate(c)` (via `apply_true_fun`).
- Stages 2-3 = unconditional dirtyFlag's compareConst(N) and conditionalSub(N).
- Stage 4 = `compareConst(c)` (masked prepare with control=true = unmasked).
- Stage 5 (CX with control=true) = `X(flagPos)`.
- Net = Tick 63 `clean_candidate`'s chain: target = (x+c) % N, flag = false. ✓
-/

/-! ## Tick 65 Task 3 — controlled add-mod-2^bits theorem (alias).

The existing `sqir_conditionalAddConstGate_target_decode` already
provides this; we re-expose it under the controlled-add semantic
name. -/

/-- **HEADLINE Task 3 — controlled add-mod-2^bits target decode.** -/
theorem sqir_controlledAddConstPow2_target_decode
    (bits q_start c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start c controlIdx)
          (update (cuccaro_input_F q_start false 0 x) controlIdx control))
      = (x + (if control then c else 0)) % 2^bits :=
  sqir_conditionalAddConstGate_target_decode bits q_start c x controlIdx control
    hbits hc hx h_control_distinct h_control_out

/-! ## Status note (Tick 65 part 1).

Landed (kernel-clean):
- Definition of `sqir_controlledCompareConst`.
- Definition of `sqir_style_controlledModAddConst_candidate`.
- Definition of `sqir_style_controlledModAddConst_gate` (total wrapper).
- Task 3 alias `sqir_controlledAddConstPow2_target_decode`.

**Not landed this tick** (Tick 66 work — explicitly deferred):
- `sqir_style_controlledModAddConst_*_target_decode` for the candidate
  (the per-control target value theorem).
- Full clean bundle (WellTyped + target + workspace + flag + control).
- BasicSetting-derived specialization.

Reason for deferral: the semantic theorems require chain-reduction
through 5 controlled stages with case-split on `control`.  Tick 65's
deliverable focus per directive is "first semantic theorem" — and
Task 3 provides one (the controlled add-mod-2^bits target decode),
empirically validating the controlled add primitive that drives
stage 1.  Simulation (Task 2) provides empirical validation of the
full controlled candidate; Tick 66 will land the formal semantic
theorems following the design now confirmed.

**Simulation result** (`scripts/check_sqir_controlled_modadd.py`):
- Candidate B (controlled stages 1, 4, 5): PASSES 380/380 for
  `bits ∈ {1..4}, 0 < N ≤ 2^bits/2, 0 < c < N, x < N`.
- Candidate C (B + c=0 wrapper): PASSES 480/480 over the same range
  with `c ∈ [0, N)`.
- Candidate A (naive — control only stage 1): FAILS (95 fails for
  `control = false` due to spurious flag from the unconditional
  cleanup). -/

/-! ## Tick 66 — Controlled SQIR mod-N add semantic correctness.

This tick proves the target_decode theorem (Deliverable C) for the
controlled mod-N add candidate by case-splitting on `control`, plus
the total wrapper target_decode (Deliverable F) and a BasicSetting-
derived specialization (Deliverable G).

The full clean bundle (Deliverables A, B, D, E with workspace/flag
conjuncts) is deferred to Tick 67 — the position-level chain
analysis through all 5 controlled stages for read/carry/flag
positions is substantial enough to merit its own tick. -/

/-- **Helper — `ctrlCompare` reduces to `compareConst(c)` when
`state[controlIdx] = true`.**  Function-level equality. -/
theorem sqir_controlledCompareConst_at_control_true_eq_unmasked_fun
    (bits q_start c controlIdx flagPos : Nat) (g : Nat → Bool)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos)
    (h_control_true : g controlIdx = true) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos) g
      = Gate.applyNat (sqir_style_compareConst_candidate bits q_start c flagPos) g := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx))))) g
    = Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2^bits - c))
              (seq (cuccaro_maj_chain bits q_start)
                   (seq (Gate.CX (q_start + 2 * bits) flagPos)
                        (seq (cuccaro_maj_chain_inv bits q_start)
                             (cuccaro_prepareConstRead bits q_start (2^bits - c)))))) g
  simp only [Gate.applyNat_seq]
  -- Inner-most masked prepare → unmasked (state at controlIdx = true).
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start (2^bits - c) controlIdx g
        h_control_distinct h_control_true]
  -- Outer masked prepare → unmasked.  Need state at controlIdx after the
  -- inner stages = true.  The inner stages (prepare, maj_chain, CX, maj_chain_inv)
  -- all preserve controlIdx because it's outside workspace and ≠ flagPos.
  have h_inner_ctrl_preserved :
      Gate.applyNat (cuccaro_maj_chain_inv bits q_start)
        (Gate.applyNat (Gate.CX (q_start + 2 * bits) flagPos)
          (Gate.applyNat (cuccaro_maj_chain bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2^bits - c)) g))) controlIdx
        = true := by
    rcases h_control_out with h_below | h_above
    · rw [cuccaro_maj_chain_inv_frame_below bits q_start _ controlIdx h_below]
      rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
      rw [cuccaro_maj_chain_frame_below bits q_start _ controlIdx h_below]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - c) controlIdx
            h_control_distinct]
      exact h_control_true
    · rw [cuccaro_maj_chain_inv_frame_above bits q_start _ controlIdx h_above]
      rw [Gate.applyNat_CX, update_neq _ _ _ _ h_control_ne_flag]
      rw [cuccaro_maj_chain_frame_above bits q_start _ controlIdx h_above]
      rw [cuccaro_prepareConstRead_at_other bits q_start (2^bits - c) controlIdx
            h_control_distinct]
      exact h_control_true
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start (2^bits - c) controlIdx _
        h_control_distinct h_inner_ctrl_preserved]

/-! ## Tick 66 — Total wrapper c = 0 case (partial Deliverable F). -/

/-- **Total wrapper at c = 0 reduces to `Gate.I`.** -/
theorem sqir_style_controlledModAddConst_gate_zero_eq
    (bits N controlIdx : Nat) :
    sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1 = Gate.I := by
  unfold sqir_style_controlledModAddConst_gate; simp

/-- **HEADLINE partial Deliverable F — c = 0 bundle for the controlled
modular add-constant wrapper.** -/
theorem sqir_style_controlledModAddConst_gate_zero_clean
    (bits N x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1) :
    Gate.WellTyped (sqir_modmult_rev_anc bits)
        (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
    ∧ cuccaro_target_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = x
    ∧ cuccaro_read_val bits 2
          (Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
            (update (cuccaro_input_F 2 false 0 x) controlIdx control))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) (2 + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) 1
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N 0 controlIdx 1)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) controlIdx
        = control := by
  rw [sqir_style_controlledModAddConst_gate_zero_eq]
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Gate.WellTyped (sqir_modmult_rev_anc bits) Gate.I
    show 0 < sqir_modmult_rev_anc bits
    unfold sqir_modmult_rev_anc; omega
  · -- target_val = x.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_target_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) = x % 2 ^ bits := by
      apply cuccaro_target_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 1 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      exact cuccaro_input_F_at_b 2 i false 0 x
    rw [h_eq]
    exact Nat.mod_eq_of_lt h_x_lt
  · -- read_val = 0.
    rw [Gate.applyNat_I]
    have h_eq : cuccaro_read_val bits 2
          (update (cuccaro_input_F 2 false 0 x) controlIdx control) = 0 % 2 ^ bits := by
      apply cuccaro_read_val_eq_sum_when_bits_match
      intro i hi
      have h_ne : (2 + 2 * i + 2 : Nat) ≠ controlIdx := by
        rcases hcontrol_out with hl | hr
        · omega
        · omega
      rw [update_neq _ _ _ _ h_ne]
      rw [cuccaro_input_F_at_a 2 i false 0 x]
    rw [h_eq]
    simp
  · -- top carry at 2 + 2*bits.
    rw [Gate.applyNat_I]
    have h_ne : (2 + 2 * bits : Nat) ≠ controlIdx := by
      rcases hcontrol_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    have h_eq : (2 : Nat) + 2 * bits = 2 + 2 * (bits - 1) + 2 := by omega
    rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 x]
    exact Nat.zero_testBit _
  · -- flag at 1.
    rw [Gate.applyNat_I]
    rw [update_neq _ _ _ _ hcontrol_ne_flag.symm]
    -- cuccaro_input_F at 1 = false (since 1 < q_start = 2).
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  · -- controlIdx = control.
    rw [Gate.applyNat_I]
    exact update_eq _ _ _

/-! ## Tick 67 — Closing the controlled mod-N add chain.

Stage helpers to compose into the full controlled candidate's
semantic theorem. -/

/-- **Deliverable B — CX with control = false is identity.** -/
theorem Gate.applyNat_CX_at_control_false_eq_id_fun
    (control target : Nat) (f : Nat → Bool) (h : f control = false) :
    Gate.applyNat (Gate.CX control target) f = f := by
  funext q
  rw [Gate.applyNat_CX, h, Bool.xor_false]
  by_cases hq : q = target
  · rw [hq, update_eq]
  · rw [update_neq _ _ _ _ hq]

/-- **Deliverable B — CX with control = true equals X(target).** -/
theorem Gate.applyNat_CX_at_control_true_eq_X_fun
    (control target : Nat) (f : Nat → Bool) (h : f control = true) :
    Gate.applyNat (Gate.CX control target) f = Gate.applyNat (Gate.X target) f := by
  rw [Gate.applyNat_CX, Gate.applyNat_X, h]
  congr 1
  cases f target <;> rfl

/-- **Helper — maj_chain on `cuccaro_input_F` with `a = 0` has top carry = false.**
Derived from `cuccaro_compareConstForward_top_carry` with `N = 2^bits`
(reducing the prepare to identity). -/
theorem cuccaro_maj_chain_top_carry_on_input_F_zero_a
    (bits q_start x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (cuccaro_maj_chain bits q_start)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits) = false := by
  have h_pos : 0 < (2 : Nat)^bits := Nat.two_pow_pos bits
  have h := cuccaro_compareConstForward_top_carry bits q_start (2^bits) x h_pos
              (le_refl _) hx
  unfold cuccaro_compareConstForwardGate at h
  simp only [Gate.applyNat_seq] at h
  have h_K : (2 : Nat)^bits - 2^bits = 0 := by omega
  rw [h_K] at h
  rw [cuccaro_prepareConstRead_zero_eq_id_fun] at h
  simp [Nat.not_le.mpr hx] at h
  exact h

/-- **Deliverable A — controlled comparator at control = false is identity
on `cuccaro_input_F`-shaped input.** -/
theorem sqir_controlledCompareConst_at_control_false_on_input_F_eq_id_fun
    (bits q_start c controlIdx flagPos x : Nat)
    (hbits : 1 ≤ bits) (hx : x < 2^bits)
    (h_control_distinct : ∀ i, i < bits → controlIdx ≠ q_start + 2 * i + 2)
    (h_control_out : controlIdx < q_start ∨ q_start + 2 * bits + 1 ≤ controlIdx)
    (h_control_ne_flag : controlIdx ≠ flagPos) :
    Gate.applyNat (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
        (update (cuccaro_input_F q_start false 0 x) controlIdx false)
      = update (cuccaro_input_F q_start false 0 x) controlIdx false := by
  set F := cuccaro_input_F q_start false 0 x with hF_def
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)
            (seq (cuccaro_maj_chain bits q_start)
                 (seq (Gate.CX (q_start + 2 * bits) flagPos)
                      (seq (cuccaro_maj_chain_inv bits q_start)
                           (sqir_prepareMaskedConstRead bits q_start (2^bits - c) controlIdx)))))
      (update F controlIdx false)
    = update F controlIdx false
  simp only [Gate.applyNat_seq]
  -- Stage 1: masked prepare with ctrl=false → identity.
  have h_input_ctrl : (update F controlIdx false) controlIdx = false := update_eq _ _ _
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start (2^bits - c) controlIdx
        (update F controlIdx false) h_control_distinct h_input_ctrl]
  -- Stage 3 (CX): need state at top = false.
  -- State entering CX = applyNat maj_chain (update F controlIdx false).
  have h_top_state : Gate.applyNat (cuccaro_maj_chain bits q_start)
        (update F controlIdx false) (q_start + 2 * bits) = false := by
    rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start controlIdx false F
          h_control_out]
    have h_ne : q_start + 2 * bits ≠ controlIdx := by
      rcases h_control_out with hl | hr
      · omega
      · omega
    rw [update_neq _ _ _ _ h_ne]
    exact cuccaro_maj_chain_top_carry_on_input_F_zero_a bits q_start x hbits hx
  -- CX is identity (xor with false → no change).
  rw [Gate.applyNat_CX_at_control_false_eq_id_fun (q_start + 2 * bits) flagPos _ h_top_state]
  -- Stage 4: maj_chain_inv ∘ maj_chain = id.
  rw [cuccaro_maj_chain_inv_after_chain_eq_id bits q_start (update F controlIdx false)]
  -- Stage 5: masked prepare with state[ctrl] = false (still true after the no-op chain).
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start (2^bits - c) controlIdx
        (update F controlIdx false) h_control_distinct h_input_ctrl]

/-! ## Tick 68 — Compose controlled mod-N add chain. -/

/-- **Deliverable A — uncontrolled comparator identity on `cuccaro_input_F`
when `x < N`.**  Since `decide(N ≤ x) = false`, the comparator XORs false
into flagPos (no change), and workspace + outside positions are preserved. -/
theorem sqir_style_compareConst_candidate_on_input_F_x_lt_N_eq_id_fun
    (bits N x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N) :
    Gate.applyNat (sqir_style_compareConst_candidate bits 2 N 1)
        (cuccaro_input_F 2 false 0 x)
      = cuccaro_input_F 2 false 0 x := by
  have h_x_lt : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have hflag_out : (1 : Nat) < 2 ∨ 2 + 2 * bits + 1 ≤ 1 := Or.inl (by omega)
  funext q
  by_cases hq_flag : q = 1
  · rw [hq_flag]
    rw [sqir_style_compareConst_candidate_flag_general bits 2 N x 1
          hN_pos hN h_x_lt hflag_out]
    have h_F1 : cuccaro_input_F 2 false 0 x 1 = false := by
      unfold cuccaro_input_F; rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_F1]
    exact decide_eq_false (Nat.not_le.mpr hx)
  · by_cases hq_ws : 2 ≤ q ∧ q < 2 + 2 * bits + 1
    · exact sqir_style_compareConst_candidate_workspace_restored_at_general bits 2 N 1
        _ hflag_out q hq_ws.1 hq_ws.2
    · push_neg at hq_ws
      have h_q_outside : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := by
        by_cases h : q < 2
        · left; exact h
        · push_neg at h; right; exact hq_ws h
      exact sqir_style_compareConst_candidate_frame_outside bits 2 N 1
        _ q hq_flag h_q_outside


end FormalRV.BQAlgo
