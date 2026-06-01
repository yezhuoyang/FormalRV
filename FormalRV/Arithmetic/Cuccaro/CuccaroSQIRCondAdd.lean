/-
  FormalRV.BQAlgo.CuccaroSQIRCondAdd — SQIR-style conditional
  add-constant / subtract-constant gates and dirty-flag modular adder.

  Tick 54: build the conditional add/sub primitives needed to turn the
  Tick 53 mod-2^bits skeleton into a true mod-N add-constant primitive.

  Route chosen: B (masked constant preparation). Our Gate IR has X,
  CX, CCX but no controlled-CCX. Following the existing Gidney-route
  `prepareMaskedConstRead`/`conditionalAddConstGate` pattern, we use
  CX(flagPos, read_pos_i) for each bit of the constant.

  This file lands:
  - `sqir_prepareMaskedConstRead`: definition.
  - per-position semantics (at_read, at_other) for masked prepare.
  - `sqir_prepareMaskedConstRead_wellTyped`.
  - `sqir_conditionalAddConstGate`: prepare(masked) ; full_adder ; prepare(masked).
  - WellTyped for the conditional add.
  - `sqir_conditionalSubConstGate`: alias for add by 2^bits - N.

  Semantic correctness (target decode) for conditional add/sub and
  the dirty-flag modular adder is left for a follow-up tick due to
  the depth of the input-state equivalence argument needed.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRModAdd

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Masked constant preparation. -/

/-- **Masked constant preparation**: for each `i < bits`, conditionally
applies `CX flagPos (q_start + 2*i + 2)` iff `N.testBit i`. -/
def sqir_prepareMaskedConstRead : Nat → Nat → Nat → Nat → Gate
  | 0,     _,       _, _       => Gate.I
  | n + 1, q_start, N, flagPos =>
      seq (sqir_prepareMaskedConstRead n q_start N flagPos)
          (cond (N.testBit n) (Gate.CX flagPos (q_start + 2 * n + 2)) Gate.I)

/-! ## Per-position semantics. -/

/-- **Frame**: the masked prepare gate doesn't touch positions outside
the read range. -/
theorem sqir_prepareMaskedConstRead_at_other
    (bits q_start N flagPos q : Nat)
    (hq : ∀ i, i < bits → q ≠ q_start + 2 * i + 2)
    (f : Nat → Bool) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f q = f q := by
  induction bits generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I)) f q = _
    simp only [Gate.applyNat_seq]
    have h_outer : ∀ g : Nat → Bool,
        Gate.applyNat (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I)
            g q = g q := by
      intro g
      cases h_n : N.testBit k with
      | false => simp [h_n]
      | true =>
          simp only [h_n, cond_true]
          show update g (q_start + 2 * k + 2) _ q = _
          rw [update_neq _ _ _ _ (hq k (by omega))]
    rw [h_outer]
    apply ih
    intros i hi
    exact hq i (by omega)

/-- **Frame for flagPos**: as long as flagPos isn't a read position,
the masked prepare gate doesn't touch flagPos (CX's control is read,
not written). -/
theorem sqir_prepareMaskedConstRead_at_flagPos
    (bits q_start N flagPos : Nat)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (f : Nat → Bool) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f flagPos = f flagPos :=
  sqir_prepareMaskedConstRead_at_other bits q_start N flagPos flagPos h_flag_distinct f

/-- **Action at read positions**: at `q_start + 2*j + 2` for `j < bits`,
the value is XORed with `(f flagPos && N.testBit j)`. -/
theorem sqir_prepareMaskedConstRead_at_read
    (bits q_start N flagPos j : Nat) (hj : j < bits) (f : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f
        (q_start + 2 * j + 2)
      = xor (f (q_start + 2 * j + 2)) (f flagPos && N.testBit j) := by
  induction bits generalizing f with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I)) f
        (q_start + 2 * j + 2) = _
    simp only [Gate.applyNat_seq]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · -- j < k. Outer's target q_start + 2*k + 2 ≠ q_start + 2*j + 2 (since k ≠ j).
      -- Outer leaves q_start + 2*j + 2 untouched.
      have h_outer : ∀ g : Nat → Bool,
          Gate.applyNat (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I)
              g (q_start + 2 * j + 2) = g (q_start + 2 * j + 2) := by
        intro g
        cases h_n : N.testBit k with
        | false => simp [h_n]
        | true =>
            simp only [h_n, cond_true]
            show update g (q_start + 2 * k + 2) _ (q_start + 2 * j + 2) = _
            rw [update_neq _ _ _ _ (by omega)]
      rw [h_outer]
      -- Inner at q_start + 2*j + 2 = ih applied at j < k.
      -- But we also need inner at flagPos to equal f flagPos (inner frame).
      have h_inner_flag : Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f flagPos
                         = f flagPos := by
        apply sqir_prepareMaskedConstRead_at_other
        intros i hi
        exact h_flag_distinct i (by omega)
      rw [ih hjk f (fun i hi => h_flag_distinct i (by omega))]
    · -- j ≥ k, and j < k+1 so j = k.
      have hjk_eq : j = k := by omega
      rw [show j = k from hjk_eq]
      -- Inner doesn't touch q_start + 2*k + 2 (since inner range is j < k, not k).
      have h_inner_eq : Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f
                          (q_start + 2 * k + 2) = f (q_start + 2 * k + 2) := by
        apply sqir_prepareMaskedConstRead_at_other
        intros i hi h_eq
        omega
      have h_inner_flag : Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f flagPos
                         = f flagPos := by
        apply sqir_prepareMaskedConstRead_at_other
        intros i hi
        exact h_flag_distinct i (by omega)
      cases h_n : N.testBit k with
      | false =>
          simp only [h_n, cond_false]
          show Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f
                (q_start + 2 * k + 2) = _
          rw [h_inner_eq]
          simp
      | true =>
          simp only [h_n, cond_true]
          show update (Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f)
                (q_start + 2 * k + 2)
                (xor ((Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f)
                       (q_start + 2 * k + 2))
                     ((Gate.applyNat (sqir_prepareMaskedConstRead k q_start N flagPos) f)
                       flagPos))
                (q_start + 2 * k + 2) = _
          rw [update_eq, h_inner_eq, h_inner_flag]
          simp

/-! ## WellTyped for masked prepare. -/

theorem sqir_prepareMaskedConstRead_wellTyped
    (bits q_start N flagPos dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    Gate.WellTyped dim (sqir_prepareMaskedConstRead bits q_start N flagPos) := by
  induction bits with
  | zero =>
    show Gate.WellTyped dim Gate.I
    show 0 < dim
    omega
  | succ k ih =>
    show Gate.WellTyped dim
        (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I))
    refine ⟨?_, ?_⟩
    · apply ih
      · omega
      · intros i hi
        exact h_flag_distinct i (by omega)
    · cases h_n : N.testBit k with
      | false =>
          simp only [h_n, cond_false]
          show 0 < dim
          omega
      | true =>
          simp only [h_n, cond_true]
          refine ⟨h_flag, ?_, ?_⟩
          · omega
          · exact h_flag_distinct k (by omega)

/-! ## Conditional add/sub gates. -/

/-- **Conditional add-constant gate**: adds `N` to the target register
iff the flag is true.  Uses masked prepare to encode the constant `N`
into the read register conditionally on the flag value. -/
def sqir_conditionalAddConstGate (bits q_start N flagPos : Nat) : Gate :=
  seq (sqir_prepareMaskedConstRead bits q_start N flagPos)
      (seq (cuccaro_n_bit_adder_full bits q_start)
           (sqir_prepareMaskedConstRead bits q_start N flagPos))

/-- **Conditional sub-constant gate**: subtracts `N` from the target
iff the flag is true.  Implemented as conditional-add of `2^bits - N`
(two's complement). -/
def sqir_conditionalSubConstGate (bits q_start N flagPos : Nat) : Gate :=
  sqir_conditionalAddConstGate bits q_start (2^bits - N) flagPos

/-! ## WellTyped for conditional add/sub. -/

theorem sqir_conditionalAddConstGate_wellTyped
    (bits q_start N flagPos dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    Gate.WellTyped dim (sqir_conditionalAddConstGate bits q_start N flagPos) := by
  refine ⟨?_, ?_, ?_⟩
  · exact sqir_prepareMaskedConstRead_wellTyped bits q_start N flagPos dim
      h_workspace h_flag h_flag_distinct
  · exact cuccaro_n_bit_adder_full_wellTyped bits q_start dim h_workspace
  · exact sqir_prepareMaskedConstRead_wellTyped bits q_start N flagPos dim
      h_workspace h_flag h_flag_distinct

theorem sqir_conditionalSubConstGate_wellTyped
    (bits q_start N flagPos dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    Gate.WellTyped dim (sqir_conditionalSubConstGate bits q_start N flagPos) := by
  unfold sqir_conditionalSubConstGate
  exact sqir_conditionalAddConstGate_wellTyped bits q_start (2^bits - N) flagPos dim
    h_workspace h_flag h_flag_distinct

/-! ## Dirty-flag modular adder candidate. -/

/-- **Dirty-flag modular add-constant candidate**:
addConst(c) ; compareConst(N) ; conditionalSubConst(N).

After this gate:
- target = `(x + c) % N` (when `x, c < N`).
- read register restored to 0.
- carry-in restored to false.
- flag (at flagPos) holds `decide(N ≤ (x+c) % 2^bits)` — DIRTY.

The flag is dirty because we don't uncompute the comparator.  A clean
modular add-constant requires either:
- a flag-uncompute step (e.g., another comparator with the right
  polarity), or
- accepting the dirty flag at the modAdd level and tracking it in
  the calling context.

For Shor's modular multiplier, the inner loops typically need a
clean flag — so the next milestone is to uncompute the flag. -/
def sqir_style_modAddConst_dirtyFlag_candidate
    (bits q_start N c flagPos : Nat) : Gate :=
  seq (cuccaro_addConstGate bits q_start c)
      (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
           (sqir_conditionalSubConstGate bits q_start N flagPos))

/-! ## WellTyped for the dirty-flag candidate. -/

theorem sqir_style_modAddConst_dirtyFlag_candidate_wellTyped
    (bits q_start N c flagPos dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_distinct_top : flagPos ≠ q_start + 2 * bits) :
    Gate.WellTyped dim
        (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos) := by
  refine ⟨?_, ?_, ?_⟩
  · exact cuccaro_addConstGate_wellTyped bits q_start c dim h_workspace
  · exact sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag h_flag_distinct_top
  · exact sqir_conditionalSubConstGate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag h_flag_distinct

/-! ## Tick 55 — Helper lemmas for masked prepare with explicit flag value. -/

/-- **Masked prepare with flag = false is identity** (per position). -/
theorem sqir_prepareMaskedConstRead_eq_id_at_flag_false
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_false : f flagPos = false) (q : Nat) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f q
      = f q := by
  by_cases hq : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · obtain ⟨i, hi, hq_eq⟩ := hq
    rw [hq_eq]
    rw [sqir_prepareMaskedConstRead_at_read bits q_start N flagPos i hi f h_flag_distinct]
    rw [h_flag_false]
    simp
  · push_neg at hq
    apply sqir_prepareMaskedConstRead_at_other
    intros i hi h_eq
    exact hq i hi h_eq

/-- **Masked prepare with flag = true equals `cuccaro_prepareConstRead N`**
(per position). -/
theorem sqir_prepareMaskedConstRead_eq_unmasked_at_flag_true
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_true : f flagPos = true) (q : Nat) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f q
      = Gate.applyNat (cuccaro_prepareConstRead bits q_start N) f q := by
  by_cases hq : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
  · obtain ⟨i, hi, hq_eq⟩ := hq
    rw [hq_eq]
    rw [sqir_prepareMaskedConstRead_at_read bits q_start N flagPos i hi f h_flag_distinct]
    rw [cuccaro_prepareConstRead_at_read bits q_start N i hi]
    rw [h_flag_true]
    simp
  · push_neg at hq
    have h_neq : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
      intros i hi h_eq
      exact hq i hi h_eq
    rw [sqir_prepareMaskedConstRead_at_other bits q_start N flagPos q h_neq]
    rw [cuccaro_prepareConstRead_at_other bits q_start N q h_neq]

/-! ## Tick 56 — Function-level reductions for conditional add.

We prove that `applyNat sqir_conditionalAddConstGate` reduces to
`applyNat cuccaro_n_bit_adder_full` (flag = false) or
`applyNat cuccaro_addConstGate N` (flag = true) at the function level. -/

/-- **Function-level: masked prepare = id when flag = false.** -/
theorem sqir_prepareMaskedConstRead_eq_id_fun
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_false : f flagPos = false) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f = f := by
  funext q
  exact sqir_prepareMaskedConstRead_eq_id_at_flag_false bits q_start N flagPos f
    h_flag_distinct h_flag_false q

/-- **Function-level: masked prepare = cuccaro_prepareConstRead N when flag = true.** -/
theorem sqir_prepareMaskedConstRead_eq_unmasked_fun
    (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_true : f flagPos = true) :
    Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f
      = Gate.applyNat (cuccaro_prepareConstRead bits q_start N) f := by
  funext q
  exact sqir_prepareMaskedConstRead_eq_unmasked_at_flag_true bits q_start N flagPos f
    h_flag_distinct h_flag_true q

/-! ## Deliverable A — False-flag reduction. -/

/-- **HEADLINE — false-flag reduction**: when the flag value in the input
state is `false`, the conditional add gate behaves like the bare full
Cuccaro adder. -/
theorem sqir_conditionalAddConstGate_apply_false_fun
    (bits q_start N flagPos : Nat) (g : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_false : g flagPos = false)
    (h_flag_disjoint : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) g
      = Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start N flagPos)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (sqir_prepareMaskedConstRead bits q_start N flagPos))) g = _
  -- Function-level via Gate.applyNat_seq.
  show Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos)
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) g)) = _
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start N flagPos g
        h_flag_distinct h_flag_false]
  -- Now: applyNat prepare_masked (applyNat adder g) = applyNat adder g.
  -- Need (applyNat adder g) flagPos = false.
  have h_adder_flag_false :
      Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g flagPos = false := by
    rcases h_flag_disjoint with h | h
    · rw [cuccaro_n_bit_adder_full_frame_below bits q_start g flagPos h]
      exact h_flag_false
    · rw [cuccaro_n_bit_adder_full_frame_above bits q_start g flagPos h]
      exact h_flag_false
  rw [sqir_prepareMaskedConstRead_eq_id_fun bits q_start N flagPos _
        h_flag_distinct h_adder_flag_false]

/-! ## Deliverable B — True-flag reduction. -/

/-- **HEADLINE — true-flag reduction**: when the flag value in the input
state is `true`, the conditional add gate behaves like
`cuccaro_addConstGate N`. -/
theorem sqir_conditionalAddConstGate_apply_true_fun
    (bits q_start N flagPos : Nat) (g : Nat → Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_true : g flagPos = true)
    (h_flag_disjoint : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) g
      = Gate.applyNat (cuccaro_addConstGate bits q_start N) g := by
  show Gate.applyNat
      (seq (sqir_prepareMaskedConstRead bits q_start N flagPos)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (sqir_prepareMaskedConstRead bits q_start N flagPos))) g
    = Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start N)
              (seq (cuccaro_n_bit_adder_full bits q_start)
                   (cuccaro_prepareConstRead bits q_start N))) g
  show Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos)
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) g))
    = Gate.applyNat (cuccaro_prepareConstRead bits q_start N)
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start N) g))
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start N flagPos g
        h_flag_distinct h_flag_true]
  -- After first prepare: state = applyNat cuccaro_prepareConstRead N g.
  -- Need this state's flagPos value to also be true to apply the helper to outer prepare.
  -- cuccaro_prepareConstRead doesn't touch flagPos (since flagPos is not a read position):
  have h_inner1_flag_true :
      Gate.applyNat (cuccaro_prepareConstRead bits q_start N) g flagPos = true := by
    rw [cuccaro_prepareConstRead_at_other bits q_start N flagPos
        (fun i hi h => h_flag_distinct i hi h)]
    exact h_flag_true
  -- And adder doesn't touch flagPos either:
  have h_inner2_flag_true :
      Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start N) g) flagPos = true := by
    rcases h_flag_disjoint with h | h
    · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ flagPos h]
      exact h_inner1_flag_true
    · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ flagPos h]
      exact h_inner1_flag_true
  rw [sqir_prepareMaskedConstRead_eq_unmasked_fun bits q_start N flagPos _
        h_flag_distinct h_inner2_flag_true]

/-! ## Deliverable C — target theorem.

We derive the target_decode from the function-level reductions plus
the existing cuccaro_addConstGate_target_decode (via locality at
workspace, which we establish separately for the simpler case). -/

/-- **Locality**: `cuccaro_carry` doesn't depend on input at positions
outside its computation support. -/
theorem cuccaro_carry_update_outside_locality
    (f : Nat → Bool) (q_start k p : Nat) (v : Bool)
    (h_p_outside : p < q_start ∨ q_start + 2 * k + 1 ≤ p) :
    cuccaro_carry (update f p v) q_start k = cuccaro_carry f q_start k := by
  induction k with
  | zero =>
    show (update f p v) q_start = f q_start
    apply update_neq
    intro h
    rcases h_p_outside with hl | hr
    · omega
    · omega
  | succ j ih =>
    unfold cuccaro_carry
    have hp_sub : p < q_start ∨ q_start + 2 * j + 1 ≤ p := by
      rcases h_p_outside with hl | hr
      · left; exact hl
      · right; omega
    rw [ih hp_sub]
    rw [update_neq _ _ _ _ (by
        intro h
        rcases h_p_outside with hl | hr
        · omega
        · omega)]
    rw [update_neq _ _ _ _ (by
        intro h
        rcases h_p_outside with hl | hr
        · omega
        · omega)]

/-! ## Tick 57 — Function-level commutativity with update outside workspace.

Strategy: prove that each gate commutes with `update f flagPos v` when
`flagPos` is outside the gate's wires/workspace. Then for the full
adder and `cuccaro_addConstGate`, derive the workspace-locality (output
at workspace = output on unupdated input). -/

/-- **`cuccaro_MAJ` commutes with `update` outside its wires.** -/
theorem cuccaro_MAJ_commute_update
    (a b c flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c)
    (h_neq_a : flagPos ≠ a) (h_neq_b : flagPos ≠ b) (h_neq_c : flagPos ≠ c) :
    Gate.applyNat (cuccaro_MAJ a b c) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_MAJ a b c) f) flagPos v := by
  funext q
  by_cases hq_flag : q = flagPos
  · rw [show q = flagPos from hq_flag]
    rw [cuccaro_MAJ_at_other a b c flagPos h_neq_a h_neq_b h_neq_c]
    rw [update_eq, update_eq]
  · rw [update_neq _ _ _ _ hq_flag]
    by_cases hqa : q = a
    · rw [show q = a from hqa]
      rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc]
      rw [update_neq _ _ _ _ (fun h => h_neq_a h.symm)]
      rw [update_neq _ _ _ _ (fun h => h_neq_c h.symm)]
      rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc]
    · by_cases hqb : q = b
      · rw [show q = b from hqb]
        rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc]
        rw [update_neq _ _ _ _ (fun h => h_neq_b h.symm)]
        rw [update_neq _ _ _ _ (fun h => h_neq_c h.symm)]
        rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc]
      · by_cases hqc : q = c
        · rw [show q = c from hqc]
          rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc]
          rw [update_neq _ _ _ _ (fun h => h_neq_a h.symm)]
          rw [update_neq _ _ _ _ (fun h => h_neq_b h.symm)]
          rw [update_neq _ _ _ _ (fun h => h_neq_c h.symm)]
          rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc]
        · rw [cuccaro_MAJ_at_other a b c q hqa hqb hqc]
          rw [cuccaro_MAJ_at_other a b c q hqa hqb hqc]
          exact update_neq _ _ _ _ hq_flag

/-- **`cuccaro_UMA` commutes with `update` outside its wires.** -/
theorem cuccaro_UMA_commute_update
    (a b c flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c)
    (h_neq_a : flagPos ≠ a) (h_neq_b : flagPos ≠ b) (h_neq_c : flagPos ≠ c) :
    Gate.applyNat (cuccaro_UMA a b c) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_UMA a b c) f) flagPos v := by
  funext q
  by_cases hq_flag : q = flagPos
  · rw [show q = flagPos from hq_flag]
    rw [cuccaro_UMA_at_other a b c flagPos h_neq_a h_neq_b h_neq_c]
    rw [update_eq, update_eq]
  · rw [update_neq _ _ _ _ hq_flag]
    by_cases hqa : q = a
    · rw [show q = a from hqa]
      rw [cuccaro_UMA_at_a a b c h_ab h_ac h_bc]
      rw [update_neq _ _ _ _ (fun h => h_neq_a h.symm)]
      rw [update_neq _ _ _ _ (fun h => h_neq_b h.symm)]
      rw [update_neq _ _ _ _ (fun h => h_neq_c h.symm)]
      rw [cuccaro_UMA_at_a a b c h_ab h_ac h_bc]
    · by_cases hqb : q = b
      · rw [show q = b from hqb]
        rw [cuccaro_UMA_at_b a b c h_ab h_ac h_bc]
        rw [update_neq _ _ _ _ (fun h => h_neq_a h.symm)]
        rw [update_neq _ _ _ _ (fun h => h_neq_b h.symm)]
        rw [update_neq _ _ _ _ (fun h => h_neq_c h.symm)]
        rw [cuccaro_UMA_at_b a b c h_ab h_ac h_bc]
      · by_cases hqc : q = c
        · rw [show q = c from hqc]
          rw [cuccaro_UMA_at_c a b c h_ab h_ac h_bc]
          rw [update_neq _ _ _ _ (fun h => h_neq_a h.symm)]
          rw [update_neq _ _ _ _ (fun h => h_neq_b h.symm)]
          rw [update_neq _ _ _ _ (fun h => h_neq_c h.symm)]
          rw [cuccaro_UMA_at_c a b c h_ab h_ac h_bc]
        · rw [cuccaro_UMA_at_other a b c q hqa hqb hqc]
          rw [cuccaro_UMA_at_other a b c q hqa hqb hqc]
          exact update_neq _ _ _ _ hq_flag

/-- **`cuccaro_maj_chain` commutes with `update` outside its workspace.** -/
theorem cuccaro_maj_chain_commute_update_outside_workspace
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_maj_chain bits q_start) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_maj_chain bits q_start) f) flagPos v := by
  induction bits generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                              (cuccaro_maj_chain k (q_start + 2)))
        (update f flagPos v)
      = update (Gate.applyNat (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                              (cuccaro_maj_chain k (q_start + 2))) f) flagPos v
    show Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
        (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) (update f flagPos v))
      = update (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
          (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)) flagPos v
    rw [cuccaro_MAJ_commute_update q_start (q_start + 1) (q_start + 2) flagPos v f
        (by omega) (by omega) (by omega)
        (by rcases hflag_out with h | h; omega; omega)
        (by rcases hflag_out with h | h; omega; omega)
        (by rcases hflag_out with h | h; omega; omega)]
    apply ih (q_start + 2) (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
    rcases hflag_out with h | h
    · left; omega
    · right; omega

/-- **`cuccaro_uma_chain_reverse` commutes with `update` outside its workspace.** -/
theorem cuccaro_uma_chain_reverse_commute_update_outside_workspace
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_uma_chain_reverse bits q_start) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_uma_chain_reverse bits q_start) f) flagPos v := by
  induction bits generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat (seq (cuccaro_uma_chain_reverse k (q_start + 2))
                              (cuccaro_UMA q_start (q_start + 1) (q_start + 2)))
        (update f flagPos v)
      = update (Gate.applyNat (seq (cuccaro_uma_chain_reverse k (q_start + 2))
                              (cuccaro_UMA q_start (q_start + 1) (q_start + 2))) f) flagPos v
    show Gate.applyNat (cuccaro_UMA q_start (q_start + 1) (q_start + 2))
        (Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2)) (update f flagPos v))
      = update (Gate.applyNat (cuccaro_UMA q_start (q_start + 1) (q_start + 2))
          (Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2)) f)) flagPos v
    have h_sub : flagPos < q_start + 2 ∨ q_start + 2 + 2 * k + 1 ≤ flagPos := by
      rcases hflag_out with h | h
      · left; omega
      · right; omega
    rw [ih (q_start + 2) f h_sub]
    have h_neq_a : flagPos ≠ q_start := by
      rcases hflag_out with h | h
      · omega
      · omega
    have h_neq_b : flagPos ≠ q_start + 1 := by
      rcases hflag_out with h | h
      · omega
      · omega
    have h_neq_c : flagPos ≠ q_start + 2 := by
      rcases hflag_out with h | h
      · omega
      · omega
    rw [cuccaro_UMA_commute_update q_start (q_start + 1) (q_start + 2) flagPos v _
        (by omega) (by omega) (by omega) h_neq_a h_neq_b h_neq_c]

/-- **`cuccaro_n_bit_adder_full` commutes with `update` outside its workspace.** -/
theorem cuccaro_n_bit_adder_full_commute_update_outside_workspace
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) f) flagPos v := by
  show Gate.applyNat (seq (cuccaro_maj_chain bits q_start)
                            (cuccaro_uma_chain_reverse bits q_start))
      (update f flagPos v)
    = update (Gate.applyNat (seq (cuccaro_maj_chain bits q_start)
                                  (cuccaro_uma_chain_reverse bits q_start)) f) flagPos v
  show Gate.applyNat (cuccaro_uma_chain_reverse bits q_start)
      (Gate.applyNat (cuccaro_maj_chain bits q_start) (update f flagPos v))
    = update (Gate.applyNat (cuccaro_uma_chain_reverse bits q_start)
        (Gate.applyNat (cuccaro_maj_chain bits q_start) f)) flagPos v
  rw [cuccaro_maj_chain_commute_update_outside_workspace bits q_start flagPos v f hflag_out]
  rw [cuccaro_uma_chain_reverse_commute_update_outside_workspace bits q_start flagPos v _ hflag_out]

/-! ## HEADLINE Deliverable A — full-adder locality and flag preservation. -/

/-- **HEADLINE — full-adder locality at workspace under outside update.** -/
theorem cuccaro_n_bit_adder_full_update_outside_workspace_at
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool) (p : Nat)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hp_in : q_start ≤ p ∧ p < q_start + 2 * bits + 1) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) (update f flagPos v) p
      = Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) f p := by
  rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start flagPos v f hflag_out]
  apply update_neq
  intro h
  rcases hflag_out with hl | hr
  · omega
  · omega

/-- **HEADLINE — full-adder preserves flagPos value.** -/
theorem cuccaro_n_bit_adder_full_preserves_outside_workspace
    (bits q_start flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (update f flagPos v) flagPos = v := by
  rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start flagPos v f hflag_out]
  exact update_eq _ _ _

/-! ## Deliverable B — addConstGate locality. -/

/-- **`cuccaro_prepareConstRead` commutes with `update` outside its workspace.** -/
theorem cuccaro_prepareConstRead_commute_update_outside_workspace
    (bits q_start c flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_prepareConstRead bits q_start c) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f) flagPos v := by
  funext q
  have h_flag_not_read : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intros i hi h
    rcases hflag_out with hl | hr
    · omega
    · omega
  by_cases hq_flag : q = flagPos
  · rw [show q = flagPos from hq_flag]
    rw [cuccaro_prepareConstRead_at_other bits q_start c flagPos h_flag_not_read]
    rw [update_eq, update_eq]
  · rw [update_neq _ _ _ _ hq_flag]
    by_cases hq_read : ∃ i, i < bits ∧ q = q_start + 2 * i + 2
    · obtain ⟨i, hi, hq_eq⟩ := hq_read
      rw [hq_eq]
      rw [cuccaro_prepareConstRead_at_read bits q_start c i hi]
      rw [cuccaro_prepareConstRead_at_read bits q_start c i hi]
      have h_neq : flagPos ≠ q_start + 2 * i + 2 := h_flag_not_read i hi
      rw [update_neq _ _ _ _ (fun h => h_neq h.symm)]
    · push_neg at hq_read
      have h_neq : ∀ i, i < bits → q ≠ q_start + 2 * i + 2 := by
        intros i hi h_eq
        exact hq_read i hi h_eq
      rw [cuccaro_prepareConstRead_at_other bits q_start c q h_neq]
      rw [cuccaro_prepareConstRead_at_other bits q_start c q h_neq]
      exact update_neq _ _ _ _ hq_flag

/-- **`cuccaro_addConstGate` commutes with `update` outside its workspace.** -/
theorem cuccaro_addConstGate_commute_update_outside_workspace
    (bits q_start c flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c) (update f flagPos v)
      = update (Gate.applyNat (cuccaro_addConstGate bits q_start c) f) flagPos v := by
  show Gate.applyNat (seq (cuccaro_prepareConstRead bits q_start c)
                            (seq (cuccaro_n_bit_adder_full bits q_start)
                                 (cuccaro_prepareConstRead bits q_start c)))
      (update f flagPos v)
    = update (Gate.applyNat (seq (cuccaro_prepareConstRead bits q_start c)
                                  (seq (cuccaro_n_bit_adder_full bits q_start)
                                       (cuccaro_prepareConstRead bits q_start c))) f) flagPos v
  show Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
      (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) (update f flagPos v)))
    = update (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f))) flagPos v
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start c flagPos v f hflag_out]
  rw [cuccaro_n_bit_adder_full_commute_update_outside_workspace bits q_start flagPos v _ hflag_out]
  rw [cuccaro_prepareConstRead_commute_update_outside_workspace bits q_start c flagPos v _ hflag_out]

/-- **HEADLINE — addConstGate locality at workspace under outside update.** -/
theorem cuccaro_addConstGate_update_outside_workspace_at
    (bits q_start c flagPos : Nat) (v : Bool) (f : Nat → Bool) (p : Nat)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hp_in : q_start ≤ p ∧ p < q_start + 2 * bits + 1) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c) (update f flagPos v) p
      = Gate.applyNat (cuccaro_addConstGate bits q_start c) f p := by
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start c flagPos v f hflag_out]
  apply update_neq
  intro h
  rcases hflag_out with hl | hr
  · omega
  · omega

/-- **HEADLINE — addConstGate preserves flagPos value.** -/
theorem cuccaro_addConstGate_preserves_outside_workspace
    (bits q_start c flagPos : Nat) (v : Bool) (f : Nat → Bool)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c)
        (update f flagPos v) flagPos = v := by
  rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start c flagPos v f hflag_out]
  exact update_eq _ _ _

/-! ## Deliverable C — Conditional add target theorem.

Combine the function-level reductions (A and B) with the locality
theorems to derive the target_decode. -/

/-- **HEADLINE Deliverable C — conditional add target decode.** -/
theorem sqir_conditionalAddConstGate_target_decode
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos flag))
      = (x + (if flag then N else 0)) % 2^bits := by
  -- The cuccaro_input_F at flagPos = false (above support when flag_out is above).
  -- For flag_out above, the input flagPos value is already false.
  cases flag with
  | false =>
    -- Use Deliverable A: gate reduces to bare adder.
    have h_flag_false : (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
                       = false := update_eq _ _ _
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start N flagPos
          _ h_flag_distinct h_flag_false hflag_out]
    -- target_val applied to bare adder on the updated input.
    -- Use addConst with c = 0: addConst 0 = prepare(0) ; adder ; prepare(0).
    -- For c = 0, prepare(0) is identity (since 0.testBit i = false for all i).
    -- So addConst 0 = adder.
    -- Then target_decode = (x + 0) % 2^bits = x.
    -- Use the locality theorem to transfer between the update and unupdated input.
    apply cuccaro_target_val_eq_sum_when_bits_match bits q_start (x + 0) _
    intro i hi
    -- show bit i of target after adder = (x+0).testBit i.
    -- Use the full-adder locality: at workspace target_i, output depends only on workspace input.
    -- The update at flagPos doesn't affect target_i (flagPos outside workspace).
    rw [cuccaro_n_bit_adder_full_update_outside_workspace_at bits q_start flagPos false
          _ (q_start + 2 * i + 1) hflag_out (by omega)]
    -- Now: applyNat adder (cuccaro_input_F q_start false 0 x) at target_i.
    -- Use sum_bit theorem.
    rw [cuccaro_n_bit_adder_full_sum_bit bits q_start
        (cuccaro_input_F q_start false 0 x) i hi]
    rw [cuccaro_input_F_at_b q_start i false 0 x]
    rw [cuccaro_input_F_at_a q_start i false 0 x]
    simp only [Nat.zero_testBit]
    rw [cuccaro_carry_eq_Adder_carry]
    rw [cuccaro_input_F_at_c_in q_start false 0 x]
    -- bit stream
    have h_b_stream : (fun k => (cuccaro_input_F q_start false 0 x) (q_start + 2 * k + 1))
                      = (fun k => x.testBit k) := by
      funext k
      exact cuccaro_input_F_at_b q_start k false 0 x
    have h_a_stream : (fun k => (cuccaro_input_F q_start false 0 x) (q_start + 2 * k + 2))
                      = (fun k => (0 : Nat).testBit k) := by
      funext k
      rw [cuccaro_input_F_at_a q_start k false 0 x]
    rw [h_b_stream, h_a_stream]
    have h_sumfb := Adder.sumfb_eq_testBit_add_gen false x 0 i
    unfold Adder.sumfb at h_sumfb
    simpa [Bool.toNat] using h_sumfb
  | true =>
    have h_flag_true : (update (cuccaro_input_F q_start false 0 x) flagPos true) flagPos
                      = true := update_eq _ _ _
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start N flagPos
          _ h_flag_distinct h_flag_true hflag_out]
    -- target_val applied to cuccaro_addConstGate N on the updated input.
    -- Use addConstGate's existing target_decode + locality.
    apply cuccaro_target_val_eq_sum_when_bits_match bits q_start (x + N) _
    intro i hi
    rw [cuccaro_addConstGate_update_outside_workspace_at bits q_start N flagPos true
          _ (q_start + 2 * i + 1) hflag_out (by omega)]
    exact cuccaro_addConstGate_target_bit bits q_start N x i hi hN

/-! ## Deliverable D — Workspace cleanup and flag preservation. -/

/-- **Conditional add carry-in restored.** -/
theorem sqir_conditionalAddConstGate_carry_in_restored
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos flag) q_start = false := by
  cases flag with
  | false =>
    have h_flag_false : (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
                       = false := update_eq _ _ _
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start N flagPos
          _ h_flag_distinct h_flag_false hflag_out]
    rw [cuccaro_n_bit_adder_full_update_outside_workspace_at bits q_start flagPos false
          _ q_start hflag_out (by omega)]
    rw [cuccaro_n_bit_adder_full_carry_in_restored bits q_start
        (cuccaro_input_F q_start false 0 x)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  | true =>
    have h_flag_true : (update (cuccaro_input_F q_start false 0 x) flagPos true) flagPos
                      = true := update_eq _ _ _
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start N flagPos
          _ h_flag_distinct h_flag_true hflag_out]
    rw [cuccaro_addConstGate_update_outside_workspace_at bits q_start N flagPos true
          _ q_start hflag_out (by omega)]
    exact cuccaro_addConstGate_carry_in_bit bits q_start N x

/-- **Conditional add read register restored.** -/
theorem sqir_conditionalAddConstGate_read_decode
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos flag)) = 0 := by
  have h_eq : cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos flag)) = 0 % 2^bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match bits q_start 0 _
    intro i hi
    cases flag with
    | false =>
      have h_flag_false : (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
                         = false := update_eq _ _ _
      rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start N flagPos
            _ h_flag_distinct h_flag_false hflag_out]
      rw [cuccaro_n_bit_adder_full_update_outside_workspace_at bits q_start flagPos false
            _ (q_start + 2 * i + 2) hflag_out (by omega)]
      rw [cuccaro_n_bit_adder_full_a_restored bits q_start
          (cuccaro_input_F q_start false 0 x) i hi]
      rw [cuccaro_input_F_at_a q_start i false 0 x]
    | true =>
      have h_flag_true : (update (cuccaro_input_F q_start false 0 x) flagPos true) flagPos
                        = true := update_eq _ _ _
      rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start N flagPos
            _ h_flag_distinct h_flag_true hflag_out]
      rw [cuccaro_addConstGate_update_outside_workspace_at bits q_start N flagPos true
            _ (q_start + 2 * i + 2) hflag_out (by omega)]
      rw [cuccaro_addConstGate_read_bit bits q_start N x i hi]
      simp [Nat.zero_testBit]
  rw [h_eq]
  simp

/-- **Conditional add flag preserved.** -/
theorem sqir_conditionalAddConstGate_flag_preserved
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
        (update (cuccaro_input_F q_start false 0 x) flagPos flag) flagPos = flag := by
  cases flag with
  | false =>
    have h_flag_false : (update (cuccaro_input_F q_start false 0 x) flagPos false) flagPos
                       = false := update_eq _ _ _
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start N flagPos
          _ h_flag_distinct h_flag_false hflag_out]
    exact cuccaro_n_bit_adder_full_preserves_outside_workspace bits q_start flagPos false
      (cuccaro_input_F q_start false 0 x) hflag_out
  | true =>
    have h_flag_true : (update (cuccaro_input_F q_start false 0 x) flagPos true) flagPos
                      = true := update_eq _ _ _
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start N flagPos
          _ h_flag_distinct h_flag_true hflag_out]
    exact cuccaro_addConstGate_preserves_outside_workspace bits q_start N flagPos true
      (cuccaro_input_F q_start false 0 x) hflag_out

/-! ## Deliverable E — Clean bundle. -/

/-- **HEADLINE Deliverable E — packaged clean conditional add.** -/
theorem sqir_conditionalAddConstGate_clean
    (bits q_start N x flagPos dim : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN : N < 2^bits) (hx : x < 2^bits)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped dim (sqir_conditionalAddConstGate bits q_start N flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos flag))
        = (x + (if flag then N else 0)) % 2^bits
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
            (update (cuccaro_input_F q_start false 0 x) flagPos flag)) = 0
    ∧ Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos flag) q_start = false
    ∧ Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos flag) flagPos = flag := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sqir_conditionalAddConstGate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag h_flag_distinct
  · exact sqir_conditionalAddConstGate_target_decode bits q_start N x flagPos flag
      hbits hN hx h_flag_distinct hflag_out
  · exact sqir_conditionalAddConstGate_read_decode bits q_start N x flagPos flag
      hbits hN hx h_flag_distinct hflag_out
  · exact sqir_conditionalAddConstGate_carry_in_restored bits q_start N x flagPos flag
      hbits hN hx h_flag_distinct hflag_out
  · exact sqir_conditionalAddConstGate_flag_preserved bits q_start N x flagPos flag
      h_flag_distinct hflag_out

/-! ## Deliverable F — Conditional sub target decode. -/

/-- **HEADLINE Deliverable F — conditional sub target decode.** -/
theorem sqir_conditionalSubConstGate_target_decode
    (bits q_start N x flagPos : Nat) (flag : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos)
          (update (cuccaro_input_F q_start false 0 x) flagPos flag))
      = (x + (if flag then 2^bits - N else 0)) % 2^bits := by
  unfold sqir_conditionalSubConstGate
  have h_K_lt : 2^bits - N < 2^bits := by omega
  exact sqir_conditionalAddConstGate_target_decode bits q_start (2^bits - N) x flagPos flag
    hbits h_K_lt hx h_flag_distinct hflag_out

/-! ## Status note (Tick 56).

Landed (kernel-clean):
- Tick 55 helpers (per-position).
- Tick 56 function-level reductions:
  * `sqir_prepareMaskedConstRead_eq_id_fun`
  * `sqir_prepareMaskedConstRead_eq_unmasked_fun`
- **HEADLINE Deliverable A** `sqir_conditionalAddConstGate_apply_false_fun`:
  conditional gate ≡ bare adder at function level when flag = false.
- **HEADLINE Deliverable B** `sqir_conditionalAddConstGate_apply_true_fun`:
  conditional gate ≡ cuccaro_addConstGate N at function level when flag = true.
- `cuccaro_carry_update_outside_locality`: cuccaro_carry's input-locality.

NOT yet landed (next tick):
- Deliverable C (target_decode): the function-level reductions reduce
  the conditional add to known primitives, but extracting target_decode
  on the `update input flagPos flag` state requires a full
  cuccaro_addConstGate locality argument (analogous to Tick 52's work
  for chain_inv). This is tractable but several theorems of work.
- Deliverables D, E, F.

The function-level reductions (A and B) are the structural foundation:
they reduce the conditional gate to gates whose behavior on
cuccaro_input_F-style states is already proved. The remaining gap is
the locality argument for transferring those theorems to states with
`update` at outside-workspace positions. -/

end FormalRV.BQAlgo
