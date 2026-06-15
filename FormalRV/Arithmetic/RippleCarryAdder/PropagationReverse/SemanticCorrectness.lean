/-
  FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.SemanticCorrectness
  Part 1/4: the reverse-cascade semantic-correctness assembly — the K-inductive
  read/target reductions, the j=0/j=1/j>=2 cases, the headline
  `gidney_classical_action_with_reverse`, `Gidney.post_full_reverse_invariant_holds`,
  and the RSA-2048 T-count examples. (One of the two headlines; the patched
  carry-clearance backbone is `CarryClearanceBackbone`.)
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Framework.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDecideWitnesses

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-- **Propagation reverse at read_j reduces to interior_reverse(j-1)**
    (2026-05-14 tick, read-side analog of line ~5488 target version).
    For j ∈ [2, K], propagation_reverse(K) g (read_idx j) equals
    interior_reverse(j-1) g (read_idx j). Same induction-on-K +
    case-split structure as target version, with read_idx in place
    of target_idx and using the read-side preserves/dependence
    helpers (`_preserves_read_above`, `_at_read_low_dependence`). -/
theorem gidney_propagation_reverse_at_read_eq_interior_reverse
    (K j : Nat) (hj : 1 < j) (hjK : j ≤ K) (g : Nat → Bool) :
    gidney_propagation_reverse_post_state K g (read_idx j)
    = gidney_interior_bit_reverse_post_state (j - 1) g (read_idx j) := by
  induction K generalizing g with
  | zero => omega
  | succ m ih =>
      match m with
      | 0 => omega
      | p + 1 =>
          show gidney_propagation_reverse_post_state (p + 1)
                (gidney_interior_bit_reverse_post_state (p + 1) g) (read_idx j)
              = gidney_interior_bit_reverse_post_state (j - 1) g (read_idx j)
          by_cases hjm : j = p + 2
          · subst hjm
            rw [gidney_propagation_reverse_preserves_read_above (p + 1) (p + 2)
                  (by omega) _, show (p + 2) - 1 = p + 1 from by omega]
          · have hjeq : (j - 1) + 1 = j := by omega
            rw [ih (by omega)]
            have key := gidney_interior_bit_reverse_at_read_low_dependence (j - 1)
              (by omega) (gidney_interior_bit_reverse_post_state (p + 1) g) g
              (hjeq ▸ gidney_interior_bit_reverse_post_state_preserves_outside
                (p + 1) g (read_idx j)
                (by unfold read_idx carry_idx; omega)
                (by unfold read_idx; omega)
                (by unfold read_idx target_idx; omega))
              (gidney_interior_bit_reverse_post_state_preserves_outside
                (p + 1) g (carry_idx (j - 1))
                (by unfold carry_idx; omega)
                (by unfold carry_idx read_idx; omega)
                (by unfold carry_idx target_idx; omega))
            simpa [hjeq] using key

/-- **Headline j ≥ 2 case** (Iter 208 STATED, sorried). For
    j ∈ [2, n-1], target_idx j after full forward+CX+reverse equals
    sum_j. The relevant per-step is `interior_reverse(j-1)` which
    fires at cascade step (n-j+1).

    Proof structure (pending):
    - "High-position frame": earlier reverses (last_reverse(n-1) +
      interior_reverse(n-2), ..., interior_reverse(j)) all modify
      positions ≥ 3j+2 (= c_j minimum). They preserve interior_reverse(j-1)'s
      input positions ≤ 3j+1.
    - Apply Iter 201's `gidney_interior_bit_reverse_computes_sum`
      with hypotheses verified from post-CX (Iter 189).
    - "Low-position frame": later reverses (interior_reverse(j-2),
      ..., first_reverse) all modify positions ≤ 3j-2. They preserve
      target_idx j = 3j+1.
    - Conclude full_reverse n f (target_idx j) = sum_j.

    Estimated 60-100 lines for the structural framing. The per-step
    computes_sum + frame conditions are mechanical mirror of the
    forward cascade pipeline (Iter 175-181). -/
theorem gidney_classical_action_with_reverse_target_geq_2
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)
    (j : Nat) (hj : 2 ≤ j) (hjn : j < n) :
    gidney_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (target_idx j)
    = adder_sum_bit_classical a b j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set f := gidney_final_cx_cascade_post_state (m + 2)
            (gidney_forward_faithful_full_post_state (m + 2) (adder_input_F (m + 2) a b))
  have h_inv : Gidney.post_forward_final_cx_invariant (m + 2) a b f :=
    Gidney.post_forward_final_cx_invariant_holds (m + 2) a b hn ha hb
  have hjm1 : 0 < j - 1 := by omega
  have hjeq : (j - 1) + 1 = j := by omega
  show gidney_propagation_reverse_post_state (m + 1)
        (gidney_last_bit_reverse_post_state (m + 1) f) (target_idx j)
      = adder_sum_bit_classical a b j
  rw [gidney_propagation_reverse_at_target_eq_interior_reverse (m + 1) j (by omega)
        (by omega) _,
      show target_idx j = target_idx ((j - 1) + 1) from by rw [hjeq],
      gidney_interior_bit_reverse_at_target_low_dependence (j - 1) hjm1
        (gidney_last_bit_reverse_post_state (m + 1) f) f
        (gidney_last_bit_reverse_post_state_preserves_outside _ _ _
          (by unfold target_idx carry_idx; omega))
        (gidney_last_bit_reverse_post_state_preserves_outside _ _ _
          (by unfold carry_idx; omega)),
      show adder_sum_bit_classical a b j = adder_sum_bit_classical a b ((j - 1) + 1)
        from by rw [hjeq]]
  exact gidney_interior_bit_reverse_computes_sum (j - 1) a b hjm1 f
    (hjeq ▸ (h_inv (j - 1) (by omega)).1 :
      f (carry_idx (j - 1)) = Adder.carry false ((j - 1) + 1) a.testBit b.testBit)
    (hjeq ▸ (h_inv j (by omega)).2.2 :
      f (target_idx ((j - 1) + 1)) = xor (a.testBit ((j - 1) + 1)) (b.testBit ((j - 1) + 1)))

/-- **First-bit reverse preserves read_0** (2026-05-14 tick). Mirror of
    `_preserves_target_0` at line 4933. first_bit_reverse modifies
    {target_1, read_1, carry_0} = {4, 3, 2}; read_idx 0 = 0 ≠ any. -/
theorem gidney_first_bit_reverse_preserves_read_0 (f : Nat → Bool) :
    gidney_first_bit_reverse_post_state f (read_idx 0) = f (read_idx 0) := by
  have h1 : read_idx 0 ≠ target_idx 1 := by unfold read_idx target_idx; omega
  have h2 : read_idx 0 ≠ read_idx 1 := by unfold read_idx; omega
  have h3 : read_idx 0 ≠ carry_idx 0 := by unfold read_idx carry_idx; omega
  unfold gidney_first_bit_reverse_post_state
  rw [update_neq _ _ _ _ h3, update_neq _ _ _ _ h2, update_neq _ _ _ _ h1]

/-- **Headline j=0 read case PROVEN parametrically over n** (2026-05-14
    tick, read-side analog of `_with_reverse_target_0` at line 5296).
    Uses `gidney_full_reverse_eq_first_rev_low` (since read_idx 0 = 0 < 5)
    to reduce to first_bit_reverse, then the just-proven
    `_first_bit_reverse_preserves_read_0` frame, then the
    `post_forward_final_cx_invariant` at j=0 simplification
    `xor a_0 (Adder.carry false 0 a b) = xor a_0 false = a_0`. -/
theorem gidney_classical_action_with_reverse_read_0
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    gidney_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (read_idx 0)
    = a.testBit 0 := by
  rw [gidney_full_reverse_eq_first_rev_low n hn _ (read_idx 0)
        (by unfold read_idx; omega),
      gidney_first_bit_reverse_preserves_read_0,
      ((Gidney.post_forward_final_cx_invariant_holds n a b hn ha hb) 0
        (by omega)).2.1]
  simp [Adder.carry]

/-- **Headline j=1 read case PROVEN parametrically over n** (2026-05-14 tick,
    read-side analog of `_with_reverse_target_1` at line 5317). Uses
    `gidney_full_reverse_eq_first_rev_low` (read_idx 1 = 3 < 5) to reduce
    to first_bit_reverse, then Iter 194's `.2.1` directly gives
    `first_bit_reverse f (read_idx 1) = a.testBit 1`. -/
theorem gidney_classical_action_with_reverse_read_1
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    gidney_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (read_idx 1)
    = a.testBit 1 := by
  rw [gidney_full_reverse_eq_first_rev_low n hn _ (read_idx 1)
        (by unfold read_idx; omega)]
  set f := gidney_final_cx_cascade_post_state n
            (gidney_forward_faithful_full_post_state n (adder_input_F n a b))
  have h_inv : Gidney.post_forward_final_cx_invariant n a b f :=
    Gidney.post_forward_final_cx_invariant_holds n a b hn ha hb
  exact (gidney_first_bit_reverse_preserves a b f
    (by rw [(h_inv 0 (by omega)).2.1]; simp [Adder.carry])
    (h_inv 0 (by omega)).2.2 (h_inv 0 (by omega)).1
    (h_inv 1 (by omega)).2.1 (h_inv 1 (by omega)).2.2).2.1

/-- **Read-side analog of `_with_reverse_target_geq_2`** (2026-05-14 tick).
    For j ∈ [2, n-1], the read_j position after the full forward+CX+reverse
    cascade equals `a.testBit j`. Same proof structure as the target version,
    using the read-side parametric `_at_read_eq_interior_reverse` and the
    read component (`.2.1`) of Iter 195's `_post_state_in_bits`, with XOR
    cancellation `xor (xor a_j c_j) c_j = a_j`. -/
theorem gidney_classical_action_with_reverse_read_geq_2
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)
    (j : Nat) (hj : 2 ≤ j) (hjn : j < n) :
    gidney_full_reverse_post_state n
      (gidney_final_cx_cascade_post_state n
        (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
      (read_idx j)
    = a.testBit j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set f := gidney_final_cx_cascade_post_state (m + 2)
            (gidney_forward_faithful_full_post_state (m + 2) (adder_input_F (m + 2) a b))
            with hf
  have h_inv : Gidney.post_forward_final_cx_invariant (m + 2) a b f :=
    Gidney.post_forward_final_cx_invariant_holds (m + 2) a b hn ha hb
  show gidney_propagation_reverse_post_state (m + 1)
        (gidney_last_bit_reverse_post_state (m + 1) f) (read_idx j)
      = a.testBit j
  rw [gidney_propagation_reverse_at_read_eq_interior_reverse (m + 1) j (by omega)
        (by omega) _]
  have hjm1 : 0 < j - 1 := by omega
  have hjeq : (j - 1) + 1 = j := by omega
  rw [show read_idx j = read_idx ((j - 1) + 1) from by rw [hjeq],
      gidney_interior_bit_reverse_at_read_low_dependence (j - 1) hjm1
        (gidney_last_bit_reverse_post_state (m + 1) f) f
        (gidney_last_bit_reverse_post_state_preserves_outside _ _ _
          (by unfold read_idx carry_idx; omega))
        (gidney_last_bit_reverse_post_state_preserves_outside _ _ _
          (by unfold carry_idx; omega)),
      (gidney_interior_bit_reverse_post_state_in_bits (j - 1) hjm1 f).2.1,
      hjeq, (h_inv j (by omega)).2.1,
      (hjeq ▸ (h_inv (j - 1) (by omega)).1 :
        f (carry_idx (j - 1)) = Adder.carry false j a.testBit b.testBit)]
  cases a.testBit j <;>
    cases (Adder.carry false j a.testBit b.testBit) <;> rfl

/-- **HEADLINE: TODO_gidney_classical_action_with_reverse PROVEN**
    (Iter 208 ASSEMBLY, modulo Iter 208's j ≥ 2 sorry). Combines:
    - Iter 202: j=0 case PARAMETRIC.
    - Iter 207: j=1 case PARAMETRIC over n.
    - Iter 208: TODO_..._target_geq_2 for j ∈ [2, n-1] (sorried). -/
theorem gidney_classical_action_with_reverse_assembled
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    ∀ i, i < n →
      gidney_full_reverse_post_state n
        (gidney_final_cx_cascade_post_state n
          (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
        (target_idx i)
      = adder_sum_bit_classical a b i := by
  intro i hi
  match i, hi with
  | 0, _ => exact gidney_classical_action_with_reverse_target_0 n a b hn ha hb
  | 1, _ => exact gidney_classical_action_with_reverse_target_1 n a b hn ha hb
  | j + 2, hi' =>
      exact gidney_classical_action_with_reverse_target_geq_2 n a b
              hn ha hb (j + 2) (by omega) hi'

/-- **HEADLINE — Iter 191's restated headline, NOW PROVEN (Iter 213,
    2026-05-13)**. The parametric semantic-correctness theorem with
    the REVERSE cascade. The Gidney ripple-carry adder is now Verified
    per CLAUDE.md taxonomy.

    Note: this theorem statement was originally drafted at line ~4605
    as `TODO_gidney_classical_action_with_reverse` (sorried, Iter 191).
    Iter 213 derives it via `gidney_classical_action_with_reverse_assembled`. -/
theorem gidney_classical_action_with_reverse (n a b : Nat)
    (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    ∀ i, i < n →
      gidney_full_reverse_post_state n
        (gidney_final_cx_cascade_post_state n
          (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))
        (target_idx i)
      = adder_sum_bit_classical a b i :=
  gidney_classical_action_with_reverse_assembled n a b hn ha hb

/-! ### Direct cascade target (relocated 2026-05-14 to clear forward refs)

    Moved here from earlier in the file. This theorem uses both
    `gidney_propagation_reverse_eq_first_rev_low` (above, line ~5248)
    and `gidney_propagation_reverse_at_target_eq_interior_reverse`
    (above, line ~5481), so it must live after both. -/

/-- **Direct (non-K-inductive) cascade target** (2026-05-14 tick).
    For register width `n ≥ 2`, the parametric `propagation_reverse(n-1)`
    applied to the post-final-CX state produces a state satisfying
    `Gidney.reverse_step_invariant (n - 1) n a b _`.

    **Proof structure**: case-split on `j` in the predicate quantifier:
    - `j = 1`: use `gidney_propagation_reverse_eq_first_rev_low` to
      reduce propagation_reverse(n-1) at target_idx 1 / read_idx 1
      to first_bit_reverse, then Iter 194's
      `gidney_first_bit_reverse_preserves` closes both, with the
      target side using `sumfb_eq_testBit_add` for the XOR identity.
    - `1 < j ≤ n - 1`: TODO_case_j_gt_1 — use
      `gidney_propagation_reverse_at_target_eq_interior_reverse` to
      reduce to interior_reverse(j-1), then Iter 201. -/
theorem Gidney.reverse_step_invariant_n_minus_1_after_propagation_reverse
    (n a b : Nat) (hn : 1 < n) (_ha : a < 2^n) (_hb : b < 2^n)
    (input : Nat → Bool)
    (h_input : Gidney.post_forward_final_cx_invariant n a b input)
    (_h_t0 : input (target_idx 0) = adder_sum_bit_classical a b 0) :
    Gidney.reverse_step_invariant (n - 1) n a b
      (gidney_propagation_reverse_post_state (n - 1) input) := by
  intro j h_lo h_hi
  rcases Nat.lt_or_ge 1 j with h_j_gt_1 | h_j_le_1
  · have hj1 : 0 < j - 1 := by omega
    have h_jj : (j - 1) + 1 = j := Nat.sub_add_cancel (by omega : 1 ≤ j)
    obtain ⟨h_c_jm1, _, _⟩ := h_input (j - 1) (by omega)
    obtain ⟨_, h_r_j_raw, _⟩ := h_input j h_hi
    have iter201 := gidney_interior_bit_reverse_computes_sum
                      (j - 1) a b hj1 input h_c_jm1
                      (by rw [h_jj]; exact (h_input j h_hi).2.2)
    refine ⟨?_, ?_⟩
    · rw [gidney_propagation_reverse_at_target_eq_interior_reverse
            (n - 1) j h_j_gt_1 (by omega) input]
      show gidney_interior_bit_reverse_post_state (j - 1) input (target_idx j)
           = adder_sum_bit_classical a b j
      rw [show target_idx j = target_idx ((j - 1) + 1) from by rw [h_jj]]
      rw [iter201, h_jj]
    · rw [gidney_propagation_reverse_at_read_eq_interior_reverse
            (n - 1) j h_j_gt_1 (by omega) input]
      rw [show read_idx j = read_idx ((j - 1) + 1) from by rw [h_jj]]
      rw [(gidney_interior_bit_reverse_post_state_in_bits (j - 1) hj1 input).2.1]
      rw [h_jj, h_r_j_raw, h_c_jm1, h_jj]
      cases a.testBit j <;>
        cases (Adder.carry false j a.testBit b.testBit) <;> rfl
  · have h_j_eq_1 : j = 1 := by omega
    subst h_j_eq_1
    have h_K_pos : 0 < n - 1 := by omega
    obtain ⟨h_c0, h_r0_raw, h_t0_pre⟩ := h_input 0 (by omega)
    obtain ⟨_, h_r1, h_t1⟩ := h_input 1 hn
    have h_r0 : input (read_idx 0) = a.testBit 0 := by
      rw [h_r0_raw]; cases a.testBit 0 <;> rfl
    have iter194 := gidney_first_bit_reverse_preserves a b input
                     h_r0 h_t0_pre h_c0 h_r1 h_t1
    refine ⟨?_, ?_⟩
    · rw [gidney_propagation_reverse_eq_first_rev_low
            (n - 1) h_K_pos input (target_idx 1) (by unfold target_idx; omega),
          iter194.2.2]
      unfold adder_sum_bit_classical
      rw [← Adder.sumfb_eq_testBit_add]
      unfold Adder.sumfb
      dsimp only
      cases a.testBit 1 <;> cases b.testBit 1 <;>
        cases (Adder.carry false 1 a.testBit b.testBit) <;> rfl
    · rw [gidney_propagation_reverse_eq_first_rev_low
            (n - 1) h_K_pos input (read_idx 1) (by unfold read_idx; omega),
          iter194.2.1]

/-! ### Closing composition discharging TODO_post_full_reverse_invariant_holds

    Composes the parametric cascade work (target side via existing Iter 213
    `gidney_classical_action_with_reverse`; read side via the new direct
    theorem + last_reverse bridging) into the original load-bearing review
    deliverable. -/

/-- **Closing composition** (2026-05-14 tick). For every n ≥ 2 and
    valid a, b inputs, the full forward + final-CX + reverse cascade
    state satisfies `Gidney.post_full_reverse_invariant`: every
    target_j equals sum_j AND every read_j equals a.testBit j.

    Target side: closed via the existing `gidney_classical_action_with_reverse`
    (Iter 213 assembly).

    Read side: TODO_read_via_direct — bridge from the new
    `_n_minus_1_after_propagation_reverse` (which proves the read side
    for the SIMPLER input `propagation_reverse(n-1) f` without the
    outer last_reverse layer) to the actual cascade
    `propagation_reverse(n-1) (last_reverse(n-1) f)`. The bridge
    requires showing that propagation_reverse is c_{n-1}-independent
    on read positions (since last_reverse modifies only c_{n-1}).
    ~30 lines of frame argument, deferred to next tick. -/
theorem Gidney.post_full_reverse_invariant_holds
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.post_full_reverse_invariant n a b
      (gidney_full_reverse_post_state n
        (gidney_final_cx_cascade_post_state n
          (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))) := by
  intro j hj
  refine ⟨?_, ?_⟩
  · -- Target side: existing Iter 213 lemma covers all j ∈ [0, n-1].
    exact gidney_classical_action_with_reverse n a b hn ha hb j hj
  · -- Read side: needs the c_{n-1}-independence bridge from the
    -- direct theorem `_n_minus_1_after_propagation_reverse` to the
    -- actual `propagation_reverse(n-1) (last_reverse(n-1) f)` form.
    -- Read side: split on j and apply the three proven cases.
    match j, hj with
    | 0,     hj => exact gidney_classical_action_with_reverse_read_0 n a b hn ha hb
    | 1,     hj => exact gidney_classical_action_with_reverse_read_1 n a b hn ha hb
    | k + 2, hj =>
        exact gidney_classical_action_with_reverse_read_geq_2
                n a b hn ha hb (k + 2) (by omega) hj

/-- **Milestone validation** (2026-05-14 tick): the proven theorem fires
    correctly on the Iter 182 counterexample case (n=2, a=1, b=1) — the
    same instance where the original `TODO_gidney_classical_action`
    was found to be UNPROVABLE as stated. Confirms semantic-correctness
    closure at the smallest non-trivial input.

    Review hygiene (via `mcp__lean-lsp__lean_verify`, 2026-05-14):
    `Gidney.post_full_reverse_invariant_holds` depends only on
    `propext` and `Quot.sound` — Lean's standard foundational axioms.
    No custom axioms. See `notes/axiom-hygiene.md`. -/
example :
    Gidney.post_full_reverse_invariant 2 1 1
      (gidney_full_reverse_post_state 2
        (gidney_final_cx_cascade_post_state 2
          (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1)))) :=
  Gidney.post_full_reverse_invariant_holds 2 1 1
    (by omega) (by omega) (by omega)

/-! ## RSA-2048-scale instantiation: q_A=33 → 462 T-gates (Iter 262, 2026-05-14)

    With the adder semantically Verified (Iter 213's
    `gidney_classical_action_with_reverse`), the parametric T-count
    theorem `tcount_gidney_adder_full_faithful_no_measurement` (= 14n)
    can now be instantiated at the RSA-2048 max adder size q_A = 33
    to give a verified-correctness cost claim. -/

/-- **RSA-2048 adder T-count = 462** (Iter 262). For the maximum adder
    size in the RSA-2048 Shor's circuit (q_A = 33, qianxu p. 22),
    `tcount (gidney_adder_full_faithful_no_measurement 33) = 14·33 = 462`.

    Per qianxu Eq. E3: τ_adder = 25 q_A τ_s = 825 τ_s. The 462 T-gates
    is the underlying T-count from which the per-Toffoli cost (here
    14n / q_A = 14) becomes a verified-correctness building block. -/
example : tcount (gidney_adder_full_faithful_no_measurement 33) = 462 :=
  tcount_gidney_adder_full_faithful_no_measurement 31

/-- **Bridge: verified parametric T-count matches the RSA-2048
    paper-claim anchor** (Iter 263). Closes the review's paper-claim-first
    discipline (CLAUDE.md): the gate-faithful adder's T-count at q_A=33
    matches the `gidney_adder_RSA2048_T_count_verified` paper-claim
    constant in `PaperClaims.lean`. -/
example :
    tcount (gidney_adder_full_faithful_no_measurement
              qianxu_q_A_RSA2048)
      = gidney_adder_RSA2048_T_count_verified := by
  unfold qianxu_q_A_RSA2048 gidney_adder_RSA2048_T_count_verified
  exact tcount_gidney_adder_full_faithful_no_measurement 31

end FormalRV.BQAlgo
