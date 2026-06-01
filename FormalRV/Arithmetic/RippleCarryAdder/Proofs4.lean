import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Corpus.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases
import FormalRV.Arithmetic.RippleCarryAdder.Defs
import FormalRV.Arithmetic.RippleCarryAdder.Proofs3

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

/-! ## `Gate.applyNat` bridge for the Gidney faithful bit-step family

The three existing `gidney_*_correct` theorems (interior, first, last)
are stated in the `uc_eval (Gate.toUCom dim _) * f_to_vec dim f
= f_to_vec dim (post_state f)` form.  The matching `Gate.applyNat`
identities follow by definitional unfolding alone — they are `rfl`
proofs.  Their value lies in giving downstream modular-multiplier
correctness proofs a *Boolean-level* description of the adder that
needs no matrix/`f_to_vec` machinery.

Together with `Gate.applyNat_oob` (in `BQAlgo/Correctness.lean`) and
`Gate.applyNat_eq_encodeDataZeroAnc_of_data_anc` (in
`BQAlgo/MCPBridge.lean`), these wrappers complete the route from the
existing Gidney bit-step corpus to the `MultiplyCircuitProperty`
obligation of `f_modmult_circuit_MMI`. -/

/-- `Gate.applyNat` form of `gidney_adder_bit_step_0_correct`.  The
i=0 step is a single CCX; its applyNat semantics matches the
single-bit Toffoli update directly. -/
theorem gidney_adder_bit_step_0_applyNat (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step 0) f
      = update f (carry_idx 0)
          (xor (f (carry_idx 0))
               (f (read_idx 0) && f (target_idx 0))) := by
  rfl

/-- `Gate.applyNat` form of `gidney_adder_bit_step_faithful_first_correct`.
The first-bit step's `applyNat` action is exactly the three-update
chain captured by `gidney_first_bit_post_state`. -/
theorem gidney_adder_bit_step_faithful_first_applyNat (f : Nat → Bool) :
    Gate.applyNat gidney_adder_bit_step_faithful_first f
      = gidney_first_bit_post_state f := by
  rfl

/-- `Gate.applyNat` form of `gidney_adder_bit_step_faithful_interior_correct`.
The interior step's `applyNat` action is exactly the four-update
chain captured by `gidney_bit_step_faithful_post_state`. -/
theorem gidney_adder_bit_step_faithful_interior_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior i) f
      = gidney_bit_step_faithful_post_state i f := by
  rfl

/-- `Gate.applyNat` form of `gidney_adder_bit_step_faithful_last_correct`.
The last-bit step's `applyNat` action is exactly the two-update
chain captured by `gidney_last_bit_post_state`. -/
theorem gidney_adder_bit_step_faithful_last_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last i) f
      = gidney_last_bit_post_state i f := by
  rfl

/-! ## `Gate.applyNat` form for the n-bit Gidney forward pass

Compositional wrappers that lift the per-bit-step `Gate.applyNat`
identities (above) into full-cascade `Gate.applyNat` statements.
All three are proved by structural recursion on `n` using the
per-bit-step wrappers; each non-base case is a single `rw` through
the recursion + the per-step wrapper, followed by `rfl`.

Together they describe the Boolean action of the **forward direction**
of the Gidney faithful adder: propagation cascade (`n` faithful interior
bit-steps), full forward pass (propagation + last-bit step), and final
CX cascade (`read[i] → target[i]` XOR for `i = 0..n-1`).  The reverse
half (needed for the full no-measurement adder) follows the same
pattern; the arithmetic-semantics theorem that connects the chained
`post_state` to `(read, target, carry) ↦ (read, read+target mod 2^n, 0)`
is a separate, still-open obligation (Iter 88-89 in the existing
review). -/

/-- `Gate.applyNat` form of the final CX cascade.  The cascade is a
sequence of `CX(read[i], target[i])` for `i = 0..n-1`; its `applyNat`
action is the chained `update` exactly captured by
`gidney_final_cx_cascade_post_state`. -/
theorem gidney_final_cx_cascade_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_final_cx_cascade n) f
        = gidney_final_cx_cascade_post_state n f
  | 0,     _ => rfl
  | n + 1, f => by
      show Gate.applyNat (Gate.CX (read_idx n) (target_idx n))
            (Gate.applyNat (gidney_final_cx_cascade n) f)
        = update (gidney_final_cx_cascade_post_state n f)
            (target_idx n)
            (xor (gidney_final_cx_cascade_post_state n f (target_idx n))
                 (gidney_final_cx_cascade_post_state n f (read_idx n)))
      rw [gidney_final_cx_cascade_applyNat n f]
      rfl

/-- `Gate.applyNat` form of the n-bit Gidney forward propagation
cascade.  Composes per-bit-step `Gate.applyNat` identities (Tick B)
via the seq case.  Base cases (`n = 0, 1`) and the inductive case all
reduce to a single rewrite through the recursive identity + the
per-step wrapper. -/
theorem gidney_adder_forward_with_propagation_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_with_propagation n) f
        = gidney_propagation_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_bit_step_faithful_interior (n + 1))
            (Gate.applyNat (gidney_adder_forward_with_propagation (n + 1)) f)
        = gidney_bit_step_faithful_post_state (n + 1)
            (gidney_propagation_post_state (n + 1) f)
      rw [gidney_adder_forward_with_propagation_applyNat (n + 1) f,
          gidney_adder_bit_step_faithful_interior_applyNat]

/-- `Gate.applyNat` form of the full Gidney forward pass.  The
`applyNat` action is the propagation post-state through bit n-1
chained with the last-bit step at position n-1. -/
theorem gidney_adder_forward_faithful_full_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_faithful_full n) f
        = gidney_forward_faithful_full_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_bit_step_faithful_last (n + 1))
            (Gate.applyNat (gidney_adder_forward_with_propagation (n + 1)) f)
        = gidney_last_bit_post_state (n + 1)
            (gidney_propagation_post_state (n + 1) f)
      rw [gidney_adder_forward_with_propagation_applyNat (n + 1) f,
          gidney_adder_bit_step_faithful_last_applyNat]

/-- Decoder bound: `read_val < 2^n` for any bit-function. -/
theorem gidney_read_val_lt : ∀ (n : Nat) (f : Nat → Bool),
    gidney_read_val n f < 2^n
  | 0,     _ => by simp [gidney_read_val]
  | n + 1, f => by
      unfold gidney_read_val
      have ih := gidney_read_val_lt n f
      rcases f (read_idx n) <;> simp <;> (rw [pow_succ]; omega)

/-- Decoder bound: `target_val < 2^n`. -/
theorem gidney_target_val_lt : ∀ (n : Nat) (f : Nat → Bool),
    gidney_target_val n f < 2^n
  | 0,     _ => by simp [gidney_target_val]
  | n + 1, f => by
      unfold gidney_target_val
      have ih := gidney_target_val_lt n f
      rcases f (target_idx n) <;> simp <;> (rw [pow_succ]; omega)

/-- Decoder bound: `carry_val < 2^n`. -/
theorem gidney_carry_val_lt : ∀ (n : Nat) (f : Nat → Bool),
    gidney_carry_val n f < 2^n
  | 0,     _ => by simp [gidney_carry_val]
  | n + 1, f => by
      unfold gidney_carry_val
      have ih := gidney_carry_val_lt n f
      rcases f (carry_idx n) <;> simp <;> (rw [pow_succ]; omega)

/-- **Target register is correct**: after the full faithful no-measurement
adder, target encodes `1 + 1 = 2`. -/
example :
    gidney_target_val 2
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement 2)
        inputF_1_plus_1_tickD) = 2 := by decide

/-- **Read register is preserved**: after the full faithful no-measurement
adder, read = 1 (unchanged). -/
example :
    gidney_read_val 2
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement 2)
        inputF_1_plus_1_tickD) = 1 := by decide

/-- **Carry register is NOT cleared**: after the full faithful
no-measurement adder, carry = 3 (binary `11`), not 0.  This is the
open gap that blocks a verified modular adder built on this circuit. -/
example :
    gidney_carry_val 2
      (Gate.applyNat (gidney_adder_full_faithful_no_measurement 2)
        inputF_1_plus_1_tickD) = 3 := by decide

/-! ## `Gate.applyNat` wrappers for the Gidney reverse cascade

Mirror of the forward-direction Tick B/C wrappers, lifting the per-bit
reverse steps and the full reverse cascade into `Gate.applyNat`
identities.  Each per-step wrapper is `rfl` (the `*_reverse_post_state`
definitions at Iter 191 are written as exactly the update chains that
`Gate.applyNat` produces); the cascade wrappers chain those rfls via
structural recursion using `rw`.

Combined with `gidney_adder_full_faithful_no_measurement_applyNat`
below, these connect the existing Iter 191 reverse-cascade analysis
(which proves target-bit correctness via `decide`-witnesses) to the
`Gate.applyNat` framework.  This is the missing infrastructure that
lets future modmult-correctness work reason about the full adder's
classical action without descending into the matrix layer. -/

/-- `Gate.applyNat` form of the first-bit reverse step. -/
theorem gidney_adder_bit_step_faithful_first_reverse_applyNat
    (f : Nat → Bool) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f
      = gidney_first_bit_reverse_post_state f := by rfl

/-- `Gate.applyNat` form of the interior-bit reverse step. -/
theorem gidney_adder_bit_step_faithful_interior_reverse_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f
      = gidney_interior_bit_reverse_post_state i f := by rfl

/-- `Gate.applyNat` form of the last-bit reverse step. -/
theorem gidney_adder_bit_step_faithful_last_reverse_applyNat
    (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f
      = gidney_last_bit_reverse_post_state i f := by rfl

/-- `Gate.applyNat` form of the n-bit propagation reverse cascade. -/
theorem gidney_adder_forward_with_propagation_reverse_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse n) f
        = gidney_propagation_reverse_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (n + 1)) f)
        = gidney_propagation_reverse_post_state (n + 1)
            (gidney_interior_bit_reverse_post_state (n + 1) f)
      rw [gidney_adder_bit_step_faithful_interior_reverse_applyNat,
          gidney_adder_forward_with_propagation_reverse_applyNat (n + 1)]

/-- `Gate.applyNat` form of the full Gidney reverse cascade. -/
theorem gidney_adder_forward_faithful_full_reverse_applyNat :
    ∀ (n : Nat) (f : Nat → Bool),
      Gate.applyNat (gidney_adder_forward_faithful_full_reverse n) f
        = gidney_full_reverse_post_state n f
  | 0,     _ => rfl
  | 1,     _ => rfl
  | n + 2, f => by
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (n + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse (n + 1)) f)
        = gidney_propagation_reverse_post_state (n + 1)
            (gidney_last_bit_reverse_post_state (n + 1) f)
      rw [gidney_adder_bit_step_faithful_last_reverse_applyNat,
          gidney_adder_forward_with_propagation_reverse_applyNat (n + 1)]

/-- `Gate.applyNat` form of the full faithful no-measurement Gidney
adder for `n ≥ 2` (the only width at which the adder does non-trivial
work; `n = 0` and `n = 1` are `Gate.I`).  Composes the three Tick C
forward wrappers + the new reverse wrapper. -/
theorem gidney_adder_full_faithful_no_measurement_applyNat
    (n : Nat) (f : Nat → Bool) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement (n + 2)) f
      = gidney_full_reverse_post_state (n + 2)
          (gidney_final_cx_cascade_post_state (n + 2)
            (gidney_forward_faithful_full_post_state (n + 2) f)) := by
  show Gate.applyNat (gidney_adder_forward_faithful_full_reverse (n + 2))
        (Gate.applyNat (gidney_final_cx_cascade (n + 2))
          (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2)) f))
    = gidney_full_reverse_post_state (n + 2)
        (gidney_final_cx_cascade_post_state (n + 2)
          (gidney_forward_faithful_full_post_state (n + 2) f))
  rw [gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat,
      gidney_adder_forward_faithful_full_reverse_applyNat]

/-! ## `Gate.applyNat` lift of the Iter 191 arithmetic-correctness theorems

The headline arithmetic-correctness theorem `gidney_classical_action_with_reverse`
(Iter 207, 2026-05-13) is stated against the chained `post_state`
expression
`gidney_full_reverse_post_state n (gidney_final_cx_cascade_post_state n
  (gidney_forward_faithful_full_post_state n (adder_input_F n a b)))`.

The Tick E wrapper `gidney_adder_full_faithful_no_measurement_applyNat`
shows that this chained `post_state` equals `Gate.applyNat
(gidney_adder_full_faithful_no_measurement n) (adder_input_F n a b)`.
Combining the two gives `Gate.applyNat`-form correctness for the
**target** and **read** registers (both already proved by the Iter 191+
work in chained-post_state form).

The matching **carry** statement is FALSE in general — see
`gidney_adder_full_does_not_clear_carries_in_general` below.  This
is the structural defect that blocks Tick D's modular adder. -/

/-- **`Gate.applyNat`-form arithmetic correctness, target register.**
For `n ≥ 2`, the full faithful Gidney adder applied to the standard
2-operand input encoding writes the correct sum bits into the target
register.  Lift of `gidney_classical_action_with_reverse` (Iter 207)
through `gidney_adder_full_faithful_no_measurement_applyNat`. -/
theorem gidney_adder_full_faithful_no_measurement_target_correct
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    ∀ i, i < n →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (target_idx i)
      = adder_sum_bit_classical a b i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro i hi
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse (m + 2) a b hn ha hb i hi

/-- **`Gate.applyNat`-form read-register preservation, j = 0.** -/
theorem gidney_adder_full_faithful_no_measurement_read_correct_0
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx 0)
      = a.testBit 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse_read_0 (m + 2) a b hn ha hb

/-- **`Gate.applyNat`-form read-register preservation, j = 1.** -/
theorem gidney_adder_full_faithful_no_measurement_read_correct_1
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx 1)
      = a.testBit 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse_read_1 (m + 2) a b hn ha hb

/-- **`Gate.applyNat`-form read-register preservation, j ≥ 2.** -/
theorem gidney_adder_full_faithful_no_measurement_read_correct_geq_2
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)
    (j : Nat) (hj : 2 ≤ j) (hjn : j < n) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx j)
      = a.testBit j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [gidney_adder_full_faithful_no_measurement_applyNat m
        (adder_input_F (m + 2) a b)]
  exact gidney_classical_action_with_reverse_read_geq_2 (m + 2) a b hn ha hb
          j hj hjn

/-- **`Gate.applyNat`-form read-register preservation, all positions.**
Assembles the three cases above. -/
theorem gidney_adder_full_faithful_no_measurement_read_correct
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    ∀ i, i < n →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
        (adder_input_F n a b) (read_idx i)
      = a.testBit i := by
  intro i hi
  match i, hi with
  | 0, _ =>
      exact gidney_adder_full_faithful_no_measurement_read_correct_0 n a b hn ha hb
  | 1, _ =>
      exact gidney_adder_full_faithful_no_measurement_read_correct_1 n a b hn ha hb
  | j + 2, hi' =>
      exact gidney_adder_full_faithful_no_measurement_read_correct_geq_2 n a b
              hn ha hb (j + 2) (by omega) hi'

/-- **Formalized Tick D finding**: the full faithful no-measurement
Gidney adder does NOT clear the carry register in general.

Proof: machine-checked counterexample at `(n=2, a=1, b=1, i=0)`.  The
existing Iter 191 work proves target-bit correctness and read-register
preservation, but does NOT — and CANNOT, as this theorem shows —
also establish carry-zeroing.

This is the precise structural defect that blocks a verified
modular adder built on this circuit: modular reduction requires
clean ancillas to compare and conditionally subtract, but the
existing adder leaves carries dirty whenever the carry chain is
non-trivial. -/
theorem gidney_adder_full_does_not_clear_carries_in_general :
    ¬ (∀ n a b, 1 < n → a < 2^n → b < 2^n → ∀ i, i < n →
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement n)
          (adder_input_F n a b)) (carry_idx i) = false) := by
  intro h
  have h1 := h 2 1 1 (by decide) (by decide) (by decide) 0 (by decide)
  revert h1
  decide

/-- **Patched adder clears carries — n=2 exhaustive**.  Over all
`(a, b) ∈ [0, 4) × [0, 4)`, every carry position of the patched full
faithful no-measurement Gidney adder is `false`. -/
theorem patched_n2_clears_carries :
    ∀ a b, a < 4 → b < 4 → ∀ i, i < 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 2)
        (adder_input_F 2 a b) (carry_idx i) = false := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder target correctness — n=2 exhaustive**. -/
theorem patched_n2_target_correct :
    ∀ a b, a < 4 → b < 4 → ∀ i, i < 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 2)
          (adder_input_F 2 a b) (target_idx i)
        = adder_sum_bit_classical a b i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder read preservation — n=2 exhaustive**. -/
theorem patched_n2_read_preserved :
    ∀ a b, a < 4 → b < 4 → ∀ i, i < 2 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 2)
          (adder_input_F 2 a b) (read_idx i)
        = a.testBit i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder clears carries — n=3 exhaustive**.  192 cases. -/
theorem patched_n3_clears_carries :
    ∀ a b, a < 8 → b < 8 → ∀ i, i < 3 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 3)
        (adder_input_F 3 a b) (carry_idx i) = false := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder target correctness — n=3 exhaustive**.  192 cases. -/
theorem patched_n3_target_correct :
    ∀ a b, a < 8 → b < 8 → ∀ i, i < 3 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 3)
          (adder_input_F 3 a b) (target_idx i)
        = adder_sum_bit_classical a b i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-- **Patched adder read preservation — n=3 exhaustive**.  192 cases. -/
theorem patched_n3_read_preserved :
    ∀ a b, a < 8 → b < 8 → ∀ i, i < 3 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched 3)
          (adder_input_F 3 a b) (read_idx i)
        = a.testBit i := by
  intro a b ha hb i hi
  interval_cases a <;> interval_cases b <;> interval_cases i <;> decide

/-! ## Parametric per-step carry-clearance theorems

Symbolic (inductive/algebraic) proofs that each patched reverse step
clears its carry bit under the post-forward-final-CX invariant.  These
are the **arbitrary-`i` correctness lemmas** that the exhaustive
`decide` tests above are smoke checks for.  No `decide`,
`native_decide`, or `interval_cases` in the main proofs — only
unfolding + structural `simp` + a single 8-case Boolean truth-table
identity proved by `cases … <;> rfl`. -/

/-- **Boolean identity at the heart of the patch.**  Given the carry
recurrence `MAJ(A, B, C) = (A∧B) ⊕ (B∧C) ⊕ (A∧C)`, the patched
reverse step's effect on `c[i]` reduces to `MAJ ⊕ C ⊕ ((A⊕C) ∧ (A⊕B)) ⊕ (A⊕C)`,
which is identically `false` for all Booleans `A`, `B`, `C`.

The role of each term in the patched step:
* `MAJ(A, B, C)` — invariant value of `c[i]` (the post-forward carry).
* `C` — invariant value of `c[i-1]` (chained out by `CX(c[i-1], c[i])`).
* `(A⊕C) ∧ (A⊕B)` — `r[i] ∧ t[i]` after final-CX, written into c[i]
  by the reverse CCX.
* `A⊕C` — `r[i]` after final-CX, written into c[i] by the patch's CX.
-/
theorem patched_carry_bool_identity (A B C : Bool) :
    xor (xor (xor (xor (xor (A && B) (B && C)) (A && C)) C)
              ((xor A C) && (xor A B)))
        (xor A C)
      = false := by
  cases A <;> cases B <;> cases C <;> rfl

/-- **Patched last-reverse step clears `carry_idx i`** for `i ≥ 1`,
under the post-forward-final-CX invariant at position `i`. -/
theorem patched_last_reverse_clears_carry_under_invariant
    (i : Nat) (a b : Nat) (f : Nat → Bool)
    (h_c   : f (carry_idx i)       = Adder.carry false (i + 1) a.testBit b.testBit)
    (h_cm1 : f (carry_idx (i - 1)) = Adder.carry false i       a.testBit b.testBit)
    (h_r   : f (read_idx i)        = xor (a.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_t   : f (target_idx i)      = xor (a.testBit i) (b.testBit i)) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched i) f
        (carry_idx i) = false := by
  have h_ri_ci : read_idx i   ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti_ci : target_idx i ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  unfold gidney_adder_bit_step_faithful_last_reverse_patched
         gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_eq, update_neq _ _ _ _ h_ri_ci, update_neq _ _ _ _ h_ti_ci]
  rw [h_c, h_cm1, h_r, h_t]
  have h_carry_succ : Adder.carry false (i + 1) a.testBit b.testBit
      = xor (xor (a.testBit i && b.testBit i)
                 (b.testBit i && Adder.carry false i a.testBit b.testBit))
            (a.testBit i && Adder.carry false i a.testBit b.testBit) := by rfl
  rw [h_carry_succ]
  exact patched_carry_bool_identity
          (a.testBit i) (b.testBit i)
          (Adder.carry false i a.testBit b.testBit)

/-- **Patched last-reverse step preserves every position outside
`carry_idx i`** (frame condition). -/
theorem patched_last_reverse_preserves_non_carry
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched i) f k
      = f k := by
  unfold gidney_adder_bit_step_faithful_last_reverse_patched
         gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k]

/-- **Patched interior-reverse step clears `carry_idx i`** for `i ≥ 1`,
under the post-forward-final-CX invariant at position `i`. -/
theorem patched_interior_reverse_clears_carry_under_invariant
    (i : Nat) (a b : Nat) (f : Nat → Bool)
    (h_c   : f (carry_idx i)       = Adder.carry false (i + 1) a.testBit b.testBit)
    (h_cm1 : f (carry_idx (i - 1)) = Adder.carry false i       a.testBit b.testBit)
    (h_r   : f (read_idx i)        = xor (a.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_t   : f (target_idx i)      = xor (a.testBit i) (b.testBit i)) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched i) f
        (carry_idx i) = false := by
  have h_ri_ci   : read_idx i        ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti_ci   : target_idx i      ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  have h_ci_ti1  : carry_idx i       ≠ target_idx (i + 1) := by
    unfold carry_idx target_idx; omega
  have h_ci_ri1  : carry_idx i       ≠ read_idx (i + 1) := by
    unfold carry_idx read_idx; omega
  have h_ri_ti1  : read_idx i        ≠ target_idx (i + 1) := by
    unfold read_idx target_idx; omega
  have h_ri_ri1  : read_idx i        ≠ read_idx (i + 1) := by
    unfold read_idx; omega
  have h_ti_ti1  : target_idx i      ≠ target_idx (i + 1) := by
    unfold target_idx; omega
  have h_ti_ri1  : target_idx i      ≠ read_idx (i + 1) := by
    unfold target_idx read_idx; omega
  have h_cm1_ti1 : carry_idx (i - 1) ≠ target_idx (i + 1) := by
    unfold carry_idx target_idx; omega
  have h_cm1_ri1 : carry_idx (i - 1) ≠ read_idx (i + 1) := by
    unfold carry_idx read_idx; omega
  unfold gidney_adder_bit_step_faithful_interior_reverse_patched
         gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_eq,
             update_neq _ _ _ _ h_ri_ci, update_neq _ _ _ _ h_ti_ci,
             update_neq _ _ _ _ h_ci_ti1, update_neq _ _ _ _ h_ci_ri1,
             update_neq _ _ _ _ h_ri_ti1, update_neq _ _ _ _ h_ri_ri1,
             update_neq _ _ _ _ h_ti_ti1, update_neq _ _ _ _ h_ti_ri1,
             update_neq _ _ _ _ h_cm1_ti1, update_neq _ _ _ _ h_cm1_ri1]
  rw [h_c, h_cm1, h_r, h_t]
  have h_carry_succ : Adder.carry false (i + 1) a.testBit b.testBit
      = xor (xor (a.testBit i && b.testBit i)
                 (b.testBit i && Adder.carry false i a.testBit b.testBit))
            (a.testBit i && Adder.carry false i a.testBit b.testBit) := by rfl
  rw [h_carry_succ]
  exact patched_carry_bool_identity
          (a.testBit i) (b.testBit i)
          (Adder.carry false i a.testBit b.testBit)

/-- Frame helper: `gidney_first_bit_reverse_post_state` doesn't touch
`read_idx 0`. -/
theorem first_reverse_post_state_preserves_read_0 (f : Nat → Bool) :
    (gidney_first_bit_reverse_post_state f) (read_idx 0) = f (read_idx 0) := by
  unfold gidney_first_bit_reverse_post_state
  have h1 : read_idx 0 ≠ target_idx 1 := by decide
  have h2 : read_idx 0 ≠ read_idx 1   := by decide
  have h3 : read_idx 0 ≠ carry_idx 0  := by decide
  rw [update_neq _ _ _ _ h3, update_neq _ _ _ _ h2, update_neq _ _ _ _ h1]

/-- **Patched first-reverse step clears `carry_idx 0`** under the
post-forward-final-CX invariant at position 0.  The proof uses the
existing `gidney_first_bit_reverse_preserves` (Iter 194) which states
that the unpatched first-reverse step produces `post(c_0) = a.testBit 0`;
the patch's `CX(read_idx 0, carry_idx 0)` then XORs this with `f (read_idx 0)
= a.testBit 0`, yielding `false`. -/
theorem patched_first_reverse_clears_carry_under_invariant
    (a b : Nat) (f : Nat → Bool)
    (h_r0 : f (read_idx 0)   = a.testBit 0)
    (h_t0 : f (target_idx 0) = xor (a.testBit 0) (b.testBit 0))
    (h_c0 : f (carry_idx 0)  = Adder.carry false 1 a.testBit b.testBit)
    (h_r1 : f (read_idx 1)   = xor (a.testBit 1) (Adder.carry false 1 a.testBit b.testBit))
    (h_t1 : f (target_idx 1) = xor (a.testBit 1) (b.testBit 1)) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f
        (carry_idx 0) = false := by
  show Gate.applyNat (Gate.CX (read_idx 0) (carry_idx 0))
        (Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f)
        (carry_idx 0) = false
  simp only [Gate.applyNat_CX, update_eq]
  rw [gidney_adder_bit_step_faithful_first_reverse_applyNat]
  rw [first_reverse_post_state_preserves_read_0]
  obtain ⟨h_post_c0, _, _⟩ :=
    gidney_first_bit_reverse_preserves a b f h_r0 h_t0 h_c0 h_r1 h_t1
  rw [h_post_c0, h_r0]
  cases a.testBit 0 <;> rfl

/-! ## Frame lemmas for the patched interior and first reverse steps.

These name the **exact** set of positions touched by each patched
step (carry_idx i for last; {carry_idx i, read_idx (i+1), target_idx (i+1)}
for interior and first), enabling the cascade-level induction. -/

theorem patched_interior_reverse_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_k_c   : k ≠ carry_idx i)
    (h_k_ri1 : k ≠ read_idx (i + 1))
    (h_k_ti1 : k ≠ target_idx (i + 1)) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched i) f k = f k := by
  unfold gidney_adder_bit_step_faithful_interior_reverse_patched
         gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k_c, update_neq _ _ _ _ h_k_ri1,
             update_neq _ _ _ _ h_k_ti1]

theorem patched_first_reverse_preserves_outside
    (f : Nat → Bool) (k : Nat)
    (h_k_c0 : k ≠ carry_idx 0)
    (h_k_r1 : k ≠ read_idx 1)
    (h_k_t1 : k ≠ target_idx 1) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f k = f k := by
  unfold gidney_adder_bit_step_faithful_first_reverse_patched
         gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k_c0, update_neq _ _ _ _ h_k_r1,
             update_neq _ _ _ _ h_k_t1]

/-- Frame for the propagation cascade: `gidney_adder_forward_with_propagation_reverse_patched
(m+1)` preserves every `carry_idx j` for `j > m`. Proved by induction
on `m` using the per-step frame lemmas above. -/
theorem propagation_reverse_patched_preserves_carry_above (m : Nat) :
    ∀ (f : Nat → Bool) (j : Nat), j > m →
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) f
        (carry_idx j) = f (carry_idx j) := by
  induction m with
  | zero =>
      intro f j hj
      apply patched_first_reverse_preserves_outside
      · unfold carry_idx; omega
      · unfold carry_idx read_idx; omega
      · unfold carry_idx target_idx; omega
  | succ k ih =>
      intro f j hj
      show Gate.applyNat
            (gidney_adder_forward_with_propagation_reverse_patched (k + 1))
            (Gate.applyNat
              (gidney_adder_bit_step_faithful_interior_reverse_patched (k + 1)) f)
            (carry_idx j) = f (carry_idx j)
      rw [ih _ j (by omega)]
      apply patched_interior_reverse_preserves_outside
      · unfold carry_idx; omega
      · unfold carry_idx read_idx; omega
      · unfold carry_idx target_idx; omega

/-- Minimal-hypothesis version of the patched first-reverse step's
carry-clearance (drops the `h_r1`, `h_t1` hypotheses that the earlier
proof used via `gidney_first_bit_reverse_preserves`).  This is the
form needed by the cascade-level induction.  Proved directly by
structural unfolding + the boundary case `Adder.carry false 1 =
MAJ(a_0, b_0, false) = a_0 ∧ b_0`. -/
theorem patched_first_reverse_clears_carry_minimal
    (a b : Nat) (f : Nat → Bool)
    (h_r0 : f (read_idx 0)   = a.testBit 0)
    (h_t0 : f (target_idx 0) = xor (a.testBit 0) (b.testBit 0))
    (h_c0 : f (carry_idx 0)  = Adder.carry false 1 a.testBit b.testBit) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f
        (carry_idx 0) = false := by
  have h_r0_c0 : read_idx 0   ≠ carry_idx 0  := by decide
  have h_r0_t1 : read_idx 0   ≠ target_idx 1 := by decide
  have h_r0_r1 : read_idx 0   ≠ read_idx 1   := by decide
  have h_t0_t1 : target_idx 0 ≠ target_idx 1 := by decide
  have h_t0_r1 : target_idx 0 ≠ read_idx 1   := by decide
  have h_c0_t1 : carry_idx 0  ≠ target_idx 1 := by decide
  have h_c0_r1 : carry_idx 0  ≠ read_idx 1   := by decide
  unfold gidney_adder_bit_step_faithful_first_reverse_patched
         gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_eq, update_neq _ _ _ _ h_r0_c0, update_neq _ _ _ _ h_r0_t1,
             update_neq _ _ _ _ h_r0_r1, update_neq _ _ _ _ h_t0_t1,
             update_neq _ _ _ _ h_t0_r1, update_neq _ _ _ _ h_c0_t1,
             update_neq _ _ _ _ h_c0_r1]
  rw [h_c0, h_r0, h_t0]
  unfold Adder.carry
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl

/-! ## Arbitrary-`n` cascade carry-clearance theorems

Three induction-based theorems for the patched reverse cascade:
1. Propagation cascade (length `m+1`) clears `carry_idx i` for `i ≤ m`.
2. Full reverse cascade (length `n+2`) clears `carry_idx i` for `i ≤ n+1`.
3. Full faithful no-measurement patched adder clears all carries
   when applied to the standard `adder_input_F n a b` input.

All three are proved by structural induction on the recursion of the
gate definitions, using the per-step lemmas + frame conditions above.
No `decide` / `native_decide` / `interval_cases` in the main proof. -/

/-- **Arbitrary-`m` propagation-cascade carry-clearance.**  Under the
post-forward-final-CX invariant at positions `0..m`, the patched
propagation cascade `gidney_adder_forward_with_propagation_reverse_patched
(m+1)` makes every `carry_idx i` (for `i ≤ m`) `false`.

Proof: induction on `m`.  Base case is the first-reverse step (using
the minimal-hypothesis version).  Inductive step uses
`patched_interior_reverse_clears_carry_under_invariant` for the
high-bit case, `propagation_reverse_patched_preserves_carry_above`
to preserve the high carry across the rest of the cascade, and the
inductive hypothesis for lower bits — with `patched_interior_reverse_preserves_outside`
showing the invariant survives the interior step. -/
theorem patched_propagation_reverse_cascade_clears_carries
    (m a b : Nat) :
    ∀ (f : Nat → Bool),
      (∀ j, j ≤ m →
        f (carry_idx j)   = Adder.carry false (j + 1) a.testBit b.testBit
        ∧ f (read_idx j)  = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit)
        ∧ f (target_idx j) = xor (a.testBit j) (b.testBit j)) →
      ∀ i, i ≤ m →
        Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (m + 1)) f
          (carry_idx i) = false := by
  induction m with
  | zero =>
      intro f h_inv i hi
      have hi_eq : i = 0 := Nat.le_zero.mp hi
      rw [hi_eq]
      obtain ⟨h_c0, h_r0, h_t0⟩ := h_inv 0 (by omega)
      have h_carry0 : Adder.carry false 0 a.testBit b.testBit = false := rfl
      rw [h_carry0, Bool.xor_false] at h_r0
      exact patched_first_reverse_clears_carry_minimal a b f h_r0 h_t0 h_c0
  | succ k ih =>
      intro f h_inv i hi
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (k + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k + 1)) f)
            (carry_idx i) = false
      set f' := Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched (k + 1)) f
        with hf'_def
      obtain ⟨h_c_k1, h_r_k1, h_t_k1⟩ := h_inv (k + 1) (by omega)
      obtain ⟨h_c_k, _, _⟩ := h_inv k (by omega)
      have h_cm1_k1 : f (carry_idx ((k + 1) - 1)) = Adder.carry false (k + 1) a.testBit b.testBit := by
        have : (k + 1) - 1 = k := by omega
        rw [this]; exact h_c_k
      by_cases h_i_eq : i = k + 1
      · rw [h_i_eq, propagation_reverse_patched_preserves_carry_above k f' (k + 1) (by omega),
            hf'_def]
        exact patched_interior_reverse_clears_carry_under_invariant
                (k + 1) a b f h_c_k1 h_cm1_k1 h_r_k1 h_t_k1
      · have hi_le_k : i ≤ k := by omega
        apply ih f'
        · intro j hjk
          obtain ⟨h_cj, h_rj, h_tj⟩ := h_inv j (by omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [hf'_def, patched_interior_reverse_preserves_outside (k + 1) f (carry_idx j)
                  (by unfold carry_idx; omega)
                  (by unfold carry_idx read_idx; omega)
                  (by unfold carry_idx target_idx; omega)]
            exact h_cj
          · rw [hf'_def, patched_interior_reverse_preserves_outside (k + 1) f (read_idx j)
                  (by unfold read_idx carry_idx; omega)
                  (by unfold read_idx; omega)
                  (by unfold read_idx target_idx; omega)]
            exact h_rj
          · rw [hf'_def, patched_interior_reverse_preserves_outside (k + 1) f (target_idx j)
                  (by unfold target_idx carry_idx; omega)
                  (by unfold target_idx read_idx; omega)
                  (by unfold target_idx; omega)]
            exact h_tj
        · exact hi_le_k

/-- **Arbitrary-`n` full-reverse-cascade carry-clearance.**  Under the
post-forward-final-CX invariant at positions `0..n+1`, the patched
full reverse cascade `gidney_adder_forward_faithful_full_reverse_patched
(n+2)` makes every `carry_idx i` (for `i ≤ n+1`) `false`. -/
theorem patched_full_reverse_cascade_clears_carries
    (n a b : Nat) (f : Nat → Bool)
    (h_inv : ∀ j, j ≤ n + 1 →
      f (carry_idx j)   = Adder.carry false (j + 1) a.testBit b.testBit
      ∧ f (read_idx j)  = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit)
      ∧ f (target_idx j) = xor (a.testBit j) (b.testBit j)) :
    ∀ i, i ≤ n + 1 →
      Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2)) f
        (carry_idx i) = false := by
  intro i hi
  show Gate.applyNat (gidney_adder_forward_with_propagation_reverse_patched (n + 1))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) f)
        (carry_idx i) = false
  set f' := Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1)) f
    with hf'_def
  obtain ⟨h_c_k1, h_r_k1, h_t_k1⟩ := h_inv (n + 1) (by omega)
  obtain ⟨h_c_k, _, _⟩ := h_inv n (by omega)
  have h_cm1_k1 : f (carry_idx ((n + 1) - 1)) = Adder.carry false (n + 1) a.testBit b.testBit := by
    have : (n + 1) - 1 = n := by omega
    rw [this]; exact h_c_k
  by_cases h_i_eq : i = n + 1
  · rw [h_i_eq, propagation_reverse_patched_preserves_carry_above n f' (n + 1) (by omega),
        hf'_def]
    exact patched_last_reverse_clears_carry_under_invariant
            (n + 1) a b f h_c_k1 h_cm1_k1 h_r_k1 h_t_k1
  · have hi_le_n : i ≤ n := by omega
    apply patched_propagation_reverse_cascade_clears_carries n a b f'
    · intro j hjn
      obtain ⟨h_cj, h_rj, h_tj⟩ := h_inv j (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [hf'_def, patched_last_reverse_preserves_non_carry (n + 1) f (carry_idx j)
              (by unfold carry_idx; omega)]
        exact h_cj
      · rw [hf'_def, patched_last_reverse_preserves_non_carry (n + 1) f (read_idx j)
              (by unfold read_idx carry_idx; omega)]
        exact h_rj
      · rw [hf'_def, patched_last_reverse_preserves_non_carry (n + 1) f (target_idx j)
              (by unfold target_idx carry_idx; omega)]
        exact h_tj
    · exact hi_le_n

/-- **Arbitrary-`n` patched-adder carry-clearance on `adder_input_F`.**
The patched full faithful no-measurement Gidney adder, applied to the
standard two-operand input `adder_input_F (n+2) a b`, leaves every
carry position `carry_idx i` (for `i ≤ n+1`) cleared to `false`.

Proof: combine the Tick C wrappers (forward + final_cx applyNat
identities), the existing `Gidney.post_forward_final_cx_invariant_holds`
(Iter 188 + Iter 189), and the new
`patched_full_reverse_cascade_clears_carries` cascade theorem above. -/
theorem gidney_adder_full_faithful_no_measurement_patched_clears_carries
    (n a b : Nat) (ha : a < 2^(n + 2)) (hb : b < 2^(n + 2)) :
    ∀ i, i ≤ n + 1 →
      Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched (n + 2))
        (adder_input_F (n + 2) a b) (carry_idx i) = false := by
  intro i hi
  show Gate.applyNat (gidney_adder_forward_faithful_full_reverse_patched (n + 2))
        (Gate.applyNat (gidney_final_cx_cascade (n + 2))
          (Gate.applyNat (gidney_adder_forward_faithful_full (n + 2))
            (adder_input_F (n + 2) a b)))
        (carry_idx i) = false
  rw [gidney_adder_forward_faithful_full_applyNat,
      gidney_final_cx_cascade_applyNat]
  apply patched_full_reverse_cascade_clears_carries n a b _
  · intro j hj
    exact Gidney.post_forward_final_cx_invariant_holds (n + 2) a b
            (by omega) ha hb j (by omega)
  · exact hi

/-! ## Per-step "patched = unpatched at non-carry" frame lemmas

These show that each patched reverse step agrees with its unpatched
counterpart on every position OTHER than the patched carry. -/

theorem patched_first_reverse_eq_unpatched_at_non_c0
    (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx 0) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse_patched f k
      = Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f k := by
  show Gate.applyNat (Gate.CX (read_idx 0) (carry_idx 0))
        (Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f) k
    = Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f k
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_k]

theorem patched_interior_reverse_eq_unpatched_at_non_ci
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse_patched i) f k
      = Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f k := by
  show Gate.applyNat (Gate.CX (read_idx i) (carry_idx i))
        (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f) k
    = Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f k
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_k]

theorem patched_last_reverse_eq_unpatched_at_non_ci
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse_patched i) f k
      = Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f k := by
  show Gate.applyNat (Gate.CX (read_idx i) (carry_idx i))
        (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f) k
    = Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f k
  simp only [Gate.applyNat_CX]
  rw [update_neq _ _ _ _ h_k]

/-! ## Frame lemmas for the unpatched reverse cascade steps (mirror of the patched versions)

These are needed for the cascade-level "patched = unpatched at
non-carry" induction. -/

theorem unpatched_interior_reverse_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_k_c   : k ≠ carry_idx i)
    (h_k_ri1 : k ≠ read_idx (i + 1))
    (h_k_ti1 : k ≠ target_idx (i + 1)) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f k = f k := by
  unfold gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k_c, update_neq _ _ _ _ h_k_ri1,
             update_neq _ _ _ _ h_k_ti1]

theorem unpatched_first_reverse_preserves_outside
    (f : Nat → Bool) (k : Nat)
    (h_k_c0 : k ≠ carry_idx 0) (h_k_r1 : k ≠ read_idx 1) (h_k_t1 : k ≠ target_idx 1) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f k = f k := by
  unfold gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k_c0, update_neq _ _ _ _ h_k_r1,
             update_neq _ _ _ _ h_k_t1]

theorem unpatched_last_reverse_preserves_non_carry
    (i : Nat) (f : Nat → Bool) (k : Nat) (h_k : k ≠ carry_idx i) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f k = f k := by
  unfold gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX,
             update_neq _ _ _ _ h_k]

/-! ## Input-independence of the unpatched cascade at carries above its range.

This is the auxiliary frame lemma required to lift the per-step
"patched = unpatched at non-carry" identities to the cascade level.

Proof structure: each gate in the unpatched cascade reads/writes
only positions outside `{carry_idx j | j > m}`, so the gate's
applyNat **commutes** with `update _ (carry_idx j) v`.  By
composition (CX/CCX commute → seq commute → per-step commute →
cascade commute), the entire cascade commutes with the update.
Specializing at the position being queried (≠ `carry_idx (m+1)`)
gives the input independence statement. -/

/-- Two `update`s at different positions commute. -/
theorem update_update_comm (f : Nat → Bool) (a b : Nat) (u w : Bool) (h : a ≠ b) :
    update (update f a u) b w = update (update f b w) a u := by
  funext k
  by_cases h_ka : k = a
  · subst h_ka; rw [update_neq _ _ _ _ h, update_eq, update_eq]
  · by_cases h_kb : k = b
    · subst h_kb; rw [update_eq, update_neq _ _ _ _ (Ne.symm h), update_eq]
    · rw [update_neq _ _ _ _ h_kb, update_neq _ _ _ _ h_ka,
          update_neq _ _ _ _ h_ka, update_neq _ _ _ _ h_kb]

/-- `applyNat (CX c t)` commutes with `update _ p v` when `p` is
disjoint from both `c` and `t`. -/
theorem applyNat_CX_commute_update_disjoint
    (c t : Nat) (f : Nat → Bool) (p : Nat) (v : Bool)
    (h_p_c : p ≠ c) (h_p_t : p ≠ t) :
    Gate.applyNat (Gate.CX c t) (update f p v)
      = update (Gate.applyNat (Gate.CX c t) f) p v := by
  simp only [Gate.applyNat_CX, update_neq _ _ _ _ h_p_t.symm,
             update_neq _ _ _ _ h_p_c.symm]
  exact update_update_comm f p t v _ h_p_t

/-- `applyNat (CCX a b c)` commutes with `update _ p v` when `p` is
disjoint from `a`, `b`, and `c`. -/
theorem applyNat_CCX_commute_update_disjoint
    (a b c : Nat) (f : Nat → Bool) (p : Nat) (v : Bool)
    (h_p_a : p ≠ a) (h_p_b : p ≠ b) (h_p_c : p ≠ c) :
    Gate.applyNat (Gate.CCX a b c) (update f p v)
      = update (Gate.applyNat (Gate.CCX a b c) f) p v := by
  simp only [Gate.applyNat_CCX, update_neq _ _ _ _ h_p_a.symm,
             update_neq _ _ _ _ h_p_b.symm, update_neq _ _ _ _ h_p_c.symm]
  exact update_update_comm f p c v _ h_p_c

/-- Sequential composition of gates commutes with `update _ p v`
when each constituent gate does. -/
theorem applyNat_seq_commute_update
    (g₁ g₂ : Gate) (f : Nat → Bool) (p : Nat) (v : Bool)
    (h₁ : ∀ f', Gate.applyNat g₁ (update f' p v) = update (Gate.applyNat g₁ f') p v)
    (h₂ : ∀ f', Gate.applyNat g₂ (update f' p v) = update (Gate.applyNat g₂ f') p v) :
    Gate.applyNat (Gate.seq g₁ g₂) (update f p v)
      = update (Gate.applyNat (Gate.seq g₁ g₂) f) p v := by
  show Gate.applyNat g₂ (Gate.applyNat g₁ (update f p v))
    = update (Gate.applyNat g₂ (Gate.applyNat g₁ f)) p v
  rw [h₁ f, h₂ (Gate.applyNat g₁ f)]

/-- Unpatched first-reverse step commutes with update at `c[j]` (`j ≥ 1`). -/
theorem unpatched_first_reverse_commute_update_at_c_above
    (f : Nat → Bool) (j : Nat) (hj : j > 0) (v : Bool) :
    Gate.applyNat gidney_adder_bit_step_faithful_first_reverse (update f (carry_idx j) v)
      = update (Gate.applyNat gidney_adder_bit_step_faithful_first_reverse f) (carry_idx j) v := by
  have h_cj_c0 : carry_idx j ≠ carry_idx 0 := by unfold carry_idx; omega
  have h_cj_t1 : carry_idx j ≠ target_idx 1 := by unfold carry_idx target_idx; omega
  have h_cj_r1 : carry_idx j ≠ read_idx 1 := by unfold carry_idx read_idx; omega
  have h_cj_r0 : carry_idx j ≠ read_idx 0 := by unfold carry_idx read_idx; omega
  have h_cj_t0 : carry_idx j ≠ target_idx 0 := by unfold carry_idx target_idx; omega
  unfold gidney_adder_bit_step_faithful_first_reverse
  apply applyNat_seq_commute_update _ _ _ _ _ ?_
    (fun _ => applyNat_CCX_commute_update_disjoint _ _ _ _ _ _ h_cj_r0 h_cj_t0 h_cj_c0)
  intro f'
  apply applyNat_seq_commute_update _ _ _ _ _
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_c0 h_cj_t1)
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_c0 h_cj_r1)

/-- Unpatched interior-reverse step commutes with update at `c[j]` (`j > i`). -/
theorem unpatched_interior_reverse_commute_update_at_c_above
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) (j : Nat) (hj : j > i) (v : Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i)
      (update f (carry_idx j) v)
      = update (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse i) f)
          (carry_idx j) v := by
  have h_cj_ci : carry_idx j ≠ carry_idx i := by unfold carry_idx; omega
  have h_cj_ti1 : carry_idx j ≠ target_idx (i+1) := by unfold carry_idx target_idx; omega
  have h_cj_ri1 : carry_idx j ≠ read_idx (i+1) := by unfold carry_idx read_idx; omega
  have h_cj_cm1 : carry_idx j ≠ carry_idx (i-1) := by unfold carry_idx; omega
  have h_cj_ri : carry_idx j ≠ read_idx i := by unfold carry_idx read_idx; omega
  have h_cj_ti : carry_idx j ≠ target_idx i := by unfold carry_idx target_idx; omega
  unfold gidney_adder_bit_step_faithful_interior_reverse
  apply applyNat_seq_commute_update _ _ _ _ _ ?_
    (fun _ => applyNat_CCX_commute_update_disjoint _ _ _ _ _ _ h_cj_ri h_cj_ti h_cj_ci)
  intro f'
  apply applyNat_seq_commute_update _ _ _ _ _ ?_
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_cm1 h_cj_ci)
  intro f''
  apply applyNat_seq_commute_update _ _ _ _ _
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_ci h_cj_ti1)
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_ci h_cj_ri1)

/-- Unpatched last-reverse step commutes with update at `c[j]` (`j > i`). -/
theorem unpatched_last_reverse_commute_update_at_c_above
    (i : Nat) (hi : 0 < i) (f : Nat → Bool) (j : Nat) (hj : j > i) (v : Bool) :
    Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) (update f (carry_idx j) v)
      = update (Gate.applyNat (gidney_adder_bit_step_faithful_last_reverse i) f) (carry_idx j) v := by
  have h_cj_ci : carry_idx j ≠ carry_idx i := by unfold carry_idx; omega
  have h_cj_cm1 : carry_idx j ≠ carry_idx (i-1) := by unfold carry_idx; omega
  have h_cj_ri : carry_idx j ≠ read_idx i := by unfold carry_idx read_idx; omega
  have h_cj_ti : carry_idx j ≠ target_idx i := by unfold carry_idx target_idx; omega
  unfold gidney_adder_bit_step_faithful_last_reverse
  apply applyNat_seq_commute_update _ _ _ _ _
    (fun _ => applyNat_CX_commute_update_disjoint _ _ _ _ _ h_cj_cm1 h_cj_ci)
    (fun _ => applyNat_CCX_commute_update_disjoint _ _ _ _ _ _ h_cj_ri h_cj_ti h_cj_ci)

/-- Unpatched propagation cascade commutes with update at `c[j]` (`j > m`). -/
theorem unpatched_propagation_reverse_commute_update_at_c_above (m : Nat) :
    ∀ (g : Nat → Bool) (v : Bool) (j : Nat), j > m →
      Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1))
        (update g (carry_idx j) v)
        = update (Gate.applyNat (gidney_adder_forward_with_propagation_reverse (m + 1)) g)
            (carry_idx j) v := by
  induction m with
  | zero => intro g v j hj; exact unpatched_first_reverse_commute_update_at_c_above g j hj v
  | succ k' ih =>
      intro g v j hj
      show Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1))
              (update g (carry_idx j) v))
        = update (Gate.applyNat (gidney_adder_forward_with_propagation_reverse (k' + 1))
            (Gate.applyNat (gidney_adder_bit_step_faithful_interior_reverse (k' + 1)) g))
            (carry_idx j) v
      rw [unpatched_interior_reverse_commute_update_at_c_above (k' + 1) (by omega) g j (by omega) v]
      rw [ih _ v j (by omega)]

end FormalRV.BQAlgo
