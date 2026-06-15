/-
  FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.PatchedCarryLemmas
  Part 3/4: parametric per-step patched carry-clearance lemmas (boolean
  identity, last/interior/first reverse clears carry under invariant) and the
  frame lemmas for the patched interior/first reverse steps.
  Builds on `ApplyNatBridge`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.PropagationReverse.ApplyNatBridge

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

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

end FormalRV.BQAlgo
