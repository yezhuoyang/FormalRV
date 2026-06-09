/-
  FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.PropagationInvariantBackbone
  BACKBONE (part 4/4): per-step frame conditions + first/interior/last
  preservation theorems, the k→k+1 cascade step `gidney_propagation_step_invariant_step`,
  and the headline parametric invariant `Gidney.propagation_step_invariant_holds`.
  Builds on `InputEval`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.InputEval

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ### Frame conditions for per-step actions (Iter 173)

    For cascade composition we need to know which positions each
    step-type modifies. Each step's post-state def is a chain of
    `update` calls; positions OUTSIDE the touched set retain the
    input value (via `update_neq`).

    These frame conditions are building blocks for the
    forward-cascade composition theorem (`TODO_gidney_forward_cascade_invariant`).
    Each is a small omega + `update_neq` proof. -/

/-- **First-bit step frame condition**: positions other than
    {carry_0, read_1, target_1} (= {2, 3, 4}) are unchanged. -/
theorem gidney_first_bit_post_state_preserves_outside
    (f : Nat → Bool) (k : Nat)
    (h_c0 : k ≠ carry_idx 0)
    (h_r1 : k ≠ read_idx 1)
    (h_t1 : k ≠ target_idx 1) :
    (gidney_first_bit_post_state f) k = f k := by
  unfold gidney_first_bit_post_state
  rw [update_neq _ _ _ _ h_t1, update_neq _ _ _ _ h_r1,
      update_neq _ _ _ _ h_c0]

/-- **Last-bit step frame condition**: positions other than
    {carry_i} are unchanged. (Last-bit only writes to carry_i.) -/
theorem gidney_last_bit_post_state_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_ci : k ≠ carry_idx i) :
    (gidney_last_bit_post_state i f) k = f k := by
  unfold gidney_last_bit_post_state
  rw [update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

/-- **Last-bit-step preservation theorem (PROVEN, Iter 171)**.
    Adapter from Iter 169's bit-extraction helper to the
    carry recurrence. Simpler than interior (no propagation).

    Given a state `f` satisfying the "step (i-1) END invariant"
    (i.e., position i-1 fully processed, position i clean):
    - `f(read_i) = a_i ⊕ c`, `f(target_i) = b_i ⊕ c`
    - `f(carry_{i-1}) = c` where `c = Adder.carry false i a.testBit b.testBit`
    - `f(carry_i) = false`

    Applying `gidney_last_bit_post_state i` yields:
    - `post(carry_i) = c_{i+1} = Adder.carry false (i+1) a.testBit b.testBit`

    No propagation to position (i+1) since this is the last bit.
    The carry-out identity `((a⊕c) ∧ (b⊕c)) ⊕ c = MAJ(a,b,c)` is
    the same as interior. -/
theorem gidney_last_bit_preserves (i a b : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_ri : f (read_idx i)
              = xor (a.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_ti : f (target_idx i)
              = xor (b.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_cim1 : f (carry_idx (i - 1))
                = Adder.carry false i a.testBit b.testBit)
    (h_ci : f (carry_idx i) = false) :
    (gidney_last_bit_post_state i f) (carry_idx i)
      = Adder.carry false (i + 1) a.testBit b.testBit := by
  rw [gidney_last_bit_post_state_in_bits i hi f h_ci, h_ri, h_ti, h_cim1,
      Adder.carry_succ]
  generalize Adder.carry false i a.testBit b.testBit = c
  cases a.testBit i <;> cases b.testBit i <;> cases c <;> rfl

/-- **Smoke-test**: `gidney_interior_bit_post_state 1` on the
    (3, 1) 3-bit input matches the existing decide-witnessed
    post-state. Validates the def's correctness on a concrete
    instance before attempting the parametric bit-extraction
    proof. -/
example :
    -- The interior step at i=1 transforms inputF_3_plus_1's post-first-bit state.
    -- inputF_3_plus_1 (a=3, b=1) → first-bit step → interior step at i=1.
    let post_first := gidney_first_bit_post_state inputF_3_plus_1
    let post_interior := gidney_interior_bit_post_state 1 post_first
    -- Expected at i=1: carry_1 = c_2 = MAJ(a_1, b_1, c_1) = MAJ(1, 0, 1) = 1.
    -- read_2 = a_2 ⊕ c_2 = 0 ⊕ 1 = 1.  But wait a_2 for a=3 is bit 2 = 0.
    -- target_2 = b_2 ⊕ c_2 = 0 ⊕ 1 = 1.
    post_interior (carry_idx 1) = true   -- c_2 = 1
    ∧ post_interior (read_idx 2) = true  -- a_2 ⊕ c_2 = 0 ⊕ 1 = 1
    ∧ post_interior (target_idx 2) = true -- b_2 ⊕ c_2 = 0 ⊕ 1 = 1
    := by decide

/-- **Bridge lemma** (Iter 172): the Iter 166-defined
    `gidney_interior_bit_post_state` is identical to the existing
    `gidney_bit_step_faithful_post_state` (line 570) used by the
    propagation cascade. Same 4-update body. Provable by `rfl`.

    Iter 166 inadvertently introduced this duplicate def. The
    bridge lets us apply Iter 170's `gidney_interior_bit_preserves`
    (which uses the Iter 166 name) to the cascade's interior steps
    (which use the existing name). -/
theorem gidney_interior_bit_post_state_eq
    (i : Nat) (f : Nat → Bool) :
    gidney_interior_bit_post_state i f
      = gidney_bit_step_faithful_post_state i f := rfl

/-- **Interior-bit step frame condition** (Iter 173): positions
    other than {carry_i, read_{i+1}, target_{i+1}} are unchanged
    by the interior-bit step at position `i`. -/
theorem gidney_interior_bit_post_state_preserves_outside
    (i : Nat) (f : Nat → Bool) (k : Nat)
    (h_ci : k ≠ carry_idx i)
    (h_ri1 : k ≠ read_idx (i + 1))
    (h_ti1 : k ≠ target_idx (i + 1)) :
    (gidney_interior_bit_post_state i f) k = f k := by
  unfold gidney_interior_bit_post_state
  rw [update_neq _ _ _ _ h_ti1, update_neq _ _ _ _ h_ri1,
      update_neq _ _ _ _ h_ci, update_neq _ _ _ _ h_ci]

/-- **Bit-extraction helper for interior step** (Iter 167, PROVEN).
    Analog of Iter 164's first-bit version. Proven via `omega`-
    derived index inequalities + `update_neq` chain. -/
theorem gidney_interior_bit_post_state_in_bits
    (i : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_cinit : f (carry_idx i) = false) :
    (gidney_interior_bit_post_state i f) (carry_idx i)
      = xor (f (read_idx i) && f (target_idx i)) (f (carry_idx (i - 1)))
    ∧ (gidney_interior_bit_post_state i f) (read_idx (i + 1))
        = xor (f (read_idx (i + 1)))
              ((gidney_interior_bit_post_state i f) (carry_idx i))
    ∧ (gidney_interior_bit_post_state i f) (target_idx (i + 1))
        = xor (f (target_idx (i + 1)))
              ((gidney_interior_bit_post_state i f) (carry_idx i)) := by
  -- Index inequalities (omega over read_idx i = 3i, target_idx i = 3i+1,
  -- carry_idx i = 3i+2, etc., with hi : 0 < i).
  have h_ri_ci : read_idx i ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti_ci : target_idx i ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  have h_cim1_ci : carry_idx (i - 1) ≠ carry_idx i := by
    unfold carry_idx; omega
  have h_ri1_ci : read_idx (i + 1) ≠ carry_idx i := by
    unfold read_idx carry_idx; omega
  have h_ti1_ci : target_idx (i + 1) ≠ carry_idx i := by
    unfold target_idx carry_idx; omega
  have h_ti1_ri1 : target_idx (i + 1) ≠ read_idx (i + 1) := by
    unfold target_idx read_idx; omega
  unfold gidney_interior_bit_post_state
  refine ⟨?_, ?_, ?_⟩
  · -- post(carry_i): chain through 4 updates, picking up gate-1+gate-2 writes.
    rw [update_neq _ _ _ _ h_ti1_ci.symm,   -- f₄: gate 4 update at target_{i+1}, not carry_i
        update_neq _ _ _ _ h_ri1_ci.symm,   -- f₃: gate 3 update at read_{i+1}, not carry_i
        update_eq,                             -- f₂: gate 2 update at carry_i (hit!)
        update_eq,                             -- f₁: gate 1 update at carry_i (hit!)
        update_neq _ _ _ _ h_cim1_ci,        -- f₁ query at carry_{i-1} not c_i (no .symm!)
        h_cinit]
    simp
  · -- post(read_{i+1}): gate 4 doesn't touch r_{i+1}; gate 3 writes there.
    rw [update_neq _ _ _ _ h_ti1_ri1.symm,  -- f₄: gate 4 at target_{i+1}, not r_{i+1}
        update_eq]                             -- f₃: gate 3 at r_{i+1} (hit!)
    -- f₂(r_{i+1}) = f(r_{i+1}) via update_neq through gates 1 + 2 (which update c_i).
    rw [update_neq _ _ _ _ h_ri1_ci, update_neq _ _ _ _ h_ri1_ci]
    -- Goal: xor (f r_{i+1}) (f₂ c_i) = xor (f r_{i+1}) (post c_i)
    -- where post c_i in the outer goal = f₄ c_i. Show they're equal via congr.
    congr 1
    rw [update_neq _ _ _ _ h_ti1_ci.symm, update_neq _ _ _ _ h_ri1_ci.symm]
  · -- post(target_{i+1}): gate 4 writes there.
    rw [update_eq]                             -- f₄: gate 4 at t_{i+1} (hit!)
    -- f₃(t_{i+1}) chain: f₂(t_{i+1}) ← f₁(t_{i+1}) ← f(t_{i+1}).
    rw [update_neq _ _ _ _ h_ti1_ri1,        -- f₃: gate 3 at r_{i+1} ≠ t_{i+1}
        update_neq _ _ _ _ h_ti1_ci,         -- f₂: gate 2 at c_i ≠ t_{i+1}
        update_neq _ _ _ _ h_ti1_ci]          -- f₁: gate 1 at c_i ≠ t_{i+1}
    -- f₃(c_i): gate 3 at r_{i+1} ≠ c_i, so f₃(c_i) = f₂(c_i).
    rw [update_neq _ _ _ _ h_ri1_ci.symm]
    -- Goal: xor (f t_{i+1}) (f₂ c_i) = xor (f t_{i+1}) (post c_i)
    congr 1
    rw [update_neq _ _ _ _ h_ti1_ci.symm, update_neq _ _ _ _ h_ri1_ci.symm]

/-- **Interior-bit-step preservation theorem (PROVEN, Iter 170)**.
    Adapter from Iter 167's bit-extraction helper to the
    classical-carry-recurrence form.

    Given a state `f` satisfying the "step (i-1) END invariant":
    - `f(read_i) = a_i ⊕ c`, `f(target_i) = b_i ⊕ c` (propagated by prev step)
    - `f(carry_{i-1}) = c` (carry from prev step)
    - `f(carry_i) = false` (carry register unmodified up to position i)
    - `f(read_{i+1}) = a_{i+1}`, `f(target_{i+1}) = b_{i+1}` (unchanged from input)

    Applying `gidney_interior_bit_post_state i` yields a state
    satisfying the "step i END invariant":
    - `post(carry_i) = c_{i+1} = Adder.carry false (i+1) a.testBit b.testBit`
    - `post(read_{i+1}) = a_{i+1} ⊕ c_{i+1}`
    - `post(target_{i+1}) = b_{i+1} ⊕ c_{i+1}`

    The carry-out identity: `((a_i ⊕ c) ∧ (b_i ⊕ c)) ⊕ c = MAJ(a_i, b_i, c)`. -/
theorem gidney_interior_bit_preserves (i a b : Nat) (hi : 0 < i) (f : Nat → Bool)
    (h_ri : f (read_idx i)
              = xor (a.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_ti : f (target_idx i)
              = xor (b.testBit i) (Adder.carry false i a.testBit b.testBit))
    (h_cim1 : f (carry_idx (i - 1))
                = Adder.carry false i a.testBit b.testBit)
    (h_ci : f (carry_idx i) = false)
    (h_ri1 : f (read_idx (i + 1)) = a.testBit (i + 1))
    (h_ti1 : f (target_idx (i + 1)) = b.testBit (i + 1)) :
    let post := gidney_interior_bit_post_state i f
    post (carry_idx i) = Adder.carry false (i + 1) a.testBit b.testBit
    ∧ post (read_idx (i + 1))
        = xor (a.testBit (i + 1)) (Adder.carry false (i + 1) a.testBit b.testBit)
    ∧ post (target_idx (i + 1))
        = xor (b.testBit (i + 1)) (Adder.carry false (i + 1) a.testBit b.testBit)
    := by
  -- Apply the in-bits helper (Iter 167).
  obtain ⟨hp_c, hp_r, hp_t⟩ :=
    gidney_interior_bit_post_state_in_bits i hi f h_ci
  -- Substitute the input hypotheses into hp_c.
  rw [h_ri, h_ti, h_cim1] at hp_c
  -- Now hp_c : post(c_i) = ((a_i ⊕ c) ∧ (b_i ⊕ c)) ⊕ c
  --   where c = Adder.carry false i a.testBit b.testBit
  -- We need: post(c_i) = Adder.carry false (i+1) a.testBit b.testBit
  --        = MAJ(a_i, b_i, c)
  -- Prove the carry equality first; read/target follow.
  have h_carry : (gidney_interior_bit_post_state i f) (carry_idx i)
                  = Adder.carry false (i + 1) a.testBit b.testBit := by
    rw [hp_c, Adder.carry_succ]
    -- LHS: ((a_i ⊕ c) ∧ (b_i ⊕ c)) ⊕ c
    -- RHS: (a_i ∧ b_i) ⊕ (b_i ∧ c) ⊕ (a_i ∧ c)   where c = Adder.carry false i ...
    -- Both are MAJ(a_i, b_i, c). Generalize c to a free Bool var, case-bash.
    generalize Adder.carry false i a.testBit b.testBit = c
    cases a.testBit i <;> cases b.testBit i <;> cases c <;> rfl
  refine ⟨h_carry, ?_, ?_⟩
  · -- post(read_{i+1}) = f(read_{i+1}) ⊕ post(carry_i) = a_{i+1} ⊕ c_{i+1}
    rw [hp_r, h_ri1, h_carry]
  · -- post(target_{i+1}) = f(target_{i+1}) ⊕ post(carry_i) = b_{i+1} ⊕ c_{i+1}
    rw [hp_t, h_ti1, h_carry]

/-- **Bit-extraction helper for first-bit step** (Iter 164):
    captures the classical action of `gidney_first_bit_post_state`
    on an arbitrary input function `f`, parameterized by the 5
    relevant bit values at positions 0, 1, 2, 3, 4.

    Per Iter 162 reflection pattern A (bit-extraction): take
    Bool values as inputs, NOT a free Nat. This avoids the
    "decide on free Nat vars" obstacle entirely — the proof is
    pure Bool case-analysis (16 sub-goals over the 4 free Bool
    vars).

    The relationship: `gidney_first_bit_post_state f` at
    positions 2 (carry_0), 3 (read_1), 4 (target_1):
    - post 2 = f 0 ∧ f 1                       (CCX write)
    - post 3 = f 3 ⊕ (f 0 ∧ f 1)               (CX propagation)
    - post 4 = f 4 ⊕ (f 0 ∧ f 1)               (CX propagation)

    Note `f 2` (= carry_0's initial value) is XOR'd into the
    CCX write, but for our adder input `f 2 = false`, so the
    XOR is trivial. We absorb this via `h2 : f 2 = false`. -/
theorem gidney_first_bit_post_state_in_bits
    (f : Nat → Bool) (h2 : f 2 = false) :
    (gidney_first_bit_post_state f) 2 = (f 0 && f 1)
    ∧ (gidney_first_bit_post_state f) 3 = xor (f 3) (f 0 && f 1)
    ∧ (gidney_first_bit_post_state f) 4 = xor (f 4) (f 0 && f 1) := by
  -- Unfold gidney_first_bit_post_state. It's 3 nested updates at positions
  -- 2 (carry_idx 0), 3 (read_idx 1), 4 (target_idx 1).
  -- Use the project's update_apply theorem (definitional unfolding).
  unfold gidney_first_bit_post_state
  simp only [carry_idx, read_idx, target_idx, update_apply,
             show (3 : Nat) * 0 = 0 from rfl,
             show (3 : Nat) * 1 = 3 from rfl,
             show (3 : Nat) * 0 + 1 = 1 from rfl,
             show (3 : Nat) * 0 + 2 = 2 from rfl,
             show (3 : Nat) * 1 + 1 = 4 from rfl,
             h2]
  refine ⟨?_, ?_, ?_⟩ <;>
    (cases f 0 <;> cases f 1 <;> cases f 3 <;> cases f 4 <;> decide)

/-- **First-bit-step preservation theorem (PROVEN, Iter 165)**:
    applying `gidney_first_bit_post_state` to the encoded input
    `adder_input_F n a b` (with `n ≥ 2`) produces a state where
    `carry_0 = c_1`, `read_1 = a_1 ⊕ c_1`, `target_1 = b_1 ⊕ c_1`,
    where `c_1 = Adder.carry false 1 (a.testBit) (b.testBit) =
    a_0 ∧ b_0`.

    **Proof** (post Iter 162 reflection's pattern A bit-extraction):
    glue `gidney_first_bit_post_state_in_bits` (Iter 164, pure
    Bool case-bash) with `adder_input_F_at_first_bit_positions`
    (Iter 165 preliminary, uses `hn : 1 < n` to evaluate the
    `decide` guards).

    Closes the original `TODO_gidney_first_bit_preserves` from
    Iter 160. -/
theorem gidney_first_bit_preserves (n a b : Nat)
    (hn : 1 < n) (_ha : a < 2^n) (_hb : b < 2^n) :
    let post := gidney_first_bit_post_state (adder_input_F n a b)
    post (carry_idx 0)
      = Adder.carry false 1 (a.testBit) (b.testBit)
    ∧ post (read_idx 1)
      = xor (a.testBit 1) (Adder.carry false 1 (a.testBit) (b.testBit))
    ∧ post (target_idx 1)
      = xor (b.testBit 1) (Adder.carry false 1 (a.testBit) (b.testBit)) := by
  -- Pull out the 5 input bit values via Iter 165 helper.
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    adder_input_F_at_first_bit_positions n a b hn
  -- Apply Iter 164 bit-extraction helper. Need h2 : f 2 = false.
  have hpost := gidney_first_bit_post_state_in_bits (adder_input_F n a b) h2
  -- hpost gives the post-state at positions 2, 3, 4 in terms of f 0, 1, 3, 4.
  -- Substitute f 0 = a.testBit 0, f 1 = b.testBit 0, f 3 = a.testBit 1, f 4 = b.testBit 1.
  rw [h0, h1, h3, h4] at hpost
  -- carry_idx 0 = 2, read_idx 1 = 3, target_idx 1 = 4. Unfold positions.
  show gidney_first_bit_post_state (adder_input_F n a b) 2 = _
    ∧ gidney_first_bit_post_state (adder_input_F n a b) 3 = _
    ∧ gidney_first_bit_post_state (adder_input_F n a b) 4 = _
  -- Adder.carry false 1 = a.testBit 0 && b.testBit 0 (unfold the recursion).
  -- hpost says post 2 = a.testBit 0 && b.testBit 0, post 3 = xor (a.testBit 1) (a.testBit 0 && b.testBit 0), etc.
  -- The RHS uses `Adder.carry false 1 a.testBit b.testBit` which unfolds to same expression.
  refine ⟨?_, ?_, ?_⟩
  · rw [hpost.1]
    -- Goal: a.testBit 0 && b.testBit 0 = Adder.carry false 1 a.testBit b.testBit
    unfold Adder.carry
    -- Adder.carry false 0 ... = false; then (a0 ∧ b0) ⊕ (b0 ∧ false) ⊕ (a0 ∧ false) = a0 ∧ b0
    cases a.testBit 0 <;> cases b.testBit 0 <;> rfl
  · rw [hpost.2.1]
    unfold Adder.carry
    cases a.testBit 0 <;> cases b.testBit 0 <;> cases a.testBit 1 <;> rfl
  · rw [hpost.2.2]
    unfold Adder.carry
    cases a.testBit 0 <;> cases b.testBit 0 <;> cases b.testBit 1 <;> rfl

/-- **Inductive step k=0 → k=1 of cascade induction** (Iter 177, PROVEN).
    Applying `gidney_first_bit_post_state` to `adder_input_F n a b`
    produces a state satisfying step-1 invariant. Uses
    `gidney_first_bit_preserves` (touched positions) + frame
    condition + adder_input_F evaluations (outside positions). -/
theorem Gidney.propagation_step_invariant_k1
    (n a b : Nat) (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.propagation_step_invariant 1 n a b
      (gidney_propagation_post_state 1 (adder_input_F n a b)) := by
  show Gidney.propagation_step_invariant 1 n a b
        (gidney_first_bit_post_state (adder_input_F n a b))
  obtain ⟨hp_c0, hp_r1, hp_t1⟩ :=
    gidney_first_bit_preserves n a b hn ha hb
  have h_r0_c0 : read_idx 0 ≠ carry_idx 0 := by unfold read_idx carry_idx; omega
  have h_r0_r1 : read_idx 0 ≠ read_idx 1 := by unfold read_idx; omega
  have h_r0_t1 : read_idx 0 ≠ target_idx 1 := by
    unfold read_idx target_idx; omega
  have h_t0_c0 : target_idx 0 ≠ carry_idx 0 := by
    unfold target_idx carry_idx; omega
  have h_t0_r1 : target_idx 0 ≠ read_idx 1 := by
    unfold target_idx read_idx; omega
  have h_t0_t1 : target_idx 0 ≠ target_idx 1 := by unfold target_idx; omega
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · by_cases hj_lt : j < 1
    · have hj0 : j = 0 := by omega
      subst hj0
      simp only [hj_lt]
      simpa using hp_c0
    · simp only [hj_lt, if_false]
      have h_cj_c0 : carry_idx j ≠ carry_idx 0 := by unfold carry_idx; omega
      have h_cj_r1 : carry_idx j ≠ read_idx 1 := by
        unfold carry_idx read_idx; omega
      have h_cj_t1 : carry_idx j ≠ target_idx 1 := by
        unfold carry_idx target_idx; omega
      rw [gidney_first_bit_post_state_preserves_outside _ _
            h_cj_c0 h_cj_r1 h_cj_t1]
      exact adder_input_F_at_carry_idx n a b j
  · by_cases hj_le1 : j ≤ 1
    · match j, hj_le1 with
      | 0, _ =>
        simp only [show (0 : Nat) ≤ 1 from by decide, if_true]
        rw [gidney_first_bit_post_state_preserves_outside _ _
              h_r0_c0 h_r0_r1 h_r0_t1]
        rw [adder_input_F_at_read_idx n a b 0 (by omega)]
        simp [Adder.carry]
      | 1, _ =>
        simp only [show (1 : Nat) ≤ 1 from by decide, if_true]
        simpa using hp_r1
    · simp only [hj_le1, if_false]
      have h_rj_c0 : read_idx j ≠ carry_idx 0 := by
        unfold read_idx carry_idx; omega
      have h_rj_r1 : read_idx j ≠ read_idx 1 := by unfold read_idx; omega
      have h_rj_t1 : read_idx j ≠ target_idx 1 := by
        unfold read_idx target_idx; omega
      rw [gidney_first_bit_post_state_preserves_outside _ _
            h_rj_c0 h_rj_r1 h_rj_t1]
      exact adder_input_F_at_read_idx n a b j hj
  · by_cases hj_le1 : j ≤ 1
    · match j, hj_le1 with
      | 0, _ =>
        simp only [show (0 : Nat) ≤ 1 from by decide, if_true]
        rw [gidney_first_bit_post_state_preserves_outside _ _
              h_t0_c0 h_t0_r1 h_t0_t1]
        rw [adder_input_F_at_target_idx n a b 0 (by omega)]
        simp [Adder.carry]
      | 1, _ =>
        simp only [show (1 : Nat) ≤ 1 from by decide, if_true]
        simpa using hp_t1
    · simp only [hj_le1, if_false]
      have h_tj_c0 : target_idx j ≠ carry_idx 0 := by
        unfold target_idx carry_idx; omega
      have h_tj_r1 : target_idx j ≠ read_idx 1 := by
        unfold target_idx read_idx; omega
      have h_tj_t1 : target_idx j ≠ target_idx 1 := by
        unfold target_idx; omega
      rw [gidney_first_bit_post_state_preserves_outside _ _
            h_tj_c0 h_tj_r1 h_tj_t1]
      exact adder_input_F_at_target_idx n a b j hj

/-- **Inductive step `k → k+1` of the forward propagation cascade.** For
    `k ≥ 1`, if the post-state after `k` steps satisfies the step-`k`
    propagation invariant, then applying the interior step at position `k`
    yields the step-`(k+1)` invariant. The workhorse of the cascade induction
    in `gidney_propagation_step_invariant_holds`. -/
theorem gidney_propagation_step_invariant_step
    (k n a b : Nat) (hk : 1 ≤ k) (hk_n : k + 1 < n)
    (hn : 1 < n) (ha : a < 2^n) (hb : b < 2^n)
    (h_prev : Gidney.propagation_step_invariant k n a b
                (gidney_propagation_post_state k (adder_input_F n a b))) :
    Gidney.propagation_step_invariant (k + 1) n a b
      (gidney_propagation_post_state (k + 1) (adder_input_F n a b)) := by
  -- Step 1: unfold the cascade at (k+1) using k ≥ 1 (i.e., k+1 = (k-1)+2).
  have h_rec : gidney_propagation_post_state (k + 1) (adder_input_F n a b)
             = gidney_interior_bit_post_state k
                (gidney_propagation_post_state k (adder_input_F n a b)) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [h_rec]
  set f_prev := gidney_propagation_post_state k (adder_input_F n a b) with hf_prev
  -- Step 2: extract f_prev's values at positions k-1, k, k+1 from h_prev.
  have hk_lt_n : k < n := by omega
  have hkm1_lt_n : k - 1 < n := by omega
  have hk1_lt_n : k + 1 < n := hk_n
  have h_ck_raw  := (h_prev k       hk_lt_n).1
  have h_rk_raw  := (h_prev k       hk_lt_n).2.1
  have h_tk_raw  := (h_prev k       hk_lt_n).2.2
  have h_ckm1_raw := (h_prev (k - 1) hkm1_lt_n).1
  have h_rk1_raw := (h_prev (k + 1) hk1_lt_n).2.1
  have h_tk1_raw := (h_prev (k + 1) hk1_lt_n).2.2
  have h_ri : f_prev (read_idx k)
              = xor (a.testBit k) (Adder.carry false k a.testBit b.testBit) := by
    rw [h_rk_raw]; simp
  have h_ti : f_prev (target_idx k)
              = xor (b.testBit k) (Adder.carry false k a.testBit b.testBit) := by
    rw [h_tk_raw]; simp
  have h_cim1 : f_prev (carry_idx (k - 1))
                = Adder.carry false k a.testBit b.testBit := by
    rw [h_ckm1_raw]
    have hkm1_lt_k : k - 1 < k := by omega
    have h_succ : k - 1 + 1 = k := by omega
    simp [hkm1_lt_k, h_succ]
  have h_ci : f_prev (carry_idx k) = false := by
    rw [h_ck_raw]; simp
  have h_ri1 : f_prev (read_idx (k + 1)) = a.testBit (k + 1) := by
    rw [h_rk1_raw]
    have hne : ¬ (k + 1 ≤ k) := by omega
    simp [hne]
  have h_ti1 : f_prev (target_idx (k + 1)) = b.testBit (k + 1) := by
    rw [h_tk1_raw]
    have hne : ¬ (k + 1 ≤ k) := by omega
    simp [hne]
  -- Step 3: apply Iter 170's gidney_interior_bit_preserves at i = k.
  obtain ⟨hp_c, hp_r, hp_t⟩ :=
    gidney_interior_bit_preserves k a b hk f_prev h_ri h_ti h_cim1 h_ci h_ri1 h_ti1
  -- Step 4: prove the step-(k+1) invariant.
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- carry_j conjunct: split on j = k (preserved cell) vs j ≠ k (frame).
    by_cases hjk : j = k
    · subst hjk
      have hjj1 : j < j + 1 := by omega
      simp only [hjj1, if_true]
      simpa using hp_c
    · have h_cj_ck  : carry_idx j ≠ carry_idx k        := by
        unfold carry_idx; omega
      have h_cj_rk1 : carry_idx j ≠ read_idx (k + 1)   := by
        unfold carry_idx read_idx; omega
      have h_cj_tk1 : carry_idx j ≠ target_idx (k + 1) := by
        unfold carry_idx target_idx; omega
      rw [gidney_interior_bit_post_state_preserves_outside _ _ _
            h_cj_ck h_cj_rk1 h_cj_tk1]
      rw [(h_prev j hj).1]
      by_cases hjk_lt : j < k
      · simp [hjk_lt, show j < k + 1 from by omega]
      · have hne : ¬ (j < k + 1) := by omega
        simp [hjk_lt, hne]
  · -- read_j conjunct: split on j = k+1 (preserved cell) vs j ≠ k+1 (frame).
    by_cases hjk1 : j = k + 1
    · subst hjk1
      rw [if_pos (le_refl (k + 1))]
      simpa using hp_r
    · have h_rj_ck  : read_idx j ≠ carry_idx k        := by
        unfold read_idx carry_idx; omega
      have h_rj_rk1 : read_idx j ≠ read_idx (k + 1)   := by
        unfold read_idx; omega
      have h_rj_tk1 : read_idx j ≠ target_idx (k + 1) := by
        unfold read_idx target_idx; omega
      rw [gidney_interior_bit_post_state_preserves_outside _ _ _
            h_rj_ck h_rj_rk1 h_rj_tk1]
      rw [(h_prev j hj).2.1]
      by_cases hjk_le : j ≤ k
      · simp [hjk_le, show j ≤ k + 1 from by omega]
      · have hne : ¬ (j ≤ k + 1) := by omega
        simp [hjk_le, hne]
  · -- target_j conjunct: same structure as read_j.
    by_cases hjk1 : j = k + 1
    · subst hjk1
      rw [if_pos (le_refl (k + 1))]
      simpa using hp_t
    · have h_tj_ck  : target_idx j ≠ carry_idx k        := by
        unfold target_idx carry_idx; omega
      have h_tj_rk1 : target_idx j ≠ read_idx (k + 1)   := by
        unfold target_idx read_idx; omega
      have h_tj_tk1 : target_idx j ≠ target_idx (k + 1) := by
        unfold target_idx; omega
      rw [gidney_interior_bit_post_state_preserves_outside _ _ _
            h_tj_ck h_tj_rk1 h_tj_tk1]
      rw [(h_prev j hj).2.2]
      by_cases hjk_le : j ≤ k
      · simp [hjk_le, show j ≤ k + 1 from by omega]
      · have hne : ¬ (j ≤ k + 1) := by omega
        simp [hjk_le, hne]

/-- **Parametric propagation invariant** (Iter 179, PROVEN — but
    depends on Iter 178's sorried step lemma). By induction on `k`:
    - Base case k=0: `propagation_step_invariant_base_k0`.
    - k=1: `propagation_step_invariant_k1`.
    - k ≥ 2: `gidney_propagation_step_invariant_step`.

    The result: for any k with `k + 1 ≤ n`,
    `gidney_propagation_post_state k (adder_input_F n a b)`
    satisfies the step-k invariant.

    With the structural recursion form, the induction goes
    via `Nat.rec`. -/
theorem Gidney.propagation_step_invariant_holds
    (k n a b : Nat) (hkn : k < n) (hn : 1 < n)
    (ha : a < 2^n) (hb : b < 2^n) :
    Gidney.propagation_step_invariant k n a b
      (gidney_propagation_post_state k (adder_input_F n a b)) := by
  induction k with
  | zero =>
      exact Gidney.propagation_step_invariant_base_k0 n a b ha hb
  | succ m ih =>
      -- ih : k = m gives the invariant at step m.
      have hmn : m < n := by omega
      have h_prev := ih hmn
      by_cases hm0 : m = 0
      · -- m = 0, so m + 1 = 1: use the Iter 177 k=1 lemma directly.
        subst hm0
        exact Gidney.propagation_step_invariant_k1 n a b hn ha hb
      · -- m ≥ 1: use the Iter 178 step lemma.
        have hm1 : 1 ≤ m := by omega
        have hm_plus_1_n : m + 1 < n := by omega
        exact gidney_propagation_step_invariant_step
                m n a b hm1 hm_plus_1_n hn ha hb h_prev

/-- **Generic ↔ concrete check #1**: `adder_input_F 2 1 0` matches
    `inputF_1_plus_0` at all 6 qubits of the 2-bit adder. -/
example :
    (∀ k, k < 6 →
       adder_input_F 2 1 0 k = inputF_1_plus_0 k) := by decide

/-- **Generic ↔ concrete check #2**: `adder_input_F 2 1 1` matches
    `inputF_1_plus_1` at all 6 qubits. -/
example :
    (∀ k, k < 6 →
       adder_input_F 2 1 1 k = inputF_1_plus_1 k) := by decide

/-- **Generic ↔ concrete check #3**: `adder_input_F 3 3 1` matches
    `inputF_3_plus_1` at all 9 qubits. -/
example :
    (∀ k, k < 9 →
       adder_input_F 3 3 1 k = inputF_3_plus_1 k) := by decide

/-- **Generic ↔ concrete check #4**: `adder_input_F 4 7 1` matches
    `inputF_7_plus_1` at all 12 qubits. -/
example :
    (∀ k, k < 12 →
       adder_input_F 4 7 1 k = inputF_7_plus_1 k) := by decide

/-- **Classical sum-bit concrete check**: bit 0 of (7+1)=8 is 0,
    bit 1 is 0, bit 2 is 0, bit 3 is 1 (binary "1000"). -/
example :
    adder_sum_bit_classical 7 1 0 = false
    ∧ adder_sum_bit_classical 7 1 1 = false
    ∧ adder_sum_bit_classical 7 1 2 = false
    ∧ adder_sum_bit_classical 7 1 3 = true := by decide

/-- **Decide-witness for `post_last_bit_invariant` on (n=2, a=1, b=1)**
    (Iter 187). Validates that after forward cascade only (no
    final-CX), `target_1 = b_1 ⊕ c_1 = 0 ⊕ 1 = 1` (still propagated,
    not yet canceled). This is the state BEFORE the final-CX layer. -/
example :
    Gidney.post_last_bit_invariant 2 1 1
      (gidney_forward_faithful_full_post_state 2 (adder_input_F 2 1 1)) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 2, h => omega

end FormalRV.BQAlgo
