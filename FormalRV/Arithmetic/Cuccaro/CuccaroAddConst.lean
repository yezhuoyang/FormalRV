/-
  FormalRV.BQAlgo.CuccaroAddConst — exact-budget Cuccaro add-constant
  primitive.

  Tick 45: build the add-constant primitive on top of the
  `cuccaro_n_bit_adder_full` machinery from Ticks 41-44.

  `cuccaro_addConstGate bits q_start c` implements
    `target ← (target + c) mod 2^bits`
  in place on the target/b register at positions `q_start + 2i + 1`,
  using a "prepare + adder + unprepare" pattern that re-encodes the
  constant `c` into the read/a register, runs the full Cuccaro adder,
  then unprepares the read register back to zero.

  Total qubit budget: `2*bits + 1` starting at `q_start` — matches
  SQIR's `modmult_rev_anc bits = 2*bits + 1` exactly.

  Structure:
  - `cuccaro_prepareConstRead`: XOR each read position with `c.testBit i`.
  - Per-position lemmas: action at read positions vs everywhere else.
  - `cuccaro_addConstGate`: composed gate.
  - Decoded correctness: target = `(x + c) % 2^bits`,
    read restored to 0, carry-in restored to false.
  - WellTyped + packaged primitive.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Definition: classical-constant preparation. -/

/-- **Constant-read preparation.**  For each bit `i < bits`, applies
`X` at the read-register position `q_start + 2*i + 2` iff `c.testBit i`.
The gate is self-inverse on the affected positions (since X² = I). -/
def cuccaro_prepareConstRead : Nat → Nat → Nat → Gate
  | 0,     _,       _ => Gate.I
  | n + 1, q_start, c =>
      seq (cuccaro_prepareConstRead n q_start c)
          (cond (c.testBit n) (Gate.X (q_start + 2 * n + 2)) Gate.I)

/-! ## Per-position semantics of `cuccaro_prepareConstRead`. -/

/-- **Frame: prepare doesn't touch positions outside the read range.**
If `q` is not equal to any read position `q_start + 2*i + 2` (i < bits),
the prepare gate leaves `f q` unchanged. -/
theorem cuccaro_prepareConstRead_at_other
    (bits q_start c q : Nat)
    (hq : ∀ i, i < bits → q ≠ q_start + 2 * i + 2)
    (f : Nat → Bool) :
    Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f q = f q := by
  induction bits generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_prepareConstRead k q_start c)
              (cond (c.testBit k) (Gate.X (q_start + 2 * k + 2)) Gate.I)) f q = _
    simp only [Gate.applyNat_seq]
    -- Push the outer (cond ... X I) through at_other (q ≠ q_start + 2*k + 2 by hq k).
    have h_outer : Gate.applyNat
            (cond (c.testBit k) (Gate.X (q_start + 2 * k + 2)) Gate.I)
            (Gate.applyNat (cuccaro_prepareConstRead k q_start c) f) q
          = Gate.applyNat (cuccaro_prepareConstRead k q_start c) f q := by
      cases h_c : c.testBit k with
      | false =>
          simp only [h_c, cond_false]
          rfl
      | true =>
          simp only [h_c, cond_true]
          show update _ (q_start + 2 * k + 2) _ q = _
          rw [update_neq _ _ _ _ (hq k (by omega))]
    rw [h_outer]
    apply ih
    intros i hi
    exact hq i (by omega)

/-- **Action at read positions.**  At read-position `q_start + 2*j + 2`
for `j < bits`, the prepare gate XOR's `c.testBit j` into the existing
value. -/
theorem cuccaro_prepareConstRead_at_read
    (bits q_start c j : Nat) (hj : j < bits) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f
        (q_start + 2 * j + 2)
      = xor (f (q_start + 2 * j + 2)) (c.testBit j) := by
  induction bits generalizing f with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_prepareConstRead k q_start c)
              (cond (c.testBit k) (Gate.X (q_start + 2 * k + 2)) Gate.I)) f
        (q_start + 2 * j + 2) = _
    simp only [Gate.applyNat_seq]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · -- j < k: outer step doesn't touch position q_start + 2*j + 2.
      have h_outer : ∀ g : Nat → Bool,
          Gate.applyNat (cond (c.testBit k) (Gate.X (q_start + 2 * k + 2)) Gate.I)
              g (q_start + 2 * j + 2) = g (q_start + 2 * j + 2) := by
        intro g
        cases h_c : c.testBit k with
        | false => simp [h_c]
        | true =>
            simp only [h_c, cond_true]
            show update g (q_start + 2 * k + 2) (!g (q_start + 2 * k + 2))
                (q_start + 2 * j + 2) = _
            rw [update_neq _ _ _ _ (by omega)]
      rw [h_outer]
      exact ih hjk f
    · -- j ≥ k. Since j < k+1, this means j = k.
      have hjk_eq : j = k := by omega
      -- Inner: prepare k doesn't touch q_start + 2*j + 2 (since i < k → i ≠ j).
      have h_inner : Gate.applyNat (cuccaro_prepareConstRead k q_start c) f
              (q_start + 2 * j + 2) = f (q_start + 2 * j + 2) := by
        apply cuccaro_prepareConstRead_at_other
        intros i hi h_eq
        omega
      -- Outer: conditional X. Case-split on c.testBit k.
      cases h_c : c.testBit k with
      | false =>
          simp only [h_c, cond_false]
          show Gate.applyNat (cuccaro_prepareConstRead k q_start c) f
                (q_start + 2 * j + 2) = _
          rw [h_inner]
          have h_cj : c.testBit j = false := by rw [hjk_eq]; exact h_c
          rw [h_cj]
          simp
      | true =>
          simp only [h_c, cond_true]
          show update (Gate.applyNat (cuccaro_prepareConstRead k q_start c) f)
                (q_start + 2 * k + 2)
                (!(Gate.applyNat (cuccaro_prepareConstRead k q_start c) f
                    (q_start + 2 * k + 2)))
                (q_start + 2 * j + 2) = _
          have hpos : q_start + 2 * k + 2 = q_start + 2 * j + 2 := by omega
          rw [hpos, update_eq, h_inner]
          have h_cj : c.testBit j = true := by rw [hjk_eq]; exact h_c
          rw [h_cj]
          cases f (q_start + 2 * j + 2) <;> rfl

/-! ## WellTyped for preparation. -/

/-- **WellTyped: prepare fits in `q_start + 2*bits + 1` qubits.** -/
theorem cuccaro_prepareConstRead_wellTyped
    (bits q_start c dim : Nat) (h : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_prepareConstRead bits q_start c) := by
  induction bits with
  | zero =>
    show Gate.WellTyped dim Gate.I
    show 0 < dim
    omega
  | succ k ih =>
    show Gate.WellTyped dim
        (seq (cuccaro_prepareConstRead k q_start c)
              (cond (c.testBit k) (Gate.X (q_start + 2 * k + 2)) Gate.I))
    refine ⟨?_, ?_⟩
    · exact ih (by omega)
    · cases h_c : c.testBit k with
      | false =>
          simp only [h_c, cond_false]
          show 0 < dim
          omega
      | true =>
          simp only [h_c, cond_true]
          show q_start + 2 * k + 2 < dim
          omega

/-! ## Composed add-constant gate. -/

/-- **Exact-budget Cuccaro add-constant gate.**  Implements
`target ← (target + c) mod 2^bits` in place via prepare-adder-unprepare.
Total qubit budget: `2*bits + 1` starting at `q_start`. -/
def cuccaro_addConstGate (bits q_start c : Nat) : Gate :=
  seq (cuccaro_prepareConstRead bits q_start c)
      (seq (cuccaro_n_bit_adder_full bits q_start)
           (cuccaro_prepareConstRead bits q_start c))

/-! ## Decoded correctness — preliminary bit-level invariants of the
composed gate. -/

/-- **Target bit at position `q_start + 2*i + 1` for `i < bits` after
the addConstGate**: equals `(x + c).testBit i`.

Proved by tracing the three-stage composition:
- After prepare₁ on input `cuccaro_input_F q_start false 0 x`:
  carry-in = false, b-bits = x.testBit, a-bits = c.testBit (XOR'd in).
- After full adder: sum bit = `(x + c).testBit i` via the sum-bit
  theorem and `Adder.sumfb_eq_testBit_add_gen`.
- After prepare₂: target b-bit position unchanged (prepare touches
  only a-positions). -/
theorem cuccaro_addConstGate_target_bit
    (bits q_start c x i : Nat) (hi : i < bits)
    (hc : c < 2^bits) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 1)
      = (x + c).testBit i := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start c)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (cuccaro_prepareConstRead bits q_start c)))
      (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 1) = _
  simp only [Gate.applyNat_seq]
  -- prepare₂ doesn't touch target position (which is q_start + 2*i + 1, odd offset).
  rw [cuccaro_prepareConstRead_at_other bits q_start c (q_start + 2 * i + 1)
      (by intros j _ h; omega)]
  -- Now apply sum-bit theorem to (cuccaro_n_bit_adder_full applied to prepared_input).
  rw [cuccaro_n_bit_adder_full_sum_bit bits q_start
      (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) i hi]
  -- Reduce post-prepare values at q_start (carry-in), q_start+2*i+1 (b), q_start+2*i+2 (a).
  -- carry-in: prepare doesn't touch (q_start ≠ q_start + 2*j + 2 for any j).
  -- b-bit at q_start+2*i+1: prepare doesn't touch.
  -- a-bit at q_start+2*i+2: XOR'd with c.testBit i.
  rw [cuccaro_carry_eq_Adder_carry]
  have h_carry_in : (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) q_start = false := by
    rw [cuccaro_prepareConstRead_at_other bits q_start c q_start
        (by intros j _ h; omega)]
    exact cuccaro_input_F_at_c_in q_start false 0 x
  rw [h_carry_in]
  have h_b : ∀ k, (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * k + 1) = x.testBit k := by
    intro k
    rw [cuccaro_prepareConstRead_at_other bits q_start c _
        (by intros j _ h; omega)]
    exact cuccaro_input_F_at_b q_start k false 0 x
  have h_a : ∀ k, k < bits →
      (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * k + 2) = c.testBit k := by
    intro k hk
    rw [cuccaro_prepareConstRead_at_read bits q_start c k hk]
    rw [cuccaro_input_F_at_a q_start k false 0 x]
    -- 0.testBit k = false, xor false (c.testBit k) = c.testBit k.
    simp [Nat.zero_testBit]
  have h_a_full : ∀ k, (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * k + 2) = c.testBit k := by
    intro k
    by_cases hk : k < bits
    · exact h_a k hk
    · -- k ≥ bits: prepare doesn't touch (q_start + 2*k + 2 ≠ q_start + 2*j + 2 for j < bits),
      --           and input has a.testBit k = 0.testBit k = false.
      -- For c < 2^bits, c.testBit k = false for k ≥ bits.
      push_neg at hk
      rw [cuccaro_prepareConstRead_at_other bits q_start c _
          (by intros j hj h; omega)]
      rw [cuccaro_input_F_at_a q_start k false 0 x]
      simp [Nat.zero_testBit]
      -- Need: c.testBit k = false for k ≥ bits with c < 2^bits.
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hk))
  -- Build the funext: ((fun i => post-prep at q_start+2*i+1) = x.testBit), same for a.
  rw [show (fun j => (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * j + 1))
        = (fun j => x.testBit j) from funext h_b]
  rw [show (fun j => (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) (q_start + 2 * j + 2))
        = (fun j => c.testBit j) from funext h_a_full]
  rw [h_b i, h_a_full i]
  -- Goal: xor (xor (Adder.carry false i x.testBit c.testBit) (x.testBit i)) (c.testBit i)
  --     = (x + c).testBit i.
  have hsumfb := Adder.sumfb_eq_testBit_add_gen false x c i
  unfold Adder.sumfb at hsumfb
  simpa [Bool.toNat] using hsumfb

/-- **Read bit at position `q_start + 2*i + 2` for `i < bits` after the
addConstGate**: equals `false` (restored to zero).

Trace:
- After prepare₁: a-bit at q_start+2*i+2 = false ⊕ c.testBit i = c.testBit i.
- After full adder: a preserved (= c.testBit i) by `_a_restored`.
- After prepare₂: c.testBit i ⊕ c.testBit i = false. -/
theorem cuccaro_addConstGate_read_bit
    (bits q_start c x i : Nat) (hi : i < bits) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2)
      = false := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start c)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (cuccaro_prepareConstRead bits q_start c)))
      (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2) = _
  simp only [Gate.applyNat_seq]
  -- prepare₂ at q_start+2*i+2: XOR with c.testBit i.
  rw [cuccaro_prepareConstRead_at_read bits q_start c i hi]
  -- Full adder preserves the a-bit position.
  rw [cuccaro_n_bit_adder_full_a_restored bits q_start
      (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x)) i hi]
  -- prepare₁ at q_start+2*i+2: XOR with c.testBit i; input has a=0.
  rw [cuccaro_prepareConstRead_at_read bits q_start c i hi]
  rw [cuccaro_input_F_at_a q_start i false 0 x]
  simp [Nat.zero_testBit]

/-- **Carry-in at position `q_start` after the addConstGate**: equals
`false` (restored). -/
theorem cuccaro_addConstGate_carry_in_bit
    (bits q_start c x : Nat) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c)
        (cuccaro_input_F q_start false 0 x) q_start = false := by
  show Gate.applyNat
      (seq (cuccaro_prepareConstRead bits q_start c)
            (seq (cuccaro_n_bit_adder_full bits q_start)
                 (cuccaro_prepareConstRead bits q_start c)))
      (cuccaro_input_F q_start false 0 x) q_start = _
  simp only [Gate.applyNat_seq]
  rw [cuccaro_prepareConstRead_at_other bits q_start c q_start
      (by intros j _ h; omega)]
  rw [cuccaro_n_bit_adder_full_carry_in_restored bits q_start
      (Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
        (cuccaro_input_F q_start false 0 x))]
  rw [cuccaro_prepareConstRead_at_other bits q_start c q_start
      (by intros j _ h; omega)]
  exact cuccaro_input_F_at_c_in q_start false 0 x

/-! ## Decoded correctness for the addConstGate. -/

/-- **HEADLINE — decoded target correctness.**  After running
`cuccaro_addConstGate bits q_start c` on
`cuccaro_input_F q_start false 0 x`, the target register decodes to
`(x + c) % 2^bits`. -/
theorem cuccaro_addConstGate_target_decode
    (bits q_start c x : Nat) (hc : c < 2^bits) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x))
      = (x + c) % 2^bits := by
  apply cuccaro_target_val_eq_sum_when_bits_match bits q_start (x + c) _
  intro i hi
  exact cuccaro_addConstGate_target_bit bits q_start c x i hi hc

/-- **Decoded read restoration.**  After running the addConstGate, the
read register decodes to `0`. -/
theorem cuccaro_addConstGate_read_decode
    (bits q_start c x : Nat) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x))
      = 0 := by
  have h_eq : cuccaro_read_val bits q_start
        (Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x))
      = 0 % 2^bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match bits q_start 0 _
    intro i hi
    rw [cuccaro_addConstGate_read_bit bits q_start c x i hi]
    simp [Nat.zero_testBit]
  rw [h_eq]
  simp

/-! ## WellTyped + packaged primitive. -/

/-- **WellTyped: addConstGate fits in `q_start + 2*bits + 1` qubits.** -/
theorem cuccaro_addConstGate_wellTyped
    (bits q_start c dim : Nat) (h : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_addConstGate bits q_start c) := by
  refine ⟨?_, ?_, ?_⟩
  · exact cuccaro_prepareConstRead_wellTyped bits q_start c dim h
  · exact cuccaro_n_bit_adder_full_wellTyped bits q_start dim h
  · exact cuccaro_prepareConstRead_wellTyped bits q_start c dim h

/-- **HEADLINE — packaged Cuccaro add-constant primitive.**
For any `bits`, `q_start`, `c < 2^bits`, and `x`, the addConstGate:
- is WellTyped at dimension `q_start + (2*bits + 1)`;
- writes `(x + c) % 2^bits` into the target register;
- restores the read register to 0;
- restores the carry-in qubit to false. -/
theorem cuccaro_addConstGate_clean
    (bits q_start c x : Nat) (hc : c < 2^bits) :
    Gate.WellTyped (q_start + (2 * bits + 1))
        (cuccaro_addConstGate bits q_start c)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat (cuccaro_addConstGate bits q_start c)
            (cuccaro_input_F q_start false 0 x))
        = (x + c) % 2^bits
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat (cuccaro_addConstGate bits q_start c)
            (cuccaro_input_F q_start false 0 x))
        = 0
    ∧ Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x) q_start = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply cuccaro_addConstGate_wellTyped bits q_start c
    omega
  · exact cuccaro_addConstGate_target_decode bits q_start c x hc
  · exact cuccaro_addConstGate_read_decode bits q_start c x
  · exact cuccaro_addConstGate_carry_in_bit bits q_start c x

end FormalRV.BQAlgo
