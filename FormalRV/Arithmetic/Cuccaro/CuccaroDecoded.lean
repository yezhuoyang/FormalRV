/-
  FormalRV.BQAlgo.CuccaroDecoded — integer-level decoded specification
  of the exact-budget full Cuccaro adder.

  Tick 44 bridges the bit-level symbolic correctness of
  `cuccaro_n_bit_adder_full` (proved in `CuccaroFull.lean`) to the
  Nat-level statement
    `cuccaro_target_val bits q_start (output) = (a + b + c_in) % 2^bits`
  using the framework's existing `Adder.carry`/`Adder.sumfb` machinery
  (proved in `RippleCarryAdder.lean`).

  This is the natural next step toward closing the original SQIR
  placeholder axioms: the adder primitive now matches the integer
  arithmetic spec, exposing a clean composable interface.

  Structure of this file:
  - decoders: `cuccaro_target_val`, `cuccaro_read_val`.
  - decoder sanity lemmas on `cuccaro_input_F`.
  - `cuccaro_target_val_eq_sum_when_bits_match` (generic bit-stream→Nat).
  - `cuccaro_carry_eq_Adder_carry` (bridge to framework `Adder.carry`).
  - decoded correctness theorems for the full adder.
  - packaged primitive `cuccaro_n_bit_adder_full_primitive`.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.Arithmetic.RippleCarryAdder

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.Boolean

/-! ## Decoders.

The Cuccaro layout for `bits`-bit addition uses `2*bits + 1` qubits
starting at `q_start`:
- `q_start + 0`: carry-in.
- `q_start + 2i + 1` (0 ≤ i < bits): bit `i` of `b` (target register).
- `q_start + 2i + 2` (0 ≤ i < bits): bit `i` of `a` (read register). -/

/-- Decoder: value of the target/b register at width `bits`, LSB-first.
Bit at `q_start + 2i + 1` contributes weight `2^i`. -/
def cuccaro_target_val (bits q_start : Nat) (f : Nat → Bool) : Nat :=
  match bits with
  | 0     => 0
  | n + 1 => cuccaro_target_val n q_start f
              + (if f (q_start + 2 * n + 1) then 2^n else 0)

/-- Decoder: value of the read/a register at width `bits`, LSB-first.
Bit at `q_start + 2i + 2` contributes weight `2^i`. -/
def cuccaro_read_val (bits q_start : Nat) (f : Nat → Bool) : Nat :=
  match bits with
  | 0     => 0
  | n + 1 => cuccaro_read_val n q_start f
              + (if f (q_start + 2 * n + 2) then 2^n else 0)

/-! ### Decoder bounds. -/

theorem cuccaro_target_val_lt (bits q_start : Nat) (f : Nat → Bool) :
    cuccaro_target_val bits q_start f < 2^bits := by
  induction bits with
  | zero => simp [cuccaro_target_val]
  | succ k ih =>
      unfold cuccaro_target_val
      have ih' := ih
      rcases f (q_start + 2 * k + 1) <;> simp <;> (rw [pow_succ]; omega)

theorem cuccaro_read_val_lt (bits q_start : Nat) (f : Nat → Bool) :
    cuccaro_read_val bits q_start f < 2^bits := by
  induction bits with
  | zero => simp [cuccaro_read_val]
  | succ k ih =>
      unfold cuccaro_read_val
      have ih' := ih
      rcases f (q_start + 2 * k + 2) <;> simp <;> (rw [pow_succ]; omega)

/-! ## Generic decoder-from-bits theorem (target register). -/

/-- **Generic bit-stream-to-Nat lemma for the target decoder.**
If `f` matches `S.testBit i` at all target positions for `i < bits`,
then `cuccaro_target_val bits q_start f = S % 2^bits`.

Same shape as `gidney_target_val_eq_sum_when_bits_match` but for the
Cuccaro layout. -/
theorem cuccaro_target_val_eq_sum_when_bits_match
    (bits q_start S : Nat) (f : Nat → Bool)
    (h : ∀ i, i < bits → f (q_start + 2 * i + 1) = S.testBit i) :
    cuccaro_target_val bits q_start f = S % 2^bits := by
  induction bits with
  | zero => simp [cuccaro_target_val, Nat.mod_one]
  | succ k ih =>
      have h_k : f (q_start + 2 * k + 1) = S.testBit k := h k (by omega)
      have ih_inst : cuccaro_target_val k q_start f = S % 2^k := by
        apply ih
        intro i hi
        exact h i (by omega)
      unfold cuccaro_target_val
      rw [ih_inst, h_k, nat_mod_two_pow_succ_eq]

/-- **Generic bit-stream-to-Nat lemma for the read decoder.**  Same
shape as above. -/
theorem cuccaro_read_val_eq_sum_when_bits_match
    (bits q_start S : Nat) (f : Nat → Bool)
    (h : ∀ i, i < bits → f (q_start + 2 * i + 2) = S.testBit i) :
    cuccaro_read_val bits q_start f = S % 2^bits := by
  induction bits with
  | zero => simp [cuccaro_read_val, Nat.mod_one]
  | succ k ih =>
      have h_k : f (q_start + 2 * k + 2) = S.testBit k := h k (by omega)
      have ih_inst : cuccaro_read_val k q_start f = S % 2^k := by
        apply ih
        intro i hi
        exact h i (by omega)
      unfold cuccaro_read_val
      rw [ih_inst, h_k, nat_mod_two_pow_succ_eq]

/-! ## Decoder sanity on `cuccaro_input_F`. -/

/-- The input encoding decodes the target register to `b % 2^bits`. -/
theorem cuccaro_target_val_input
    (bits q_start a b : Nat) (c_in : Bool) (hb : b < 2^bits) :
    cuccaro_target_val bits q_start (cuccaro_input_F q_start c_in a b) = b := by
  have := cuccaro_target_val_eq_sum_when_bits_match bits q_start b
            (cuccaro_input_F q_start c_in a b)
            (fun i _ => cuccaro_input_F_at_b q_start i c_in a b)
  rw [this]
  exact Nat.mod_eq_of_lt hb

/-- The input encoding decodes the read register to `a % 2^bits`. -/
theorem cuccaro_read_val_input
    (bits q_start a b : Nat) (c_in : Bool) (ha : a < 2^bits) :
    cuccaro_read_val bits q_start (cuccaro_input_F q_start c_in a b) = a := by
  have := cuccaro_read_val_eq_sum_when_bits_match bits q_start a
            (cuccaro_input_F q_start c_in a b)
            (fun i _ => cuccaro_input_F_at_a q_start i c_in a b)
  rw [this]
  exact Nat.mod_eq_of_lt ha

/-! ## Bridge `cuccaro_carry` ↔ `Adder.carry`.

`cuccaro_carry` is defined via `Boolean.majority`; `Adder.carry` is
defined via XOR of pairwise ANDs. They coincide as Boolean functions
of the three inputs — the XOR-of-pairs form of majority. -/

/-- **Boolean majority = XOR-pairwise-AND.**  Local algebraic
identity used by the carry bridge. -/
theorem majority_eq_xor_pairs (a b c : Bool) :
    Boolean.majority a b c
      = xor (xor (a && b) (b && c)) (a && c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- **Carry-function bridge.**  The Cuccaro carry function on a
state `f` and origin `q_start` equals the framework `Adder.carry` on
the corresponding bit streams, with carry-in `f q_start`.

Bit stream conventions:
- f-stream of `Adder.carry`: `i ↦ f (q_start + 2i + 1)` (the b-bits).
- g-stream of `Adder.carry`: `i ↦ f (q_start + 2i + 2)` (the a-bits).

Note: `Adder.carry` is symmetric in its two streams
(`Adder.carry_sym`), so the order doesn't affect the carry. -/
theorem cuccaro_carry_eq_Adder_carry
    (f : Nat → Bool) (q_start k : Nat) :
    cuccaro_carry f q_start k
      = Adder.carry (f q_start) k
          (fun i => f (q_start + 2 * i + 1))
          (fun i => f (q_start + 2 * i + 2)) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    unfold cuccaro_carry
    rw [ih]
    rw [majority_eq_xor_pairs]
    -- Goal: xor (xor (carry && f_b_j) (f_b_j && f_a_j)) (carry && f_a_j)
    --     = Adder.carry (f q_start) (j+1) f-stream g-stream
    -- Adder.carry_succ unfolds to: xor (xor (f_b_j && f_a_j) (f_a_j && c)) (f_b_j && c)
    -- where c = Adder.carry _ j _ _.
    rw [Adder.carry_succ]
    -- Reassociate the XOR/AND terms.
    cases (Adder.carry (f q_start) j (fun i => f (q_start + 2 * i + 1))
                                    (fun i => f (q_start + 2 * i + 2)))
      <;> cases f (q_start + 2 * j + 1) <;> cases f (q_start + 2 * j + 2)
      <;> rfl

/-! ## Decoded correctness of the full Cuccaro adder. -/

/-- **HEADLINE — decoded target-register correctness for arbitrary
carry-in.**  After running the full Cuccaro adder on
`cuccaro_input_F q_start c_in a b`, the target register decodes to
`(a + b + c_in.toNat) % 2^bits`. -/
theorem cuccaro_n_bit_adder_full_target_decode_carry
    (bits q_start a b : Nat) (c_in : Bool) (ha : a < 2^bits) (hb : b < 2^bits) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start c_in a b))
      = (a + b + c_in.toNat) % 2^bits := by
  apply cuccaro_target_val_eq_sum_when_bits_match
        bits q_start (a + b + c_in.toNat) _
  intro i hi
  -- Sum-bit theorem gives the bit-level formula in terms of cuccaro_carry.
  rw [cuccaro_n_bit_adder_full_sum_bit bits q_start
        (cuccaro_input_F q_start c_in a b) i hi]
  -- Decoder sanity: cuccaro_input_F at positions q_start, q_start+2i+1, q_start+2i+2.
  rw [cuccaro_carry_eq_Adder_carry]
  rw [cuccaro_input_F_at_c_in q_start c_in a b]
  rw [cuccaro_input_F_at_b q_start i c_in a b]
  rw [cuccaro_input_F_at_a q_start i c_in a b]
  -- Bridge to the framework Adder.sumfb formula then to (a + b + c_in.toNat).testBit.
  have hstreams : ∀ k, (fun j => cuccaro_input_F q_start c_in a b
                                    (q_start + 2 * j + 1)) k = b.testBit k := by
    intro k
    exact cuccaro_input_F_at_b q_start k c_in a b
  have hstreams_a : ∀ k, (fun j => cuccaro_input_F q_start c_in a b
                                       (q_start + 2 * j + 2)) k = a.testBit k := by
    intro k
    exact cuccaro_input_F_at_a q_start k c_in a b
  -- Convert Adder.carry on cuccaro_input_F-streams to Adder.carry on testBit-streams.
  rw [show (fun j => cuccaro_input_F q_start c_in a b (q_start + 2 * j + 1))
        = (fun j => b.testBit j) from funext hstreams]
  rw [show (fun j => cuccaro_input_F q_start c_in a b (q_start + 2 * j + 2))
        = (fun j => a.testBit j) from funext hstreams_a]
  -- Now goal: xor (xor (Adder.carry c_in i b.testBit a.testBit) b.testBit i) a.testBit i
  --        = (a + b + c_in.toNat).testBit i.
  -- This is Adder.sumfb on the streams (b, a) with carry-in c_in.
  -- Adder.sumfb b₀ f g i = xor (xor (carry b₀ i f g) (f i)) (g i)
  -- We have: f = b.testBit, g = a.testBit.
  -- By Adder.sumfb_eq_testBit_add_gen with a := b, b := a (note arg swap!):
  --   Adder.sumfb b₀ b.testBit a.testBit i = (b + a + b₀.toNat).testBit i
  -- And (b + a + c_in.toNat) = (a + b + c_in.toNat).
  have h := Adder.sumfb_eq_testBit_add_gen c_in b a i
  unfold Adder.sumfb at h
  rw [show b + a + c_in.toNat = a + b + c_in.toNat from by ring] at h
  exact h

/-- **HEADLINE — decoded target-register correctness for carry-in
`false`.**  After running the full Cuccaro adder on
`cuccaro_input_F q_start false a b`, the target register decodes to
`(a + b) % 2^bits`. -/
theorem cuccaro_n_bit_adder_full_target_decode
    (bits q_start a b : Nat) (ha : a < 2^bits) (hb : b < 2^bits) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start false a b))
      = (a + b) % 2^bits := by
  have := cuccaro_n_bit_adder_full_target_decode_carry bits q_start a b false ha hb
  simpa [Bool.toNat] using this

/-- **Decoded read-register restoration.**  After running the full
Cuccaro adder, the read register still decodes to `a`. -/
theorem cuccaro_n_bit_adder_full_read_decode
    (bits q_start a b : Nat) (c_in : Bool) (ha : a < 2^bits) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start c_in a b))
      = a := by
  have h_eq : cuccaro_read_val bits q_start
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start c_in a b))
      = a % 2^bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match bits q_start a _
    intro i hi
    rw [cuccaro_n_bit_adder_full_a_restored bits q_start _ i hi]
    exact cuccaro_input_F_at_a q_start i c_in a b
  rw [h_eq, Nat.mod_eq_of_lt ha]

/-- **Decoded carry-in restoration.**  After running the full Cuccaro
adder on `cuccaro_input_F q_start c_in a b`, the carry-in qubit at
`q_start` still holds `c_in`. -/
theorem cuccaro_n_bit_adder_full_carry_in_decode
    (bits q_start a b : Nat) (c_in : Bool) :
    Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (cuccaro_input_F q_start c_in a b) q_start = c_in := by
  rw [cuccaro_n_bit_adder_full_carry_in_restored bits q_start
      (cuccaro_input_F q_start c_in a b)]
  exact cuccaro_input_F_at_c_in q_start c_in a b

/-! ## Packaged exact-budget Cuccaro adder primitive (Deliverable E).

Bundles WellTyped + target decode + read restored + carry-in restored
into a single theorem so downstream consumers (controlled add-constant,
modular reduction, modular multiplication) can rely on a single import.

Dimension statement: `q_start + (2*bits + 1)`, matching the form
`q_start + 2*n + 1` used by `cuccaro_n_bit_adder_full_wellTyped`. -/

/-- **HEADLINE — exact-budget Cuccaro adder primitive.**
For any `bits`, `q_start`, and `a, b < 2^bits`, the full Cuccaro adder:
- is WellTyped at dimension `q_start + (2*bits + 1)`;
- writes `(a + b) % 2^bits` into the target register;
- preserves the read register `a`;
- restores the carry-in qubit (when initialized to `false`). -/
theorem cuccaro_n_bit_adder_full_primitive
    (bits q_start a b : Nat) (ha : a < 2^bits) (hb : b < 2^bits) :
    Gate.WellTyped (q_start + (2 * bits + 1))
        (cuccaro_n_bit_adder_full bits q_start)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (cuccaro_input_F q_start false a b))
        = (a + b) % 2^bits
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (cuccaro_input_F q_start false a b))
        = a
    ∧ Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
          (cuccaro_input_F q_start false a b) q_start = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- WellTyped at dim = q_start + (2*bits + 1).
    apply cuccaro_n_bit_adder_full_wellTyped bits q_start
    omega
  · exact cuccaro_n_bit_adder_full_target_decode bits q_start a b ha hb
  · exact cuccaro_n_bit_adder_full_read_decode bits q_start a b false ha
  · exact cuccaro_n_bit_adder_full_carry_in_decode bits q_start a b false

end FormalRV.BQAlgo
