/-
  FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.SumfbTestBit
  Part 2/4: the classical-arithmetic bridge `Adder.sumfb b f g i = (a+b).testBit i`
  (testBit_add_zero, carry_shift_one, the carry-in-parametric gen lemma, and the
  headline `Adder.sumfb_eq_testBit_add`). Builds on `UnfoldAndCarry`.
-/
import FormalRV.Arithmetic.RippleCarryAdder.ClassicalBridge.UnfoldAndCarry

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode

/-! ### Classical-correctness bridge: `sumfb` ↔ `Nat.testBit` (Iter 158)

    SQIR's
    [`sumfb_correct_carry0`](../../../SQIR/examples/shor/ModMult.v:769)
    is the load-bearing classical lemma:

    ```
    Lemma sumfb_correct_carry0 :
      forall x y, sumfb false (nat2fb x) (nat2fb y) = nat2fb (x + y).
    ```

    It says: the bit-level sum (`Adder.sumfb`) on the bit-streams
    of two Nats equals the bit-stream of their integer sum.
    Combined with "quantum cascade preserves the bit-level invariant"
    (to be proven in later ticks), this gives the headline
    semantic correctness theorem.

    This tick STATES the lemma + decide-witnesses on small (a, b, i).
    The full proof needs an inductive argument coupling
    `Nat.testBit (a+b) i` to the recursive carry computation —
    Mathlib doesn't expose a direct `testBit_add` lemma, so the
    proof is non-trivial.

    Named-sorried as `TODO_sumfb_eq_testBit_add`. Future ticks
    close it via induction on `i` with `Nat.shiftRight_succ` +
    case analysis on the bottom bits of `a` and `b`. -/

/-- **Base case of the classical-correctness bridge** (Iter 163,
    new):  `(a + b).testBit 0 = a.testBit 0 ⊕ b.testBit 0`.

    This is the i=0 specialization of
    `Adder.sumfb_eq_testBit_add`. The proof goes via Nat's
    mod-2 arithmetic: `Nat.testBit n 0 ↔ n % 2 = 1`, and
    `(a + b) % 2 = (a % 2 + b % 2) % 2` (which equals
    `a % 2 ⊕ b % 2` for Bool-valued mods).

    This closes the base case of the planned induction on i for
    `TODO_sumfb_eq_testBit_add`. -/
theorem Adder.testBit_add_zero (a b : Nat) :
    (a + b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := by
  -- Nat.testBit_zero : n.testBit 0 = decide (n % 2 = 1) — or
  -- the equivalent boolean form. Let's use simp + omega via
  -- mod-2 case analysis.
  simp only [Nat.testBit_zero]
  -- Goal: ((a + b) % 2 == 1) = ((a % 2 == 1) ⊕ (b % 2 == 1))
  -- (or similar form). Case-split on (a % 2) and (b % 2).
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp_all <;> omega

/-- **Carry-shift auxiliary lemma** (Iter 199, 2026-05-13). Relates
    `Adder.carry b₀ (k+1)` on (a, b) to `Adder.carry initial k` on
    (a/2, b/2), where `initial = Adder.carry b₀ 1 a b = MAJ(a_0, b_0, b₀)`.

    Proof by induction on k: the carry recurrence `carry _ (k+1) = MAJ(...)`
    + `Nat.testBit_add_one` gives `(a/2).testBit m = a.testBit (m+1)`. -/
lemma Adder.carry_shift_one (b₀ : Bool) (a b k : Nat) :
    Adder.carry b₀ (k + 1) (fun i => a.testBit i) (fun i => b.testBit i)
    = Adder.carry (Adder.carry b₀ 1 (fun i => a.testBit i) (fun i => b.testBit i))
        k (fun i => (a / 2).testBit i) (fun i => (b / 2).testBit i) := by
  induction k with
  | zero => rfl
  | succ m ih =>
      -- LHS: carry b₀ (m+2) ab = MAJ(a_{m+1}, b_{m+1}, carry b₀ (m+1) ab)
      -- RHS (m+1): carry init (m+1) (a/2)bit (b/2)bit
      --         = MAJ((a/2)_m, (b/2)_m, carry init m ...)
      -- After unfolding both sides: substitute IH and testBit_add_one.
      rw [show m + 1 + 1 = m + 2 from rfl, Adder.carry_succ b₀ (m + 1),
          show (Adder.carry _ (m + 1) (fun i => (a / 2).testBit i)
                  (fun i => (b / 2).testBit i))
              = _ from Adder.carry_succ _ m _ _,
          ih, Nat.testBit_add_one a m, Nat.testBit_add_one b m]

/-- **Strengthened classical-correctness bridge with carry-in**
    (Iter 196, 2026-05-13). Generalizes `Adder.sumfb_eq_testBit_add`
    by adding a carry-in parameter `b₀ : Bool`, which lets the
    inductive step thread through `Nat.testBit_add_one` + `Nat.add_div`
    decomposition cleanly.

    Base case (i=0) is the existing `Adder.testBit_add_zero` analog
    extended with b₀; succ case is named-sorried per Iter 190's
    strategy doc (uses the gen IH applied to a/2, b/2, new carry-in
    derived from `Nat.add_div` decomposition). -/
theorem Adder.sumfb_eq_testBit_add_gen (b₀ : Bool) (a b i : Nat) :
    Adder.sumfb b₀ (fun k => a.testBit k) (fun k => b.testBit k) i
      = (a + b + b₀.toNat).testBit i := by
  induction i generalizing a b b₀ with
  | zero =>
      -- Base case: sumfb b₀ ab 0 = xor (xor b₀ a_0) b_0
      --          = (a + b + b₀.toNat).testBit 0
      -- Mod-2 case-bash on a%2, b%2, plus b₀: Bool.
      simp only [Adder.sumfb, Adder.carry, Nat.testBit_zero]
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
      have hb0 : b₀.toNat = 0 ∨ b₀.toNat = 1 := by
        cases b₀ <;> simp [Bool.toNat]
      have hsum : (a + b + b₀.toNat) % 2 = 0 ∨ (a + b + b₀.toNat) % 2 = 1 := by omega
      cases b₀ <;>
        (rcases ha with ha | ha <;> rcases hb with hb | hb <;>
         rcases hsum with hsum | hsum <;>
         simp_all [Bool.toNat] <;> omega)
  | succ k ih =>
      -- Strategy: apply IH with new args (carry b₀ 1 a b, a/2, b/2),
      -- using carry_shift_one + h_div arithmetic identity.
      have h_div : (a + b + b₀.toNat) / 2
                 = (a/2) + (b/2)
                   + (Adder.carry b₀ 1 (fun i => a.testBit i)
                        (fun i => b.testBit i)).toNat := by
        cases b₀ <;>
          rcases (show a % 2 = 0 ∨ a % 2 = 1 from by omega) with ha | ha <;>
          rcases (show b % 2 = 0 ∨ b % 2 = 1 from by omega) with hb | hb <;>
          simp [Adder.carry, Nat.testBit_zero, Bool.toNat, ha, hb] <;>
          omega
      rw [Nat.testBit_add_one, h_div, ← ih]
      -- Goal: sumfb b₀ a.testBit b.testBit (k+1) = sumfb (carry _) (a/2)bit (b/2)bit k
      -- Unfold sumfb on both sides, use carry_shift_one + testBit_add_one.
      show xor (xor (Adder.carry b₀ (k + 1) _ _) (a.testBit (k + 1))) (b.testBit (k + 1))
         = xor (xor (Adder.carry _ k _ _) ((a/2).testBit k)) ((b/2).testBit k)
      rw [Adder.carry_shift_one, Nat.testBit_add_one a k, Nat.testBit_add_one b k]

/-- **The classical-correctness bridge, parametric** (Iter 196 PROVEN
    via gen helper). `sumfb` on Nat-derived bit-streams equals
    `testBit (a+b)`. SQIR's `sumfb_correct_carry0` analog.

    Was sorried as `TODO_sumfb_eq_testBit_add` until Iter 196.
    Now derived from `Adder.sumfb_eq_testBit_add_gen` by specializing
    `b₀ = false` (and using `Bool.toNat false = 0`). Iter 196 also
    introduced a new sorry `TODO_sumfb_eq_testBit_add_gen_succ` for
    the gen-helper's succ case. Net sorry delta = 0; the new sorry
    has cleaner inductive structure. -/
theorem Adder.sumfb_eq_testBit_add (a b i : Nat) :
    Adder.sumfb false (fun k => a.testBit k) (fun k => b.testBit k) i
      = (a + b).testBit i := by
  -- Specialize the gen helper to b₀ = false (toNat = 0, so a + b + 0 = a + b).
  have h := Adder.sumfb_eq_testBit_add_gen false a b i
  simpa [Bool.toNat] using h

/-- **Small-instance validation** of the bridge at `(a=3, b=1)`.
    Sum = 4 = 0b100. Decide-witnesses confirm the statement
    `sumfb false ... i = (3+1).testBit i` for i = 0, 1, 2, 3. -/
example :
    Adder.sumfb false (fun k => (3 : Nat).testBit k)
                      (fun k => (1 : Nat).testBit k) 0
      = ((3 : Nat) + 1).testBit 0
    ∧ Adder.sumfb false (fun k => (3 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 1
        = ((3 : Nat) + 1).testBit 1
    ∧ Adder.sumfb false (fun k => (3 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 2
        = ((3 : Nat) + 1).testBit 2
    ∧ Adder.sumfb false (fun k => (3 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 3
        = ((3 : Nat) + 1).testBit 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold Adder.sumfb Adder.carry; decide)

/-- **Small-instance validation** at `(a=7, b=1)`. Sum = 8 = 0b1000.
    Bit 0/1/2 of 8 = false; bit 3 of 8 = true. -/
example :
    Adder.sumfb false (fun k => (7 : Nat).testBit k)
                      (fun k => (1 : Nat).testBit k) 0
      = ((7 : Nat) + 1).testBit 0
    ∧ Adder.sumfb false (fun k => (7 : Nat).testBit k)
                        (fun k => (1 : Nat).testBit k) 3
        = ((7 : Nat) + 1).testBit 3 := by
  refine ⟨?_, ?_⟩ <;> (unfold Adder.sumfb Adder.carry; decide)

/-- **Validation on the (7, 1) 4-bit case**: decide-witnesses that
    the invariant predicate is SATISFIED by the actual forward
    cascade post-state computed by
    `gidney_forward_faithful_full_post_state 4 inputF_7_plus_1`.

    This confirms the invariant statement matches the observed
    post-state (Iter 116's decide-table). The parametric "for all
    `a b n`" claim will be a separate SORRIED theorem below. -/
example :
    Gidney.forward_cascade_post_invariant 4 7 1
      (gidney_forward_faithful_full_post_state 4 inputF_7_plus_1) := by
  intro i hi
  -- Case-split on i: 4 cases (0, 1, 2, 3). Manual match since
  -- `interval_cases` is not imported in this file.
  match i, hi with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 3, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 4, hbig => omega

/-- **Validation on (3, 1) n=3 k=1**: after the first-bit step
    (k=1) on `adder_input_F 3 3 1`, the propagation invariant
    holds at all 3 positions. Decide-witness via manual match. -/
example :
    Gidney.propagation_step_invariant 1 3 3 1
      (gidney_propagation_post_state 1 (adder_input_F 3 3 1)) := by
  intro j hj
  match j, hj with
  | 0, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 1, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | 2, _ => refine ⟨?_, ?_, ?_⟩ <;> decide
  | _ + 3, h => omega

/- **`TODO_gidney_forward_cascade_invariant` REMOVED (Iter 214,
   2026-05-13)**. Originally sorried at this location (Iter 159), the
   theorem `forward_cascade_post_invariant` was superseded by Iter 188-189's
   `Gidney.post_last_bit_invariant_holds`, which is FULLY PROVEN
   parametrically and captures the same content (modulo the predicate
   choice). The `Gidney.forward_cascade_post_invariant` def above
   remains as historical record of the original Iter 159 attempt. -/

end FormalRV.BQAlgo
