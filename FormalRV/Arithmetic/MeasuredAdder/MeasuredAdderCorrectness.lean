/-
  FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderCorrectness
  ───────────────────────────────────────────────────────────
  VALUE correctness for the measured Gidney adder family — the FAITHFUL sum on the
  target register, for both the uncontrolled (`a + b`) and the controlled
  (`ctrl ? (a+b) : b`) adders.  Imports only the shared base `MeasuredAdderDef`;
  every proof here is byte-for-byte the one that used to live in
  `GidneyMeasured.lean` / `GidneyMeasuredControlled.lean`.

  ## Why the value is still `a + b` (the frame argument, uncontrolled)

  Each measured reverse step equals the unitary reverse step followed by clearing
  its own carry (`*_eq` lemmas, in Def).  Crucially, the carry an interior step
  writes is read by NO later (lower-index) step, so forcing it to `false` is
  INVISIBLE to every `read`/`target` output of the remaining cascade
  (`gidneyMeasFullReverse_rt`, via `propagation_reverse_clear_carry_insensitive`).
  Hence:
    • `target` after the measured adder = `target` after the reversible adder
      = `(a + b) % 2^bits`  (REUSING `gidney_adder_full_faithful_no_measurement_target_correct`);
    • the carry register is `false` everywhere (`gidneyMeasFullReverse` clears it).

  ## Why the value is `ctrl ? (a+b) : b` (the reuse argument, controlled)

  After the mask, the adder-block sub-state is **literally**
  `adder_input_F n (if ctrl then a else 0) b` (read register = the gated addend,
  target = `b`, carries = 0).  The control bit and the source register live at
  HIGH indices (`≥ adder_n_qubits = 3n+2`), and the measured adder only ever
  touches indices `< 3n+2` (`gidneyAdderMeasured_boundedBy`).  A clean
  index-congruence (`EGate.applyNat_congr_lt`) swaps the masked state for the
  literal `adder_input_F`, and we REUSE `gidneyAdderMeasured_correct` verbatim —
  NO arithmetic is re-proved.

  Refs: Gidney arXiv:1709.06648 (temporary AND); Cain–Xu 2026.
-/
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderDef

namespace FormalRV.Arithmetic.MeasuredAdder

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute

/-! ## §1. Value correctness (uncontrolled): the FAITHFUL sum `(a+b) % 2^bits`. -/

/-- **Value correctness of the measured adder — FAITHFUL `a + b`.**  On the clean
two-operand input `adder_input_F (n+2) a b`, the measured Gidney adder writes the
true sum bits `(a + b).testBit i` to the target register for every `i < n+2`, AND
releases every carry ancilla to `false`:

  • `target[i] = (a + b).testBit i`   (= `adder_sum_bit_classical a b i`),
  • `carry[i]  = false`.

The target value is REUSED verbatim from the reversible adder's correctness
(`gidney_adder_full_faithful_no_measurement_target_correct`): the measured reverse
agrees with the reversible reverse on every `target` position
(`gidneyMeasFullReverse_rt`), and the reversible adder's target is the sum.  The
carries are released by the measurement-uncompute (`gidneyMeasFullReverse_carry_clear`),
citing `MeasuredANDUncompute.measANDUncompute_perfect` for the quantum
justification that this reset IS the perfect AND-uncompute. -/
theorem gidneyAdderMeasured_correct
    (n a b q_start : Nat) (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    ∀ i, i < n + 2 →
      (EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
          (adder_input_F (n + 2) a b) (target_idx i)
        = adder_sum_bit_classical a b i)
      ∧ (EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
          (adder_input_F (n + 2) a b) (carry_idx i) = false) := by
  intro i hi
  refine ⟨?_, ?_⟩
  · -- target = sum: route through the reversible adder's proven target correctness.
    rw [gidneyAdderMeasured_applyNat,
        gidneyMeasFullReverse_rt n _ (target_idx i) (by intro m; unfold target_idx carry_idx; omega)]
    -- now the goal is the reversible reverse post-state target = sum
    have hrev : gidney_full_reverse_post_state (n + 2)
        (gidney_final_cx_cascade_post_state (n + 2)
          (gidney_forward_faithful_full_post_state (n + 2) (adder_input_F (n + 2) a b))) (target_idx i)
        = adder_sum_bit_classical a b i := by
      rw [← gidney_adder_full_faithful_no_measurement_applyNat n (adder_input_F (n + 2) a b)]
      exact gidney_adder_full_faithful_no_measurement_target_correct (n + 2) a b
        (by omega) ha hb i hi
    exact hrev
  · -- carry = false: the measured reverse clears it.
    rw [gidneyAdderMeasured_applyNat]
    exact gidneyMeasFullReverse_carry_clear n _ i hi

/-- **Decoded value form: the target register holds `(a + b) % 2^(n+2)`.**  The
LSB-first `gidney_target_val` decoder of the measured adder's output equals
`(a + b) % 2^(n+2)` — the faithful arithmetic sum.  Derived from the per-bit
`gidneyAdderMeasured_correct` and the reversible adder's decoded-value theorem
`gidney_adder_correct_full` (which both equal `(a+b) % 2^bits` bit-for-bit). -/
theorem gidneyAdderMeasured_target_val
    (n a b q_start : Nat) (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    gidney_target_val (n + 2)
        (EGate.applyNat (gidneyAdderMeasured (n + 2) q_start) (adder_input_F (n + 2) a b))
      = (a + b) % 2 ^ (n + 2) := by
  -- Each target bit equals `(a+b).testBit i` (= `adder_sum_bit_classical`), so the
  -- LSB-first decoder evaluates to `(a+b) % 2^bits` by `gidney_target_val_eq_sum_when_bits_match`.
  apply gidney_target_val_eq_sum_when_bits_match (n + 2) (a + b)
  intro i hi
  have := (gidneyAdderMeasured_correct n a b q_start ha hb i hi).1
  rwa [adder_sum_bit_classical] at this

/-! ## §2. Value correctness (controlled) — the CONTROLLED sum `ctrl ? (a+b) : b`.

We split the controlled adder as `mask ; measured-adder`.  The mask turns the
clean input into `adder_input_F (n+2) (if cval=1 then a else 0) b` ON the adder
block (`ctrlMaskRead_eq_adder_input`); the measured adder only touches the block
(`gidneyAdderMeasured_boundedBy`), so by index-congruence (`EGate.applyNat_congr_lt`)
its target/carry outputs equal those on the literal `adder_input_F`.  We then
REUSE `gidneyAdderMeasured_correct` verbatim — the arithmetic is NOT re-proved. -/

/-- **Value correctness of the controlled measured adder — the CONTROLLED sum.**
With the control register placed above the adder block (`adder_n_qubits (n+2) ≤
ctrl`) and the classical control bit `cval`, on the clean input
`ctrlAdder_input_F (n+2) a b ctrl cval` the controlled measured Gidney adder writes
to the target register, for every `i < n+2`,

  • `target[i] = (if cval = 1 then a + b else b).testBit i`   (the CONTROLLED sum),
  • `carry[i]  = false`                                        (carries released).

The target value is the measured adder's faithful sum of `b` with the GATED addend
`if cval = 1 then a else 0`, reused from `gidneyAdderMeasured_correct`. -/
theorem gidneyAdderMeasuredControlled_correct
    (n a b q_start ctrl cval : Nat)
    (hctrl : adder_n_qubits (n + 2) ≤ ctrl)
    (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    ∀ i, i < n + 2 →
      (EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
          (ctrlAdder_input_F (n + 2) a b ctrl cval) (target_idx i)
        = (if cval = 1 then a + b else b).testBit i)
      ∧ (EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
          (ctrlAdder_input_F (n + 2) a b ctrl cval) (carry_idx i) = false) := by
  intro i hi
  set a' := if cval = 1 then a else 0 with ha'
  have ha'lt : a' < 2 ^ (n + 2) := by rw [ha']; split <;> [exact ha; exact Nat.pos_of_ne_zero (by positivity)]
  -- split the controlled adder: mask ; measured adder
  have hsplit : ∀ q,
      EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
        (ctrlAdder_input_F (n + 2) a b ctrl cval) q
      = EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
        (Gate.applyNat (ctrlMaskRead ctrl (n + 2)) (ctrlAdder_input_F (n + 2) a b ctrl cval)) q := by
    intro q; rfl
  -- congruence: swap the masked state for the literal `adder_input_F (n+2) a' b`
  have hswap : ∀ q, q < adder_n_qubits (n + 2) →
      EGate.applyNat (gidneyAdderMeasured (n + 2) q_start)
        (Gate.applyNat (ctrlMaskRead ctrl (n + 2)) (ctrlAdder_input_F (n + 2) a b ctrl cval)) q
      = EGate.applyNat (gidneyAdderMeasured (n + 2) q_start) (adder_input_F (n + 2) a' b) q := by
    intro q hq
    exact EGate.applyNat_congr_lt (adder_n_qubits (n + 2)) (gidneyAdderMeasured (n + 2) q_start)
      (gidneyAdderMeasured_boundedBy n q_start) _ _
      (fun p hp => by rw [ha']; exact ctrlMaskRead_eq_adder_input n a b ctrl cval hctrl p hp) q hq
  have htidx : target_idx i < adder_n_qubits (n + 2) := by unfold target_idx adder_n_qubits; omega
  have hcidx : carry_idx i < adder_n_qubits (n + 2) := by unfold carry_idx adder_n_qubits; omega
  obtain ⟨htgt, hcar⟩ := gidneyAdderMeasured_correct n a' b q_start ha'lt hb i hi
  refine ⟨?_, ?_⟩
  · rw [hsplit, hswap _ htidx, htgt]
    -- adder_sum_bit_classical a' b i = (if cval=1 then a+b else b).testBit i
    unfold adder_sum_bit_classical
    rw [ha']; split
    · rfl
    · rw [Nat.zero_add]
  · rw [hsplit, hswap _ hcidx, hcar]

/-- **Decoded value form: the target register holds `if cval = 1 then (a+b) else b`
mod `2^(n+2)`.**  The LSB-first `gidney_target_val` decoder of the controlled
measured adder's output equals `(if cval = 1 then a + b else b) % 2^(n+2)` — the
faithful CONTROLLED sum: the arithmetic sum `(a+b) % 2^bits` when the control is
set, and the unchanged accumulator `b % 2^bits` when it is not.  Derived from the
per-bit `gidneyAdderMeasuredControlled_correct` via
`gidney_target_val_eq_sum_when_bits_match`. -/
theorem gidneyAdderMeasuredControlled_target_val
    (n a b q_start ctrl cval : Nat)
    (hctrl : adder_n_qubits (n + 2) ≤ ctrl)
    (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    gidney_target_val (n + 2)
        (EGate.applyNat (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
          (ctrlAdder_input_F (n + 2) a b ctrl cval))
      = (if cval = 1 then a + b else b) % 2 ^ (n + 2) := by
  apply gidney_target_val_eq_sum_when_bits_match (n + 2) (if cval = 1 then a + b else b)
  intro i hi
  exact (gidneyAdderMeasuredControlled_correct n a b q_start ctrl cval hctrl ha hb i hi).1

end FormalRV.Arithmetic.MeasuredAdder
