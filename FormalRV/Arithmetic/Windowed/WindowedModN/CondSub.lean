/- WindowedModN — §5 general-state conditional subtract.
   Part of `WindowedModN` (the `WindowedModN.lean` shim re-exports all parts). -/
import FormalRV.Arithmetic.Windowed.WindowedModN.Comparators

namespace FormalRV.Shor.WindowedCircuit
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §5. General-state conditional subtract.

`sqir_conditionalSubConstGate` (masked-prepare `2^bits−N` ; adder ;
masked-unprepare) on an ARBITRARY state with clear carry-in and clear read
register: subtracts `N` from the accumulator iff the flag is set, restores
read/carry, preserves the flag and everything outside the workspace. -/

theorem condSub_state_general
    (bits q_start N flagPos x : Nat) (f : Nat → Bool)
    (hx : x < 2 ^ bits)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (h_cin : f q_start = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = x.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    (∀ i, i < bits →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f
            (q_start + 2 * i + 1)
          = ((x + if f flagPos then 2 ^ bits - N else 0) % 2 ^ bits).testBit i)
    ∧ (∀ i, i < bits →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f
            (q_start + 2 * i + 2) = false)
    ∧ Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f q_start
        = false
    ∧ (∀ p, p < q_start ∨ q_start + 2 * bits + 1 ≤ p →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f p = f p) := by
  have h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intro i hi
    rcases hflag_out with h | h <;> omega
  unfold sqir_conditionalSubConstGate
  by_cases hfl : f flagPos
  · -- Flag set: the gate acts as `cuccaro_addConstGate (2^bits − N)`.
    rw [sqir_conditionalAddConstGate_apply_true_fun bits q_start (2 ^ bits - N) flagPos f
          h_flag_distinct hfl hflag_out]
    unfold cuccaro_addConstGate
    simp only [Gate.applyNat_seq]
    -- The prepared state: read register holds `K := 2^bits − N`.
    have h1_read : ∀ i, i < bits →
        Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
            (q_start + 2 * i + 2) = (2 ^ bits - N).testBit i := by
      intro i hi
      rw [cuccaro_prepareConstRead_at_read bits q_start (2 ^ bits - N) i hi,
          h_read i hi, Bool.false_xor]
    have h1_tgt : ∀ i, i < bits →
        Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
            (q_start + 2 * i + 1) = x.testBit i := by
      intro i hi
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) _
            (fun k _ => by omega)]
      exact h_tgt i hi
    have h1_cin : Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f
        q_start = false := by
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q_start
            (fun k _ => by omega)]
      exact h_cin
    -- The adder output on the prepared state.
    have h2_tgt : ∀ i, i < bits →
        Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)
            (q_start + 2 * i + 1) = (x + (2 ^ bits - N)).testBit i :=
      fun i hi => cuccaro_adder_sum_bits_general bits q_start x (2 ^ bits - N) _
        h1_cin h1_tgt h1_read i hi
    have h2_read : ∀ i, i < bits →
        Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)
            (q_start + 2 * i + 2) = (2 ^ bits - N).testBit i := by
      intro i hi
      rw [(cuccaro_n_bit_adder_full_correct bits q_start _).2.2 i hi]
      exact h1_read i hi
    have h2_cin : Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start (2 ^ bits - N)) f)
        q_start = false := by
      rw [(cuccaro_n_bit_adder_full_correct bits q_start _).1]
      exact h1_cin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) _
            (fun k _ => by omega)]
      rw [h2_tgt i hi, hfl, if_pos rfl]
      rw [Nat.testBit_mod_two_pow,
          show decide (i < bits) = true from decide_eq_true hi, Bool.true_and]
    · intro i hi
      rw [cuccaro_prepareConstRead_at_read bits q_start (2 ^ bits - N) i hi,
          h2_read i hi, Bool.xor_self]
    · rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) q_start
            (fun k _ => by omega)]
      exact h2_cin
    · intro p hp
      have hp_not_read : ∀ k, k < bits → p ≠ q_start + 2 * k + 2 := by
        intro k hk
        rcases hp with h | h <;> omega
      rw [cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) p hp_not_read]
      rcases hp with h | h
      · rw [cuccaro_n_bit_adder_full_frame_below bits q_start _ p h]
        exact cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) p hp_not_read f
      · rw [cuccaro_n_bit_adder_full_frame_above bits q_start _ p h]
        exact cuccaro_prepareConstRead_at_other bits q_start (2 ^ bits - N) p hp_not_read f
  · -- Flag clear: the gate acts as the bare adder with a zero addend.
    have hfl' : f flagPos = false := by
      revert hfl
      cases f flagPos <;> simp
    rw [sqir_conditionalAddConstGate_apply_false_fun bits q_start (2 ^ bits - N) flagPos f
          h_flag_distinct hfl' hflag_out]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [cuccaro_adder_sum_bits_general bits q_start x 0 f h_cin h_tgt
            (fun k hk => by rw [h_read k hk, Nat.zero_testBit]) i hi]
      rw [hfl', if_neg (by simp), Nat.add_zero, Nat.mod_eq_of_lt hx]
    · intro i hi
      rw [(cuccaro_n_bit_adder_full_correct bits q_start f).2.2 i hi]
      exact h_read i hi
    · rw [(cuccaro_n_bit_adder_full_correct bits q_start f).1]
      exact h_cin
    · intro p hp
      rcases hp with h | h
      · exact cuccaro_n_bit_adder_full_frame_below bits q_start f p h
      · exact cuccaro_n_bit_adder_full_frame_above bits q_start f p h


end FormalRV.Shor.WindowedCircuit
