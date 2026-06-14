/-
  FormalRV.Shor.CosetEigenstate.CuccaroStructuredOutput — the cuccaro addConst gate maps
  the structured layout funbool to the structured funbool of `(x+c) mod 2^bits` (bitwise).
  ════════════════════════════════════════════════════════════════════════════

  This is the SINGLE bitwise statement of the four layout facts the layout-conjugation
  bridge needs:  on the structured input `cuccaro_input_F q_start false 0 x`
    * target b-register (positions `q_start+2i+1`) updates by `+c mod 2^bits`,
    * read a-register (positions `q_start+2i+2`) restored to `0`,
    * carry-in (`q_start`) restored to `false`,
    * everything outside the block `[q_start, q_start+2·bits+1)` is preserved (frame),
  packaged as the FUNBOOL equality
      applyNat (cuccaro_addConstGate bits q_start c) (cuccaro_input_F q_start false 0 x)
        = cuccaro_input_F q_start false 0 ((x+c) % 2^bits).
  So the gate carries the structured-layout subspace to itself, acting as `+c mod 2^bits`
  on the (interleaved) target value — exactly the gate-preserves-the-layout fact a SWAP /
  layout-relabeling (`CosetLayoutTransport`) conjugates to a contiguous `addPerm`.

  Built from the repo's bit-level cuccaro lemmas (`cuccaro_addConstGate_target_bit`,
  `_read_bit`, `_carry_in_bit`) and the workspace frame
  (`cuccaro_addConstGate_commute_update_outside_workspace`), by a `funext` over the six
  position classes (carry / target k<bits / target k≥bits / read k<bits / read k≥bits /
  below `q_start`).  The fiddly position-casing was de-risked via 3 parallel verified
  attempts; this is the cleanest.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **THE CUCCARO STRUCTURED-OUTPUT THEOREM.**  The literal cuccaro addConst gate maps the
    structured input funbool (target `= x`, read `= 0`, carry `= 0`) to the structured
    funbool for `(x+c) mod 2^bits` — target `+c mod 2^bits`, read/carry restored, frame
    preserved — as ONE bitwise equality. -/
theorem cuccaro_addConstGate_structured_output (bits q_start c x : Nat)
    (hc : c < 2 ^ bits) (hx : x < 2 ^ bits) :
    Gate.applyNat (cuccaro_addConstGate bits q_start c) (cuccaro_input_F q_start false 0 x)
      = cuccaro_input_F q_start false 0 ((x + c) % 2 ^ bits) := by
  -- Frame fact: outside the block, applyNat fixes the input.
  have hframe : ∀ q, (q < q_start ∨ q_start + 2 * bits + 1 ≤ q) →
      Gate.applyNat (cuccaro_addConstGate bits q_start c)
          (cuccaro_input_F q_start false 0 x) q
        = cuccaro_input_F q_start false 0 x q := by
    intro q hq
    conv_lhs =>
      rw [show cuccaro_input_F q_start false 0 x
            = update (cuccaro_input_F q_start false 0 x) q
                (cuccaro_input_F q_start false 0 x q) from by
          funext q'; by_cases hqq : q' = q
          · subst hqq; rw [update_eq]
          · rw [update_neq _ _ _ _ hqq]]
    rw [cuccaro_addConstGate_commute_update_outside_workspace bits q_start c q
        (cuccaro_input_F q_start false 0 x q) (cuccaro_input_F q_start false 0 x) hq]
    rw [update_eq]
  funext q
  by_cases hlt : q < q_start
  · -- (a) q < q_start: outside block, both sides false.
    rw [hframe q (Or.inl hlt)]
    unfold cuccaro_input_F
    simp [hlt]
  · -- q ≥ q_start.  Set i := q - q_start.
    set i := q - q_start with hi_def
    have hq_eq : q = q_start + i := by omega
    by_cases hi0 : i = 0
    · -- (b) q = q_start: carry-in.
      have hqs : q = q_start := by omega
      rw [hqs]
      rw [cuccaro_addConstGate_carry_in_bit bits q_start c x]
      rw [cuccaro_input_F_at_c_in q_start false 0 ((x + c) % 2 ^ bits)]
    · -- i ≥ 1.  Split on parity of i.
      rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- i = 2k.  Since i ≥ 1, k ≥ 1; q = q_start + 2*(k-1) + 2 (read position).
        have hk1 : k ≥ 1 := by omega
        set m := k - 1 with hm_def
        have hi_read : i = 2 * m + 2 := by omega
        have hq_read : q = q_start + 2 * m + 2 := by omega
        by_cases hmb : m < bits
        · -- (e) read position, m < bits.
          rw [hq_read]
          rw [cuccaro_addConstGate_read_bit bits q_start c x m hmb]
          rw [cuccaro_input_F_at_a q_start m false 0 ((x + c) % 2 ^ bits)]
          rw [Nat.zero_testBit]
        · -- (f) read position, m ≥ bits: outside block.
          rw [hq_read]
          rw [hframe (q_start + 2 * m + 2) (Or.inr (by omega))]
          rw [cuccaro_input_F_at_a q_start m false 0 x]
          rw [cuccaro_input_F_at_a q_start m false 0 ((x + c) % 2 ^ bits)]
      · -- i = 2k + 1.  q = q_start + 2k + 1 (target position).
        have hq_tgt : q = q_start + 2 * k + 1 := by omega
        by_cases hkb : k < bits
        · -- (c) target position, k < bits.
          rw [hq_tgt]
          rw [cuccaro_addConstGate_target_bit bits q_start c x k hkb hc]
          rw [cuccaro_input_F_at_b q_start k false 0 ((x + c) % 2 ^ bits)]
          -- RHS = ((x+c) % 2^bits).testBit k = (x+c).testBit k for k < bits.
          rw [Nat.testBit_mod_two_pow]
          simp [hkb]
        · -- (d) target position, k ≥ bits: outside block.
          simp only [Nat.not_lt] at hkb
          rw [hq_tgt]
          rw [hframe (q_start + 2 * k + 1) (Or.inr (by omega))]
          rw [cuccaro_input_F_at_b q_start k false 0 x]
          rw [cuccaro_input_F_at_b q_start k false 0 ((x + c) % 2 ^ bits)]
          -- both = x.testBit k = false and ((x+c)%2^bits).testBit k = false (k ≥ bits).
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
            (Nat.pow_le_pow_right (by omega) hkb))]
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
            (Nat.mod_lt _ (Nat.two_pow_pos bits))
            (Nat.pow_le_pow_right (by omega) hkb))]

end FormalRV.BQAlgo
