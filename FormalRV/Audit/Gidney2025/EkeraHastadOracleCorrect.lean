/-
  FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect — Boolean correctness of the concrete EH oracle
  gate `ehOracleGate` (Milestone 1).  WORK IN PROGRESS, built bottom-up from VERIFIED Cuccaro lemmas.

  Strategy: the oracle's input has the control registers (`x`, `y`) set as flags plus a clean target
  block.  The per-gadget Cuccaro lemmas (`sqir_conditionalAddConstGate_target_decode`, etc.) are
  stated for the clean single-flag input `update (cuccaro_input_F q false 0 v) flagPos flag`.  We
  bridge the gap by COMMUTING each gadget past the *other* control-bit updates (they lie outside the
  gadget's workspace), reducing every step to the clean single-flag form.

  This file currently establishes the foundational "commute past a list of control updates" lemmas.
  The accumulation fold and the final in-range value computation build on these.

  No `sorry`, no `native_decide`.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroControlledModularAddCorrectness
import FormalRV.Verifier.ProofGate

namespace FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect

open FormalRV.Framework
open FormalRV.BQAlgo

/-- Layer a list of bit-updates (control register contents) onto a base bit-function. -/
def overlay (L : List (Nat × Bool)) (f : Nat → Bool) : Nat → Bool :=
  L.foldr (fun pb g => update g pb.1 pb.2) f

@[simp] theorem overlay_nil (f : Nat → Bool) : overlay [] f = f := rfl

theorem overlay_cons (pb : Nat × Bool) (L : List (Nat × Bool)) (f : Nat → Bool) :
    overlay (pb :: L) f = update (overlay L f) pb.1 pb.2 := rfl

/-- **A conditional-add gadget commutes past a list of control-bit updates**, provided every update
sits outside the gadget's workspace `[q, q+2·bits+1)` and is not the flag qubit. -/
theorem condAdd_commute_overlay (bits q_start N flagPos : Nat) (L : List (Nat × Bool)) (f : Nat → Bool)
    (hL : ∀ pb ∈ L, (pb.1 < q_start ∨ q_start + 2 * bits + 1 ≤ pb.1) ∧ pb.1 ≠ flagPos) :
    Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) (overlay L f)
      = overlay L (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f) := by
  induction L with
  | nil => rfl
  | cons pb rest ih =>
      rw [overlay_cons]
      rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start N flagPos pb.1 pb.2
            (overlay rest f) (hL pb (List.mem_cons_self ..)).1 (hL pb (List.mem_cons_self ..)).2]
      rw [ih (fun pb' hpb' => hL pb' (List.mem_cons_of_mem _ hpb'))]
      rw [overlay_cons]

/-- **A conditional-sub gadget commutes past a list of control-bit updates** (same as add). -/
theorem condSub_commute_overlay (bits q_start N flagPos : Nat) (L : List (Nat × Bool)) (f : Nat → Bool)
    (hL : ∀ pb ∈ L, (pb.1 < q_start ∨ q_start + 2 * bits + 1 ≤ pb.1) ∧ pb.1 ≠ flagPos) :
    Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) (overlay L f)
      = overlay L (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f) := by
  unfold sqir_conditionalSubConstGate
  exact condAdd_commute_overlay bits q_start (2 ^ bits - N) flagPos L f hL

/-! ## §2. Value → bits (the binary representation read off the block is unique) -/

/-- The `i`-th bit of the decoded target value is the target qubit `q+2i+1`. -/
theorem cuccaro_target_val_testBit (q_start : Nat) (f : Nat → Bool) :
    ∀ bits i, i < bits → (cuccaro_target_val bits q_start f).testBit i = f (q_start + 2 * i + 1) := by
  intro bits
  induction bits with
  | zero => intro i hi; omega
  | succ k ih =>
      intro i hi
      have hVk : cuccaro_target_val k q_start f < 2 ^ k := cuccaro_target_val_lt k q_start f
      show (cuccaro_target_val k q_start f + (if f (q_start + 2 * k + 1) then 2 ^ k else 0)).testBit i
        = f (q_start + 2 * i + 1)
      rcases Nat.lt_or_ge i k with hik | hik
      · -- i < k : the high `2^k` term does not affect bit i
        have hmod : (cuccaro_target_val k q_start f
              + (if f (q_start + 2 * k + 1) then 2 ^ k else 0)) % 2 ^ k
            = cuccaro_target_val k q_start f := by
          rcases f (q_start + 2 * k + 1) <;> simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hVk]
        have h1 : (cuccaro_target_val k q_start f
              + (if f (q_start + 2 * k + 1) then 2 ^ k else 0)).testBit i
            = ((cuccaro_target_val k q_start f
              + (if f (q_start + 2 * k + 1) then 2 ^ k else 0)) % 2 ^ k).testBit i := by
          rw [Nat.testBit_mod_two_pow]; simp [hik]
        rw [h1, hmod, ih i hik]
      · have hik' : i = k := by omega
        subst hik'
        cases hb : f (q_start + 2 * i + 1) with
        | false => simp [hb, Nat.testBit_lt_two_pow hVk]
        | true =>
            simp only [hb, if_true]
            rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hVk]
            rfl

/-- The `i`-th bit of the decoded read value is the read qubit `q+2i+2`. -/
theorem cuccaro_read_val_testBit (q_start : Nat) (f : Nat → Bool) :
    ∀ bits i, i < bits → (cuccaro_read_val bits q_start f).testBit i = f (q_start + 2 * i + 2) := by
  intro bits
  induction bits with
  | zero => intro i hi; omega
  | succ k ih =>
      intro i hi
      have hVk : cuccaro_read_val k q_start f < 2 ^ k := cuccaro_read_val_lt k q_start f
      show (cuccaro_read_val k q_start f + (if f (q_start + 2 * k + 2) then 2 ^ k else 0)).testBit i
        = f (q_start + 2 * i + 2)
      rcases Nat.lt_or_ge i k with hik | hik
      · have hmod : (cuccaro_read_val k q_start f
              + (if f (q_start + 2 * k + 2) then 2 ^ k else 0)) % 2 ^ k
            = cuccaro_read_val k q_start f := by
          rcases f (q_start + 2 * k + 2) <;> simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hVk]
        have h1 : (cuccaro_read_val k q_start f
              + (if f (q_start + 2 * k + 2) then 2 ^ k else 0)).testBit i
            = ((cuccaro_read_val k q_start f
              + (if f (q_start + 2 * k + 2) then 2 ^ k else 0)) % 2 ^ k).testBit i := by
          rw [Nat.testBit_mod_two_pow]; simp [hik]
        rw [h1, hmod, ih i hik]
      · have hik' : i = k := by omega
        subst hik'
        cases hb : f (q_start + 2 * i + 2) with
        | false => simp [hb, Nat.testBit_lt_two_pow hVk]
        | true =>
            simp only [hb, if_true]
            rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hVk]
            rfl

/-! ## §3. General-input adder value lemma -/

/-- The ripple carry depends only on the carry-in and the block bits, so it is congruent under any
two states agreeing there. -/
theorem cuccaro_carry_congr (f f' : Nat → Bool) (q_start : Nat) :
    ∀ k, f q_start = f' q_start →
      (∀ j, j < k → f (q_start + 2 * j + 1) = f' (q_start + 2 * j + 1)) →
      (∀ j, j < k → f (q_start + 2 * j + 2) = f' (q_start + 2 * j + 2)) →
      cuccaro_carry f q_start k = cuccaro_carry f' q_start k := by
  intro k
  induction k with
  | zero => intro hq _ _; exact hq
  | succ n ih =>
      intro hq hb ha
      show Boolean.majority (cuccaro_carry f q_start n) (f (q_start + 2 * n + 1)) (f (q_start + 2 * n + 2))
        = Boolean.majority (cuccaro_carry f' q_start n) (f' (q_start + 2 * n + 1)) (f' (q_start + 2 * n + 2))
      rw [ih hq (fun j hj => hb j (by omega)) (fun j hj => ha j (by omega)),
          hb n (by omega), ha n (by omega)]

/-- **★ General-input adder value lemma. ★**  For ANY state `g`, the Cuccaro adder leaves the target
register holding `(target + read + carry-in) mod 2^bits`.  (The existing value lemmas are only for
`cuccaro_input_F`-shaped inputs; this lifts to arbitrary `g` via value→bits + carry congruence.) -/
theorem adder_target_val_general (bits q_start : Nat) (g : Nat → Bool) :
    cuccaro_target_val bits q_start (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g)
      = (cuccaro_target_val bits q_start g + cuccaro_read_val bits q_start g
          + (g q_start).toNat) % 2 ^ bits := by
  have hR : cuccaro_read_val bits q_start g < 2 ^ bits := cuccaro_read_val_lt bits q_start g
  have hV : cuccaro_target_val bits q_start g < 2 ^ bits := cuccaro_target_val_lt bits q_start g
  set R := cuccaro_read_val bits q_start g
  set V := cuccaro_target_val bits q_start g
  set cif := cuccaro_input_F q_start (g q_start) R V with hcifdef
  have hcif : cuccaro_target_val bits q_start (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) cif)
      = (R + V + (g q_start).toNat) % 2 ^ bits :=
    cuccaro_n_bit_adder_full_target_decode_carry bits q_start R V (g q_start) hR hV
  apply cuccaro_target_val_eq_sum_when_bits_match bits q_start (V + R + (g q_start).toNat) _
  intro i hi
  have hbit : Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g (q_start + 2 * i + 1)
            = Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) cif (q_start + 2 * i + 1) := by
    rw [cuccaro_n_bit_adder_full_sum_bit bits q_start g i hi,
        cuccaro_n_bit_adder_full_sum_bit bits q_start cif i hi]
    have hcarry : cuccaro_carry g q_start i = cuccaro_carry cif q_start i := by
      apply cuccaro_carry_congr g cif q_start i
      · rw [hcifdef, cuccaro_input_F_at_c_in]
      · intro j hj; rw [hcifdef, cuccaro_input_F_at_b]
        exact (cuccaro_target_val_testBit q_start g bits j (by omega)).symm
      · intro j hj; rw [hcifdef, cuccaro_input_F_at_a]
        exact (cuccaro_read_val_testBit q_start g bits j (by omega)).symm
    rw [hcarry]
    congr 1
    · congr 1
      rw [hcifdef, cuccaro_input_F_at_b]; exact (cuccaro_target_val_testBit q_start g bits i hi).symm
    · rw [hcifdef, cuccaro_input_F_at_a]; exact (cuccaro_read_val_testBit q_start g bits i hi).symm
  rw [hbit, ← cuccaro_target_val_testBit q_start
        (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) cif) bits i hi, hcif,
      Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  congr 1
  omega

end FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect

#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.condAdd_commute_overlay
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.condSub_commute_overlay
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.cuccaro_target_val_testBit
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.cuccaro_read_val_testBit
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.adder_target_val_general
