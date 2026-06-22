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

/-! ## §4. Decoder congruences (value depends only on the register bits) -/

theorem cuccaro_target_val_congr (q_start : Nat) (f f' : Nat → Bool) :
    ∀ bits, (∀ i, i < bits → f (q_start + 2 * i + 1) = f' (q_start + 2 * i + 1)) →
      cuccaro_target_val bits q_start f = cuccaro_target_val bits q_start f' := by
  intro bits
  induction bits with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      show cuccaro_target_val k q_start f + (if f (q_start + 2 * k + 1) then 2 ^ k else 0)
        = cuccaro_target_val k q_start f' + (if f' (q_start + 2 * k + 1) then 2 ^ k else 0)
      rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem cuccaro_read_val_congr (q_start : Nat) (f f' : Nat → Bool) :
    ∀ bits, (∀ i, i < bits → f (q_start + 2 * i + 2) = f' (q_start + 2 * i + 2)) →
      cuccaro_read_val bits q_start f = cuccaro_read_val bits q_start f' := by
  intro bits
  induction bits with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      show cuccaro_read_val k q_start f + (if f (q_start + 2 * k + 2) then 2 ^ k else 0)
        = cuccaro_read_val k q_start f' + (if f' (q_start + 2 * k + 2) then 2 ^ k else 0)
      rw [ih (fun i hi => h i (by omega)), h k (by omega)]

/-! ## §5. The general single-gadget step -/

private theorem mask_read_pos_ne (q_start i j : Nat) : q_start + 2 * i + 1 ≠ q_start + 2 * j + 2 := by omega

/-- **★ General conditional-add step. ★**  For ANY clean-ancilla input `f` (read register and carry
both zero) with the flag outside the workspace, the gadget adds `(if flag then N else 0)` to the
target (mod `2^bits`), restores the read register and carry to zero, and preserves all positions
outside the workspace. -/
theorem condAdd_step (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (hN : N < 2 ^ bits)
    (hread : ∀ j, j < bits → f (q_start + 2 * j + 2) = false)
    (hcarry : f q_start = false)
    (hdist : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hout : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f)
      = (cuccaro_target_val bits q_start f + (if f flagPos then N else 0)) % 2 ^ bits
    ∧ (∀ j, j < bits →
        Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f (q_start + 2 * j + 2)
          = false)
    ∧ Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f q_start = false
    ∧ (∀ p, (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) →
        Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f p = f p) := by
  have hPMother : ∀ (g : Nat → Bool) (p : Nat), (∀ i, i < bits → p ≠ q_start + 2 * i + 2) →
      Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) g p = g p :=
    fun g p hp => sqir_prepareMaskedConstRead_at_other bits q_start N flagPos p hp g
  -- the gadget unfolds to PM ; A ; PM
  have hgeq : Gate.applyNat (sqir_conditionalAddConstGate bits q_start N flagPos) f
      = Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos)
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f)) := by
    unfold sqir_conditionalAddConstGate
    simp only [Gate.applyNat_seq]
  -- stage-1 facts (g1 = applyNat PM f)
  have hg1_read : ∀ j, j < bits →
      Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f (q_start + 2 * j + 2)
        = (f flagPos && N.testBit j) := by
    intro j hj
    rw [sqir_prepareMaskedConstRead_at_read bits q_start N flagPos j hj f hdist, hread j hj]
    simp
  have hg1_target : ∀ i, i < bits →
      Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f (q_start + 2 * i + 1)
        = f (q_start + 2 * i + 1) := fun i _ => hPMother f _ (fun k _ => mask_read_pos_ne q_start i k)
  have hg1_carry : Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f q_start
        = false := by
    rw [hPMother f q_start (fun k _ => by omega), hcarry]
  have hg1_flag : Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f flagPos
        = f flagPos := hPMother f flagPos (fun k hk => by
          rcases hout with h | h
          · omega
          · exact hdist k hk)
  -- value of the read register after stage 1
  have hg1_readval : cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f)
        = (if f flagPos then N else 0) := by
    by_cases hflag : f flagPos = true
    · rw [cuccaro_read_val_eq_sum_when_bits_match bits q_start N _ (fun j hj => by
            rw [hg1_read j hj, hflag]; simp), Nat.mod_eq_of_lt hN, if_pos hflag]
    · rw [cuccaro_read_val_eq_sum_when_bits_match bits q_start 0 _ (fun j hj => by
            rw [hg1_read j hj]; simp [hflag]), Nat.zero_mod]
      simp [hflag]
  -- abbreviations
  set g1 := Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) f with hg1
  set g2 := Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g1 with hg2
  -- stage-2 facts
  have hg2_read : ∀ j, j < bits → g2 (q_start + 2 * j + 2) = (f flagPos && N.testBit j) := by
    intro j hj
    rw [hg2, cuccaro_n_bit_adder_full_a_restored bits q_start g1 j hj]
    exact hg1_read j hj
  have hg2_carry : g2 q_start = false := by
    rw [hg2, cuccaro_n_bit_adder_full_carry_in_restored bits q_start g1]
    exact hg1_carry
  have hg2_flag : g2 flagPos = f flagPos := by
    rw [hg2]
    rcases hout with h | h
    · rw [cuccaro_n_bit_adder_full_frame_below bits q_start g1 flagPos h]; exact hg1_flag
    · rw [cuccaro_n_bit_adder_full_frame_above bits q_start g1 flagPos h]; exact hg1_flag
  have hg2_target : cuccaro_target_val bits q_start g2
        = (cuccaro_target_val bits q_start f + (if f flagPos then N else 0)) % 2 ^ bits := by
    rw [hg2, adder_target_val_general, hg1_carry, hg1_readval,
        cuccaro_target_val_congr q_start g1 f bits (fun i hi => hg1_target i hi)]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- target value
    rw [hgeq,
        cuccaro_target_val_congr q_start
          (Gate.applyNat (sqir_prepareMaskedConstRead bits q_start N flagPos) g2) g2 bits
          (fun i _ => hPMother g2 _ (fun k _ => mask_read_pos_ne q_start i k))]
    exact hg2_target
  · -- read clean
    intro j hj
    rw [hgeq, sqir_prepareMaskedConstRead_at_read bits q_start N flagPos j hj g2 hdist,
        hg2_read j hj, hg2_flag]
    simp
  · -- carry clean
    rw [hgeq, hPMother g2 q_start (fun k _ => by omega)]
    exact hg2_carry
  · -- outside preserved
    intro p hp
    exact sqir_conditionalAddConstGate_preserves_outside bits q_start N flagPos p f
      (fun i hi => by rcases hp with h | h
                      · omega
                      · omega) hp

/-- **General unconditional add-constant step** (for the `2^(ℓ+m)` offset gadget). -/
theorem addConst_step (bits q_start c : Nat) (f : Nat → Bool)
    (hc : c < 2 ^ bits)
    (hread : ∀ j, j < bits → f (q_start + 2 * j + 2) = false)
    (hcarry : f q_start = false) :
    cuccaro_target_val bits q_start (Gate.applyNat (cuccaro_addConstGate bits q_start c) f)
      = (cuccaro_target_val bits q_start f + c) % 2 ^ bits
    ∧ (∀ j, j < bits → Gate.applyNat (cuccaro_addConstGate bits q_start c) f (q_start + 2 * j + 2) = false)
    ∧ Gate.applyNat (cuccaro_addConstGate bits q_start c) f q_start = false
    ∧ (∀ p, (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) →
        Gate.applyNat (cuccaro_addConstGate bits q_start c) f p = f p) := by
  have hPCRother : ∀ (g : Nat → Bool) (p : Nat), (∀ i, i < bits → p ≠ q_start + 2 * i + 2) →
      Gate.applyNat (cuccaro_prepareConstRead bits q_start c) g p = g p :=
    fun g p hp => cuccaro_prepareConstRead_at_other bits q_start c p hp g
  have hgeq : Gate.applyNat (cuccaro_addConstGate bits q_start c) f
      = Gate.applyNat (cuccaro_prepareConstRead bits q_start c)
          (Gate.applyNat (cuccaro_n_bit_adder_full bits q_start)
            (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f)) := by
    unfold cuccaro_addConstGate; simp only [Gate.applyNat_seq]
  have hg1_read : ∀ j, j < bits →
      Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f (q_start + 2 * j + 2) = c.testBit j := by
    intro j hj; rw [cuccaro_prepareConstRead_at_read bits q_start c j hj f, hread j hj]; simp
  have hg1_target : ∀ i, i < bits →
      Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f (q_start + 2 * i + 1)
        = f (q_start + 2 * i + 1) := fun i _ => hPCRother f _ (fun k _ => mask_read_pos_ne q_start i k)
  have hg1_carry : Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f q_start = false := by
    rw [hPCRother f q_start (fun k _ => by omega), hcarry]
  have hg1_readval : cuccaro_read_val bits q_start
        (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f) = c := by
    rw [cuccaro_read_val_eq_sum_when_bits_match bits q_start c _ (fun j hj => hg1_read j hj),
        Nat.mod_eq_of_lt hc]
  set g1 := Gate.applyNat (cuccaro_prepareConstRead bits q_start c) f with hg1
  set g2 := Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g1 with hg2
  have hg2_read : ∀ j, j < bits → g2 (q_start + 2 * j + 2) = c.testBit j := by
    intro j hj; rw [hg2, cuccaro_n_bit_adder_full_a_restored bits q_start g1 j hj]; exact hg1_read j hj
  have hg2_carry : g2 q_start = false := by
    rw [hg2, cuccaro_n_bit_adder_full_carry_in_restored bits q_start g1]; exact hg1_carry
  have hg2_target : cuccaro_target_val bits q_start g2 = (cuccaro_target_val bits q_start f + c) % 2 ^ bits := by
    rw [hg2, adder_target_val_general, hg1_carry, hg1_readval,
        cuccaro_target_val_congr q_start g1 f bits (fun i hi => hg1_target i hi)]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgeq, cuccaro_target_val_congr q_start
          (Gate.applyNat (cuccaro_prepareConstRead bits q_start c) g2) g2 bits
          (fun i _ => hPCRother g2 _ (fun k _ => mask_read_pos_ne q_start i k))]
    exact hg2_target
  · intro j hj
    rw [hgeq, cuccaro_prepareConstRead_at_read bits q_start c j hj g2, hg2_read j hj]; simp
  · rw [hgeq, hPCRother g2 q_start (fun k _ => by omega)]; exact hg2_carry
  · intro p hp
    rw [hgeq, hPCRother g2 p (fun i _ => by rcases hp with h | h
                                            · omega
                                            · omega)]
    rcases hp with h | h
    · rw [hg2, cuccaro_n_bit_adder_full_frame_below bits q_start g1 p h, hg1,
          hPCRother f p (fun i _ => by omega)]
    · rw [hg2, cuccaro_n_bit_adder_full_frame_above bits q_start g1 p h, hg1,
          hPCRother f p (fun i _ => by omega)]

/-- **General conditional-sub step** (for the `− d·2^i` gadgets): subtracts `(if flag then N else 0)`
mod `2^bits`, i.e. adds the two's complement `2^bits − N`. -/
theorem condSub_step (bits q_start N flagPos : Nat) (f : Nat → Bool)
    (hN0 : 0 < N) (hN : N ≤ 2 ^ bits)
    (hread : ∀ j, j < bits → f (q_start + 2 * j + 2) = false)
    (hcarry : f q_start = false)
    (hdist : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hout : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f)
      = (cuccaro_target_val bits q_start f + (if f flagPos then 2 ^ bits - N else 0)) % 2 ^ bits
    ∧ (∀ j, j < bits →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f (q_start + 2 * j + 2)
          = false)
    ∧ Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f q_start = false
    ∧ (∀ p, (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) →
        Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) f p = f p) := by
  unfold sqir_conditionalSubConstGate
  exact condAdd_step bits q_start (2 ^ bits - N) flagPos f (Nat.sub_lt (Nat.two_pow_pos bits) hN0)
    hread hcarry hdist hout

/-! ## §6. Accumulation fold over the gadget list -/

/-- The ancilla (read register + carry) is all zero. -/
def CleanState (bits q_start : Nat) (f : Nat → Bool) : Prop :=
  (∀ j, j < bits → f (q_start + 2 * j + 2) = false) ∧ f q_start = false

/-- A gadget `g` is a clean step with target-delta `δ`: on any clean state it adds `δ f` to the
target (mod `2^bits`), keeps the ancilla clean, and preserves all positions outside the workspace. -/
def CleanStep (bits q_start : Nat) (g : Gate) (δ : (Nat → Bool) → Nat) : Prop :=
  ∀ f, CleanState bits q_start f →
    (cuccaro_target_val bits q_start (Gate.applyNat g f)
        = (cuccaro_target_val bits q_start f + δ f) % 2 ^ bits)
    ∧ CleanState bits q_start (Gate.applyNat g f)
    ∧ (∀ p, (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) → Gate.applyNat g f p = f p)

/-- `δ` depends only on the positions outside the workspace (where flag qubits live). -/
def OutsideStable (bits q_start : Nat) (δ : (Nat → Bool) → Nat) : Prop :=
  ∀ f f', (∀ p, (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) → f p = f' p) → δ f = δ f'

theorem condAdd_cleanStep (bits q_start N flagPos : Nat) (hN : N < 2 ^ bits)
    (hdist : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hout : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    CleanStep bits q_start (sqir_conditionalAddConstGate bits q_start N flagPos)
      (fun f => if f flagPos then N else 0) := by
  intro f hf
  obtain ⟨ht, hr, hc, ho⟩ := condAdd_step bits q_start N flagPos f hN hf.1 hf.2 hdist hout
  exact ⟨ht, ⟨hr, hc⟩, ho⟩

theorem condSub_cleanStep (bits q_start N flagPos : Nat) (hN0 : 0 < N) (hN : N ≤ 2 ^ bits)
    (hdist : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (hout : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    CleanStep bits q_start (sqir_conditionalSubConstGate bits q_start N flagPos)
      (fun f => if f flagPos then 2 ^ bits - N else 0) := by
  intro f hf
  obtain ⟨ht, hr, hc, ho⟩ := condSub_step bits q_start N flagPos f hN0 hN hf.1 hf.2 hdist hout
  exact ⟨ht, ⟨hr, hc⟩, ho⟩

theorem addConst_cleanStep (bits q_start c : Nat) (hc : c < 2 ^ bits) :
    CleanStep bits q_start (cuccaro_addConstGate bits q_start c) (fun _ => c) := by
  intro f hf
  obtain ⟨ht, hr, hc', ho⟩ := addConst_step bits q_start c f hc hf.1 hf.2
  exact ⟨ht, ⟨hr, hc'⟩, ho⟩

theorem condAdd_outsideStable (bits q_start N flagPos : Nat)
    (hout : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    OutsideStable bits q_start (fun f => if f flagPos then N else 0) := fun f f' h => by
  show (if f flagPos then N else 0) = (if f' flagPos then N else 0); rw [h flagPos hout]

theorem condSub_outsideStable (bits q_start N flagPos : Nat)
    (hout : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos) :
    OutsideStable bits q_start (fun f => if f flagPos then 2 ^ bits - N else 0) := fun f f' h => by
  show (if f flagPos then 2 ^ bits - N else 0) = (if f' flagPos then 2 ^ bits - N else 0)
  rw [h flagPos hout]

theorem const_outsideStable (bits q_start c : Nat) :
    OutsideStable bits q_start (fun _ => c) := fun _ _ _ => rfl

/-- **★ The accumulation fold. ★**  Folding a list of clean steps (with outside-stable deltas) over a
clean state adds the sum of the deltas to the target (mod `2^bits`), keeps the ancilla clean, and
preserves the workspace exterior. -/
theorem cleanStep_fold (bits q_start : Nat) :
    ∀ (gds : List (Gate × ((Nat → Bool) → Nat))),
      (∀ gd ∈ gds, CleanStep bits q_start gd.1 gd.2) →
      (∀ gd ∈ gds, OutsideStable bits q_start gd.2) →
      ∀ f, CleanState bits q_start f →
        (cuccaro_target_val bits q_start
            (Gate.applyNat ((gds.map Prod.fst).foldr Gate.seq Gate.I) f)
          = (cuccaro_target_val bits q_start f + (gds.map (fun gd => gd.2 f)).sum) % 2 ^ bits)
        ∧ CleanState bits q_start (Gate.applyNat ((gds.map Prod.fst).foldr Gate.seq Gate.I) f)
        ∧ (∀ p, (p < q_start ∨ q_start + 2 * bits + 1 ≤ p) →
            Gate.applyNat ((gds.map Prod.fst).foldr Gate.seq Gate.I) f p = f p) := by
  intro gds
  induction gds with
  | nil =>
      intro _ _ f hf
      refine ⟨?_, hf, fun p _ => rfl⟩
      simp only [List.map_nil, List.foldr_nil, List.sum_nil, Nat.add_zero]
      show cuccaro_target_val bits q_start f = cuccaro_target_val bits q_start f % 2 ^ bits
      rw [Nat.mod_eq_of_lt (cuccaro_target_val_lt bits q_start f)]
  | cons gd rest ih =>
      intro hstep hstable f hf
      obtain ⟨hg_t, hg_clean, hg_out⟩ := hstep gd (List.mem_cons_self ..) f hf
      obtain ⟨hr_t, hr_clean, hr_out⟩ :=
        ih (fun g' hg' => hstep g' (List.mem_cons_of_mem _ hg'))
           (fun g' hg' => hstable g' (List.mem_cons_of_mem _ hg'))
           (Gate.applyNat gd.1 f) hg_clean
      have hfold : Gate.applyNat (((gd :: rest).map Prod.fst).foldr Gate.seq Gate.I) f
          = Gate.applyNat ((rest.map Prod.fst).foldr Gate.seq Gate.I) (Gate.applyNat gd.1 f) := by
        show Gate.applyNat (Gate.seq gd.1 ((rest.map Prod.fst).foldr Gate.seq Gate.I)) f = _
        rw [Gate.applyNat_seq]
      refine ⟨?_, ?_, ?_⟩
      · rw [hfold, hr_t, hg_t]
        have hsum_eq : (rest.map (fun g' => g'.2 (Gate.applyNat gd.1 f))).sum
            = (rest.map (fun g' => g'.2 f)).sum :=
          congrArg List.sum (List.map_congr_left (fun g' hg' =>
            hstable g' (List.mem_cons_of_mem _ hg') (Gate.applyNat gd.1 f) f hg_out))
        rw [hsum_eq, Nat.mod_add_mod, List.map_cons, List.sum_cons]
        congr 1; ring
      · rw [hfold]; exact hr_clean
      · intro p hp; rw [hfold, hr_out p hp, hg_out p hp]

end FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect

#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.condAdd_commute_overlay
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.condSub_commute_overlay
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.cuccaro_target_val_testBit
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.cuccaro_read_val_testBit
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.adder_target_val_general
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.condAdd_step
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.addConst_step
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.condSub_step
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleCorrect.cleanStep_fold
