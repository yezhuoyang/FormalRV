/-
  FormalRV.Arithmetic.Adder.Cuccaro
  ─────────────────────────────────
  The exact-budget full Cuccaro ripple adder, packaged as an instance of
  the layout-parametric `Adder` interface (`FormalRV/Arithmetic/Adder.lean`).

  Layout (width `n`, base offset `q`, span `2n+1`):
  - `q + 0`        : carry-in qubit (`ancClean := f q = false`).
  - `q + 2i + 1`   : augend / running-sum bit `i` (modified in place).
  - `q + 2i + 2`   : addend bit `i` (restored).

  All five interface obligations are discharged from the symbolic and
  decoded Cuccaro correctness theorems already proved in
  `Cuccaro/CuccaroFull.lean` and `Cuccaro/CuccaroDecoded.lean`.
-/
import FormalRV.Arithmetic.Adder
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Bridge: `decodeReg` over the Cuccaro layout = the Cuccaro decoders. -/

/-- `decodeReg (fun i => q + 2i + 1)` agrees with the `cuccaro_target_val`
recursive decoder.  Both read LSB-first the qubits `q + 2i + 1`. -/
theorem decodeReg_augend_eq_target (n q : Nat) (f : Nat → Bool) :
    decodeReg (fun i => q + 2 * i + 1) n f = cuccaro_target_val n q f := by
  unfold decodeReg
  have key : ∀ (m : Nat) (init : Nat),
      (List.range m).foldl
          (fun acc i => acc + if f (q + 2 * i + 1) then 2 ^ i else 0) init
        = init + cuccaro_target_val m q f := by
    intro m
    induction m with
    | zero => intro init; simp [cuccaro_target_val]
    | succ k ih =>
        intro init
        rw [List.range_succ, List.foldl_append, ih init]
        simp only [List.foldl_cons, List.foldl_nil, cuccaro_target_val]
        ring
  have := key n 0
  simpa using this

/-- `decodeReg (fun i => q + 2i + 2)` agrees with the `cuccaro_read_val`
recursive decoder.  Both read LSB-first the qubits `q + 2i + 2`. -/
theorem decodeReg_addend_eq_read (n q : Nat) (f : Nat → Bool) :
    decodeReg (fun i => q + 2 * i + 2) n f = cuccaro_read_val n q f := by
  unfold decodeReg
  have key : ∀ (m : Nat) (init : Nat),
      (List.range m).foldl
          (fun acc i => acc + if f (q + 2 * i + 2) then 2 ^ i else 0) init
        = init + cuccaro_read_val m q f := by
    intro m
    induction m with
    | zero => intro init; simp [cuccaro_read_val]
    | succ k ih =>
        intro init
        rw [List.range_succ, List.foldl_append, ih init]
        simp only [List.foldl_cons, List.foldl_nil, cuccaro_read_val]
        ring
  have := key n 0
  simpa using this

/-! ## Per-bit extraction of the decoders (converse direction). -/

/-- Each target bit `i < bits` of `cuccaro_target_val bits q f` reads back the
state bit at `q + 2i + 1`.  (Self-contained converse to
`cuccaro_target_val_eq_sum_when_bits_match`, by uniqueness of binary digits.) -/
theorem cuccaro_target_val_testBit
    (bits q : Nat) (f : Nat → Bool) (i : Nat) (hi : i < bits) :
    (cuccaro_target_val bits q f).testBit i = f (q + 2 * i + 1) := by
  induction bits generalizing i with
  | zero => omega
  | succ n ih =>
    have hTn_lt : cuccaro_target_val n q f < 2 ^ n := cuccaro_target_val_lt n q f
    -- cuccaro_target_val (n+1) = cuccaro_target_val n + (if f(q+2n+1) then 2^n else 0)
    by_cases hi_eq : i = n
    · subst hi_eq
      unfold cuccaro_target_val
      by_cases hv : f (q + 2 * i + 1)
      · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_eq,
            Nat.testBit_lt_two_pow hTn_lt, hv]; rfl
      · rw [if_neg hv, Nat.add_zero, Nat.testBit_lt_two_pow hTn_lt]
        cases hh : f (q + 2 * i + 1)
        · rfl
        · exact absurd hh hv
    · have hi_lt : i < n := by omega
      unfold cuccaro_target_val
      by_cases hv : f (q + 2 * n + 1)
      · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_gt hi_lt, ih i hi_lt]
      · rw [if_neg hv, Nat.add_zero, ih i hi_lt]

/-- Each read bit `i < bits` of `cuccaro_read_val bits q f` reads back the state
bit at `q + 2i + 2`. -/
theorem cuccaro_read_val_testBit
    (bits q : Nat) (f : Nat → Bool) (i : Nat) (hi : i < bits) :
    (cuccaro_read_val bits q f).testBit i = f (q + 2 * i + 2) := by
  induction bits generalizing i with
  | zero => omega
  | succ n ih =>
    have hTn_lt : cuccaro_read_val n q f < 2 ^ n := cuccaro_read_val_lt n q f
    by_cases hi_eq : i = n
    · subst hi_eq
      unfold cuccaro_read_val
      by_cases hv : f (q + 2 * i + 2)
      · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_eq,
            Nat.testBit_lt_two_pow hTn_lt, hv]; rfl
      · rw [if_neg hv, Nat.add_zero, Nat.testBit_lt_two_pow hTn_lt]
        cases hh : f (q + 2 * i + 2)
        · rfl
        · exact absurd hh hv
    · have hi_lt : i < n := by omega
      unfold cuccaro_read_val
      by_cases hv : f (q + 2 * n + 2)
      · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_gt hi_lt, ih i hi_lt]
      · rw [if_neg hv, Nat.add_zero, ih i hi_lt]

/-! ## Carry / sum-bit extensionality (carries depend only on lower indices). -/

/-- `Adder.carry b₀ k f g` consults `f`/`g` only at indices `< k`, so it agrees
under any pair of streams that match below `k`. -/
theorem Adder.carry_ext_below
    (b₀ : Bool) (k : Nat) (f g f' g' : Nat → Bool)
    (hf : ∀ j, j < k → f j = f' j) (hg : ∀ j, j < k → g j = g' j) :
    Adder.carry b₀ k f g = Adder.carry b₀ k f' g' := by
  induction k with
  | zero => rfl
  | succ m ih =>
      rw [Adder.carry_succ, Adder.carry_succ,
          ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)),
          hf m (by omega), hg m (by omega)]

/-! ## The Cuccaro adder as an `Adder` instance. -/

/-- **The exact-budget Cuccaro ripple adder, as an `Adder`.**
The augend (running-sum) register lives at `q + 2i + 1`, the addend
register at `q + 2i + 2`, with the carry-in ancilla at `q` required clean
(`= false`). -/
def cuccaroAdder : Adder where
  span      := fun n => 2 * n + 1
  augendIdx := fun q i => q + 2 * i + 1
  addendIdx := fun q i => q + 2 * i + 2
  ancClean  := fun f _ q => f q = false
  circuit   := fun n q => cuccaro_n_bit_adder_full n q
  sumCorrect := by
    intro n q f hclean
    rw [decodeReg_augend_eq_target, decodeReg_augend_eq_target,
        decodeReg_addend_eq_read]
    set A := cuccaro_target_val n q f with hA
    set B := cuccaro_read_val n q f with hB
    have hAlt : A < 2 ^ n := by rw [hA]; exact cuccaro_target_val_lt n q f
    have hBlt : B < 2 ^ n := by rw [hB]; exact cuccaro_read_val_lt n q f
    -- Decode the output via the generic bit-stream lemma with S := A + B.
    apply cuccaro_target_val_eq_sum_when_bits_match n q (A + B)
    intro i hi
    -- Symbolic sum-bit formula (conjunct 2 of `cuccaro_n_bit_adder_full_correct`).
    rw [(cuccaro_n_bit_adder_full_correct n q f).2.1 i hi]
    -- Bridge `cuccaro_carry` → `Adder.carry`; carry-in is `f q = false`.
    rw [cuccaro_carry_eq_Adder_carry, hclean]
    -- The carry only consults indices `< i ≤ n`, where the `f`-streams agree
    -- with `A.testBit` / `B.testBit` (by the converse extraction lemmas).
    have hfb : ∀ j, j < i → f (q + 2 * j + 1) = A.testBit j := fun j hj =>
      (cuccaro_target_val_testBit n q f j (by omega)).symm
    have hga : ∀ j, j < i → f (q + 2 * j + 2) = B.testBit j := fun j hj =>
      (cuccaro_read_val_testBit n q f j (by omega)).symm
    rw [Adder.carry_ext_below false i
          (fun j => f (q + 2 * j + 1)) (fun j => f (q + 2 * j + 2))
          (fun j => A.testBit j) (fun j => B.testBit j) hfb hga]
    -- Replace the two outer (index-`i`) bits as well.
    rw [(cuccaro_target_val_testBit n q f i hi).symm,
        (cuccaro_read_val_testBit n q f i hi).symm]
    -- Now the goal is exactly `Adder.sumfb false A.testBit B.testBit i`.
    have h := Adder.sumfb_eq_testBit_add_gen false A B i
    unfold Adder.sumfb at h
    simpa [Bool.toNat] using h
  addendRestored := by
    intro n q f _ i hi
    exact (cuccaro_n_bit_adder_full_correct n q f).2.2 i hi
  ancRestored := by
    intro n q f hclean
    show Gate.applyNat (cuccaro_n_bit_adder_full n q) f q = false
    rw [(cuccaro_n_bit_adder_full_correct n q f).1]
    exact hclean
  frame := by
    intro n q f p hp
    unfold inBlock at hp
    push Not at hp
    by_cases hlt : p < q
    · exact cuccaro_n_bit_adder_full_frame_below n q f p hlt
    · have hge : q + 2 * n + 1 ≤ p := by
        have := hp (Nat.not_lt.mp hlt); omega
      exact cuccaro_n_bit_adder_full_frame_above n q f p hge
  wellTyped := by
    intro n q
    exact cuccaro_n_bit_adder_full_wellTyped n q (q + (2 * n + 1)) (by omega)
  augendIdx_inBlock := by
    intro n q i hi; unfold inBlock; omega
  addendIdx_inBlock := by
    intro n q i hi; unfold inBlock; omega
  addendIdx_inj := by
    intro q i j h; omega
  augend_addend_disjoint := by
    intro q i j; omega
  ancClean_ext := by
    intro n q f g hagree hclean
    show g q = false
    rw [← hagree q (by intro i hi; constructor <;> omega)]
    exact hclean

end FormalRV.BQAlgo
