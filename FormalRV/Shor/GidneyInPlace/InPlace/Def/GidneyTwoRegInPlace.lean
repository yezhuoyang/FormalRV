/-
  FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  ──────────────────────────────────────────────────
  The faithful two-register in-place coset multiplier GATE — DEFINITION +
  WELL-TYPEDNESS + the reverse-leg cancellation guard ONLY.  NO arithmetic /
  coset / deviation correctness (deferred).

  Construction (Gidney 1905.07682 `times_equal_exp_mod`):
    pass1 :  b += a·k        (forward product-add: accumulator b, multiplicand a)
    pass2 :  a += b·kInv      (forward product-add: accumulator a, multiplicand b)
    gate  :  pass1 ; Gate.reverse pass2
  Running `Gate.reverse pass2` AFTER pass1 performs `a -= b·kInv` (the uncompute leg)
  — but this is NOT asserted by the word "subtract"; it is pinned by genuine
  reversibility (`applyNat_reverse_cancel`, see `gidneyTwoReg_reverse_leg_cancel`).
  The logical relabel `(a,b) := (b,a)` is NOT a physical gate — it is an output-decoder
  convention represented in the spec, never inside `Gate.seq`.

  Faithful `cosetDim = 2+2w+3·bits` layout (see `ProductAddLayout`/`ProductAddArith`):
    register a @ `1+2w`, register b @ `1+2w+bits`, shared addend-temp @ `1+2w+2bits`,
    carry @ `1+2w+3bits`.  So pass1 has acc=b, mult=a; pass2 has acc=a, mult=b.
-/
import FormalRV.Shor.GidneyInPlace.Adder.Def.ProductAddWrapper
import FormalRV.Shor.GidneyInPlace.Adder.Spec.ProductAddArith
import FormalRV.Shor.GidneyInPlace.Gate.Def.GateReversible
import FormalRV.Shor.GidneyInPlace.Gate.Def.GatePerm

namespace FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit (encodeReg decodeReg_eq_zero decodeReg_eq_mod_of_testBit)
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper
  (gidneyProductAddTOf gidneyProductAdd_pass1_wellTyped gidneyProductAdd_pass2_wellTyped)
open FormalRV.Shor.GidneyInPlace.ProductAddArith
  (RelocStepInv gidneyProductAddTOf_state gidneyProductAddTOf_decode)

/-! ## §1. The two passes and the in-place gate. -/

/-- Pass 1 (`b += a·k`): accumulator `b @ 1+2w+bits`, multiplicand `a @ 1+2w`. -/
def pass1 (w bits : Nat) (TfamK : Nat → Nat → Nat) (numWin : Nat) : Gate :=
  gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin

/-- Pass 2 (`a += b·kInv`, FORWARD — it is reversed inside the gate): accumulator
    `a @ 1+2w`, multiplicand `b @ 1+2w+bits`. -/
def pass2 (w bits : Nat) (TfamKinv : Nat → Nat → Nat) (numWin : Nat) : Gate :=
  gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin

/-- **The faithful two-register in-place coset multiply gate**: `pass1 ; reverse pass2`.
    (Logical relabel is interface-level, NOT here.) -/
def gidneyTwoRegInPlaceCosetMul (w bits : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) : Gate :=
  Gate.seq (pass1 w bits TfamK numWin)
           (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin))

/-- **Structure guard (`rfl`).**  Pins that pass 2 is REVERSED and pass 1 is FORWARD,
    so no later proof can confuse the two legs. -/
theorem gidneyTwoRegInPlaceCosetMul_unfold (w bits : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) :
    gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin
      = Gate.seq (pass1 w bits TfamK numWin)
                 (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) := rfl

/-! ## §2. Well-typedness (the only correctness discharged here). -/

/-- **The in-place gate is well-typed at `cosetDim = 2+2w+3·bits`.**  `seq` of pass 1
    (forward, `gidneyProductAdd_pass1_wellTyped`) and the reverse of pass 2
    (`reverse_wellTyped` of `gidneyProductAdd_pass2_wellTyped`). -/
theorem gidneyTwoRegInPlaceCosetMul_wellTyped (w bits : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (2 + 2 * w + 3 * bits)
      (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) :=
  ⟨gidneyProductAdd_pass1_wellTyped w bits TfamK numWin hw hbits,
   GatePerm.reverse_wellTyped (pass2 w bits TfamKinv numWin) (2 + 2 * w + 3 * bits)
     (gidneyProductAdd_pass2_wellTyped w bits TfamKinv numWin hw hbits)⟩

/-! ## §3. The reverse-leg guard: cancellation by genuine reversibility (NOT "subtract"). -/

/-- **Reverse-leg cancellation.**  `reverse pass2` maps any post-state `applyNat pass2 f`
    back to `f` — pure reversibility (`applyNat_reverse_cancel` instantiated for `pass2`,
    using its well-typedness).  This is the ONLY sense in which the uncompute leg
    "undoes" pass 2; later correctness must pin its action via THIS lemma, never via an
    informal "reverse = subtraction". -/
theorem gidneyTwoReg_reverse_leg_cancel (w bits : Nat) (TfamKinv : Nat → Nat → Nat)
    (numWin : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (f : Nat → Bool) :
    Gate.applyNat (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin))
        (Gate.applyNat (pass2 w bits TfamKinv numWin) f) = f :=
  GateReversible.applyNat_reverse_cancel (pass2 w bits TfamKinv numWin) (2 + 2 * w + 3 * bits)
    (gidneyProductAdd_pass2_wellTyped w bits TfamKinv numWin hw hbits) f

/-! ## §4. Basis-level two-register correctness (bare inverse-sum hypothesis). -/

/-- The cleared post-state: `pass1 g` with register `a @ 1+2w` zeroed. -/
def basisFinal0 (w bits : Nat) (TfamK : Nat → Nat → Nat) (numWin : Nat) (g : Nat → Bool) :
    Nat → Bool :=
  fun p => if 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + bits then false
           else Gate.applyNat (pass1 w bits TfamK numWin) g p

/-- Footprint cover for pass 1 (acc=b@1+2w+bits, mult=a@1+2w, packed). -/
private theorem hcov1 (w bits numWin : Nat) (_hbits : numWin * w = bits) : ∀ q,
    1 + 2 * w + bits ≤ q → q < 1 + 2 * w + 2 * bits + bits + 1 →
    (∃ i, i < bits ∧ q = 1 + 2 * w + bits + i) ∨ (∃ i, i < bits ∧ q = 1 + 2 * w + 2 * bits + i)
      ∨ q = 1 + 2 * w + 2 * bits + bits ∨ (∃ i, i < numWin * w ∧ q = 1 + 2 * w + i) := by
  intro q h1 h2
  by_cases hc : q < 1 + 2 * w + 2 * bits
  · exact Or.inl ⟨q - (1 + 2 * w + bits), by omega, by omega⟩
  · by_cases hc2 : q < 1 + 2 * w + 3 * bits
    · exact Or.inr (Or.inl ⟨q - (1 + 2 * w + 2 * bits), by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl (by omega)))

/-- Footprint cover for pass 2 (acc=a@1+2w, mult=b@1+2w+bits, gap = b). -/
private theorem hcov2 (w bits numWin : Nat) (hbits : numWin * w = bits) : ∀ q,
    1 + 2 * w ≤ q → q < 1 + 2 * w + 2 * bits + bits + 1 →
    (∃ i, i < bits ∧ q = 1 + 2 * w + i) ∨ (∃ i, i < bits ∧ q = 1 + 2 * w + 2 * bits + i)
      ∨ q = 1 + 2 * w + 2 * bits + bits ∨ (∃ i, i < numWin * w ∧ q = 1 + 2 * w + bits + i) := by
  intro q h1 h2
  by_cases hc : q < 1 + 2 * w + bits
  · exact Or.inl ⟨q - (1 + 2 * w), by omega, by omega⟩
  · by_cases hc2 : q < 1 + 2 * w + 2 * bits
    · exact Or.inr (Or.inr (Or.inr ⟨q - (1 + 2 * w + bits), by omega, by omega⟩))
    · by_cases hc3 : q < 1 + 2 * w + 3 * bits
      · exact Or.inr (Or.inl ⟨q - (1 + 2 * w + 2 * bits), by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl (by omega)))

/-- **Full post-state — the gate maps the canonical input to `basisFinal0`** (register a
    cleared, register b = P1, scratch restored).  The reusable WHOLE-STATE core: the
    decodes and the coset-state lift both build on this. -/
theorem gidneyTwoRegInPlace_maps_to_final0 (w bits numWin : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (x : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (g : Nat → Bool)
    (hg : RelocStepInv w bits numWin x (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) 0 g)
    (hInvSum : (∑ k ∈ Finset.range numWin, TfamKinv k (WindowedArith.window w
        ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits) k)) % 2 ^ bits = x) :
    Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g
      = basisFinal0 w bits TfamK numWin g := by
  set P1 := (∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits with hP1
  have hp1 : ∀ p, Gate.applyNat (pass1 w bits TfamK numWin) g p
      = if 1 + 2 * w + bits ≤ p ∧ p < 1 + 2 * w + bits + bits then P1.testBit (p - (1 + 2 * w + bits))
        else g p := fun p =>
    gidneyProductAddTOf_state w bits numWin TfamK x (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w)
      hw hbits (by omega) (by omega) (by omega) (by omega)
      (fun f' i hi => relocated_pass1_multiplicand_preserved w bits f' i (by omega))
      (hcov1 w bits numWin hbits) g hg p
  have hfin : RelocStepInv w bits numWin P1 (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) 0
      (basisFinal0 w bits TfamK numWin g) := by
    obtain ⟨hgc, hg1, hg2, hg3, hg4, hg5, _⟩ := hg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (if _ then _ else _) = true
      rw [if_neg (by unfold ulookup_ctrl_idx; omega), hp1, if_neg (by unfold ulookup_ctrl_idx; omega)]
      exact hgc
    · intro i hi; show (if _ then _ else _) = false
      rw [if_neg (by unfold ulookup_address_idx; omega), hp1,
          if_neg (by unfold ulookup_address_idx; omega)]
      exact hg1 i hi
    · intro i hi; show (if _ then _ else _) = false
      rw [if_neg (by unfold ulookup_and_idx; omega), hp1, if_neg (by unfold ulookup_and_idx; omega)]
      exact hg2 i hi
    · intro i hi; show (if _ then _ else _) = false
      rw [if_neg (by omega), hp1, if_neg (by omega)]
      exact hg3 i hi
    · show (if _ then _ else _) = false
      rw [if_neg (by omega), hp1, if_neg (by omega)]
      exact hg4
    · intro i hi; show (if _ then _ else _) = encodeReg (1 + 2 * w + bits) (numWin * w) P1 _
      rw [if_neg (by omega), hp1, if_pos (by omega)]
      show P1.testBit (1 + 2 * w + bits + i - (1 + 2 * w + bits)) = _
      rw [show 1 + 2 * w + bits + i - (1 + 2 * w + bits) = i from by omega]
      unfold encodeReg; rw [if_pos (by omega)]
      rw [show 1 + 2 * w + bits + i - (1 + 2 * w + bits) = i from by omega]
    · show decodeReg _ bits (basisFinal0 w bits TfamK numWin g) = 0 % 2 ^ bits
      rw [Nat.zero_mod]
      apply decodeReg_eq_zero
      intro i hi; show (if _ then _ else _) = false; rw [if_pos (by omega)]
  have hp2 : ∀ p, Gate.applyNat (pass2 w bits TfamKinv numWin) (basisFinal0 w bits TfamK numWin g) p
      = if 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + bits
        then ((∑ k ∈ Finset.range numWin, TfamKinv k (WindowedArith.window w P1 k)) % 2 ^ bits).testBit (p - (1 + 2 * w))
        else basisFinal0 w bits TfamK numWin g p := fun p =>
    gidneyProductAddTOf_state w bits numWin TfamKinv P1 (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits)
      hw hbits (by omega) (by omega) (by omega) (by omega)
      (fun f' i hi => relocated_pass2_multiplicand_preserved w bits f' i (by omega))
      (hcov2 w bits numWin hbits) (basisFinal0 w bits TfamK numWin g) hfin p
  have heq : Gate.applyNat (pass2 w bits TfamKinv numWin) (basisFinal0 w bits TfamK numWin g)
      = Gate.applyNat (pass1 w bits TfamK numWin) g := by
    obtain ⟨_, _, _, _, _, hgy, _⟩ := hg
    funext p
    rw [hp2 p]
    by_cases hpa : 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + bits
    · rw [if_pos hpa, hInvSum, hp1 p, if_neg (by omega)]
      have := hgy (p - (1 + 2 * w)) (by omega)
      rw [show 1 + 2 * w + (p - (1 + 2 * w)) = p from by omega] at this
      rw [this]; unfold encodeReg
      rw [if_pos (by omega)]
    · rw [if_neg hpa]; show basisFinal0 w bits TfamK numWin g p = _
      unfold basisFinal0; rw [if_neg hpa]
  rw [gidneyTwoRegInPlaceCosetMul_unfold, Gate.applyNat_seq, ← heq]
  exact gidneyTwoReg_reverse_leg_cancel w bits TfamKinv numWin hw hbits
    (basisFinal0 w bits TfamK numWin g)

/-- **Basis-level two-register in-place correctness** (Option 1: bare inverse-sum hyp).
    Input `g`: register `a @ 1+2w` = `x`, register `b @ 1+2w+bits` = `0`, scratch clean
    (`= RelocStepInv … x (1+2w+bits) (1+2w+2bits) (1+2w) 0 g`, pass-1's invariant).
    Given `hInvSum` (pass-2's table sum on `P1` returns `x`), the gate `pass1 ; reverse pass2`
    leaves register `a = 0` and register `b = P1 = (∑ₖ TfamK k (window w x k)) mod 2^bits`.
    NO modular/coset number theory — `hInvSum` is the sole arithmetic input. -/
theorem gidneyTwoRegInPlace_basis_correct (w bits numWin : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (x : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (g : Nat → Bool)
    (hg : RelocStepInv w bits numWin x (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) 0 g)
    (hInvSum : (∑ k ∈ Finset.range numWin, TfamKinv k (WindowedArith.window w
        ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits) k)) % 2 ^ bits = x) :
    decodeReg (fun i => 1 + 2 * w + i) bits
        (Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g) = 0
    ∧ decodeReg (fun i => 1 + 2 * w + bits + i) bits
        (Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g)
      = (∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits := by
  set P1 := (∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits with hP1
  have hP1lt : P1 < 2 ^ bits := by rw [hP1]; exact Nat.mod_lt _ (by positivity)
  have hp1 : ∀ p, Gate.applyNat (pass1 w bits TfamK numWin) g p
      = if 1 + 2 * w + bits ≤ p ∧ p < 1 + 2 * w + bits + bits then P1.testBit (p - (1 + 2 * w + bits))
        else g p := fun p =>
    gidneyProductAddTOf_state w bits numWin TfamK x (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w)
      hw hbits (by omega) (by omega) (by omega) (by omega)
      (fun f' i hi => relocated_pass1_multiplicand_preserved w bits f' i (by omega))
      (hcov1 w bits numWin hbits) g hg p
  -- final0 satisfies pass-2's invariant (acc = a @ 1+2w, mult = b @ 1+2w+bits = P1).
  have hfin : RelocStepInv w bits numWin P1 (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) 0
      (basisFinal0 w bits TfamK numWin g) := by
    obtain ⟨hgc, hg1, hg2, hg3, hg4, hg5, _⟩ := hg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (if _ then _ else _) = true
      rw [if_neg (by unfold ulookup_ctrl_idx; omega), hp1, if_neg (by unfold ulookup_ctrl_idx; omega)]
      exact hgc
    · intro i hi; show (if _ then _ else _) = false
      rw [if_neg (by unfold ulookup_address_idx; omega), hp1,
          if_neg (by unfold ulookup_address_idx; omega)]
      exact hg1 i hi
    · intro i hi; show (if _ then _ else _) = false
      rw [if_neg (by unfold ulookup_and_idx; omega), hp1, if_neg (by unfold ulookup_and_idx; omega)]
      exact hg2 i hi
    · intro i hi; show (if _ then _ else _) = false
      rw [if_neg (by omega), hp1, if_neg (by omega)]
      exact hg3 i hi
    · show (if _ then _ else _) = false
      rw [if_neg (by omega), hp1, if_neg (by omega)]
      exact hg4
    · intro i hi; show (if _ then _ else _) = encodeReg (1 + 2 * w + bits) (numWin * w) P1 _
      rw [if_neg (by omega), hp1, if_pos (by omega)]
      show P1.testBit (1 + 2 * w + bits + i - (1 + 2 * w + bits)) = _
      rw [show 1 + 2 * w + bits + i - (1 + 2 * w + bits) = i from by omega]
      unfold encodeReg; rw [if_pos (by omega)]
      rw [show 1 + 2 * w + bits + i - (1 + 2 * w + bits) = i from by omega]
    · show decodeReg _ bits (basisFinal0 w bits TfamK numWin g) = 0 % 2 ^ bits
      rw [Nat.zero_mod]
      apply decodeReg_eq_zero
      intro i hi; show (if _ then _ else _) = false; rw [if_pos (by omega)]
  -- pass-2 full-state form on final0 (acc = a @ 1+2w).
  have hp2 : ∀ p, Gate.applyNat (pass2 w bits TfamKinv numWin) (basisFinal0 w bits TfamK numWin g) p
      = if 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + bits
        then ((∑ k ∈ Finset.range numWin, TfamKinv k (WindowedArith.window w P1 k)) % 2 ^ bits).testBit (p - (1 + 2 * w))
        else basisFinal0 w bits TfamK numWin g p := fun p =>
    gidneyProductAddTOf_state w bits numWin TfamKinv P1 (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits)
      hw hbits (by omega) (by omega) (by omega) (by omega)
      (fun f' i hi => relocated_pass2_multiplicand_preserved w bits f' i (by omega))
      (hcov2 w bits numWin hbits) (basisFinal0 w bits TfamK numWin g) hfin p
  -- pass2 final0 = pass1 g.
  have heq : Gate.applyNat (pass2 w bits TfamKinv numWin) (basisFinal0 w bits TfamK numWin g)
      = Gate.applyNat (pass1 w bits TfamK numWin) g := by
    obtain ⟨_, _, _, _, _, hgy, _⟩ := hg
    funext p
    rw [hp2 p]
    by_cases hpa : 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + bits
    · rw [if_pos hpa, hInvSum, hp1 p, if_neg (by omega)]
      have := hgy (p - (1 + 2 * w)) (by omega)
      rw [show 1 + 2 * w + (p - (1 + 2 * w)) = p from by omega] at this
      rw [this]; unfold encodeReg
      rw [if_pos (by omega)]
    · rw [if_neg hpa]; show basisFinal0 w bits TfamK numWin g p = _
      unfold basisFinal0; rw [if_neg hpa]
  -- gate g = final0 (cancel).
  have hgate : Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g
      = basisFinal0 w bits TfamK numWin g := by
    rw [gidneyTwoRegInPlaceCosetMul_unfold, Gate.applyNat_seq, ← heq]
    exact gidneyTwoReg_reverse_leg_cancel w bits TfamKinv numWin hw hbits
      (basisFinal0 w bits TfamK numWin g)
  rw [hgate]
  refine ⟨?_, ?_⟩
  · apply decodeReg_eq_zero; intro i hi
    show basisFinal0 w bits TfamK numWin g (1 + 2 * w + i) = false
    unfold basisFinal0; rw [if_pos (by omega)]
  · rw [decodeReg_eq_mod_of_testBit (fun i => 1 + 2 * w + bits + i) bits P1 _
          (fun i hi => by
            show basisFinal0 w bits TfamK numWin g (1 + 2 * w + bits + i) = P1.testBit i
            unfold basisFinal0
            rw [if_neg (by omega), hp1, if_pos (by omega),
                show 1 + 2 * w + bits + i - (1 + 2 * w + bits) = i from by omega]),
        Nat.mod_eq_of_lt hP1lt]

/-! ## §5. Specialization of `hInvSum` to the ordinary/modular basis (no-wrap). -/

/-- **`hInvSum` specialization (basis / no-wrap case).**  Derives the BARE
    mod-`2^bits` equality `S2 % 2^bits = x` that `gidneyTwoRegInPlace_basis_correct`
    consumes, from:
      * pass-1 table-sum correctness (canonical): `P1 = (k * x) % N`;
      * pass-2 inverse table-sum residue (mod `N`): `S2 % N = (kInv * P1) % N`;
      * pass-2 NO-WRAP (the inverse sum is canonical in `2^bits`): `S2 % 2^bits = S2 % N`;
      * the modular inverse `kInv * k ≡ 1 [MOD N]`;
      * `x < N`.
    The number theory is `kInv·P1 ≡ kInv·k·x ≡ x [MOD N]`; the NO-WRAP hypothesis is
    what turns the resulting `≡ [MOD N]` into the LITERAL mod-`2^bits` equality
    (`S2 % 2^bits = x`) — so no `[MOD N]` leaks into `basis_correct`. -/
theorem hInvSum_specialized_basis (bits N k kInv x P1 S2 : Nat)
    (hxN : x < N) (hP1 : P1 = (k * x) % N)
    (hS2N : S2 % N = (kInv * P1) % N) (hS2nowrap : S2 % 2 ^ bits = S2 % N)
    (hkkinv : (kInv * k) % N = 1 % N) :
    S2 % 2 ^ bits = x := by
  have key : S2 ≡ x [MOD N] :=
    calc S2 ≡ kInv * P1 [MOD N] := hS2N
      _ ≡ kInv * (k * x) [MOD N] := by
            rw [hP1]; exact Nat.ModEq.mul_left kInv (Nat.mod_modEq _ _)
      _ = kInv * k * x := by ring
      _ ≡ 1 * x [MOD N] := Nat.ModEq.mul_right x hkkinv
      _ = x := one_mul x
  have hk : S2 % N = x % N := key
  rw [hS2nowrap, hk, Nat.mod_eq_of_lt hxN]

/-! ## §6. Good runway branch (basis level) — the conservative first coset step. -/

/-- **Good runway branch (basis level).**  For ONE branch with input residue `x < N`, if the
    pass-1/pass-2 table sums are canonical/no-wrap and `kInv · k ≡ 1 [MOD N]`, the gate maps the
    branch to the correct branch: the full post-state is `basisFinal0` (so scratch is restored),
    register `a` clears, and register `b` receives `(k * x) % N`.  Combines
    `hInvSum_specialized_basis` (the modular arithmetic) with `…_maps_to_final0` (full post-state)
    and `…_basis_correct` (the decodes).  NO coset superposition yet — the bad-set definition,
    its Born-mass bound, and the runway-branch sum are the NEXT steps. -/
theorem gidneyTwoRegInPlace_coset_basis_good_branch (w bits numWin N k kInv x : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat) (hw : 0 < w) (hbits : numWin * w = bits) (g : Nat → Bool)
    (hg : RelocStepInv w bits numWin x (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) 0 g)
    (hxN : x < N)
    (hP1 : (∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits = (k * x) % N)
    (hS2N : (∑ k' ∈ Finset.range numWin, TfamKinv k' (WindowedArith.window w
        ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits) k')) % N
        = (kInv * ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits)) % N)
    (hS2nowrap : (∑ k' ∈ Finset.range numWin, TfamKinv k' (WindowedArith.window w
          ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits) k')) % 2 ^ bits
        = (∑ k' ∈ Finset.range numWin, TfamKinv k' (WindowedArith.window w
          ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits) k')) % N)
    (hkkinv : (kInv * k) % N = 1 % N) :
    Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g
        = basisFinal0 w bits TfamK numWin g
    ∧ decodeReg (fun i => 1 + 2 * w + i) bits
        (Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g) = 0
    ∧ decodeReg (fun i => 1 + 2 * w + bits + i) bits
        (Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g) = (k * x) % N := by
  have hInvSum := hInvSum_specialized_basis bits N k kInv x
    ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits)
    (∑ k' ∈ Finset.range numWin, TfamKinv k' (WindowedArith.window w
        ((∑ j ∈ Finset.range numWin, TfamK j (WindowedArith.window w x j)) % 2 ^ bits) k'))
    hxN hP1 hS2N hS2nowrap hkkinv
  have hbc := gidneyTwoRegInPlace_basis_correct w bits numWin TfamK TfamKinv x hw hbits g hg hInvSum
  exact ⟨gidneyTwoRegInPlace_maps_to_final0 w bits numWin TfamK TfamKinv x hw hbits g hg hInvSum,
         hbc.1, hP1 ▸ hbc.2⟩

end FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
