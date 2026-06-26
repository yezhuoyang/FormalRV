/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.TwoSegment
  ──────────────────────────────────────────────────
  Submodule of `RunwayAdderFunctional` (split out for per-file compile memory).
  Contains §1–§10: the k = 2 (one-runway) oblivious-carry-runway adder — layout,
  circuit, concrete decodes, operand values, well-typedness, `decodeReg` helpers,
  cross-block frame lemmas, per-segment exactness, the headline `runwayAdd2_exact`,
  and the k = 2 advance bound.

  Re-exported VERBATIM from the original `RunwayAdderFunctional.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.Adder.Cuccaro

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §1. Layout. -/

/-- Base qubit of the HIGH Cuccaro block: it sits immediately above the LOW
    block, whose span is `2·(gSep+1)+1 = 2·gSep+3`. -/
def highBase (gSep : Nat) : Nat := 2 * gSep + 3

/-- Total qubit width of the k = 2 runway register: the low width-`(gSep+1)`
    Cuccaro span plus the high width-`gSep` Cuccaro span. -/
def runwayWidth2 (gSep : Nat) : Nat := (2 * gSep + 3) + (2 * gSep + 1)

/-! ## §2. The circuit.

`runwayAdd2 gSep` is the sequential composition of two Cuccaro adds over the
DISJOINT low/high blocks.  The low add is a width-`(gSep+1)` Cuccaro at base `0`
(so its top augend bit, the runway, can hold the carry-out of the `gSep`-bit
operands); the high add is a width-`gSep` Cuccaro at `highBase`.  No fold: the
runway carry is deposited and left there. -/

/-- The LOW segment add: a width-`(gSep+1)` Cuccaro at base `0`. -/
def lowAdd (gSep : Nat) : Gate := cuccaroAdder.circuit (gSep + 1) 0

/-- The HIGH segment add: a width-`gSep` Cuccaro at `highBase gSep`. -/
def highAdd (gSep : Nat) : Gate := cuccaroAdder.circuit gSep (highBase gSep)

/-- **The k = 2 oblivious-carry-runway adder.**  Low add (carry → runway), then
    high add (oblivious — runway not folded). -/
def runwayAdd2 (gSep : Nat) : Gate := Gate.seq (lowAdd gSep) (highAdd gSep)

/-! ## §3. Concrete decodes (real `def`s, NOT structure fields).

`augendIdx 0 i = 2i+1`, `addendIdx 0 i = 2i+2` for the low block;
`augendIdx (highBase) i = highBase + 2i+1`, etc., for the high block. -/

/-- Low augend register value: the `(gSep+1)`-bit running-sum register at the
    low block (positions `2i+1`, i = 0…gSep).  Bits `0…gSep-1` are the low data;
    bit `gSep` is the runway. -/
def lowReg (gSep : Nat) (f : Nat → Bool) : Nat :=
  decodeReg (cuccaroAdder.augendIdx 0) (gSep + 1) f

/-- High augend register value: the `gSep`-bit running-sum register at the high
    block (positions `highBase + 2i+1`, i = 0…gSep-1). -/
def highReg (gSep : Nat) (f : Nat → Bool) : Nat :=
  decodeReg (cuccaroAdder.augendIdx (highBase gSep)) gSep f

/-- The runway bit value (0 or 1): the top augend bit of the low block. -/
def runwayBit (gSep : Nat) (f : Nat → Bool) : Nat :=
  if f (cuccaroAdder.augendIdx 0 gSep) then 1 else 0

/-- **Concrete full-register place-value decode.**  The low `(gSep+1)`-bit
    register at place `2^0` (its top bit, the runway, sits at place `2^gSep`),
    plus the high `gSep`-bit register at place `2^(gSep+1)`.  The gap at place
    `2^gSep` is exactly where the deferred low-segment carry (the runway) lives. -/
def fullDecode (gSep : Nat) (f : Nat → Bool) : Nat :=
  lowReg gSep f + 2 ^ (gSep + 1) * highReg gSep f

/-! ## §4. Operand values (concrete).

The augend is `a_lo + 2^(gSep+1)·a_hi`, reading the low data from the low augend
register (bits `0…gSep-1`, NOT the runway) and the high data from the high
augend register.  The addend `b_lo + 2^(gSep+1)·b_hi` reads the low/high ADDEND
registers.  The low data is read at width `gSep` (excluding the runway bit,
which is an ancilla pre-cleared to 0 on input). -/

/-- Input augend value: low data (`gSep` bits at the low augend register) plus
    `2^(gSep+1)·` high data (`gSep` bits at the high augend register). -/
def augendValue (gSep : Nat) (f : Nat → Bool) : Nat :=
  decodeReg (cuccaroAdder.augendIdx 0) gSep f
    + 2 ^ (gSep + 1) * decodeReg (cuccaroAdder.augendIdx (highBase gSep)) gSep f

/-- Input addend value: low addend (`gSep` bits at the low addend register) plus
    `2^(gSep+1)·` high addend (`gSep` bits at the high addend register). -/
def addendValue (gSep : Nat) (f : Nat → Bool) : Nat :=
  decodeReg (cuccaroAdder.addendIdx 0) gSep f
    + 2 ^ (gSep + 1) * decodeReg (cuccaroAdder.addendIdx (highBase gSep)) gSep f

/-! ## §5. Well-typedness. -/

/-- **`runwayAdd2` is well-typed** at `runwayWidth2 gSep`.  Both Cuccaro blocks
    fit (the low at `[0, 2·gSep+3)`, the high at `[2·gSep+3, 4·gSep+4)`). -/
theorem runwayAdd2_wellTyped (gSep : Nat) :
    Gate.WellTyped (runwayWidth2 gSep) (runwayAdd2 gSep) := by
  refine ⟨?_, ?_⟩
  · -- low add: a width-`(gSep+1)` Cuccaro at base `0`, fits in `runwayWidth2`.
    show Gate.WellTyped (runwayWidth2 gSep) (cuccaro_n_bit_adder_full (gSep + 1) 0)
    exact cuccaro_n_bit_adder_full_wellTyped (gSep + 1) 0 (runwayWidth2 gSep)
      (by show 0 + 2 * (gSep + 1) + 1 ≤ (2 * gSep + 3) + (2 * gSep + 1); omega)
  · -- high add: a width-`gSep` Cuccaro at `highBase`, fits in `runwayWidth2`.
    show Gate.WellTyped (runwayWidth2 gSep)
      (cuccaro_n_bit_adder_full gSep (highBase gSep))
    exact cuccaro_n_bit_adder_full_wellTyped gSep (highBase gSep) (runwayWidth2 gSep)
      (by show highBase gSep + 2 * gSep + 1 ≤ (2 * gSep + 3) + (2 * gSep + 1)
          unfold highBase; omega)

/-! ## §6. `decodeReg` helpers. -/

/-- **Append the top bit.**  Reading `n+1` register bits = reading the low `n`
    bits plus the weighted top bit. -/
theorem decodeReg_succ (idx : Nat → Nat) (n : Nat) (f : Nat → Bool) :
    decodeReg idx (n + 1) f
      = decodeReg idx n f + (if f (idx n) then 2 ^ n else 0) := by
  unfold decodeReg
  rw [List.range_succ, List.foldl_append]
  simp

/-- **Dropping a clear top bit.**  If the top register bit `idx n` is `false`,
    reading `n+1` bits is the same as reading the low `n` bits. -/
theorem decodeReg_succ_of_top_false (idx : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (h : f (idx n) = false) :
    decodeReg idx (n + 1) f = decodeReg idx n f := by
  rw [decodeReg_succ, h]; simp

/-- A register value at width `n` is `< 2^n`. -/
theorem decodeReg_lt (idx : Nat → Nat) (n : Nat) (f : Nat → Bool) :
    decodeReg idx n f < 2 ^ n := by
  induction n with
  | zero => simp [decodeReg]
  | succ k ih =>
      rw [decodeReg_succ]
      have hk : (if f (idx k) then 2 ^ k else 0) ≤ 2 ^ k := by
        by_cases hb : f (idx k) <;> simp [hb]
      have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
      omega

/-! ## §7. Cross-block frame lemmas (the two blocks are disjoint). -/

/-- The high block leaves the low augend register untouched: every low augend
    position `2i+1` (i ≤ gSep) is below `highBase`, hence outside the high block. -/
theorem lowReg_highAdd (gSep : Nat) (f : Nat → Bool) :
    lowReg gSep (Gate.applyNat (highAdd gSep) f) = lowReg gSep f := by
  unfold lowReg
  apply decodeReg_ext
  intro i hi
  -- low augend position `0 + 2i+1`; show high add (block `[highBase, …)`) fixes it.
  show Gate.applyNat (cuccaroAdder.circuit gSep (highBase gSep)) f
        (cuccaroAdder.augendIdx 0 i) = f (cuccaroAdder.augendIdx 0 i)
  apply cuccaroAdder.frame gSep (highBase gSep) f
  -- `augendIdx 0 i = 0 + 2i+1 ≤ 2gSep+1 < highBase`; not in the high block.
  show ¬ inBlock (highBase gSep) (cuccaroAdder.span gSep) (cuccaroAdder.augendIdx 0 i)
  unfold inBlock highBase
  show ¬ (2 * gSep + 3 ≤ 0 + 2 * i + 1 ∧ 0 + 2 * i + 1 < 2 * gSep + 3 + (2 * gSep + 1))
  omega

/-- The low block leaves any HIGH-block position untouched: every high position
    `highBase + j` (`j ≥ 0`) is at least `highBase = span(gSep+1)`, hence outside
    the low block `[0, span(gSep+1))`.  Stated for a general high read index. -/
theorem lowAdd_fixes_high (gSep : Nat) (f : Nat → Bool) (j : Nat) :
    Gate.applyNat (lowAdd gSep) f (highBase gSep + j) = f (highBase gSep + j) := by
  unfold lowAdd
  apply cuccaroAdder.frame (gSep + 1) 0 f
  show ¬ inBlock 0 (cuccaroAdder.span (gSep + 1)) (highBase gSep + j)
  unfold inBlock highBase
  show ¬ (0 ≤ 2 * gSep + 3 + j ∧ 2 * gSep + 3 + j < 0 + (2 * (gSep + 1) + 1))
  omega

/-! ## §8. Per-segment exactness about `applyNat`. -/

/-- **Low segment exactness (EXACT, with the deferred carry in the runway).**
    Running the low width-`(gSep+1)` Cuccaro add on an input whose runway bit
    (low augend bit `gSep`) and low-addend top bit are pre-cleared to `0`, the
    low `(gSep+1)`-bit register holds EXACTLY `a_lo + b_lo` (no truncation): the
    low data is `(a_lo+b_lo) mod 2^gSep` and the runway bit is the carry-out
    `(a_lo+b_lo)/2^gSep`.  This is the genuine carry deposit into the runway. -/
theorem lowReg_lowAdd_exact (gSep : Nat) (f : Nat → Bool)
    (hLowAnc : f 0 = false)
    (hRunway0 : f (cuccaroAdder.augendIdx 0 gSep) = false)
    (hLowAddTop : f (cuccaroAdder.addendIdx 0 gSep) = false) :
    lowReg gSep (Gate.applyNat (lowAdd gSep) f)
      = decodeReg (cuccaroAdder.augendIdx 0) gSep f
          + decodeReg (cuccaroAdder.addendIdx 0) gSep f := by
  unfold lowReg lowAdd
  -- Apply the Cuccaro sum-correctness at width `gSep+1`, base `0`.
  have hclean : cuccaroAdder.ancClean f (gSep + 1) 0 := by
    show f 0 = false; exact hLowAnc
  have hsum := cuccaroAdder.sumCorrect (gSep + 1) 0 f hclean
  rw [hsum]
  -- The width-`(gSep+1)` augend/addend reads = the width-`gSep` reads (top bit 0).
  rw [decodeReg_succ_of_top_false _ gSep f hRunway0,
      decodeReg_succ_of_top_false _ gSep f hLowAddTop]
  -- `a_lo + b_lo < 2^(gSep+1)`, so the mod is the identity.
  have ha : decodeReg (cuccaroAdder.augendIdx 0) gSep f < 2 ^ gSep :=
    decodeReg_lt _ gSep f
  have hb : decodeReg (cuccaroAdder.addendIdx 0) gSep f < 2 ^ gSep :=
    decodeReg_lt _ gSep f
  have hpow : (2 : Nat) ^ gSep + 2 ^ gSep = 2 ^ (gSep + 1) := by rw [pow_succ]; ring
  apply Nat.mod_eq_of_lt
  omega

/-- **High segment exactness** (about `applyNat (highAdd) g`).  Running the high
    width-`gSep` Cuccaro add on any state `g` with its carry-in clean, the high
    register holds `(a_hi + b_hi) mod 2^gSep` read off `g`. -/
theorem highReg_highAdd (gSep : Nat) (g : Nat → Bool)
    (hHighAnc : g (highBase gSep) = false) :
    highReg gSep (Gate.applyNat (highAdd gSep) g)
      = (decodeReg (cuccaroAdder.augendIdx (highBase gSep)) gSep g
          + decodeReg (cuccaroAdder.addendIdx (highBase gSep)) gSep g) % 2 ^ gSep := by
  unfold highReg highAdd
  have hclean : cuccaroAdder.ancClean g gSep (highBase gSep) := by
    show g (highBase gSep) = false; exact hHighAnc
  exact cuccaroAdder.sumCorrect gSep (highBase gSep) g hclean

/-! ## §9. THE HEADLINE — exact deferred-carry correctness, wired to `applyNat`. -/

/-- **k = 2 oblivious-carry-runway adder, EXACT.**  With each segment's carry-in
    ancilla clean, the runway pre-cleared, the low addend's top bit clear, and
    the HIGH segment not itself overflowing (`a_hi+b_hi < 2^gSep`; there is no
    second runway in k = 2 to absorb a high carry), the concrete full-register
    place-value decode of the runway adder's output equals the true sum EXACTLY:

        fullDecode (applyNat (runwayAdd2 gSep) f) = augendValue f + addendValue f.

    The low-segment carry is genuinely CHAINED into the runway bit (place
    `2^gSep`) and reconstructed by `fullDecode`; the high data occupies place
    `2^(gSep+1)` and is independent — the carry was DEFERRED into the runway, not
    propagated.  This is real carry arithmetic, not a tautology: every term is a
    `Gate.applyNat (runwayAdd2 …) f` read through concrete `def` decodes. -/
theorem runwayAdd2_exact (gSep : Nat) (f : Nat → Bool)
    (hLowAnc : f 0 = false)
    (hHighAnc : f (highBase gSep) = false)
    (hRunway0 : f (cuccaroAdder.augendIdx 0 gSep) = false)
    (hLowAddTop : f (cuccaroAdder.addendIdx 0 gSep) = false)
    (hHighNoOverflow :
      decodeReg (cuccaroAdder.augendIdx (highBase gSep)) gSep f
        + decodeReg (cuccaroAdder.addendIdx (highBase gSep)) gSep f < 2 ^ gSep) :
    fullDecode gSep (Gate.applyNat (runwayAdd2 gSep) f)
      = augendValue gSep f + addendValue gSep f := by
  -- Unfold the sequential composition: high add ∘ low add.
  have hseq : Gate.applyNat (runwayAdd2 gSep) f
      = Gate.applyNat (highAdd gSep) (Gate.applyNat (lowAdd gSep) f) := rfl
  set f1 := Gate.applyNat (lowAdd gSep) f with hf1
  unfold fullDecode
  rw [hseq]
  -- LOW register: high add fixes it, then low-segment exactness gives a_lo+b_lo.
  rw [lowReg_highAdd gSep f1]
  rw [lowReg_lowAdd_exact gSep f hLowAnc hRunway0 hLowAddTop]
  -- HIGH register: high-segment exactness on f1, then push the reads back to f.
  -- f1's high carry-in is clean (low add fixes high positions).
  have hHighAnc1 : f1 (highBase gSep) = false := by
    rw [hf1]; rw [show highBase gSep = highBase gSep + 0 from rfl,
      lowAdd_fixes_high gSep f 0]; exact hHighAnc
  rw [highReg_highAdd gSep f1 hHighAnc1]
  -- The high augend/addend reads on f1 equal the reads on f (low add fixes them).
  have hHA : decodeReg (cuccaroAdder.augendIdx (highBase gSep)) gSep f1
      = decodeReg (cuccaroAdder.augendIdx (highBase gSep)) gSep f := by
    apply decodeReg_ext
    intro i hi
    show f1 (cuccaroAdder.augendIdx (highBase gSep) i)
      = f (cuccaroAdder.augendIdx (highBase gSep) i)
    rw [hf1]
    show Gate.applyNat (lowAdd gSep) f (highBase gSep + 2 * i + 1)
      = f (highBase gSep + 2 * i + 1)
    rw [show highBase gSep + 2 * i + 1 = highBase gSep + (2 * i + 1) by ring]
    exact lowAdd_fixes_high gSep f (2 * i + 1)
  have hHB : decodeReg (cuccaroAdder.addendIdx (highBase gSep)) gSep f1
      = decodeReg (cuccaroAdder.addendIdx (highBase gSep)) gSep f := by
    apply decodeReg_ext
    intro i hi
    show f1 (cuccaroAdder.addendIdx (highBase gSep) i)
      = f (cuccaroAdder.addendIdx (highBase gSep) i)
    rw [hf1]
    show Gate.applyNat (lowAdd gSep) f (highBase gSep + 2 * i + 2)
      = f (highBase gSep + 2 * i + 2)
    rw [show highBase gSep + 2 * i + 2 = highBase gSep + (2 * i + 2) by ring]
    exact lowAdd_fixes_high gSep f (2 * i + 2)
  rw [hHA, hHB]
  -- High segment doesn't overflow: the mod is the identity.
  rw [Nat.mod_eq_of_lt hHighNoOverflow]
  -- Assemble: (a_lo+b_lo) + 2^(gSep+1)·(a_hi+b_hi) = augendValue + addendValue.
  unfold augendValue addendValue
  ring

/-! ## §10. The advance bound — wired to `applyNat`. -/

/-- The low `(gSep+1)`-bit register splits as low data (`gSep` bits) plus the
    runway bit at place `2^gSep`. -/
theorem lowReg_eq_data_add_runway (gSep : Nat) (f : Nat → Bool) :
    lowReg gSep f
      = decodeReg (cuccaroAdder.augendIdx 0) gSep f + 2 ^ gSep * runwayBit gSep f := by
  unfold lowReg runwayBit
  rw [decodeReg_succ]
  by_cases hb : f (cuccaroAdder.augendIdx 0 gSep) <;> simp [hb]

/-- The runway position lies in the LOW block, so the HIGH add fixes it: the
    output runway bit equals the runway bit right after the LOW add. -/
theorem runwayBit_runwayAdd2_eq (gSep : Nat) (f : Nat → Bool) :
    runwayBit gSep (Gate.applyNat (runwayAdd2 gSep) f)
      = runwayBit gSep (Gate.applyNat (lowAdd gSep) f) := by
  show (if Gate.applyNat (runwayAdd2 gSep) f (cuccaroAdder.augendIdx 0 gSep)
          then 1 else 0)
     = (if Gate.applyNat (lowAdd gSep) f (cuccaroAdder.augendIdx 0 gSep)
          then 1 else 0)
  have hfix : Gate.applyNat (runwayAdd2 gSep) f (cuccaroAdder.augendIdx 0 gSep)
      = Gate.applyNat (lowAdd gSep) f (cuccaroAdder.augendIdx 0 gSep) := by
    show Gate.applyNat (highAdd gSep) (Gate.applyNat (lowAdd gSep) f)
        (cuccaroAdder.augendIdx 0 gSep)
      = Gate.applyNat (lowAdd gSep) f (cuccaroAdder.augendIdx 0 gSep)
    apply cuccaroAdder.frame gSep (highBase gSep)
    show ¬ inBlock (highBase gSep) (cuccaroAdder.span gSep) (cuccaroAdder.augendIdx 0 gSep)
    unfold inBlock highBase
    show ¬ (2 * gSep + 3 ≤ 0 + 2 * gSep + 1 ∧ _)
    omega
  rw [hfix]

/-- **The deferred carry IS the runway bit** (exact).  After the runway add, the
    runway bit holds exactly the genuine carry-out `(a_lo+b_lo)/2^gSep` of the
    low segment — proving the runway holds the REAL deferred carry, not a free
    qubit.  Wired to `Gate.applyNat (runwayAdd2 gSep) f`. -/
theorem runwayAdd2_runway_eq_carry (gSep : Nat) (f : Nat → Bool)
    (hLowAnc : f 0 = false)
    (hRunway0 : f (cuccaroAdder.augendIdx 0 gSep) = false)
    (hLowAddTop : f (cuccaroAdder.addendIdx 0 gSep) = false) :
    runwayBit gSep (Gate.applyNat (runwayAdd2 gSep) f)
      = (decodeReg (cuccaroAdder.augendIdx 0) gSep f
          + decodeReg (cuccaroAdder.addendIdx 0) gSep f) / 2 ^ gSep := by
  rw [runwayBit_runwayAdd2_eq]
  set f1 := Gate.applyNat (lowAdd gSep) f with hf1
  -- lowReg f1 = a_lo + b_lo (exact), and lowReg f1 = data(f1) + 2^gSep·runway(f1).
  have hExact : lowReg gSep f1
      = decodeReg (cuccaroAdder.augendIdx 0) gSep f
          + decodeReg (cuccaroAdder.addendIdx 0) gSep f := by
    rw [hf1]; exact lowReg_lowAdd_exact gSep f hLowAnc hRunway0 hLowAddTop
  have hSplit := lowReg_eq_data_add_runway gSep f1
  -- data(f1) < 2^gSep, runway(f1) ∈ {0,1}: solve the division.
  have hdata : decodeReg (cuccaroAdder.augendIdx 0) gSep f1 < 2 ^ gSep :=
    decodeReg_lt _ gSep f1
  set S := decodeReg (cuccaroAdder.augendIdx 0) gSep f
          + decodeReg (cuccaroAdder.addendIdx 0) gSep f with hS
  set d := decodeReg (cuccaroAdder.augendIdx 0) gSep f1 with hd
  set r := runwayBit gSep f1 with hr
  -- S = d + 2^gSep·r with d < 2^gSep, so S / 2^gSep = r.
  have hSeq : S = d + 2 ^ gSep * r := by rw [← hExact, hSplit]
  rw [hSeq, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hdata]
  simp

/-- **THE ADVANCE BOUND (audit-critical), wired to `applyNat`.**  After the k = 2
    runway add, the deferred-carry occupancy of the runway is at most ONE bit —
    the single deferred carry of the scheme.  Literally about
    `Gate.applyNat (runwayAdd2 gSep) f`. -/
theorem runwayAdd2_advance (gSep : Nat) (f : Nat → Bool) :
    runwayBit gSep (Gate.applyNat (runwayAdd2 gSep) f) ≤ 1 := by
  unfold runwayBit
  by_cases hb : Gate.applyNat (runwayAdd2 gSep) f (cuccaroAdder.augendIdx 0 gSep)
    <;> simp [hb]

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
