/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  ──────────────────────────────────────────────────
  A GENUINELY FUNCTIONAL oblivious-carry-runway adder, built as a verified
  `Gate` over the Cuccaro adder, with a CONCRETE full-register place-value
  decode and an EXACT deferred-carry correctness theorem.

  Everything proved here is wired to `Gate.applyNat (runwayAdd2 …) f` literally,
  with the decode given by concrete `def`s (NOT free structure fields).  No
  `sorry`, no `native_decide`, no axioms beyond the prelude.

  ════════════════════════════════════════════════════════════════════════════
  THE CONSTRUCTION (k = 2 — ONE runway — fully wired)
  ════════════════════════════════════════════════════════════════════════════

  Layout over a `4·gSep+4`-qubit register, two DISJOINT Cuccaro blocks:

    • LOW block  [0, 2·gSep+3):  a width-`(gSep+1)` Cuccaro add.  Its augend
      register has `gSep+1` bits at positions `2i+1` (i = 0 … gSep).  The TOP
      augend bit (i = gSep, position `2·gSep+1`) is the RUNWAY: with both
      `gSep`-bit operands `< 2^gSep`, their sum is `< 2^(gSep+1)`, so the
      width-`(gSep+1)` add is EXACT and the runway bit holds the genuine
      carry-out `(a_lo+b_lo)/2^gSep ∈ {0,1}`.  The low data is augend bits
      `0…gSep-1`.

    • HIGH block [2·gSep+3, 4·gSep+4):  a width-`gSep` Cuccaro add of the high
      segment.  It is run WITHOUT folding the runway (oblivious: the deferred
      carry STAYS in the runway bit, it is never propagated into the high data).

  The full-register place-value decode `fullDecode` reads the low `(gSep+1)`-bit
  register at place `2^0` and the high `gSep`-bit register at place `2^(gSep+1)`
  — leaving place `2^gSep` for the runway bit, which is exactly where the
  deferred low-segment carry lives.

  THE HEADLINE (real carry arithmetic, NOT vacuous):

    fullDecode (Gate.applyNat (runwayAdd2 gSep) f)
        = augendValue gSep f + addendValue gSep f                    (EXACT)

  provided each segment's carry-in ancilla is clean and the HIGH segment does
  not itself overflow (`a_hi + b_hi < 2^gSep`; in k = 2 there is no second
  runway to absorb a high overflow).  The low-segment carry is genuinely
  CHAINED into the runway bit and is reconstructed by the place-value decode;
  the sum is preserved exactly, the carry just lives in the runway instead of
  having propagated.

  THE GENUINE CONTENT is `runwayAdd2_exact` / `runwayAddK_exact` (exact sum, real
  carry arithmetic) and `runwayAdd2_runway_eq_carry` (the runway bit IS the real
  carry).  The "advance" theorems (`runwayAdd2_advance : … ≤ 1`,
  `runwayAddK_advance : … ≤ k`) are STRUCTURALLY TRIVIAL — a runway is one bit, so
  ≤ 1, and `k` runways sum to ≤ k, for ANY state; the `applyNat` there is
  decorative.  They express "we built `k` runways," NOT the paper's deviation-
  relevant `Δ`, which is a MULTI-ADD value-advance vs the coset padding and is NOT
  established here.  See the per-theorem caveats in §10/§14.

  WHAT THIS FILE IS NOT: it does not connect the runway-interspersed encoding to
  the contiguous coset value, and does not formalize the multi-add deferred-carry
  advance.  It IS a faithful, exact, single-addition oblivious-runway adder —
  which is the functional correctness the earlier `ObliviousRunwayAdder` skeleton
  lacked.
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

/-! ## §11. Generalization to k segments (uniform — every segment has a runway).

The uniform k-segment runway adder gives every segment its OWN width-`(gSep+1)`
Cuccaro add with its OWN runway pad.  Carries do NOT propagate between segments:
each segment deposits its carry-out into its own runway.  Because every segment
has a runway to absorb its single carry bit, the full place-value decode equals
`augend + addend` EXACTLY with NO overflow precondition (unlike k = 2, whose top
segment had no runway and so needed `a_hi+b_hi < 2^gSep`).

  • segment `j` lives in the DISJOINT block `[segBase j, segBase j + 2·gSep+3)`;
  • the full decode reads each segment's `(gSep+1)`-bit register at place
    `2^(j·(gSep+1))`;
  • advance: each runway holds ≤ 1 bit, so total runway occupancy ≤ k. -/

/-- Qubits reserved per segment: the width-`(gSep+1)` Cuccaro span `2·gSep+3`
    (the `+1` augend bit is the runway). -/
def segStride (gSep : Nat) : Nat := 2 * gSep + 3

/-- Base qubit of segment `j`. -/
def segBase (gSep j : Nat) : Nat := j * segStride gSep

/-- Segment `j`'s width-`(gSep+1)` Cuccaro add (runway = its top augend bit). -/
def segAdd (gSep j : Nat) : Gate := cuccaroAdder.circuit (gSep + 1) (segBase gSep j)

/-- **The uniform k-segment oblivious-carry-runway adder.**  Segments added
    low-to-high; segment `k` is applied last (outermost). -/
def runwayAddK (gSep : Nat) : Nat → Gate
  | 0 => Gate.I
  | k + 1 => Gate.seq (runwayAddK gSep k) (segAdd gSep k)

/-- Segment `j`'s `(gSep+1)`-bit register value (its data + runway). -/
def segReg (gSep j : Nat) (f : Nat → Bool) : Nat :=
  decodeReg (cuccaroAdder.augendIdx (segBase gSep j)) (gSep + 1) f

/-- Segment `j`'s runway bit (its top augend bit). -/
def segRunway (gSep j : Nat) (f : Nat → Bool) : Nat :=
  if f (cuccaroAdder.augendIdx (segBase gSep j) gSep) then 1 else 0

/-- **k-segment place-value decode** (concrete): `Σ_{j<k} segReg j · 2^(j·(gSep+1))`. -/
def kDecode (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f => kDecode gSep k f + segReg gSep k f * 2 ^ (k * (gSep + 1))

/-- k-segment input augend value: `Σ_{j<k} a_j · 2^(j·(gSep+1))`, reading the
    `gSep` data bits of each segment's augend register (runways pre-cleared). -/
def kAugend (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f =>
      kAugend gSep k f
        + decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep f
            * 2 ^ (k * (gSep + 1))

/-- k-segment input addend value: `Σ_{j<k} b_j · 2^(j·(gSep+1))`. -/
def kAddend (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f =>
      kAddend gSep k f
        + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep f
            * 2 ^ (k * (gSep + 1))

/-! ## §12. k-segment frame lemmas. -/

/-- Segment `k`'s add fixes every position strictly below its base — lower
    segments are untouched by a higher segment's add. -/
theorem segAdd_fixes_below (gSep k : Nat) (f : Nat → Bool) (p : Nat)
    (hp : p < segBase gSep k) :
    Gate.applyNat (segAdd gSep k) f p = f p := by
  unfold segAdd
  apply cuccaroAdder.frame (gSep + 1) (segBase gSep k)
  show ¬ inBlock (segBase gSep k) (cuccaroAdder.span (gSep + 1)) p
  unfold inBlock
  omega

/-- `runwayAddK gSep k` (segments `0…k-1`) fixes every position at or above
    `segBase gSep k`: each lower segment `j < k` lives in
    `[segBase j, (j+1)·stride)` and `(j+1)·stride ≤ k·stride = segBase k ≤ p`. -/
theorem runwayAddK_fixes_above (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool) (p : Nat), segBase gSep k ≤ p →
      Gate.applyNat (runwayAddK gSep k) f p = f p := by
  intro k
  induction k with
  | zero => intro f p _; rfl
  | succ m ih =>
      intro f p hp
      -- `segBase (m+1) = (m+1)·stride ≥ segBase m`, so the IH applies to `p`.
      have hbase_mono : segBase gSep m ≤ segBase gSep (m + 1) := by
        unfold segBase segStride; have : m ≤ m + 1 := by omega
        exact Nat.mul_le_mul_right _ this
      show Gate.applyNat (segAdd gSep m) (Gate.applyNat (runwayAddK gSep m) f) p = f p
      -- segAdd m has block `[segBase m, (m+1)·stride)`; `p ≥ segBase (m+1) = (m+1)·stride`.
      have hfix : Gate.applyNat (segAdd gSep m) (Gate.applyNat (runwayAddK gSep m) f) p
          = Gate.applyNat (runwayAddK gSep m) f p := by
        unfold segAdd
        apply cuccaroAdder.frame (gSep + 1) (segBase gSep m)
        show ¬ inBlock (segBase gSep m) (cuccaroAdder.span (gSep + 1)) p
        unfold inBlock
        -- `p ≥ segBase (m+1) = (m+1)·(2gSep+3) = segBase m + (2gSep+3)`.
        have hexp : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
          unfold segBase segStride; ring
        show ¬ (segBase gSep m ≤ p ∧ p < segBase gSep m + (2 * (gSep + 1) + 1))
        have : segBase gSep m + (2 * gSep + 3) ≤ p := by omega
        omega
      rw [hfix]
      exact ih f p (le_trans hbase_mono hp)

/-! ## §13. k-segment exactness, by induction. -/

/-- **Per-segment exactness at an arbitrary base** (generalizes
    `lowReg_lowAdd_exact` to base `q`).  A width-`(gSep+1)` Cuccaro at base `q`,
    run with its carry-in clean, runway pre-cleared, and addend top bit clear,
    leaves its `(gSep+1)`-bit register holding EXACTLY `a + b` (the carry-out is
    deposited in the runway, no truncation). -/
theorem segReg_segAdd_exact_base (gSep q : Nat) (f : Nat → Bool)
    (hAnc : f q = false)
    (hRunway0 : f (cuccaroAdder.augendIdx q gSep) = false)
    (hAddTop : f (cuccaroAdder.addendIdx q gSep) = false) :
    decodeReg (cuccaroAdder.augendIdx q) (gSep + 1)
        (Gate.applyNat (cuccaroAdder.circuit (gSep + 1) q) f)
      = decodeReg (cuccaroAdder.augendIdx q) gSep f
          + decodeReg (cuccaroAdder.addendIdx q) gSep f := by
  have hclean : cuccaroAdder.ancClean f (gSep + 1) q := by
    show f q = false; exact hAnc
  rw [cuccaroAdder.sumCorrect (gSep + 1) q f hclean]
  rw [decodeReg_succ_of_top_false _ gSep f hRunway0,
      decodeReg_succ_of_top_false _ gSep f hAddTop]
  have ha : decodeReg (cuccaroAdder.augendIdx q) gSep f < 2 ^ gSep :=
    decodeReg_lt _ gSep f
  have hb : decodeReg (cuccaroAdder.addendIdx q) gSep f < 2 ^ gSep :=
    decodeReg_lt _ gSep f
  have hpow : (2 : Nat) ^ gSep + 2 ^ gSep = 2 ^ (gSep + 1) := by rw [pow_succ]; ring
  apply Nat.mod_eq_of_lt; omega

/-- `kDecode gSep k` depends only on the state at positions `< segBase gSep k`:
    its segment registers `j < k` all sit below `segBase gSep k`. -/
theorem kDecode_congr (gSep : Nat) :
    ∀ (k : Nat) (f g : Nat → Bool),
      (∀ p, p < segBase gSep k → f p = g p) →
      kDecode gSep k f = kDecode gSep k g := by
  intro k
  induction k with
  | zero => intro f g _; rfl
  | succ m ih =>
      intro f g hagree
      have hbase_mono : segBase gSep m ≤ segBase gSep (m + 1) := by
        unfold segBase segStride
        exact Nat.mul_le_mul_right _ (by omega)
      show kDecode gSep m f + segReg gSep m f * 2 ^ (m * (gSep + 1))
        = kDecode gSep m g + segReg gSep m g * 2 ^ (m * (gSep + 1))
      have h1 : kDecode gSep m f = kDecode gSep m g :=
        ih f g (fun p hp => hagree p (lt_of_lt_of_le hp hbase_mono))
      have h2 : segReg gSep m f = segReg gSep m g := by
        unfold segReg
        apply decodeReg_ext
        intro i hi
        -- augend position `segBase m + 2i+1`; need it `< segBase (m+1)`.
        have hpos : cuccaroAdder.augendIdx (segBase gSep m) i < segBase gSep (m + 1) := by
          show segBase gSep m + 2 * i + 1 < segBase gSep (m + 1)
          have hexp : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
            unfold segBase segStride; ring
          omega
        exact hagree _ hpos
      rw [h1, h2]

/-- Input cleanliness for the k-segment runway adder: every segment `j < k` has
    its carry-in ancilla, runway bit, and addend top bit pre-cleared to `0`. -/
def kClean (gSep k : Nat) (f : Nat → Bool) : Prop :=
  ∀ j, j < k →
    f (segBase gSep j) = false
    ∧ f (cuccaroAdder.augendIdx (segBase gSep j) gSep) = false
    ∧ f (cuccaroAdder.addendIdx (segBase gSep j) gSep) = false

/-- **k-segment runway adder, EXACT** (the genuine `Δ = n/g_sep` construction).
    With every segment pre-cleared (`kClean`), the concrete k-segment place-value
    decode of the output equals `augend + addend` EXACTLY — NO overflow
    precondition, because every segment has its own runway absorbing its single
    carry bit.  Proven by induction on `k`; wired to
    `Gate.applyNat (runwayAddK gSep k) f`. -/
theorem runwayAddK_exact (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f →
      kDecode gSep k (Gate.applyNat (runwayAddK gSep k) f)
        = kAugend gSep k f + kAddend gSep k f := by
  intro k
  induction k with
  | zero => intro f _; rfl
  | succ m ih =>
      intro f hclean
      set g := Gate.applyNat (runwayAddK gSep m) f with hg
      -- The lower-segment cleanliness restricts to `m`.
      have hcleanm : kClean gSep m f := fun j hj => hclean j (by omega)
      -- ① Lower segments' decode is unaffected by segment m's add.
      have hlow : kDecode gSep m (Gate.applyNat (segAdd gSep m) g)
          = kDecode gSep m g := by
        apply kDecode_congr
        intro p hp
        exact segAdd_fixes_below gSep m g p hp
      -- ② g restricted to segment m's positions equals f (lower segs don't touch m).
      have hfix : ∀ q, segBase gSep m ≤ q → g q = f q := by
        intro q hq; rw [hg]; exact runwayAddK_fixes_above gSep m f q hq
      -- segment m's carry-in / runway / addend-top, on g, are clean.
      obtain ⟨hAnc, hRun, hAddTop⟩ := hclean m (by omega)
      have hAnc' : g (segBase gSep m) = false := by rw [hfix _ (le_refl _)]; exact hAnc
      have hRun' : g (cuccaroAdder.augendIdx (segBase gSep m) gSep) = false := by
        rw [hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * gSep + 1; omega)]
        exact hRun
      have hAddTop' : g (cuccaroAdder.addendIdx (segBase gSep m) gSep) = false := by
        rw [hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * gSep + 2; omega)]
        exact hAddTop
      -- ③ segment m's register after its add = a_m + b_m (read off g).
      have hseg : segReg gSep m (Gate.applyNat (segAdd gSep m) g)
          = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep g
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g := by
        unfold segReg segAdd
        exact segReg_segAdd_exact_base gSep (segBase gSep m) g hAnc' hRun' hAddTop'
      -- ④ The gSep reads on g equal the reads on f (lower segs fix seg-m positions).
      have hAread : decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep g
          = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f := by
        apply decodeReg_ext; intro i hi
        exact hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * i + 1; omega)
      have hBread : decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g
          = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
        apply decodeReg_ext; intro i hi
        exact hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * i + 2; omega)
      -- ⑤ Lower segments' decode on g = the IH value.
      have hlowdecode : kDecode gSep m g = kAugend gSep m f + kAddend gSep m f := by
        rw [hg]; exact ih f hcleanm
      -- Assemble the (m+1) layer.
      show kDecode gSep m (Gate.applyNat (segAdd gSep m) g)
          + segReg gSep m (Gate.applyNat (segAdd gSep m) g) * 2 ^ (m * (gSep + 1))
        = (kAugend gSep m f
            + decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f
                * 2 ^ (m * (gSep + 1)))
          + (kAddend gSep m f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
                * 2 ^ (m * (gSep + 1)))
      rw [hlow, hlowdecode, hseg, hAread, hBread]
      ring

/-! ## §14. k-segment advance bound — `Δ = n/g_sep` AS A CIRCUIT PROPERTY. -/

/-- Total deferred-carry occupancy across the `k` runways: `Σ_{j<k} segRunway j`. -/
def kRunwayOccupancy (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f => kRunwayOccupancy gSep k f + segRunway gSep k f

/-- Each segment runway holds at most one bit. -/
theorem segRunway_le_one (gSep j : Nat) (f : Nat → Bool) :
    segRunway gSep j f ≤ 1 := by
  unfold segRunway; by_cases h : f (cuccaroAdder.augendIdx (segBase gSep j) gSep)
    <;> simp [h]

/-- **The k-segment runway-occupancy bound.**  The total occupancy of the `k`
    runways is at most `k`.  HONEST CAVEAT: this is STRUCTURALLY TRIVIAL — the
    proof (`key : ∀ j g, …`) holds for ANY state, since occupancy is a sum of `k`
    single-bit runways; the `Gate.applyNat (runwayAddK gSep k) f` argument is
    decorative here.  It expresses only "we built `k` runways," NOT a non-trivial
    property of the circuit's action.  The genuine circuit content lives in
    `runwayAddK_exact` (exact sum with carries deferred into the runways) and, for
    k = 2, `runwayAdd2_runway_eq_carry` (the runway bit IS the real carry). -/
theorem runwayAddK_advance (gSep k : Nat) (f : Nat → Bool) :
    kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f) ≤ k := by
  induction k with
  | zero => simp [kRunwayOccupancy]
  | succ m _ =>
      -- Bound the (m+1)-fold occupancy by `(m+1)·1`: every summand is ≤ 1.
      have key : ∀ (j : Nat) (g : Nat → Bool), kRunwayOccupancy gSep j g ≤ j := by
        intro j
        induction j with
        | zero => intro g; simp [kRunwayOccupancy]
        | succ n ihn =>
            intro g
            show kRunwayOccupancy gSep n g + segRunway gSep n g ≤ n + 1
            have := ihn g
            have := segRunway_le_one gSep n g
            omega
      exact key (m + 1) (Gate.applyNat (runwayAddK gSep (m + 1)) f)

/-- Number of `gSep`-data segments an `n`-bit register splits into. -/
def numSegments (n gSep : Nat) : Nat := n / gSep

/-- **Runway count at `k = n/gSep`.**  Instantiating the occupancy bound at
    `k = n/gSep` segments gives `≤ n/gSep`.  HONEST CAVEAT (do NOT overstate, cf.
    `runwayAddK_advance`): this is the STRUCTURAL "there are `n/gSep` runways, each
    ≤ 1 bit" fact — true for any state, `applyNat` decorative.  It is NOT the
    deviation-relevant `Δ`.  The paper's `Δ = n/g_sep` advance is about the
    deferred-carry VALUE accumulating over a SEQUENCE of additions relative to the
    coset padding — a multi-add invariant this single-add count does NOT establish.
    What IS genuinely circuit-wired is `runwayAddK_exact` (this adder computes the
    exact sum, carries deferred into the runways, in the runway-interspersed
    encoding).  Connecting that encoding to the contiguous coset value, and the
    multi-add value-advance, remain open. -/
theorem runwayAddK_advance_div (n gSep : Nat) (f : Nat → Bool) :
    kRunwayOccupancy gSep (numSegments n gSep)
        (Gate.applyNat (runwayAddK gSep (numSegments n gSep)) f)
      ≤ n / gSep :=
  runwayAddK_advance gSep (numSegments n gSep) f

/-! ## §15. k-segment well-typedness. -/

/-- **WellTyped monotonicity** (local; enlarging the dimension preserves it).
    A self-contained copy so this file needs only the Cuccaro import. -/
theorem wellTyped_mono {dim dim' : Nat} {g : Gate}
    (h : Gate.WellTyped dim g) (hle : dim ≤ dim') : Gate.WellTyped dim' g := by
  induction g with
  | I => show 0 < dim'; have : 0 < dim := h; omega
  | X q => show q < dim'; have : q < dim := h; omega
  | CX a b => obtain ⟨_, _, hab⟩ := h; exact ⟨by omega, by omega, hab⟩
  | CCX a b c =>
      obtain ⟨_, _, _, hab, hac, hbc⟩ := h
      exact ⟨by omega, by omega, by omega, hab, hac, hbc⟩
  | seq g₁ g₂ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := h; exact ⟨ih₁ h₁, ih₂ h₂⟩

/-- Total qubit width of the k-segment runway adder. -/
def runwayWidthK (gSep k : Nat) : Nat := k * segStride gSep

/-- **`runwayAddK gSep k` is well-typed** at `runwayWidthK gSep k`.  Each segment
    `j < k` fits in `[segBase j, (j+1)·stride) ⊆ [0, k·stride)`. -/
theorem runwayAddK_wellTyped (gSep : Nat) :
    ∀ (k : Nat), 0 < k → Gate.WellTyped (runwayWidthK gSep k) (runwayAddK gSep k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ m ih =>
      intro _
      refine ⟨?_, ?_⟩
      · -- prefix `runwayAddK gSep m`: WellTyped at `m·stride ≤ (m+1)·stride`.
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          show Gate.WellTyped (runwayWidthK gSep 1) Gate.I
          show 0 < runwayWidthK gSep 1
          unfold runwayWidthK segStride; omega
        · have hwm := ih hm
          refine wellTyped_mono hwm ?_
          unfold runwayWidthK
          exact Nat.mul_le_mul_right _ (by omega)
      · -- segment m: width-`(gSep+1)` Cuccaro at base `segBase m`, fits in `(m+1)·stride`.
        show Gate.WellTyped (runwayWidthK gSep (m + 1))
          (cuccaro_n_bit_adder_full (gSep + 1) (segBase gSep m))
        apply cuccaro_n_bit_adder_full_wellTyped (gSep + 1) (segBase gSep m)
        show segBase gSep m + 2 * (gSep + 1) + 1 ≤ runwayWidthK gSep (m + 1)
        unfold runwayWidthK segBase segStride
        have : m * (2 * gSep + 3) + (2 * gSep + 3) = (m + 1) * (2 * gSep + 3) := by ring
        omega

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
