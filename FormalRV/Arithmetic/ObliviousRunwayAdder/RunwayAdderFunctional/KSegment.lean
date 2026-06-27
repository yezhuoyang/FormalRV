/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.KSegment
  ──────────────────────────────────────────────────
  Submodule of `RunwayAdderFunctional` (split out for per-file compile memory).
  Contains §11–§13: the generalization to `k` uniform runway segments — the
  `runwayAddK` circuit, the k-segment decodes/operand values, the k-segment frame
  lemmas, and the headline `runwayAddK_exact`.

  Re-exported VERBATIM from the original `RunwayAdderFunctional.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.TwoSegment

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

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

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
