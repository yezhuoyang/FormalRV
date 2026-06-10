/-
  FormalRV.Arithmetic.Windowed.RunwayAdderContiguous
  ──────────────────────────────────────────────────
  CLOSING THE "runway-interspersed encoding ↔ contiguous integer value" GAP.

  The committed `RunwayAdderFunctional`/`RunwayAdderAdvance` prove that the
  k-segment oblivious-carry-runway adder leaves each segment `m`'s width-`(gSep+1)`
  register holding EXACTLY `a_m + b_m` (data + the deferred carry, in the runway
  bit at place `2^gSep` of that register).  Those files read each segment's
  register at the SPREAD place value `2^(m·(gSep+1))`, which keeps every runway
  carry "parked" — the carries are deferred, not folded.

  THE KEY INSIGHT OF THIS FILE.  Re-read those same registers at CONTIGUOUS place
  value `2^(m·gSep)` (NOT the spread `2^(m·(gSep+1))`).  Then segment `m`'s runway
  carry, which lives at the segment-internal bit `2^gSep`, lands at GLOBAL place
  `2^(m·gSep) · 2^gSep = 2^((m+1)·gSep)` — i.e. EXACTLY segment `(m+1)`'s low
  place.  So reading at contiguous spacing performs the inter-segment carry FOLD
  FOR FREE, by place value alone:

      Σ_{m<k} segReg_m(output) · 2^(m·gSep)
        = Σ_{m<k} (a_m + b_m) · 2^(m·gSep)
        = contiguousAugend f + contiguousAddend f.

  Once each `segReg_m(output) = a_m + b_m` is in hand (the MAIN lemma below, which
  MIRRORS `RunwayAdderAdvance.segRunway_runwayAddK_eq` but for the FULL register
  instead of just the runway bit), the headline is pure place-value algebra — no
  division, no truncation, no overflow precondition.

  THE HEADLINE (wired to `applyNat`, concrete recursive RHS, NOT free fields):

      contiguousDecode gSep k (Gate.applyNat (runwayAddK gSep k) f)
        = contiguousAugend gSep k f + contiguousAddend gSep k f.

  Everything is `Gate.applyNat (runwayAddK gSep k) f` read through concrete `def`s;
  no `sorry`, no `native_decide`, no axioms beyond the prelude.

  WHAT IS STILL OPEN (carried over).  The multi-add SEQUENCE: between successive
  oblivious adds the runways must be folded/cleared for `kClean` to hold again, so
  the deferred carries accumulate across adds — the value-advance `Δ` relevant to
  the wrap/deviation bound.  And the probabilistic wrap bound itself.  This file
  closes ONLY the single-add encoding↔contiguous-value connection: at contiguous
  spacing the runway register decodes to exactly `contiguous(a) + contiguous(b)`,
  the inter-segment carry-fold performed implicitly by place value.
-/
import FormalRV.Arithmetic.Windowed.RunwayAdderAdvance

namespace FormalRV.Arithmetic.Windowed.RunwayAdderContiguous

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.Windowed.RunwayAdderFunctional
open FormalRV.Arithmetic.Windowed.RunwayAdderAdvance

/-! ## §1. Frame — a higher segment fixes a lower segment's FULL register read. -/

/-- **Frame lemma (FULL register).**  For `m < j`, running segment `j`'s
    width-`(gSep+1)` add leaves segment `m`'s WHOLE `(gSep+1)`-bit register
    unchanged: every position `segBase m + 2i+1` (i ≤ gSep) is `< segBase j`,
    hence below segment `j`'s block `[segBase j, segBase j + (2gSep+3))`.  Mirrors
    `RunwayAdderAdvance.segAdd_fixes_runway_below` but for the entire register, not
    just the runway bit. -/
theorem segAdd_fixes_segReg_below (gSep j m : Nat) (g : Nat → Bool) (hm : m < j) :
    decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) (gSep + 1)
        (Gate.applyNat (segAdd gSep j) g)
      = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) (gSep + 1) g := by
  apply decodeReg_ext
  intro i hi
  -- position `segBase m + 2i+1` with `i ≤ gSep`; show segAdd j fixes it.
  show Gate.applyNat (segAdd gSep j) g (cuccaroAdder.augendIdx (segBase gSep m) i)
    = g (cuccaroAdder.augendIdx (segBase gSep m) i)
  unfold segAdd
  apply cuccaroAdder.frame (gSep + 1) (segBase gSep j)
  show ¬ inBlock (segBase gSep j) (cuccaroAdder.span (gSep + 1))
        (cuccaroAdder.augendIdx (segBase gSep m) i)
  unfold inBlock
  show ¬ (segBase gSep j ≤ segBase gSep m + 2 * i + 1
        ∧ segBase gSep m + 2 * i + 1 < segBase gSep j + (2 * (gSep + 1) + 1))
  -- segBase (m+1) = segBase m + (2gSep+3) ≤ segBase j, and 2i+1 ≤ 2gSep+1 < 2gSep+3.
  have hstep : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
    unfold segBase segStride; ring
  have hmono : segBase gSep (m + 1) ≤ segBase gSep j := by
    unfold segBase segStride
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## §2. MAIN — every segment's FULL register = its `a_m + b_m`, by induction. -/

/-- **MAIN.**  After running the full `k`-segment runway adder on a clean input,
    EACH segment `m < k`'s width-`(gSep+1)` register holds EXACTLY that segment's
    `a_m + b_m` (the gSep-bit augend read + the gSep-bit addend read), the carry
    deposited in the runway bit, NO truncation.  Proved by induction on `k`,
    MIRRORING `RunwayAdderAdvance.segRunway_runwayAddK_eq` but for the full register
    (`segReg`) instead of the runway bit — no division.  Literally about
    `Gate.applyNat (runwayAddK gSep k) f` with a CONCRETE `a_m + b_m` RHS. -/
theorem segReg_runwayAddK_eq (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f → ∀ (m : Nat), m < k →
      segReg gSep m (Gate.applyNat (runwayAddK gSep k) f)
        = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
  intro k
  induction k with
  | zero => intro f _ m hm; omega
  | succ k ih =>
      intro f hclean m hm
      -- runwayAddK (k+1) = segAdd k ∘ runwayAddK k.
      set g := Gate.applyNat (runwayAddK gSep k) f with hg
      have happ : Gate.applyNat (runwayAddK gSep (k + 1)) f
          = Gate.applyNat (segAdd gSep k) g := rfl
      have hcleank : kClean gSep k f := fun j hj => hclean j (by omega)
      rcases Nat.lt_or_ge m k with hmk | hmk
      · -- case m < k: segAdd k fixes segment m's full register; conclude by IH.
        rw [happ]
        have hfixreg : segReg gSep m (Gate.applyNat (segAdd gSep k) g)
            = segReg gSep m g := by
          unfold segReg
          exact segAdd_fixes_segReg_below gSep k m g hmk
        rw [hfixreg, hg]
        exact ih f hcleank m hmk
      · -- case m = k: apply per-segment exactness to g, then push g-reads back to f.
        have hmeq : m = k := by omega
        subst hmeq
        rw [happ]
        -- g agrees with f on all positions ≥ segBase gSep m (lower segs fix above).
        have hfix : ∀ q, segBase gSep m ≤ q → g q = f q := by
          intro q hq; rw [hg]; exact runwayAddK_fixes_above gSep m f q hq
        obtain ⟨hAnc, hRun, hAddTop⟩ := hclean m hm
        have hAnc' : g (segBase gSep m) = false := by
          rw [hfix _ (le_refl _)]; exact hAnc
        have hRun' : g (cuccaroAdder.augendIdx (segBase gSep m) gSep) = false := by
          rw [hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * gSep + 1; omega)]
          exact hRun
        have hAddTop' : g (cuccaroAdder.addendIdx (segBase gSep m) gSep) = false := by
          rw [hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * gSep + 2; omega)]
          exact hAddTop
        -- segReg after segment m's add = a_m + b_m (EXACT), read off g.
        have hseg : segReg gSep m (Gate.applyNat (segAdd gSep m) g)
            = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep g
              + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g := by
          unfold segReg segAdd
          exact segReg_segAdd_exact_base gSep (segBase gSep m) g hAnc' hRun' hAddTop'
        rw [hseg]
        -- the gSep data reads on g equal the reads on f.
        have hAread : decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep g
            = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f := by
          apply decodeReg_ext; intro i hi
          exact hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * i + 1; omega)
        have hBread : decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g
            = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
          apply decodeReg_ext; intro i hi
          exact hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * i + 2; omega)
        rw [hAread, hBread]

/-! ## §3. Contiguous decode + operand values (concrete recursive defs). -/

/-- **Contiguous place-value decode.**  Read each segment's width-`(gSep+1)`
    register at the CONTIGUOUS place `2^(m·gSep)` (NOT the spread
    `2^(m·(gSep+1))`).  Each segment's runway carry, internal place `2^gSep`, then
    lands at global place `2^((m+1)·gSep)` — segment `(m+1)`'s low place — so the
    inter-segment carry-fold is performed implicitly by place value. -/
def contiguousDecode (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f => contiguousDecode gSep k f + segReg gSep k f * 2 ^ (k * gSep)

/-- Contiguous augend value: `Σ_{m<k} a_m · 2^(m·gSep)`, reading each segment's
    `gSep`-bit augend register at contiguous spacing. -/
def contiguousAugend (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f =>
      contiguousAugend gSep k f
        + decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep f * 2 ^ (k * gSep)

/-- Contiguous addend value: `Σ_{m<k} b_m · 2^(m·gSep)`. -/
def contiguousAddend (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f =>
      contiguousAddend gSep k f
        + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep f * 2 ^ (k * gSep)

/-! ## §4. HEADLINE — contiguous correctness. -/

/-- `contiguousDecode gSep k` depends only on the state at positions
    `< segBase gSep k`: each of its segment registers `m < k` sits entirely below
    `segBase gSep k`.  (Folds the FULL-register frame over the `k` summands.) -/
theorem contiguousDecode_congr (gSep : Nat) :
    ∀ (k : Nat) (f g : Nat → Bool),
      (∀ p, p < segBase gSep k → f p = g p) →
      contiguousDecode gSep k f = contiguousDecode gSep k g := by
  intro k
  induction k with
  | zero => intro f g _; rfl
  | succ m ih =>
      intro f g hagree
      have hbase_mono : segBase gSep m ≤ segBase gSep (m + 1) := by
        unfold segBase segStride
        exact Nat.mul_le_mul_right _ (by omega)
      show contiguousDecode gSep m f + segReg gSep m f * 2 ^ (m * gSep)
        = contiguousDecode gSep m g + segReg gSep m g * 2 ^ (m * gSep)
      have h1 : contiguousDecode gSep m f = contiguousDecode gSep m g :=
        ih f g (fun p hp => hagree p (lt_of_lt_of_le hp hbase_mono))
      have h2 : segReg gSep m f = segReg gSep m g := by
        unfold segReg
        apply decodeReg_ext
        intro i hi
        -- augend position `segBase m + 2i+1` with i ≤ gSep; show it `< segBase (m+1)`.
        have hpos : cuccaroAdder.augendIdx (segBase gSep m) i < segBase gSep (m + 1) := by
          show segBase gSep m + 2 * i + 1 < segBase gSep (m + 1)
          have hexp : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
            unfold segBase segStride; ring
          omega
        exact hagree _ hpos
      rw [h1, h2]

/-- **HEADLINE — contiguous correctness.**  Reading the runway adder's output at
    CONTIGUOUS place value yields EXACTLY `contiguous(a) + contiguous(b)`: the
    inter-segment carry-fold is done implicitly by place value.  Proved by
    induction on `k`; the top segment is rewritten via the MAIN lemma (at `m = k`),
    the lower segments stay (the full-register frame, folded through
    `contiguousDecode_congr`) and reduce to the IH on
    `Gate.applyNat (runwayAddK gSep k) f`; then `ring`.  Literally about
    `Gate.applyNat (runwayAddK gSep k) f` with a CONCRETE contiguous-sum RHS. -/
theorem runwayAddK_contiguous (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f →
      contiguousDecode gSep k (Gate.applyNat (runwayAddK gSep k) f)
        = contiguousAugend gSep k f + contiguousAddend gSep k f := by
  intro k
  induction k with
  | zero => intro f _; rfl
  | succ k ih =>
      intro f hclean
      set g := Gate.applyNat (runwayAddK gSep k) f with hg
      have happ : Gate.applyNat (runwayAddK gSep (k + 1)) f
          = Gate.applyNat (segAdd gSep k) g := rfl
      have hcleank : kClean gSep k f := fun j hj => hclean j (by omega)
      -- Unfold the (k+1) layer of contiguousDecode on the full output.
      show contiguousDecode gSep k (Gate.applyNat (runwayAddK gSep (k + 1)) f)
          + segReg gSep k (Gate.applyNat (runwayAddK gSep (k + 1)) f) * 2 ^ (k * gSep)
        = (contiguousAugend gSep k f
            + decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep f * 2 ^ (k * gSep))
          + (contiguousAddend gSep k f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep f * 2 ^ (k * gSep))
      -- ① The top segment's register = a_k + b_k (MAIN lemma at m = k).
      have htop : segReg gSep k (Gate.applyNat (runwayAddK gSep (k + 1)) f)
          = decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep f
              + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep f :=
        segReg_runwayAddK_eq gSep (k + 1) f hclean k (by omega)
      -- ② The lower-k contiguous decode of the FULL output reduces to the IH:
      --    segAdd k fixes every position < segBase k, so the lower decode is the
      --    same as on g = applyNat (runwayAddK gSep k) f.
      have hlow : contiguousDecode gSep k (Gate.applyNat (runwayAddK gSep (k + 1)) f)
          = contiguousDecode gSep k g := by
        rw [happ]
        apply contiguousDecode_congr
        intro p hp
        exact segAdd_fixes_below gSep k g p hp
      have hlowIH : contiguousDecode gSep k g
          = contiguousAugend gSep k f + contiguousAddend gSep k f := by
        rw [hg]; exact ih f hcleank
      rw [htop, hlow, hlowIH]
      ring

end FormalRV.Arithmetic.Windowed.RunwayAdderContiguous
