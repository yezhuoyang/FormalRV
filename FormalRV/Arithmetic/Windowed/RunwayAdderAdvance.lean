/-
  FormalRV.Arithmetic.Windowed.RunwayAdderAdvance
  ───────────────────────────────────────────────
  The k-segment oblivious-runway adder's RUNWAY OCCUPANCY EQUALS THE ACTUAL
  DEFERRED CARRIES — a genuine circuit property, wired to `applyNat`.

  The committed `RunwayAdderFunctional.lean` proves `runwayAddK_advance :
  kRunwayOccupancy … ≤ k`, but that bound is STRUCTURALLY TRIVIAL (a sum of `k`
  single-bit runways is ≤ k for ANY state — the `applyNat` is decorative).

  This file UPGRADES that bound into a real theorem about the circuit's action.
  For each segment `m < k`, after running `runwayAddK gSep k` on a clean input,
  the runway bit of segment `m` holds EXACTLY the genuine carry-out of that
  segment's `gSep`-bit add:

      segRunway gSep m (applyNat (runwayAddK gSep k) f)
        = (a_m + b_m) / 2^gSep                                      (lemma #4)

  where `a_m`, `b_m` are the segment's `gSep`-bit augend/addend reads.  Summing
  over the segments gives the OCCUPANCY = CARRY-SUM equality:

      kRunwayOccupancy gSep k (applyNat (runwayAddK gSep k) f)
        = kCarrySum gSep k f                                        (lemma #5)

  and then `runwayAddK_advance_genuine : occupancy ≤ k` is re-proved THROUGH this
  carry equality (each `(a_m+b_m)/2^gSep ≤ 1` because the runway is one bit) — the
  occupancy is the REAL deferred-carry count, not just "we built k runways."

  Everything is `Gate.applyNat (runwayAddK gSep k) f` read through the concrete
  `def`s of `RunwayAdderFunctional`; the RHS of each headline is a CONCRETE carry
  expression `(a_m + b_m) / 2^gSep`, never a free field.  No `sorry`, no
  `native_decide`, no axioms beyond the prelude.

  WHAT IS STILL OPEN (carried over from `RunwayAdderFunctional`): the MULTI-ADD
  accumulation — how the deferred carries fold/accumulate across a SEQUENCE of
  oblivious adds — and the connection between the runway-interspersed encoding and
  the contiguous coset value.  This file establishes the single-add per-segment
  carry-occupancy equality only.
-/
import FormalRV.Arithmetic.Windowed.RunwayAdderFunctional

namespace FormalRV.Arithmetic.Windowed.RunwayAdderAdvance

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.Windowed.RunwayAdderFunctional

/-! ## §1. Split a segment's `(gSep+1)`-bit register into data + runway.

Mimics `lowReg_eq_data_add_runway`: peel the top bit with `decodeReg_succ`. -/

/-- **Split lemma.**  Segment `k`'s `(gSep+1)`-bit register splits as its low
    `gSep`-bit data plus the runway bit at place `2^gSep`. -/
theorem segReg_eq_data_add_runway (gSep k : Nat) (f : Nat → Bool) :
    segReg gSep k f
      = decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep f
          + 2 ^ gSep * segRunway gSep k f := by
  unfold segReg segRunway
  rw [decodeReg_succ]
  by_cases hb : f (cuccaroAdder.augendIdx (segBase gSep k) gSep) <;> simp [hb]

/-! ## §2. Per-segment runway = genuine carry-out (about `applyNat (segAdd …)`). -/

/-- **Per-segment runway = carry.**  Running segment `k`'s width-`(gSep+1)` add on
    a state `g` with its carry-in ancilla, runway bit, and addend-top bit clear,
    the runway bit holds EXACTLY the genuine carry-out `(a + b) / 2^gSep` of the
    segment's `gSep`-bit operands.  Wired to `Gate.applyNat (segAdd gSep k) g`. -/
theorem segRunway_segAdd_eq_carry (gSep k : Nat) (g : Nat → Bool)
    (hAnc : g (segBase gSep k) = false)
    (hRun : g (cuccaroAdder.augendIdx (segBase gSep k) gSep) = false)
    (hAddTop : g (cuccaroAdder.addendIdx (segBase gSep k) gSep) = false) :
    segRunway gSep k (Gate.applyNat (segAdd gSep k) g)
      = (decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep g
          + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep g) / 2 ^ gSep := by
  -- segReg after the add = a + b (EXACT), via `segReg_segAdd_exact_base`.
  set g1 := Gate.applyNat (segAdd gSep k) g with hg1
  have hExact : segReg gSep k g1
      = decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep g
          + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep g := by
    unfold segReg
    rw [hg1]
    show decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) (gSep + 1)
        (Gate.applyNat (cuccaroAdder.circuit (gSep + 1) (segBase gSep k)) g)
      = _
    exact segReg_segAdd_exact_base gSep (segBase gSep k) g hAnc hRun hAddTop
  -- segReg = data + 2^gSep·runway (split lemma), with data < 2^gSep.
  have hSplit := segReg_eq_data_add_runway gSep k g1
  have hdata : decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep g1 < 2 ^ gSep :=
    decodeReg_lt _ gSep g1
  set S := decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep g
          + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep g with hS
  set d := decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep g1 with hd
  set r := segRunway gSep k g1 with hr
  -- S = d + 2^gSep·r with d < 2^gSep, so S / 2^gSep = r.
  have hSeq : S = d + 2 ^ gSep * r := by rw [← hExact, hSplit]
  rw [hSeq, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hdata]
  simp

/-! ## §3. Frame: a HIGHER segment fixes a LOWER segment's runway position. -/

/-- **A higher segment's add fixes a lower segment's runway position.**  For
    `m < j`, segment `m`'s runway sits at `segBase m + 2gSep+1`, which is below
    `segBase (m+1) = segBase m + (2gSep+3) ≤ segBase j` — outside segment `j`'s
    block `[segBase j, segBase j + (2gSep+3))`. -/
theorem segAdd_fixes_runway_below (gSep j m : Nat) (g : Nat → Bool) (hm : m < j) :
    Gate.applyNat (segAdd gSep j) g (cuccaroAdder.augendIdx (segBase gSep m) gSep)
      = g (cuccaroAdder.augendIdx (segBase gSep m) gSep) := by
  unfold segAdd
  apply cuccaroAdder.frame (gSep + 1) (segBase gSep j)
  show ¬ inBlock (segBase gSep j) (cuccaroAdder.span (gSep + 1))
        (cuccaroAdder.augendIdx (segBase gSep m) gSep)
  unfold inBlock
  -- runway position = segBase m + 2gSep + 1; need it < segBase j.
  show ¬ (segBase gSep j ≤ segBase gSep m + 2 * gSep + 1
        ∧ segBase gSep m + 2 * gSep + 1 < segBase gSep j + (2 * (gSep + 1) + 1))
  -- segBase is monotone with step (2gSep+3): segBase (m+1) = segBase m + (2gSep+3).
  have hstep : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
    unfold segBase segStride; ring
  have hmono : segBase gSep (m + 1) ≤ segBase gSep j := by
    unfold segBase segStride
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## §4. MAIN — every segment's runway = its genuine carry-out, by induction. -/

/-- **MAIN.**  After running the full `k`-segment runway adder on a clean input,
    EACH segment `m < k`'s runway bit holds EXACTLY that segment's genuine
    carry-out `(a_m + b_m) / 2^gSep`.  Proved by induction on `k`; literally about
    `Gate.applyNat (runwayAddK gSep k) f` and a CONCRETE carry RHS. -/
theorem segRunway_runwayAddK_eq (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f → ∀ (m : Nat), m < k →
      segRunway gSep m (Gate.applyNat (runwayAddK gSep k) f)
        = (decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f) / 2 ^ gSep := by
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
      · -- case m < k: segAdd k fixes segment m's runway position; conclude by IH.
        rw [happ]
        have hfixrw : segRunway gSep m (Gate.applyNat (segAdd gSep k) g)
            = segRunway gSep m g := by
          unfold segRunway
          rw [segAdd_fixes_runway_below gSep k m g hmk]
        rw [hfixrw, hg]
        exact ih f hcleank m hmk
      · -- case m = k: apply lemma 2 to g, then push g-reads back to f.
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
        rw [segRunway_segAdd_eq_carry gSep m g hAnc' hRun' hAddTop']
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

/-! ## §5. Total runway occupancy = total deferred-carry sum. -/

/-- Total deferred-carry value across the `k` segments: `Σ_{j<k} (a_j+b_j)/2^gSep`,
    reading each segment's `gSep`-bit augend/addend off `f` at the same `segBase`
    positions used by `kRunwayOccupancy` / `segRunway`. -/
def kCarrySum (gSep : Nat) : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f =>
      kCarrySum gSep k f
        + (decodeReg (cuccaroAdder.augendIdx (segBase gSep k)) gSep f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep k)) gSep f) / 2 ^ gSep

/-- **Occupancy = carry-sum.**  The total runway occupancy after the full
    `k`-segment runway add equals the total genuine deferred-carry sum — every
    runway holds its segment's real carry-out (folding the MAIN lemma over all
    segments).  Wired to `Gate.applyNat (runwayAddK gSep k) f`. -/
theorem runwayAddK_occupancy_eq_carries (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f →
      kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f)
        = kCarrySum gSep k f := by
  intro k f hclean
  -- Each segment runway of the FULL output is its carry (MAIN lemma).
  have hseg : ∀ m, m < k →
      segRunway gSep m (Gate.applyNat (runwayAddK gSep k) f)
        = (decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f) / 2 ^ gSep :=
    fun m hm => segRunway_runwayAddK_eq gSep k f hclean m hm
  -- Fold over the first `j ≤ k` segments.
  set h := Gate.applyNat (runwayAddK gSep k) f with hh
  have aux : ∀ j, j ≤ k →
      kRunwayOccupancy gSep j h = kCarrySum gSep j f := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ n ihn =>
        intro hjk
        show kRunwayOccupancy gSep n h + segRunway gSep n h
          = kCarrySum gSep n f
            + (decodeReg (cuccaroAdder.augendIdx (segBase gSep n)) gSep f
                + decodeReg (cuccaroAdder.addendIdx (segBase gSep n)) gSep f) / 2 ^ gSep
        rw [ihn (by omega), hh, hseg n (by omega)]
  exact aux k (le_refl _)

/-! ## §6. Genuine advance bound — re-proved THROUGH the carry equality. -/

/-- A single segment's deferred carry is at most one bit: `a + b < 2^(gSep+1)`,
    so `(a + b) / 2^gSep ≤ 1`.  This is what makes each runway a genuine 0/1
    carry. -/
theorem segCarry_le_one (gSep j : Nat) (f : Nat → Bool) :
    (decodeReg (cuccaroAdder.augendIdx (segBase gSep j)) gSep f
      + decodeReg (cuccaroAdder.addendIdx (segBase gSep j)) gSep f) / 2 ^ gSep ≤ 1 := by
  have ha : decodeReg (cuccaroAdder.augendIdx (segBase gSep j)) gSep f < 2 ^ gSep :=
    decodeReg_lt _ gSep f
  have hb : decodeReg (cuccaroAdder.addendIdx (segBase gSep j)) gSep f < 2 ^ gSep :=
    decodeReg_lt _ gSep f
  -- a + b < 2 * 2^gSep, so (a+b)/2^gSep < 2, i.e. ≤ 1.
  have hlt : decodeReg (cuccaroAdder.augendIdx (segBase gSep j)) gSep f
      + decodeReg (cuccaroAdder.addendIdx (segBase gSep j)) gSep f < 2 * 2 ^ gSep := by
    omega
  have hdiv : (decodeReg (cuccaroAdder.augendIdx (segBase gSep j)) gSep f
      + decodeReg (cuccaroAdder.addendIdx (segBase gSep j)) gSep f) / 2 ^ gSep < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    omega
  omega

/-- The total deferred-carry sum is at most `k` — NON-trivially: it is a sum of
    `k` genuine 0/1 carries (`segCarry_le_one`), not an abstract bit count. -/
theorem kCarrySum_le (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kCarrySum gSep k f ≤ k := by
  intro k
  induction k with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      show kCarrySum gSep n f
          + (decodeReg (cuccaroAdder.augendIdx (segBase gSep n)) gSep f
              + decodeReg (cuccaroAdder.addendIdx (segBase gSep n)) gSep f) / 2 ^ gSep
        ≤ n + 1
      have h1 := ih f
      have h2 := segCarry_le_one gSep n f
      omega

/-- **THE ADVANCE BOUND, RE-PROVED AS A GENUINE CIRCUIT PROPERTY.**  The total
    runway occupancy after the full `k`-segment runway add is `≤ k` — and now this
    is proved THROUGH the carry equality (`runwayAddK_occupancy_eq_carries` +
    `kCarrySum_le`): the occupancy IS the real deferred-carry count, each runway
    holding its segment's genuine 0/1 carry-out.  Contrast the structurally-trivial
    bit-count proof of `RunwayAdderFunctional.runwayAddK_advance`, which holds for
    any state and never inspects the circuit's action. -/
theorem runwayAddK_advance_genuine (gSep k : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k f) :
    kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f) ≤ k := by
  rw [runwayAddK_occupancy_eq_carries gSep k f hclean]
  exact kCarrySum_le gSep k f

end FormalRV.Arithmetic.Windowed.RunwayAdderAdvance
