/-
  FormalRV.Arithmetic.Windowed.RunwayAdderMultiAdd
  ────────────────────────────────────────────────
  CLOSING THE MULTI-ADD GAP for the oblivious-carry-runway adder.

  The committed files prove the SINGLE-ADD facts:
    • `RunwayAdderFunctional.runwayAddK_exact` — one runway add computes the exact
      sum in the spread (interspersed) encoding;
    • `RunwayAdderContiguous.runwayAddK_contiguous` — read at contiguous spacing
      the same single add equals `contiguous(a) + contiguous(b)`.

  THE GAP THIS FILE CLOSES.  Iterate the runway adder `t` times against the SAME
  addend register (which the Cuccaro adder RESTORES bit-for-bit each add, and whose
  carry-in ancilla it likewise RESTORES).  Then the contiguous reading accumulates

      contiguousDecode (applyNat (iterGate (runwayAddK gSep k) t) f)
        = contiguousAugend' f + t · contiguousAddend f,

  EXACT under the per-segment no-overflow hypothesis `segReg_m f + t·b_m < 2^(gSep+1)`
  (each segment's `(gSep+1)`-bit register, runway included, never overflows over the
  whole run).  This is the deterministic core of the deferred-accumulation deviation:
  the gap-2 wrap/deviation bound is precisely the probability that this no-overflow
  condition fails.

  ════════════════════════════════════════════════════════════════════════════
  WHY THE MATH IS CLEAN (and what the iteration invariant must carry)

  The per-segment add is `cuccaroAdder.circuit (gSep+1) (segBase m)`.  Its
  `sumCorrect` needs ONLY the carry-in ancilla clean (`f (segBase m) = false`) — NOT
  the runway/top augend bit clean.  So on the FULL `(gSep+1)`-bit augend it gives

      segReg_m(after) = (segReg_m(before) + addend_{gSep+1}) mod 2^(gSep+1).

  The adder RESTORES the carry-in ancilla (`ancRestored`) and the addend register
  (`addendRestored`) each add, so the precondition for the NEXT iteration holds and
  the addend `addend_{gSep+1}` is unchanged.  Crucially the iteration invariant
  `IterReady` does NOT require the runways clean — only the carry-in ancilla AND the
  addend's top bit (so that `addend_{gSep+1} = b_m`, the gSep-bit segment addend).

  Hence after `t` iterations `segReg_m = (segReg_m(f) + t·b_m) mod 2^(gSep+1)`; under
  per-segment no-overflow this is `segReg_m(f) + t·b_m`, and the contiguous decode
  (which folds runways by place value) gives `augend' + t·b`.

  ════════════════════════════════════════════════════════════════════════════
  SCOPE.  This is SAME-ADDEND iteration: the addend register is restored each add,
  so `t` adds accumulate `+ t·b`.  Distinct-addend sequences (the windowed-lookup
  loop, where a fresh `b` is loaded each step via a table lookup) compose
  identically but need the lookup modeled separately — out of scope here.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.  Every headline is
  `Gate.applyNat (iterGate (runwayAddK gSep k) t) f` read through concrete `def`s,
  with a concrete `+ t·b` RHS.
-/
import FormalRV.Arithmetic.Windowed.RunwayAdderContiguous

namespace FormalRV.Arithmetic.Windowed.RunwayAdderMultiAdd

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.Windowed.RunwayAdderFunctional
open FormalRV.Arithmetic.Windowed.RunwayAdderContiguous

/-! ## §1. Iterating a gate. -/

/-- `iterGate g t` runs `g` sequentially `t` times.  `iterGate g (t+1)` puts the
    fresh copy LAST, so it unfolds to "run `iterGate g t`, then `g`". -/
def iterGate (g : Gate) : Nat → Gate
  | 0 => Gate.I
  | t + 1 => Gate.seq (iterGate g t) g

/-- The defining `applyNat` recursion for `iterGate`. -/
@[simp] theorem applyNat_iterGate_succ (g : Gate) (t : Nat) (f : Nat → Bool) :
    Gate.applyNat (iterGate g (t + 1)) f
      = Gate.applyNat g (Gate.applyNat (iterGate g t) f) := rfl

/-- `iterGate g 0` is the identity on states. -/
@[simp] theorem applyNat_iterGate_zero (g : Gate) (f : Nat → Bool) :
    Gate.applyNat (iterGate g 0) f = f := rfl

/-! ## §2. The iteration invariant.

`IterReady gSep k f` is what every iteration needs and re-establishes: for each
segment `m < k`, the carry-in ancilla (`segBase m`) and the addend's TOP bit
(`addendIdx (segBase m) gSep`) are clear.  It does NOT require the runways clean —
the runways accumulate the deferred carries across the run, and the next add only
needs its carry-in ancilla clean (for `sumCorrect`) and the addend top clear (so
the `(gSep+1)`-bit addend read equals the `gSep`-bit segment addend `b_m`). -/
def IterReady (gSep k : Nat) (f : Nat → Bool) : Prop :=
  ∀ m, m < k →
    f (segBase gSep m) = false
    ∧ f (cuccaroAdder.addendIdx (segBase gSep m) gSep) = false

/-! ## §3. Cross-segment frame for the carry-in / addend-top positions.

A segment `j`'s add either restores those two positions in its own block
(`ancRestored` / `addendRestored`, needing only its carry-in clean) or leaves
another segment's positions untouched (disjoint blocks, `frame`). -/

/-- A DIFFERENT segment `j ≠ m`'s add fixes segment `m`'s carry-in ancilla
    position `segBase m` (disjoint Cuccaro blocks). -/
theorem segAdd_fixes_anc_off (gSep j m : Nat) (g : Nat → Bool) (hjm : j ≠ m) :
    Gate.applyNat (segAdd gSep j) g (segBase gSep m) = g (segBase gSep m) := by
  unfold segAdd
  apply cuccaroAdder.frame (gSep + 1) (segBase gSep j)
  show ¬ inBlock (segBase gSep j) (cuccaroAdder.span (gSep + 1)) (segBase gSep m)
  unfold inBlock cuccaroAdder
  -- block j = [j·s, j·s + (2gSep+3)); segBase m = m·s; for j ≠ m these are disjoint.
  show ¬ (segBase gSep j ≤ segBase gSep m ∧ segBase gSep m < segBase gSep j + (2 * (gSep + 1) + 1))
  have hjlt : segBase gSep (j + 1) = segBase gSep j + (2 * gSep + 3) := by
    unfold segBase segStride; ring
  have hmlt : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
    unfold segBase segStride; ring
  rcases Nat.lt_or_ge j m with hlt | hge
  · -- j < m: segBase (j+1) ≤ segBase m, so segBase m ≥ segBase j + (2gSep+3).
    have : segBase gSep (j + 1) ≤ segBase gSep m := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    omega
  · -- j > m (j ≠ m so j ≥ m+1): segBase (m+1) ≤ segBase j, so segBase m < segBase j.
    have hmj : m < j := by omega
    have : segBase gSep (m + 1) ≤ segBase gSep j := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- A DIFFERENT segment `j ≠ m`'s add fixes segment `m`'s addend-top position
    `addendIdx (segBase m) gSep = segBase m + 2gSep+2` (disjoint blocks). -/
theorem segAdd_fixes_addTop_off (gSep j m : Nat) (g : Nat → Bool) (hjm : j ≠ m) :
    Gate.applyNat (segAdd gSep j) g (cuccaroAdder.addendIdx (segBase gSep m) gSep)
      = g (cuccaroAdder.addendIdx (segBase gSep m) gSep) := by
  unfold segAdd
  apply cuccaroAdder.frame (gSep + 1) (segBase gSep j)
  show ¬ inBlock (segBase gSep j) (cuccaroAdder.span (gSep + 1))
        (cuccaroAdder.addendIdx (segBase gSep m) gSep)
  unfold inBlock
  show ¬ (segBase gSep j ≤ segBase gSep m + 2 * gSep + 2
        ∧ segBase gSep m + 2 * gSep + 2 < segBase gSep j + (2 * (gSep + 1) + 1))
  rcases Nat.lt_or_ge j m with hlt | hge
  · have : segBase gSep (j + 1) ≤ segBase gSep m := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    have hjlt : segBase gSep (j + 1) = segBase gSep j + (2 * gSep + 3) := by
      unfold segBase segStride; ring
    omega
  · have hmj : m < j := by omega
    have : segBase gSep (m + 1) ≤ segBase gSep j := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    have hmlt : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
      unfold segBase segStride; ring
    omega

/-- Segment `j`'s own add restores its carry-in ancilla (`ancRestored`, needs only
    the carry-in clean before the add). -/
theorem segAdd_restores_anc (gSep j : Nat) (g : Nat → Bool)
    (hAnc : g (segBase gSep j) = false) :
    Gate.applyNat (segAdd gSep j) g (segBase gSep j) = false := by
  unfold segAdd
  have hclean : cuccaroAdder.ancClean g (gSep + 1) (segBase gSep j) := by
    show g (segBase gSep j) = false; exact hAnc
  have := cuccaroAdder.ancRestored (gSep + 1) (segBase gSep j) g hclean
  -- ancClean of the output is exactly `output (segBase j) = false`.
  show Gate.applyNat (cuccaroAdder.circuit (gSep + 1) (segBase gSep j)) g (segBase gSep j)
      = false
  exact this

/-- Segment `j`'s own add restores its addend's top bit (`addendRestored` at index
    `gSep < gSep+1`, needs only the carry-in clean before the add). -/
theorem segAdd_restores_addTop (gSep j : Nat) (g : Nat → Bool)
    (hAnc : g (segBase gSep j) = false) :
    Gate.applyNat (segAdd gSep j) g (cuccaroAdder.addendIdx (segBase gSep j) gSep)
      = g (cuccaroAdder.addendIdx (segBase gSep j) gSep) := by
  unfold segAdd
  have hclean : cuccaroAdder.ancClean g (gSep + 1) (segBase gSep j) := by
    show g (segBase gSep j) = false; exact hAnc
  exact cuccaroAdder.addendRestored (gSep + 1) (segBase gSep j) g hclean gSep (by omega)

/-- **One segment add preserves `IterReady`.**  If segment `j`'s carry-in is clean
    before its add (so `ancRestored`/`addendRestored` apply), then `segAdd gSep j`
    re-establishes `IterReady` for every segment `m < k`: its own positions are
    restored, the others are untouched (disjoint blocks). -/
theorem segAdd_preserves_IterReady (gSep k j : Nat) (g : Nat → Bool)
    (hjk : j < k) (hready : IterReady gSep k g) :
    IterReady gSep k (Gate.applyNat (segAdd gSep j) g) := by
  intro m hm
  obtain ⟨hAncm, hAddTopm⟩ := hready m hm
  obtain ⟨hAncj, _⟩ := hready j hjk
  by_cases hjm : j = m
  · -- own segment: restoration lemmas, then the input value is `false`.
    subst hjm
    refine ⟨segAdd_restores_anc gSep j g hAncj, ?_⟩
    rw [segAdd_restores_addTop gSep j g hAncj]; exact hAddTopm
  · -- other segment: frame lemmas, value carried from `g`.
    refine ⟨?_, ?_⟩
    · rw [segAdd_fixes_anc_off gSep j m g hjm]; exact hAncm
    · rw [segAdd_fixes_addTop_off gSep j m g hjm]; exact hAddTopm

/-! ## §4. Deliverable #2 — the full adder preserves `IterReady`. -/

/-- **A PREFIX `runwayAddK gSep j` (`j ≤ k`) preserves `IterReady gSep k`.**  Each
    constituent `segAdd i` (`i < j ≤ k`) restores its own carry-in/addend-top and
    leaves the others untouched (`segAdd_preserves_IterReady`); fold over the `j`
    segments.  This prefix form is what the addend/step inductions need. -/
theorem runwayAddK_prefix_preserves_IterReady (gSep k : Nat) :
    ∀ (j : Nat), j ≤ k → ∀ (f : Nat → Bool), IterReady gSep k f →
      IterReady gSep k (Gate.applyNat (runwayAddK gSep j) f) := by
  intro j
  induction j with
  | zero => intro _ f hready; exact hready
  | succ n ih =>
      intro hjk f hready
      -- runwayAddK (n+1) = segAdd n ∘ runwayAddK n.
      show IterReady gSep k (Gate.applyNat (segAdd gSep n)
            (Gate.applyNat (runwayAddK gSep n) f))
      have hprefix : IterReady gSep k (Gate.applyNat (runwayAddK gSep n) f) :=
        ih (by omega) f hready
      exact segAdd_preserves_IterReady gSep k n
        (Gate.applyNat (runwayAddK gSep n) f) (by omega) hprefix

/-- **`runwayAddK gSep k` preserves `IterReady gSep k`.**  So the precondition for
    the NEXT iteration of the runway adder holds.  (The `j = k` case of the prefix
    lemma.) -/
theorem runwayAddK_preserves_IterReady (gSep : Nat) (k : Nat)
    (f : Nat → Bool) (hready : IterReady gSep k f) :
    IterReady gSep k (Gate.applyNat (runwayAddK gSep k) f) :=
  runwayAddK_prefix_preserves_IterReady gSep k k (le_refl _) f hready

/-! ## §5. Deliverable #3 — the addend register `b_m` is invariant. -/

/-- A DIFFERENT segment `j ≠ m`'s add fixes every addend-register position
    `addendIdx (segBase m) i` (`i < gSep`) of segment `m` (disjoint blocks). -/
theorem segAdd_fixes_addend_off (gSep j m : Nat) (g : Nat → Bool) (hjm : j ≠ m)
    (i : Nat) (hi : i < gSep) :
    Gate.applyNat (segAdd gSep j) g (cuccaroAdder.addendIdx (segBase gSep m) i)
      = g (cuccaroAdder.addendIdx (segBase gSep m) i) := by
  unfold segAdd
  apply cuccaroAdder.frame (gSep + 1) (segBase gSep j)
  show ¬ inBlock (segBase gSep j) (cuccaroAdder.span (gSep + 1))
        (cuccaroAdder.addendIdx (segBase gSep m) i)
  unfold inBlock
  show ¬ (segBase gSep j ≤ segBase gSep m + 2 * i + 2
        ∧ segBase gSep m + 2 * i + 2 < segBase gSep j + (2 * (gSep + 1) + 1))
  rcases Nat.lt_or_ge j m with hlt | hge
  · have : segBase gSep (j + 1) ≤ segBase gSep m := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    have hjlt : segBase gSep (j + 1) = segBase gSep j + (2 * gSep + 3) := by
      unfold segBase segStride; ring
    omega
  · have hmj : m < j := by omega
    have : segBase gSep (m + 1) ≤ segBase gSep j := by
      unfold segBase segStride; exact Nat.mul_le_mul_right _ (by omega)
    have hmlt : segBase gSep (m + 1) = segBase gSep m + (2 * gSep + 3) := by
      unfold segBase segStride; ring
    omega

/-- Segment `j`'s own add restores every addend-register bit `i < gSep`
    (`addendRestored`, needs only the carry-in clean). -/
theorem segAdd_restores_addend (gSep j : Nat) (g : Nat → Bool)
    (hAnc : g (segBase gSep j) = false) (i : Nat) (hi : i < gSep) :
    Gate.applyNat (segAdd gSep j) g (cuccaroAdder.addendIdx (segBase gSep j) i)
      = g (cuccaroAdder.addendIdx (segBase gSep j) i) := by
  unfold segAdd
  have hclean : cuccaroAdder.ancClean g (gSep + 1) (segBase gSep j) := by
    show g (segBase gSep j) = false; exact hAnc
  exact cuccaroAdder.addendRestored (gSep + 1) (segBase gSep j) g hclean i (by omega)

/-- **One segment add fixes every segment's addend register** (under `IterReady`).
    Its own register is restored bit-for-bit (`addendRestored`), the others are
    disjoint (frame). -/
theorem segAdd_fixes_addend (gSep k j : Nat) (g : Nat → Bool)
    (hjk : j < k) (hready : IterReady gSep k g) (m : Nat) (hm : m < k)
    (i : Nat) (hi : i < gSep) :
    Gate.applyNat (segAdd gSep j) g (cuccaroAdder.addendIdx (segBase gSep m) i)
      = g (cuccaroAdder.addendIdx (segBase gSep m) i) := by
  by_cases hjm : j = m
  · subst hjm
    obtain ⟨hAncj, _⟩ := hready j hjk
    exact segAdd_restores_addend gSep j g hAncj i hi
  · exact segAdd_fixes_addend_off gSep j m g hjm i hi

/-- **Deliverable #3 — addend invariance.**  Under `IterReady`, the full runway
    adder leaves each segment `m`'s `gSep`-bit addend register `b_m` unchanged: each
    `segAdd j` restores its own register and fixes the others.  Wired to
    `Gate.applyNat (runwayAddK gSep k) f`. -/
theorem runwayAddK_addend_eq (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), IterReady gSep k f → ∀ (m : Nat), m < k →
      decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
          (Gate.applyNat (runwayAddK gSep k) f)
        = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
  intro k
  -- Generalize over a `j ≤ k` prefix (so the IterReady stays at width `k`).
  suffices h : ∀ (j : Nat), j ≤ k → ∀ (f : Nat → Bool), IterReady gSep k f →
      ∀ (m : Nat), m < k →
        decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
            (Gate.applyNat (runwayAddK gSep j) f)
          = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f by
    intro f hready m hm; exact h k (le_refl _) f hready m hm
  intro j
  induction j with
  | zero => intro _ f _ m _; rfl
  | succ n ih =>
      intro hjk f hready m hm
      set g := Gate.applyNat (runwayAddK gSep n) f with hg
      -- runwayAddK (n+1) = segAdd n ∘ runwayAddK n.
      show decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
            (Gate.applyNat (segAdd gSep n) g)
        = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
      -- `g` is still IterReady at width `k` (prefix preservation).
      have hreadyg : IterReady gSep k g := by
        rw [hg]
        exact runwayAddK_prefix_preserves_IterReady gSep k n (by omega) f hready
      -- The outer `segAdd n` fixes segment m's whole addend register (under IterReady).
      have houter : decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
            (Gate.applyNat (segAdd gSep n) g)
          = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g := by
        apply decodeReg_ext
        intro i hi
        exact segAdd_fixes_addend gSep k n g (by omega) hreadyg m hm i hi
      rw [houter, hg]
      exact ih (by omega) f hready m hm

/-! ## §6. Deliverable #4 — the per-segment add step (the engine).

The single segment add, on a state with only its carry-in ancilla and addend-top
clear (NOT its runway), advances its `(gSep+1)`-bit register by the gSep-bit addend,
mod `2^(gSep+1)`.  This is `sumCorrect` on the FULL `(gSep+1)`-bit augend (no
runway-clean assumption), then collapsing the addend's clean top bit. -/

/-- **Per-segment step engine** (about `applyNat (segAdd gSep m) g`).  With only the
    carry-in clean and the addend top clear, segment `m`'s register advances by its
    gSep-bit addend, mod `2^(gSep+1)`.  Uses `sumCorrect` directly on the full
    `(gSep+1)`-bit augend — the runway/top augend bit is NOT assumed clean. -/
theorem segReg_segAdd_step (gSep m : Nat) (g : Nat → Bool)
    (hAnc : g (segBase gSep m) = false)
    (hAddTop : g (cuccaroAdder.addendIdx (segBase gSep m) gSep) = false) :
    segReg gSep m (Gate.applyNat (segAdd gSep m) g)
      = (segReg gSep m g
          + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g) % 2 ^ (gSep + 1) := by
  unfold segReg segAdd
  have hclean : cuccaroAdder.ancClean g (gSep + 1) (segBase gSep m) := by
    show g (segBase gSep m) = false; exact hAnc
  -- sumCorrect at width gSep+1: (full augend + full addend) mod 2^(gSep+1).
  rw [cuccaroAdder.sumCorrect (gSep + 1) (segBase gSep m) g hclean]
  -- The (gSep+1)-bit addend read collapses to the gSep-bit read (top bit clean).
  rw [decodeReg_succ_of_top_false _ gSep g hAddTop]

/-- **Deliverable #4 — the per-segment step for the FULL runway adder.**  Under
    `IterReady`, running the whole `runwayAddK gSep k` advances segment `m`'s
    `(gSep+1)`-bit register by its gSep-bit addend, mod `2^(gSep+1)`.  Wired to
    `Gate.applyNat (runwayAddK gSep k) f`, with the addend read off `f`. -/
theorem runwayAddK_step_segReg (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), IterReady gSep k f → ∀ (m : Nat), m < k →
      segReg gSep m (Gate.applyNat (runwayAddK gSep k) f)
        = (segReg gSep m f
            + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f) % 2 ^ (gSep + 1) := by
  intro k
  induction k with
  | zero => intro f _ m hm; omega
  | succ k ih =>
      intro f hready m hm
      set g := Gate.applyNat (runwayAddK gSep k) f with hg
      have happ : Gate.applyNat (runwayAddK gSep (k + 1)) f
          = Gate.applyNat (segAdd gSep k) g := rfl
      rcases Nat.lt_or_ge m k with hmk | hmk
      · -- m < k: segAdd k fixes segment m's register; conclude by IH (still at width k).
        rw [happ]
        have hfixreg : segReg gSep m (Gate.applyNat (segAdd gSep k) g)
            = segReg gSep m g := by
          unfold segReg
          exact segAdd_fixes_segReg_below gSep k m g hmk
        rw [hfixreg, hg]
        exact ih f (fun p hp => hready p (by omega)) m hmk
      · -- m = k: the top segment's own add, on g.
        have hmeq : m = k := by omega
        subst hmeq
        rw [happ]
        -- g agrees with f on all positions ≥ segBase gSep m (lower segs fix above).
        have hfix : ∀ q, segBase gSep m ≤ q → g q = f q := by
          intro q hq; rw [hg]; exact runwayAddK_fixes_above gSep m f q hq
        obtain ⟨hAnc, hAddTop⟩ := hready m hm
        have hAnc' : g (segBase gSep m) = false := by
          rw [hfix _ (le_refl _)]; exact hAnc
        have hAddTop' : g (cuccaroAdder.addendIdx (segBase gSep m) gSep) = false := by
          rw [hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * gSep + 2; omega)]
          exact hAddTop
        -- per-segment step engine, on g.
        rw [segReg_segAdd_step gSep m g hAnc' hAddTop']
        -- push the segReg / addend reads on g back to f.
        have hsegRead : segReg gSep m g = segReg gSep m f := by
          unfold segReg
          apply decodeReg_ext; intro i hi
          exact hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * i + 1; omega)
        have hBread : decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep g
            = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
          apply decodeReg_ext; intro i hi
          exact hfix _ (by show segBase gSep m ≤ segBase gSep m + 2 * i + 2; omega)
        rw [hsegRead, hBread]

/-! ## §7. Iterated preservation (over `t` runway adds). -/

/-- `IterReady` is preserved by `t` iterations of the runway adder. -/
theorem iterGate_preserves_IterReady (gSep k : Nat) :
    ∀ (t : Nat) (f : Nat → Bool), IterReady gSep k f →
      IterReady gSep k (Gate.applyNat (iterGate (runwayAddK gSep k) t) f) := by
  intro t
  induction t with
  | zero => intro f hready; simpa using hready
  | succ n ih =>
      intro f hready
      rw [applyNat_iterGate_succ]
      exact runwayAddK_preserves_IterReady gSep k _ (ih f hready)

/-- The addend register `b_m` is invariant under `t` iterations of the runway adder. -/
theorem iterGate_addend_eq (gSep k : Nat) :
    ∀ (t : Nat) (f : Nat → Bool), IterReady gSep k f → ∀ (m : Nat), m < k →
      decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
          (Gate.applyNat (iterGate (runwayAddK gSep k) t) f)
        = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
  intro t
  induction t with
  | zero => intro f _ m _; simp
  | succ n ih =>
      intro f hready m hm
      rw [applyNat_iterGate_succ]
      -- one more runway add fixes the addend (IterReady holds after n iterations).
      have hreadyn : IterReady gSep k (Gate.applyNat (iterGate (runwayAddK gSep k) n) f) :=
        iterGate_preserves_IterReady gSep k n f hready
      rw [runwayAddK_addend_eq gSep k _ hreadyn m hm]
      exact ih f hready m hm

/-! ## §8. Deliverable #5 — MAIN multi-add per-segment, by induction on `t`. -/

/-- **Deliverable #5 — MAIN.**  Iterating the runway adder `t` times advances each
    segment `m`'s `(gSep+1)`-bit register by `t·b_m`, mod `2^(gSep+1)`:

        segReg_m (applyNat (iterGate (runwayAddK gSep k) t) f)
          = (segReg_m f + t · b_m f) mod 2^(gSep+1).

    Induction on `t`: base `t = 0` collapses the mod (`segReg < 2^(gSep+1)`); step
    uses the per-segment engine (#4) on the `t`-fold state (IterReady preserved, #2)
    with the addend fixed (#3) plus mod algebra.  Wired to
    `Gate.applyNat (iterGate (runwayAddK gSep k) t) f`, with the concrete `t·b_m`
    RHS read off `f`. -/
theorem runwayAddK_iter_segReg (gSep k : Nat) :
    ∀ (t : Nat) (f : Nat → Bool), IterReady gSep k f → ∀ (m : Nat), m < k →
      segReg gSep m (Gate.applyNat (iterGate (runwayAddK gSep k) t) f)
        = (segReg gSep m f
            + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f)
          % 2 ^ (gSep + 1) := by
  intro t
  induction t with
  | zero =>
      intro f _ m _
      -- iterGate g 0 = id; RHS = (segReg + 0) % 2^(gSep+1) = segReg (< 2^(gSep+1)).
      simp only [applyNat_iterGate_zero, Nat.zero_mul, Nat.add_zero]
      symm
      apply Nat.mod_eq_of_lt
      exact decodeReg_lt _ (gSep + 1) f
  | succ n ih =>
      intro f hready m hm
      rw [applyNat_iterGate_succ]
      set h := Gate.applyNat (iterGate (runwayAddK gSep k) n) f with hh
      -- IterReady holds after n iterations.
      have hreadyh : IterReady gSep k h := by
        rw [hh]; exact iterGate_preserves_IterReady gSep k n f hready
      -- one runway add on h: advance by b_m(h).
      rw [runwayAddK_step_segReg gSep k h hreadyh m hm]
      -- b_m(h) = b_m(f) (addend invariant over n iterations).
      have hBh : decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep h
          = decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f := by
        rw [hh]; exact iterGate_addend_eq gSep k n f hready m hm
      rw [hBh]
      -- segReg m h = (segReg m f + n·b_m f) % 2^(gSep+1) (IH).
      rw [show segReg gSep m h
            = (segReg gSep m f
                + n * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f)
              % 2 ^ (gSep + 1) from (by rw [hh]; exact ih f hready m hm)]
      -- mod algebra: ((S + n·b) % M + b) % M = (S + (n+1)·b) % M.
      set b := decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f with hb
      set S := segReg gSep m f with hS
      rw [show (n + 1) * b = n * b + b by ring, ← Nat.add_assoc, Nat.mod_add_mod]

/-! ## §9. Deliverable #6 — HEADLINE: contiguous multi-add, exact under no-overflow.

The augend term reads each segment's FULL `(gSep+1)`-bit register `segReg_m` at
contiguous spacing — i.e. it is literally `contiguousDecode gSep k f`, the contiguous
decode of the INPUT.  (When the input runways are clean, `segReg_m = a_m`, so this
coincides with `contiguousAugend gSep k f`; in general it is the input's contiguous
reading.)  The addend term is `contiguousAddend gSep k f = Σ b_m · 2^(m·gSep)`. -/

/-- **Deliverable #6 — HEADLINE, contiguous multi-add (EXACT under per-segment
    no-overflow).**  Iterating the runway adder `t` times accumulates, in the
    CONTIGUOUS reading,

        contiguousDecode gSep k (applyNat (iterGate (runwayAddK gSep k) t) f)
          = contiguousDecode gSep k f + t · contiguousAddend gSep k f,

    EXACT, provided each segment's `(gSep+1)`-bit register never overflows over the
    whole run: `segReg_m f + t·b_m f < 2^(gSep+1)` for `m < k`.  The augend term is
    the contiguous decode of the INPUT (each segment read at its full register, so
    `a + t·b` in the contiguous place-value reading).  Proved by induction on a
    prefix `j ≤ k`, folding the MAIN per-segment multi-add (#5, mod dropped by
    no-overflow) into the `contiguousDecode`/`contiguousAddend` place-value
    recursion; `ring`.  Wired to `Gate.applyNat (iterGate (runwayAddK gSep k) t) f`
    with a concrete `contiguousDecode f + t·contiguousAddend f` RHS. -/
theorem runwayAddK_iter_contiguous (gSep k t : Nat) (f : Nat → Bool)
    (hready : IterReady gSep k f)
    (hno : ∀ m, m < k →
      segReg gSep m f
        + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
        < 2 ^ (gSep + 1)) :
    contiguousDecode gSep k (Gate.applyNat (iterGate (runwayAddK gSep k) t) f)
      = contiguousDecode gSep k f + t * contiguousAddend gSep k f := by
  set out := Gate.applyNat (iterGate (runwayAddK gSep k) t) f with hout
  -- Induct on a prefix `j ≤ k`; the per-segment multi-add applies for each m < k.
  suffices h : ∀ (j : Nat), j ≤ k →
      contiguousDecode gSep j out
        = contiguousDecode gSep j f + t * contiguousAddend gSep j f by
    exact h k (le_refl _)
  intro j
  induction j with
  | zero => intro _; simp [contiguousDecode, contiguousAddend]
  | succ n ih =>
      intro hjk
      -- unfold the (n+1) layer of contiguousDecode (out / f) and contiguousAddend f.
      show contiguousDecode gSep n out + segReg gSep n out * 2 ^ (n * gSep)
        = (contiguousDecode gSep n f + segReg gSep n f * 2 ^ (n * gSep))
          + t * (contiguousAddend gSep n f
              + decodeReg (cuccaroAdder.addendIdx (segBase gSep n)) gSep f
                  * 2 ^ (n * gSep))
      -- ① the top segment's register: MAIN multi-add (#5) at m = n, mod dropped.
      have hstep : segReg gSep n out
          = segReg gSep n f
            + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep n)) gSep f := by
        rw [hout, runwayAddK_iter_segReg gSep k t f hready n (by omega)]
        exact Nat.mod_eq_of_lt (hno n (by omega))
      -- ② the lower-n contiguous decode reduces to the IH.
      have hlow : contiguousDecode gSep n out
          = contiguousDecode gSep n f + t * contiguousAddend gSep n f :=
        ih (by omega)
      rw [hstep, hlow]
      ring

/-! ## §10. Corollary — standard `a + t·b` form when the INPUT runways are clean.

`kClean` (the standard input precondition: carry-in, runway, AND addend-top all
clear per segment) is stronger than `IterReady` (carry-in + addend-top only).  Under
`kClean` the input runways are 0, so each `segReg_m f = a_m` and the augend term
becomes the standard contiguous augend `contiguousAugend gSep k f`. -/

/-- `kClean` implies `IterReady` (it additionally clears the runways). -/
theorem IterReady_of_kClean (gSep k : Nat) (f : Nat → Bool)
    (h : kClean gSep k f) : IterReady gSep k f :=
  fun m hm => ⟨(h m hm).1, (h m hm).2.2⟩

/-- With the input runways clean, the contiguous decode of the input equals the
    standard contiguous augend (`segReg_m f = a_m`, top runway bit dropped). -/
theorem contiguousDecode_eq_augend_of_kClean (gSep : Nat) :
    ∀ (k : Nat) (f : Nat → Bool), kClean gSep k f →
      contiguousDecode gSep k f = contiguousAugend gSep k f := by
  intro k
  induction k with
  | zero => intro f _; rfl
  | succ n ih =>
      intro f hclean
      show contiguousDecode gSep n f + segReg gSep n f * 2 ^ (n * gSep)
        = contiguousAugend gSep n f
          + decodeReg (cuccaroAdder.augendIdx (segBase gSep n)) gSep f * 2 ^ (n * gSep)
      have hlow : contiguousDecode gSep n f = contiguousAugend gSep n f :=
        ih f (fun j hj => hclean j (by omega))
      have hseg : segReg gSep n f
          = decodeReg (cuccaroAdder.augendIdx (segBase gSep n)) gSep f := by
        unfold segReg
        exact decodeReg_succ_of_top_false _ gSep f (hclean n (by omega)).2.1
      rw [hlow, hseg]

/-- **Corollary — standard contiguous multi-add `a + t·b`.**  Under the full input
    cleanliness `kClean` (runways included), iterating the runway adder `t` times
    accumulates EXACTLY `contiguousAugend + t·contiguousAddend` in the contiguous
    reading, under per-segment no-overflow.  This is the headline in the standard
    `a + t·b` shape. -/
theorem runwayAddK_iter_contiguous_clean (gSep k t : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k f)
    (hno : ∀ m, m < k →
      decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f
        + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
        < 2 ^ (gSep + 1)) :
    contiguousDecode gSep k (Gate.applyNat (iterGate (runwayAddK gSep k) t) f)
      = contiguousAugend gSep k f + t * contiguousAddend gSep k f := by
  -- Rewrite the no-overflow hypothesis in terms of `segReg_m f = a_m`.
  have hno' : ∀ m, m < k →
      segReg gSep m f
        + t * decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep f
        < 2 ^ (gSep + 1) := by
    intro m hm
    have hseg : segReg gSep m f
        = decodeReg (cuccaroAdder.augendIdx (segBase gSep m)) gSep f := by
      unfold segReg
      exact decodeReg_succ_of_top_false _ gSep f (hclean m hm).2.1
    rw [hseg]; exact hno m hm
  rw [runwayAddK_iter_contiguous gSep k t f (IterReady_of_kClean gSep k f hclean) hno',
      contiguousDecode_eq_augend_of_kClean gSep k f hclean]

end FormalRV.Arithmetic.Windowed.RunwayAdderMultiAdd
