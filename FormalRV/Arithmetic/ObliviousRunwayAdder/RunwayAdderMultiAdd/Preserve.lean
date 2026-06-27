/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.Preserve
  ────────────────────────────────────────────────
  Submodule of `RunwayAdderMultiAdd` (split out for per-file compile memory).
  Contains §1–§5: gate iteration (`iterGate`), the iteration invariant
  (`IterReady`), the cross-segment carry-in/addend-top frame lemmas, the
  `IterReady`-preservation chain (`segAdd_preserves_IterReady` …
  `runwayAddK_preserves_IterReady`), and addend invariance
  (`segAdd_fixes_addend_off` … `runwayAddK_addend_eq`).

  Re-exported VERBATIM from the original `RunwayAdderMultiAdd.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous

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

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
