/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.MultiAddStep
  ────────────────────────────────────────────────
  Submodule of `RunwayAdderMultiAdd` (split out for per-file compile memory).
  Contains §6–§8: the per-segment add step engine (`segReg_segAdd_step`,
  `runwayAddK_step_segReg`), iterated preservation over `t` runway adds
  (`iterGate_preserves_IterReady`, `iterGate_addend_eq`), and the MAIN
  per-segment multi-add `runwayAddK_iter_segReg`.

  Re-exported VERBATIM from the original `RunwayAdderMultiAdd.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.Preserve

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous

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

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd
