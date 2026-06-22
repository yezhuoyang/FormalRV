/-
  FormalRV.Arithmetic.Adder.TwoBaseBoundedAdder
  ──────────────────────────────────────────────
  A TWO-BASE, bounded, width-aware adder interface — the abstraction the faithful
  Gidney two-register product-add wants:

      b += a*k          (accumulator b, multiplicand a in their OWN blocks)
      a -= b*kInv

  The accumulator and the addend live at INDEPENDENT base offsets `accBase` /
  `addBase`, each a contiguous (or stride-based) block, rather than the rigid
  single-base packing `addend = augend + n` of the single-base interface.

  This SUPERSEDES the earlier single-base `BoundedAdder` (now removed): it keeps
  the same two corrections forced by a contiguous layout —
    • width-aware indices `accIdx n accBase i` / `addIdx n addBase i`, and
    • bounded disjointness (`i, j < n`) —
  and adds a `valid : n → accBase → addBase → Prop` predicate so an instance can
  declare exactly which base layouts it supports.  All correctness obligations are
  conditioned on `valid`.

  Two instances:
    • `Adder.toTwoBaseBounded` — every single-base `Adder` is a degenerate two-base
      adder with `accBase = addBase` (`valid := addBase = accBase`).  So this is a
      strict generalization: existing Cuccaro/Gidney `Adder`s feed any consumer
      written against this interface, with no re-proof and no change to `Adder`.
    • `contiguousPackedAdder` (in `ContiguousTransport.lean`) — the contiguous
      Cuccaro transport, packed at `addBase = accBase + n` (`valid := addBase =
      accBase + n`); the convenience specialization that the §1–§4 transport built.

  NOTE on scope (honest): the footprint used by `frame`/`wellTyped` is the single
  bounding interval `[accBase, accBase + span n)` anchored at `accBase`.  `valid`
  is expected to place the addend block inside it (`accBase ≤ addBase`, addend
  fits).  A fully-relocatable footprint (addend block BELOW `accBase`, or far away
  with a disjoint-union footprint) is a further generalization, deliberately not
  built here.  Whether to instead globally bound/refactor `Adder` is a separate
  library-level checkpoint requiring an instance/consumer audit. -/
import FormalRV.Arithmetic.Adder

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **The two-base bounded adder interface.**  `accIdx`/`addIdx` take the operand's
    own base; `valid n accBase addBase` says the instance is correct for that base
    layout; every obligation that depends on the layout is conditioned on it. -/
structure TwoBaseBoundedAdder where
  /-- Footprint width: the circuit lives in `[accBase, accBase + span n accBase addBase)`.
      Width-AND-base-aware, because a relocated addend block (at `addBase`) pushes the
      footprint top out to `addBase + n + 1` (the carry), which depends on `addBase`. -/
  span     : Nat → Nat → Nat → Nat
  /-- Accumulator / running-sum bit `i`, at width `n`, accumulator base `accBase`. -/
  accIdx   : Nat → Nat → Nat → Nat
  /-- Addend bit `i`, at width `n`, addend base `addBase`. -/
  addIdx   : Nat → Nat → Nat → Nat
  /-- Which base layouts `(n, accBase, addBase)` this adder is correct for. -/
  valid    : Nat → Nat → Nat → Prop
  /-- The adder's internal carry / ancilla block is clean (0) in `f`. -/
  ancClean : (Nat → Bool) → Nat → Nat → Nat → Prop
  /-- The adder circuit at width `n`, accumulator base `accBase`, addend base `addBase`. -/
  circuit  : Nat → Nat → Nat → Gate
  /-- The accumulator decodes to `(accumulator + addend) mod 2^n`. -/
  sumCorrect : ∀ n accBase addBase f, valid n accBase addBase → ancClean f n accBase addBase →
      decodeReg (accIdx n accBase) n (Gate.applyNat (circuit n accBase addBase) f)
        = (decodeReg (accIdx n accBase) n f + decodeReg (addIdx n addBase) n f) % 2 ^ n
  /-- The addend register is restored bit-for-bit. -/
  addendRestored : ∀ n accBase addBase f, valid n accBase addBase → ancClean f n accBase addBase →
      ∀ i, i < n →
        Gate.applyNat (circuit n accBase addBase) f (addIdx n addBase i) = f (addIdx n addBase i)
  /-- The ancilla block is returned clean. -/
  ancRestored : ∀ n accBase addBase f, valid n accBase addBase → ancClean f n accBase addBase →
      ancClean (Gate.applyNat (circuit n accBase addBase) f) n accBase addBase
  /-- Anything outside the footprint `[accBase, accBase + span n accBase addBase)` is
      untouched.  (Bounding interval — sound even when the touched set has a gap; the
      "register in the gap is untouched" fact, when needed, is a separate lemma.) -/
  frame : ∀ n accBase addBase f p, valid n accBase addBase →
      ¬ inBlock accBase (span n accBase addBase) p →
      Gate.applyNat (circuit n accBase addBase) f p = f p
  /-- The circuit is well-typed at dimension `accBase + span n accBase addBase`. -/
  wellTyped : ∀ n accBase addBase, valid n accBase addBase →
      Gate.WellTyped (accBase + span n accBase addBase) (circuit n accBase addBase)
  /-- Accumulator positions lie inside the footprint (needs a valid layout). -/
  accIdx_inBlock : ∀ n accBase addBase i, valid n accBase addBase → i < n →
      inBlock accBase (span n accBase addBase) (accIdx n accBase i)
  /-- Addend positions lie inside the footprint (needs a valid layout). -/
  addIdx_inBlock : ∀ n accBase addBase i, valid n accBase addBase → i < n →
      inBlock accBase (span n accBase addBase) (addIdx n addBase i)
  /-- Addend positions are pairwise distinct. -/
  addIdx_inj : ∀ n addBase i j, addIdx n addBase i = addIdx n addBase j → i = j
  /-- **Bounded disjointness** (preserved): accumulator and addend never collide for
      the indices in use (`i, j < n`), in any valid layout. -/
  acc_add_disjoint : ∀ n accBase addBase i j, valid n accBase addBase → i < n → j < n →
      accIdx n accBase i ≠ addIdx n addBase j
  /-- `ancClean` looks only at IN-FOOTPRINT non-data positions. -/
  ancClean_ext : ∀ n accBase addBase f g, valid n accBase addBase →
      (∀ p, inBlock accBase (span n accBase addBase) p →
        (∀ i, i < n → p ≠ accIdx n accBase i ∧ p ≠ addIdx n addBase i) → f p = g p) →
      ancClean f n accBase addBase → ancClean g n accBase addBase

/-- **Every single-base `Adder` is a (degenerate) two-base adder** with the two
    bases coinciding (`valid := addBase = accBase`).  The interleaved Cuccaro/Gidney
    layout is NOT a contiguous two-base layout (its addend `q+2i+2` is not `addBase+i`
    for any fixed `addBase`), so this records the honest fact that old `Adder`s only
    support the FIXED RELATIVE single-base layout — exposed here as the diagonal
    `accBase = addBase`, with the original (single-base) index functions. -/
def Adder.toTwoBaseBounded (A : Adder) : TwoBaseBoundedAdder where
  span     := fun n _ _ => A.span n
  accIdx   := fun _ accBase => A.augendIdx accBase
  addIdx   := fun _ addBase => A.addendIdx addBase
  valid    := fun _ accBase addBase => addBase = accBase
  ancClean := fun f n accBase _ => A.ancClean f n accBase
  circuit  := fun n accBase _ => A.circuit n accBase
  sumCorrect := by
    intro n accBase addBase f hv hclean; subst addBase
    exact A.sumCorrect n accBase f hclean
  addendRestored := by
    intro n accBase addBase f hv hclean i hi; subst addBase
    exact A.addendRestored n accBase f hclean i hi
  ancRestored := by
    intro n accBase addBase f hv hclean; subst addBase
    exact A.ancRestored n accBase f hclean
  frame := by
    intro n accBase addBase f p _ hp
    exact A.frame n accBase f p hp
  wellTyped := by
    intro n accBase addBase _
    exact A.wellTyped n accBase
  accIdx_inBlock := fun n accBase _ i _ hi => A.augendIdx_inBlock n accBase i hi
  addIdx_inBlock := by
    intro n accBase addBase i hv hi; subst addBase
    exact A.addendIdx_inBlock n accBase i hi
  addIdx_inj := fun _ addBase i j h => A.addendIdx_inj addBase i j h
  acc_add_disjoint := by
    intro n accBase addBase i j hv _ _; subst addBase
    exact A.augend_addend_disjoint accBase i j
  ancClean_ext := by
    intro n accBase addBase f g hv hagree hclean; subst addBase
    exact A.ancClean_ext n accBase f g hagree hclean

end FormalRV.BQAlgo
