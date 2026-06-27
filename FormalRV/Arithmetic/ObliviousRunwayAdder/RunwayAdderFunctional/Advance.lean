/-
  FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.Advance
  ──────────────────────────────────────────────────
  Submodule of `RunwayAdderFunctional` (split out for per-file compile memory).
  Contains §14: the k-segment advance bound — total runway occupancy ≤ k, and its
  `k = n/gSep` instantiation.

  Re-exported VERBATIM from the original `RunwayAdderFunctional.lean`; the
  declarations, statements, names, namespace and `open`s are unchanged.
-/
import FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional.KSegment

namespace FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

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

end FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
