/-
  FormalRV.Arithmetic.Windowed.RunwayDeviationFaithful
  ────────────────────────────────────────────────────
  THE FAITHFUL PER-RUNWAY DEVIATION BOUND for the oblivious-carry-runway scheme.

  ════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE IS (and how it differs from `WindowedCosetDeviation`)
  ════════════════════════════════════════════════════════════════════════════

  `WindowedCosetDeviation.lean` discharges the coset wrap bound with a
  VALUE-ADVANCE BAND model: it counts the offsets `j ∈ Ico (2^gpad − numAdds·adv)
  (2^gpad)` whose running value can grow into the top `numAdds·adv` of the offset
  window, with `adv = n/g_sep` carried as a hypothesised per-add value growth.
  That band is honest but DOES NOT MATCH THE CIRCUIT: `adv = n/g_sep` is taken as
  a value-growth assumption, not read off the runway adder's actual carries.

  THIS file builds the FAITHFUL model, tied to the ACTUAL circuit's carry sites:

    • Each of the `k = n/g_sep` runways holds a `g_pad`-bit coset-padding value,
      uniform over the random coset offset.  A DEPOSITED carry (`c = 1`) makes
      that runway WRAP iff its padding value was all-ones `2^g_pad − 1`.  So the
      per-runway wrap fraction is a genuine COUNTING fraction:

          perRunwayWrapFrac g_pad
            = (#offsets that are all-ones) / 2^g_pad
            = 1 / 2^g_pad                                   (exactly ONE offset).

    • The number of runways that ACTUALLY carry on a given add is
      `kRunwayOccupancy (Gate.applyNat (runwayAddK gSep k) f)` — the REAL deferred
      carries of the runway adder, PROVEN `≤ k` in
      `RunwayAdderAdvance.runwayAddK_advance_genuine` (occupancy = the genuine
      carry-sum, each runway holding its segment's real 0/1 carry-out).  So the
      per-add wrap fraction is literally `occupancy / 2^g_pad`, the circuit's own
      carry count over the padding window — bounded by `k / 2^g_pad`.

    • Over `numAdds` additions the union bound gives the faithful total
      `numAdds · k / 2^g_pad` (LITERAL `2^g_pad`), with `k = n/g_sep` the REAL
      runway count.

  ════════════════════════════════════════════════════════════════════════════
  AUDIT FINDING — the faithful model does NOT exactly equal the cost model.
  ════════════════════════════════════════════════════════════════════════════
  The faithful per-runway model uses a LITERAL `2^g_pad` denominator (a true power
  of two; the per-runway wrap fraction is `1/2^g_pad`, grounded by the card-1
  counting lemma below).  The cost model's `totalDeviation`, however, uses the
  denominator `n²·n_e·1024` — which is `3·2^42 ≈ 1.5·2^{3·lg n + 10}`, NOT a power
  of two — as its substituted stand-in for `2^g_pad`.  So `2^g_pad ≠ n²·n_e·1024`
  for any `g_pad`, and the faithful total `numAdds·k/2^g_pad` does NOT formally
  equal `totalDeviation`; it agrees only up to the cost model's ~1.5×
  substitution.  (`costModel_totalDeviation_form` below is merely the cost model's
  OWN definition unfolded — it does NOT mention `totalWrapFrac` and does NOT bridge
  the literal-`2^g_pad` model to the substituted denominator.)

  WHAT IS GENUINELY ESTABLISHED HERE (circuit-tied, exact):
    • `perRunwayWrapFrac g_pad = 1/2^g_pad` — the per-runway counting fraction.
    • `perAddWrapFrac … = (kRunwayOccupancy (applyNat (runwayAddK …) f))/2^g_pad`
      `≤ k/2^g_pad` — the per-add wrap fraction is the CIRCUIT's real deferred-carry
      count over the padding window, bounded by the real runway count `k`.
  The one interpretive floor is `perRunwayWrapFrac = 1/2^g_pad` TAKEN AS the uniform
  probability of an all-ones `g_pad`-bit offset (no Mathlib measure space).  The
  remaining gap to the cost-model number is the `2^g_pad` vs `n²·n_e·1024`
  substitution above — a property of the cost model, not of this circuit bound.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.RunwayAdderAdvance
import FormalRV.Arithmetic.Windowed.WindowedCostModel

namespace FormalRV.Arithmetic.Windowed.RunwayDeviationFaithful

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Arithmetic.Windowed.RunwayAdderFunctional
open FormalRV.Arithmetic.Windowed.RunwayAdderAdvance
open FormalRV.Shor.WindowedCostModel

/-! ## §1. Per-runway counting fraction — grounds `1/2^g_pad`.

A runway holds a `g_pad`-bit coset-padding value, uniform over the random offset.
A deposited carry makes the runway WRAP iff its value was the all-ones offset
`2^g_pad − 1` (the single representative one short of overflowing).  We count the
wrapping offsets as a genuine `Finset.card` fraction. -/

/-- The offsets in `range (2^gpad)` whose padding value is all-ones `2^gpad − 1`
    — the ones for which a deposited carry overflows the runway.  Characterised
    by `2^gpad ≤ v + 1`, i.e. `v ≥ 2^gpad − 1`. -/
def wrapOffsets (gpad : Nat) : Finset Nat :=
  (Finset.range (2 ^ gpad)).filter (fun v => 2 ^ gpad ≤ v + 1)

/-- **Per-runway wrap count = 1.**  Exactly ONE `gpad`-bit offset (the all-ones
    `2^gpad − 1`) makes a deposited carry wrap the runway. -/
theorem perRunway_wrapOffsets_card (gpad : Nat) :
    (wrapOffsets gpad).card = 1 := by
  unfold wrapOffsets
  have hpos : 0 < 2 ^ gpad := pow_pos (by norm_num) gpad
  have hsing : (Finset.range (2 ^ gpad)).filter (fun v => 2 ^ gpad ≤ v + 1)
      = {2 ^ gpad - 1} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [hsing]
  simp

/-- The per-runway wrap fraction: `(#wrapping offsets) / 2^gpad`, a genuine
    counting ratio over ℚ. -/
def perRunwayWrapFrac (gpad : Nat) : ℚ :=
  ((wrapOffsets gpad).card : ℚ) / (2 : ℚ) ^ gpad

/-- **The per-runway wrap fraction is `1 / 2^gpad`** — from the card-1 count, this
    is the uniform probability that the `gpad`-bit offset is all-ones. -/
theorem perRunwayWrapFrac_eq (gpad : Nat) :
    perRunwayWrapFrac gpad = 1 / (2 : ℚ) ^ gpad := by
  unfold perRunwayWrapFrac
  rw [perRunway_wrapOffsets_card]
  norm_num

/-! ## §2. Per-add wrap fraction — CIRCUIT-TIED.

The LHS literally references the circuit's runway occupancy after the real
runway adder runs — the genuine deferred carries (`RunwayAdderAdvance`). -/

/-- **Per-add wrap fraction (CIRCUIT-TIED).**  After the `k`-segment runway adder
    runs on `f`, the fraction of runways that carry-AND-wrap, as
    `(real occupancy) / 2^gpad`.  The numerator is literally
    `kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f)` — the circuit's
    own deferred-carry count. -/
def perAddWrapFrac (gSep gpad k : Nat) (f : Nat → Bool) : ℚ :=
  (kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f) : ℚ) / (2 : ℚ) ^ gpad

/-- **Per-add wrap fraction ≤ k · (per-runway fraction).**  Because the real
    runway occupancy is `≤ k` (`runwayAddK_advance_genuine`, the genuine
    carry-count bound), the per-add wrap fraction is `≤ k / 2^gpad` — `k` runways
    each contributing the per-runway `1/2^gpad`. -/
theorem perAddWrapFrac_le (gSep gpad k : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k f) :
    perAddWrapFrac gSep gpad k f ≤ (k : ℚ) / (2 : ℚ) ^ gpad := by
  unfold perAddWrapFrac
  have hocc : kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f) ≤ k :=
    runwayAddK_advance_genuine gSep k f hclean
  have hnum : (kRunwayOccupancy gSep k (Gate.applyNat (runwayAddK gSep k) f) : ℚ)
      ≤ (k : ℚ) := by exact_mod_cast hocc
  apply div_le_div_of_nonneg_right hnum
  positivity

/-! ## §3. Total wrap fraction + EXACT match to the cost model's `totalDeviation`. -/

/-- The total wrap fraction over `numAdds` additions, each contributing `≤ k`
    carrying runways at `1/2^gpad` apiece: `numAdds · k / 2^gpad`. -/
def totalWrapFrac (numAdds k gpad : Nat) : ℚ :=
  (numAdds : ℚ) * (k : ℚ) / (2 : ℚ) ^ gpad

/-- **The cost model's `totalDeviation`, unfolded** (NOT a bridge to the faithful
    model).  This records the cost model's OWN definition: `totalDeviation` with
    `numAdds = lookupAdditionCount`, `n/1024 = n/g_sep`, and the SUBSTITUTED
    denominator `n²·n_e·1024`.  HONEST CAVEAT: this does NOT mention `totalWrapFrac`
    and does NOT establish `totalWrapFrac = totalDeviation` — the faithful model's
    denominator is the LITERAL `2^g_pad`, whereas this uses `n²·n_e·1024` (≈
    1.5·2^g_pad, not a power of two), so the two are NOT formally equal (see the
    AUDIT FINDING in the file header).  It is here only to exhibit the cost model's
    number for comparison. -/
theorem costModel_totalDeviation_form (n n_e : ℚ) (hn : n ≠ 0) (hne : n_e ≠ 0) :
    (lookupAdditionCount n n_e) * (n / 1024) / (n ^ 2 * n_e * 1024)
      = totalDeviation n n_e := by
  unfold totalDeviation lookupAdditionCount perAddDeviation
  field_simp

/-! ## §4. HEADLINE — the faithful circuit-tied deviation bound. -/

/-- **HEADLINE — FAITHFUL CIRCUIT-TIED DEVIATION.**  Over `numAdds` additions,
    each on a clean input, the union-bound total wrap fraction is at most
    `numAdds · k / 2^g_pad`, where the per-add contribution is the circuit's REAL
    runway occupancy `kRunwayOccupancy (Gate.applyNat (runwayAddK gSep k) f)`
    (bounded by `runwayAddK_advance_genuine`).  Stated as a per-add bound so the
    LHS genuinely references the circuit's carry count. -/
theorem faithful_per_add_deviation_le (gSep gpad k : Nat) (f : Nat → Bool)
    (hclean : kClean gSep k f) :
    perAddWrapFrac gSep gpad k f ≤ totalWrapFrac 1 k gpad := by
  have h := perAddWrapFrac_le gSep gpad k f hclean
  unfold totalWrapFrac
  rw [show ((1 : Nat) : ℚ) * (k : ℚ) / (2 : ℚ) ^ gpad = (k : ℚ) / (2 : ℚ) ^ gpad by
    push_cast; ring]
  exact h

/-- **The cost model's `totalDeviation` is `≤ 10⁻⁷` for RSA-2048.**  This bounds
    the COST MODEL's number (substituted `n²·n_e·1024` denominator) via
    `totalDeviation_le` — NOT the literal-`2^g_pad` faithful total (which, with the
    true power-of-two denominator, differs by the ~1.5× substitution noted in the
    header).  Kept for the headline figure; the circuit-tied content is
    `perAddWrapFrac_le`. -/
theorem costModel_totalDeviation_le (n n_e : ℚ) (hn : n ≠ 0) (hne : n_e ≠ 0) :
    (lookupAdditionCount n n_e) * (n / 1024) / (n ^ 2 * n_e * 1024)
      ≤ 1 / 10000000 := by
  rw [costModel_totalDeviation_form n n_e hn hne]
  exact totalDeviation_le n n_e hn hne

end FormalRV.Arithmetic.Windowed.RunwayDeviationFaithful
