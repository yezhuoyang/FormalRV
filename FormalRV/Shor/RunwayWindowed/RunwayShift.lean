/-
  FormalRV.Shor.RunwayWindowed.RunwayShift — cuccaro/runway translation-equivariance.
  ════════════════════════════════════════════════════════════════════════════

  The Cuccaro adder is translation-equivariant: shifting its `q_start` by `base`
  equals shifting every qubit index by `base` (`shiftBy`).  Since the
  oblivious-carry-runway adder is a sequence of Cuccaro segment-adds, it inherits
  the same equivariance:

      runwayAddKAt gSep base k  =  shiftBy base (runwayAddK gSep k).

  Composed with `GateShift.applyNat_shiftBy`, this is what lets the base-0-proven
  runway correctness (`runwayAddK_iter_contiguous_clean`, …) be TRANSPORTED to the
  re-based adder `runwayAddKAt` (above the windowed lookup zone) — no re-derivation.

  REUSE: the cuccaro defs (cuccaro_MAJ/UMA, the maj/uma chains, the full adder),
  `runwayAddK`/`segAdd`/`segBase` (RunwayAdderFunctional), `runwayAddKAt`/`segAddAt`
  (RunwayLayout), `shiftBy` (GateShift).  NEW: only the equivariance inductions.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.RunwayWindowed.GateShift
import FormalRV.Shor.RunwayWindowed.RunwayLayout

namespace FormalRV.Shor.RunwayWindowed.RunwayShift

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.RunwayWindowed.GateShift (shiftBy applyNat_shiftBy)
open FormalRV.Shor.RunwayWindowed.RunwayLayout (segAddAt runwayAddKAt)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  (segBase segAdd runwayAddK)

/-! ## §1. Atomic-gadget + chain equivariance. -/

/-- MAJ is translation-equivariant (it is `CX`/`CCX` at `a,b,c`). -/
theorem shiftBy_cuccaro_MAJ (base a b c : Nat) :
    shiftBy base (cuccaro_MAJ a b c)
      = cuccaro_MAJ (a + base) (b + base) (c + base) := rfl

/-- UMA is translation-equivariant. -/
theorem shiftBy_cuccaro_UMA (base a b c : Nat) :
    shiftBy base (cuccaro_UMA a b c)
      = cuccaro_UMA (a + base) (b + base) (c + base) := rfl

/-- The forward MAJ chain is translation-equivariant (the recursion threads
    `q_start + 2`, so the shift commutes with the chain). -/
theorem shiftBy_cuccaro_maj_chain (base : Nat) :
    ∀ (n q : Nat),
      shiftBy base (cuccaro_maj_chain n q) = cuccaro_maj_chain n (q + base) := by
  intro n
  induction n with
  | zero => intro q; rfl
  | succ m ih =>
    intro q
    show seq (shiftBy base (cuccaro_MAJ q (q + 1) (q + 2)))
          (shiftBy base (cuccaro_maj_chain m (q + 2))) = _
    rw [shiftBy_cuccaro_MAJ, ih (q + 2),
        show q + 1 + base = q + base + 1 from by omega,
        show q + 2 + base = q + base + 2 from by omega]
    rfl

/-- The reverse UMA chain is translation-equivariant. -/
theorem shiftBy_cuccaro_uma_chain_reverse (base : Nat) :
    ∀ (n q : Nat),
      shiftBy base (cuccaro_uma_chain_reverse n q)
        = cuccaro_uma_chain_reverse n (q + base) := by
  intro n
  induction n with
  | zero => intro q; rfl
  | succ m ih =>
    intro q
    show seq (shiftBy base (cuccaro_uma_chain_reverse m (q + 2)))
          (shiftBy base (cuccaro_UMA q (q + 1) (q + 2))) = _
    rw [shiftBy_cuccaro_UMA, ih (q + 2),
        show q + 1 + base = q + base + 1 from by omega,
        show q + 2 + base = q + base + 2 from by omega]
    rfl

/-- **The full Cuccaro adder is translation-equivariant.** -/
theorem shiftBy_cuccaro_n_bit_adder_full (base n q : Nat) :
    shiftBy base (cuccaro_n_bit_adder_full n q)
      = cuccaro_n_bit_adder_full n (q + base) := by
  show seq (shiftBy base (cuccaro_maj_chain n q))
        (shiftBy base (cuccaro_uma_chain_reverse n q)) = _
  rw [shiftBy_cuccaro_maj_chain base n q, shiftBy_cuccaro_uma_chain_reverse base n q]
  rfl

/-! ## §2. Runway-adder equivariance — the base-shift IS a `shiftBy`. -/

/-- **`runwayAddKAt gSep base k = shiftBy base (runwayAddK gSep k)`.**  The
    re-based runway adder is exactly the base-0 one with every qubit shifted by
    `base` — so all its base-0 theorems transport via `GateShift.applyNat_shiftBy`. -/
theorem runwayAddKAt_eq_shiftBy (gSep base : Nat) :
    ∀ (k : Nat), runwayAddKAt gSep base k = shiftBy base (runwayAddK gSep k) := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih =>
    show seq (runwayAddKAt gSep base m) (segAddAt gSep base m)
      = seq (shiftBy base (runwayAddK gSep m)) (shiftBy base (segAdd gSep m))
    rw [ih]
    congr 1
    -- `segAddAt gSep base m = shiftBy base (segAdd gSep m)` (cuccaro equivariance + comm).
    show cuccaro_n_bit_adder_full (gSep + 1) (base + segBase gSep m)
      = shiftBy base (cuccaro_n_bit_adder_full (gSep + 1) (segBase gSep m))
    rw [shiftBy_cuccaro_n_bit_adder_full, Nat.add_comm base (segBase gSep m)]

/-! ## §3. The correctness-transport bridge (M1.7).

The DOWN-SHIFT (by `base`) of the re-based adder's output equals the base-0
adder's output on the down-shifted input.  So every base-0 runway theorem
(`runwayAddK_iter_contiguous_clean`, the `contiguousDecode`/`segReg`/`kClean`
facts) applies verbatim to the down-shifted picture, and reading the re-based
accumulator at `base + segBase + offset` IS reading the base-0 decode of the
down-shifted state — no decode functions re-stated at `base`. -/

/-- **The down-shift bridge.**  `(λ q, applyNat (runwayAddKAt gSep base k) f
    (q + base))  =  applyNat (runwayAddK gSep k) (λ q, f (q + base))`.  Combines
    the runway equivariance with `applyNat_shiftBy` (the shifted gate acts on
    `[base, ∞)` exactly as the base-0 one reading the state at offset `base`). -/
theorem runwayAddKAt_downshift (gSep base k : Nat) (f : Nat → Bool) :
    (fun q => Gate.applyNat (runwayAddKAt gSep base k) f (q + base))
      = Gate.applyNat (runwayAddK gSep k) (fun q => f (q + base)) := by
  funext q
  rw [runwayAddKAt_eq_shiftBy, applyNat_shiftBy]
  simp only [if_neg (by omega : ¬ q + base < base), Nat.add_sub_cancel]

end FormalRV.Shor.RunwayWindowed.RunwayShift
