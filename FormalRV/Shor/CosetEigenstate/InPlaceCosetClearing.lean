/-
  FormalRV.Shor.CosetEigenstate.InPlaceCosetClearing — CHECKPOINT 3 of the in-place phase:
  the swap + second-forward-pass two-register transform (the clearing).
  ════════════════════════════════════════════════════════════════════════════

  Clones the PROVEN `windowedModNMulInPlace_correct` (WindowedModNInPlace.lean:224) at the
  COSET (runway, no-flag) level.  The in-place gate is

      inplaceCosetGate = mulFwd(a) ; accYSwap ; mulFwd(N − aInv)

  and checkpoint 3 proves the accumulator CLEARS to the coset of `0` while the y-register
  holds the coset of `(a·y) mod N`, off the phase-independent wrap bad set.

  KEY ENABLER (this file's brick 1): `cosetModMulCircuitOf cuccaroAdder w bits N c numWin`
  is DEFEQ to the table-generic `windowedMulTOf cuccaroAdder w bits (tableValue c N w) …`
  (`reducedWindowStepOf` and `windowStepTOf` have byte-identical bodies), so the VERIFIED
  accumulator-agnostic basis fold `stepInv_foldT_acc` applies to BOTH forward passes with
  ZERO new fold induction.  It tracks the UNREDUCED runway sum `acc₀ + ∑ tableValue`
  (no modular flag) — exactly the coset behavior.

  THE CLEARING (for every runway term, confirmed):  a `StepInv` term at `acc₀ = j·N`
  advances under pass 1 to `j·N + Sa` (`Sa = ∑ tableValue a`, `≡ a·y mod N`); the swap puts
  this in the y-register and `y` in the accumulator; pass 2 adds `Sb = ∑ tableValue (N−aInv)`
  reading the swapped multiplicand `V ≡ a·y (mod N)`, giving accumulator `y + Sb ≡
  y − aInv·(a·y) − aInv·(j·N) ≡ 0 (mod N)` — since `acc₀ = j·N ≡ 0 (mod N)`, EVERY runway
  term clears to a coset-0 point.  Honest deviation: forward-wrap ∪ reverse-wrap,
  `≤ 2·numWin/2^cm` (the swap contributes 0 by `normSqDist_perm_invariant`).

  STATUS: brick 1 (this file) — the reusable coset basis fold.  Remaining bricks (next):
  per-runway-term basis in-place action (clone of the template via `stepInv_init_acc` +
  brick 1 + `accYSwap_apply` + `stepInv_determines_mulInputAccOf` + the windowed value
  identity for the clearing); then the `cosetState`/`cosetInput` superposition lift
  (`uc_eval_eq_permState` + branch classification) + the bad-set transport through
  `accYSwap` (OBLIGATION (b), phase-independent).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.InPlaceCosetGate
import FormalRV.Shor.CosetEigenstate.InPlaceCosetForward
import FormalRV.Shor.CosetEigenstate.ReducedLookupStepAction

namespace FormalRV.Shor.CosetEigenstate.InPlaceCosetClearing

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (tableValue window)
open FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate (cosetModMulCircuitOf)
open FormalRV.Shor.CosetEigenstate.ReducedLookupStepAction (stepInv_determines_mulInputAccOf)

/-- **CHECKPOINT 3, brick 1 — the coset multiplier's basis fold (reusable, BOTH passes).**
    A `StepInv` state at partial sum `acc₀` advances under the whole forward coset
    multiplier `cosetModMulCircuitOf … c` to `StepInv` at `acc₀ + ∑ tableValue c` — the
    UNREDUCED runway sum.  Direct application of the verified accumulator-agnostic
    `stepInv_foldT_acc` through the `cosetModMulCircuitOf = windowedMulTOf (tableValue c N w)`
    defeq.  This is the per-pass engine of the clearing (pass 1 at constant `a`, pass 2 at
    `N − aInv`). -/
theorem cosetMul_stepInv_fold (w bits N c numWin y acc₀ : Nat) (hw : 0 < w)
    (f : Nat → Bool) (hf : StepInv cuccaroAdder w bits numWin y acc₀ f) :
    StepInv cuccaroAdder w bits numWin y
        (acc₀ + ∑ k ∈ Finset.range numWin, tableValue c N w k (window w y k))
        (Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N c numWin) f) :=
  stepInv_foldT_acc cuccaroAdder w bits (tableValue c N w) numWin y acc₀ hw f hf
    numWin (le_refl numWin)

/-- **CHECKPOINT 3, brick 2a — the concrete per-pass action (reusable for BOTH passes).**
    On the literal nonzero-accumulator input `mulInputAccOf acc₀ y` (accumulator `acc₀`,
    multiplicand `y`, everything else clean), one whole forward coset pass at constant `c`
    produces `mulInputAccOf` with the accumulator advanced to the LITERAL transformed value
    `(acc₀ + ∑ tableValue c) % 2^bits` (the unreduced runway sum, mod the register width) —
    NOT a modular congruence.  Clones `reducedWindowStep_applyNat`'s structure
    (`hinj`/`hclean`/`stepInv_init_acc`) but folds the WHOLE multiplier via brick 1
    (`cosetMul_stepInv_fold`) instead of one step.  Pass 1 = this at `(c := a, acc₀)`;
    pass 2 = this at `(c := N − aInv, acc₀ := y, multiplicand := V)`. -/
theorem cosetMul_pass_concrete (w bits N c numWin acc₀ y : Nat) (hw : 0 < w) :
    Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N c numWin)
        (mulInputAccOf cuccaroAdder w bits numWin acc₀ y)
      = mulInputAccOf cuccaroAdder w bits numWin
          ((acc₀ + ∑ k ∈ Finset.range numWin, tableValue c N w k (window w y k)) % 2 ^ bits) y := by
  have hinj : ∀ i j, i < bits → j < bits →
      cuccaroAdder.augendIdx (1 + 2 * w) i = cuccaroAdder.augendIdx (1 + 2 * w) j → i = j :=
    fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h
  have hclean : cuccaroAdder.ancClean (mulInputAccOf cuccaroAdder w bits numWin acc₀ y) bits
      (1 + 2 * w) := by
    show mulInputAccOf cuccaroAdder w bits numWin acc₀ y (1 + 2 * w) = false
    unfold mulInputAccOf
    rw [writeReg_frame _ _ _ _ _ (fun i hi heq => by
      have : cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := rfl
      omega)]
    have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx; omega) (by rw [hspan]; omega)
  have hstart := stepInv_init_acc cuccaroAdder w bits numWin acc₀ y hinj hclean
  exact stepInv_determines_mulInputAccOf w bits numWin y _ _
    (cosetMul_stepInv_fold w bits N c numWin y acc₀ hw _ hstart)

/-- **CHECKPOINT 3, brick 2b — the swap leg (PURE register layout, no arithmetic).**
    `accYSwap` exchanges the accumulator and y-registers bit-for-bit, so it maps the
    nonzero-accumulator input `mulInputAccOf acc₀ y` (accumulator `acc₀`, multiplicand `y`)
    to `mulInputAccOf y acc₀` (accumulator `y`, multiplicand `acc₀`).  Depends ONLY on
    register layout / bit extraction (`accYSwap_apply` + `writeReg`/`mulInputOf` position
    lemmas) — NO correctness of any multiplier, NO modular arithmetic. -/
theorem accYSwap_mulInputAccOf (w bits numWin acc₀ y : Nat) (hbits : numWin * w = bits) :
    Gate.applyNat (accYSwap cuccaroAdder w bits)
        (mulInputAccOf cuccaroAdder w bits numWin acc₀ y)
      = mulInputAccOf cuccaroAdder w bits numWin y acc₀ := by
  have hinj : ∀ i j, i < bits → j < bits →
      cuccaroAdder.augendIdx (1 + 2 * w) i = cuccaroAdder.augendIdx (1 + 2 * w) j → i = j :=
    fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h
  obtain ⟨hsw_acc, hsw_y, hsw_fr⟩ := accYSwap_apply cuccaroAdder w bits
    (mulInputAccOf cuccaroAdder w bits numWin acc₀ y) hinj
  -- The accumulator (augend) bit of `mulInputAccOf z v` is `z.testBit i`.
  have hacc : ∀ (z v : Nat) i, i < bits →
      mulInputAccOf cuccaroAdder w bits numWin z v (cuccaroAdder.augendIdx (1 + 2 * w) i)
        = z.testBit i := by
    intro z v i hi
    exact writeReg_at _ bits z _ hinj i hi
  -- The y-register bit of `mulInputAccOf z v` is `v.testBit i` (off the augend).
  have hyreg : ∀ (z v : Nat) i, i < bits →
      mulInputAccOf cuccaroAdder w bits numWin z v
          (1 + 2 * w + cuccaroAdder.span bits + i) = v.testBit i := by
    intro z v i hi
    unfold mulInputAccOf
    rw [writeReg_frame _ _ _ _ _ (fun k _ heq => by
          have : cuccaroAdder.augendIdx (1 + 2 * w) k = 1 + 2 * w + 2 * k + 1 := rfl
          have hsp : cuccaroAdder.span bits = 2 * bits + 1 := rfl
          omega),
        mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v _
          (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_at (1 + 2 * w + cuccaroAdder.span bits) (numWin * w) v i (by omega)
  -- mulInputOf is multiplicand-INDEPENDENT off the y-register (the crux of "pure layout").
  have hindep : ∀ (u v p : Nat), (∀ i, i < bits → p ≠ 1 + 2 * w + cuccaroAdder.span bits + i) →
      mulInputOf cuccaroAdder w bits numWin u p = mulInputOf cuccaroAdder w bits numWin v p := by
    intro u v p hp
    have hsp : cuccaroAdder.span bits = 2 * bits + 1 := rfl
    by_cases hc : p = ulookup_ctrl_idx
    · rw [hc, mulInputOf_ctrl, mulInputOf_ctrl]
    · by_cases hlow : p < 1 + 2 * w + cuccaroAdder.span bits
      · rw [mulInputOf_low cuccaroAdder w bits numWin u p hc hlow,
            mulInputOf_low cuccaroAdder w bits numWin v p hc hlow]
      · have hhigh : 1 + 2 * w + cuccaroAdder.span bits + (numWin * w) ≤ p := by
          rw [hbits]
          by_contra hcon
          exact hp (p - (1 + 2 * w + cuccaroAdder.span bits)) (by omega) (by omega)
        rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin u p hc,
            mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v p hc,
            encodeReg_high _ _ _ _ hhigh, encodeReg_high _ _ _ _ hhigh]
  funext p
  by_cases hA : ∃ i, i < bits ∧ p = cuccaroAdder.augendIdx (1 + 2 * w) i
  · obtain ⟨i, hi, rfl⟩ := hA
    rw [hsw_acc i hi, hyreg acc₀ y i hi, hacc y acc₀ i hi]
  · by_cases hY : ∃ i, i < bits ∧ p = 1 + 2 * w + cuccaroAdder.span bits + i
    · obtain ⟨i, hi, rfl⟩ := hY
      rw [hsw_y i hi, hacc acc₀ y i hi, hyreg y acc₀ i hi]
    · push_neg at hA hY
      rw [hsw_fr p (fun i hi => ⟨hA i hi, hY i hi⟩)]
      show mulInputAccOf cuccaroAdder w bits numWin acc₀ y p
        = mulInputAccOf cuccaroAdder w bits numWin y acc₀ p
      unfold mulInputAccOf
      rw [writeReg_frame _ _ _ _ _ (fun i hi h => hA i hi h),
          writeReg_frame _ _ _ _ _ (fun i hi h => hA i hi h)]
      exact hindep y acc₀ p hY

open FormalRV.Shor.CosetEigenstate.InPlaceCosetGate (inplaceCosetGate inplaceCosetGate_unfold)

/-- **CHECKPOINT 3, brick 2c — the full per-term LITERAL action** (`pass1 ; swap ; pass2`).
    On the nonzero-accumulator input `mulInputAccOf acc₀ y`, the whole in-place gate produces
    `mulInputAccOf cleared V`, where BOTH transformed register values are exposed as LITERAL
    `% 2^bits` integers (NOT collapsed to `0` or to `% N`):

      V       = (acc₀ + ∑ tableValue a      (window y)) % 2^bits   -- result register (pass 1)
      cleared = (y    + ∑ tableValue (N−aInv)(window V)) % 2^bits   -- accumulator (pass 2)

    Proof: `inplaceCosetGate_unfold` exposes the three legs; `Gate.applyNat_seq` threads them;
    brick 2a (pass 1, `c := a`), brick 2b (swap), brick 2a (pass 2, `c := N−aInv`, accumulator
    `y`, multiplicand `V`).  Pure register arithmetic — the coset-residue form of `cleared`
    (that it lands in the finite coset-0 window OFF the reverse-wrap bad set) is brick 3,
    proven SEPARATELY; it is deliberately NOT reduced here. -/
theorem inplaceCosetGate_per_term (w bits N a aInv numWin acc₀ y : Nat) (hw : 0 < w)
    (hbits : numWin * w = bits) :
    Gate.applyNat (inplaceCosetGate w bits N a aInv numWin)
        (mulInputAccOf cuccaroAdder w bits numWin acc₀ y)
      = mulInputAccOf cuccaroAdder w bits numWin
          ((y + ∑ k ∈ Finset.range numWin, tableValue (N - aInv) N w k
              (window w
                ((acc₀ + ∑ k ∈ Finset.range numWin, tableValue a N w k (window w y k)) % 2 ^ bits)
                k)) % 2 ^ bits)
          ((acc₀ + ∑ k ∈ Finset.range numWin, tableValue a N w k (window w y k)) % 2 ^ bits) := by
  rw [inplaceCosetGate_unfold]
  simp only [Gate.applyNat_seq]
  rw [cosetMul_pass_concrete w bits N a numWin acc₀ y hw,
      accYSwap_mulInputAccOf w bits numWin _ y hbits,
      cosetMul_pass_concrete w bits N (N - aInv) numWin y _ hw]

end FormalRV.Shor.CosetEigenstate.InPlaceCosetClearing
