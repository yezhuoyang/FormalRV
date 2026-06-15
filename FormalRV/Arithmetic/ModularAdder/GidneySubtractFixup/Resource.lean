/-
  FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Resource
  ──────────────────────────────────────────────────────────────
  COUNT theorem for the faithful Gidney-2025 subtract-fixup modular adder, and its
  link to the paper's headline `2.5n` figure.

  ## The exact count

  `gidneyModAddFixup bits p c` is TWO measured Gidney adds (the subtraction of `p−c`
  and the conditional add-back of `p`) plus Toffoli-FREE glue (the constant/masked
  load cascades are X/CX, the flag copy is a CX, the flag release is a measurement).
  Each measured add at width `W = bits + 1` costs `W` Toffoli
  (`toffoli_gidneyAdderMeasured`), so the total is exactly

      toffoli (gidneyModAddFixup bits p c) = 2·(bits + 1)        (= `2n` essentially).

  ## Relation to the paper

  Gidney 2025 (main.tex L977) charges `2.5n` Toffoli to its modular adder (the audit
  constant `g2025_modadd_toffoli_halves n = 5n` half-units, i.e. `2.5n` full), versus
  Berry et al.'s `3.5n`. The `2.5n` figure INCLUDES a deferred phase-correction
  overhead; the paper itself notes the construction is `2n` "if the phase correction
  is deferred". Our measurement-based Boolean construction realises exactly that `2n`
  lower variant — `2·(bits + 1)` Toffoli, two `n`-Toffoli measured adds — so it MEETS
  (indeed BEATS, for `bits ≥ 4`) the paper's `2.5n` headline.

  `gidneyModAddFixup_meets_g2025_modadd` states the head-to-head in the paper's
  half-Toffoli currency: `2 · toffoli ≤ g2025_modadd_toffoli_halves bits` for
  `4 ≤ bits`.
-/
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Def
import FormalRV.Audit.Gidney2025.SystemZones

namespace FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder

/-! ## §1. Toffoli-freeness of the glue cascades. -/

/-- The constant-load cascade is Toffoli-free (only `X` / `I`). -/
theorem tcount_loadConst : ∀ (W d : Nat), Gate.tcount (loadConst W d) = 0
  | 0,     _ => rfl
  | k + 1, d => by
      simp only [loadConst, Gate.tcount, tcount_loadConst k d]
      split <;> simp [Gate.tcount]

/-- The masked-prepare cascade is Toffoli-free (only `CX` / `I`). -/
theorem tcount_prepareMaskedP : ∀ (flagIdx W p : Nat),
    Gate.tcount (prepareMaskedP flagIdx W p) = 0
  | _,       0,     _ => rfl
  | flagIdx, k + 1, p => by
      simp only [prepareMaskedP, Gate.tcount, tcount_prepareMaskedP flagIdx k p]
      split <;> simp [Gate.tcount]

/-! ## §2. The exact Toffoli count: two measured adds = `2·(bits+1)`. -/

/-- `addConstMeasured W d` costs exactly `W` Toffoli (the measured add; the load
cascades are Toffoli-free). -/
theorem tcount_addConstMeasured (n d : Nat) :
    EGate.tcount (addConstMeasured (n + 2) d) = 7 * (n + 2) := by
  show EGate.tcount
    (EGate.seq (EGate.seq (EGate.base (loadConst (n + 2) d)) (gidneyAdderMeasured (n + 2) 0))
      (EGate.base (loadConst (n + 2) d))) = 7 * (n + 2)
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) 0) = 7 * (n + 2) := by
    show EGate.tcount
      (EGate.seq
        (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                              (gidney_final_cx_cascade (n + 2))))
        (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
               tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  simp only [EGate.tcount, tcount_loadConst, hadd, Nat.add_zero, Nat.zero_add]

/-- `conditionalAddP W flagIdx p` costs exactly `W` Toffoli (one measured add; the
masked prepare/un-prepare cascades are Toffoli-free). -/
theorem tcount_conditionalAddP (n flagIdx p : Nat) :
    EGate.tcount (conditionalAddP (n + 2) flagIdx p) = 7 * (n + 2) := by
  show EGate.tcount
    (EGate.seq
      (EGate.seq (EGate.base (prepareMaskedP flagIdx (n + 2) p)) (gidneyAdderMeasured (n + 2) 0))
      (EGate.base (prepareMaskedP flagIdx (n + 2) p))) = 7 * (n + 2)
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) 0) = 7 * (n + 2) := by
    show EGate.tcount
      (EGate.seq
        (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                              (gidney_final_cx_cascade (n + 2))))
        (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
               tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  simp only [EGate.tcount, tcount_prepareMaskedP, hadd, Nat.add_zero, Nat.zero_add]

/-- **★ THE COUNT — `gidneyModAddFixup bits p c` is exactly `2·(bits+1)` Toffoli.**
Two measured Gidney adds at width `bits+1` (`bits+1` Toffoli each); the constant /
masked-load cascades, the flag-copy CX, and the flag-release measurement are all
Toffoli-free. With `bits = n+1` this is `2·(n+2)`. -/
theorem toffoli_gidneyModAddFixup (n p c : Nat) :
    EGate.toffoli (gidneyModAddFixup (n + 1) p c) = 2 * (n + 2) := by
  show EGate.toffoli
    (EGate.seq
      (EGate.seq
        (EGate.seq
          (addConstMeasured (n + 2) (2 ^ (n + 2) - (p - c)))
          (EGate.base (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2)))))
        (conditionalAddP (n + 2) (adder_n_qubits (n + 2)) p))
      (EGate.mz (adder_n_qubits (n + 2)))) = 2 * (n + 2)
  unfold EGate.toffoli
  simp only [EGate.tcount, Gate.tcount, tcount_addConstMeasured, tcount_conditionalAddP,
             Nat.add_zero]
  rw [show 7 * (n + 2) + 7 * (n + 2) = 2 * (n + 2) * 7 by ring, Nat.mul_div_cancel _ (by norm_num)]

/-! ## §3. Head-to-head with the paper's `2.5n` headline. -/

/-- **The fixup adder MEETS (and beats) Gidney's `2.5n`.** In the paper's
half-Toffoli currency, twice the verified Toffoli count of `gidneyModAddFixup`
(i.e. its cost in half-units) is `≤` the paper's `g2025_modadd_toffoli_halves bits =
5·bits` for `bits ≥ 4`. Our measurement-based construction realises the paper's
deferred-phase-correction `2n` variant (two `n`-Toffoli measured adds), strictly
below the `2.5n` headline once `bits ≥ 4`. -/
theorem gidneyModAddFixup_meets_g2025_modadd (n : Nat) (hn : 3 ≤ n) :
    2 * EGate.toffoli (gidneyModAddFixup (n + 1) 0 0)
      ≤ FormalRV.Audit.Gidney2025.g2025_modadd_toffoli_halves (n + 1) := by
  rw [toffoli_gidneyModAddFixup,
      show FormalRV.Audit.Gidney2025.g2025_modadd_toffoli_halves (n + 1) = 5 * (n + 1) from rfl]
  omega

end FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
