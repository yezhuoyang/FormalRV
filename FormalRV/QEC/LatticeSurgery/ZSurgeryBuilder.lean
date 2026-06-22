/-
  FormalRV.QEC.LatticeSurgery.ZSurgeryBuilder
  ───────────────────────────────────────────
  **The canonical logical-Z̄ surgery builder — pure-Z measurements made
  first-class (completeness step 1).**

  A Z-type joint logical measurement is an X-type measurement on the CSS DUAL
  code (`hx ↔ hz`).  So `canonicalZSurgery qec ℓ` is literally
  `canonicalXSurgery (cssDual qec) ℓ`, and EVERY X-surgery theorem
  (`verify_surgery_gadget`, `surgery_implements_logical_measurement`) applies
  verbatim — the dual's X-logical IS the original code's Z-logical.  This
  lifts the previously hand-rolled per-instance dual swap
  (`surface3x2_dual`, …) into a parametric builder.
-/
import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder

namespace FormalRV.QEC

open FormalRV.Framework FormalRV.Framework.LDPC

/-- The CSS dual of a code: swap the X- and Z-check matrices.  A Z-logical of
`qec` is an X-logical of `cssDual qec`. -/
def cssDual (qec : QECCode) : QECCode :=
  { qec with hx := qec.hz, hz := qec.hx }

/-- **The canonical single-ancilla logical-Z̄ surgery gadget on `qec`**,
measuring the Z-type logical with support `ℓ` — by construction, the X-surgery
on the dual code.  Inherits all X-surgery verification and correctness. -/
def canonicalZSurgery (qec : QECCode) (ℓ : BoolVec) (tau bound : Nat) :
    SurgeryGadget :=
  canonicalXSurgery (cssDual qec) ℓ tau bound

/-- The Z-surgery gadget IS the dual's X-surgery gadget — so its structural
verifier reduces to the dual's (definitionally). -/
theorem canonicalZSurgery_eq (qec : QECCode) (ℓ : BoolVec) (tau bound : Nat) :
    canonicalZSurgery qec ℓ tau bound
      = canonicalXSurgery (cssDual qec) ℓ tau bound := rfl

/-- The dual of the dual is the original code (`hx`/`hz` swapped twice). -/
theorem cssDual_cssDual (qec : QECCode) : cssDual (cssDual qec) = qec := rfl

end FormalRV.QEC
