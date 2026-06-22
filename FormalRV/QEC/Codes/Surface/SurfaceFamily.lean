/-
  FormalRV.QEC.Codes.Surface.SurfaceFamily — the surface-code family at
  ARBITRARY distance `d`.

  The generator `code d` (= `surfaceHGP d`, the HGP of two distance-d
  repetition checks) is total in `d`: for ANY distance it produces the
  `[[d² + (d−1)², 1, d]]` check matrices, the lowered stabilizer list, the
  compiled syndrome-extraction circuit, and its Stim text — the review/use
  artifacts.  The compiled-circuit SEMANTICS theorem
  (`family_extraction_measures`) holds at EVERY `d`, conditional only on the
  decidable `well_shaped` check, which is discharged below at d = 3 (kernel)
  and d = 5 (native) and is believed ∀d (the parametric well-shapedness /
  CSS programme for HGP is tracked work, mirroring `LPCssCondition`).

  No `sorry`; no project axioms beyond the noted `native_decide` pins.
-/

import FormalRV.QEC.Codes.Surface.SurfaceChain

namespace FormalRV.QEC.Codes.Surface

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.PauliSem

/-! ## The arbitrary-distance generator and its review artifacts -/

/-- The unrotated surface code at ARBITRARY distance `d`. -/
abbrev code (d : Nat) : FormalRV.QEC.CSSCode := FormalRV.QEC.Algebraic.surfaceHGP d

/-- X / Z check matrices at arbitrary distance (external review/use). -/
abbrev checkMatrixX (d : Nat) : FormalRV.Framework.LDPC.BoolMat := (code d).hx
abbrev checkMatrixZ (d : Nat) : FormalRV.Framework.LDPC.BoolMat := (code d).hz

/-- The detailed stabilizer generators (phased Pauli strings) at arbitrary
    distance. -/
abbrev stabilizers (d : Nat) : List PauliString := (code d).toStabilizers

/-- The compiled syndrome-extraction round at arbitrary distance. -/
abbrev extractionRound (d : Nat) : Round :=
  FormalRV.QEC.CSSCode.extractionRound (code d)

/-- Its Stim text — the machine-readable review artifact. -/
abbrev extractionStim (d : Nat) : String := toStim (Round.ops (extractionRound d))

/-- `[[d² + (d−1)², ·, ·]]` at every distance (definitional). -/
theorem code_n (d : Nat) : (code d).n = d * d + (d - 1) * (d - 1) := rfl

/-! ## Semantics at EVERY distance -/

/-- **Arbitrary-distance semantics.**  For every `d`, the compiled extraction
    round measures exactly the code's stabilizers — the parametric
    `extractionRound_measures_code` specialized to the family generator,
    conditional only on the decidable shape check. -/
theorem family_extraction_measures (d : Nat)
    (h : (code d).well_shaped = true) :
    Round.measuredDataObs
        ((code d).n + (code d).hx.length + (code d).hz.length)
        (code d).n (extractionRound d)
      = (code d).toStabilizers :=
  extractionRound_measures_code (code d) h

/-! ## Sampled-parameter validity (the hypothesis is dischargeable) -/

/-- d = 3 validity — REUSED from the chain file's theorems (`code 3` is
    definitionally `Instances.surface3`), not re-decided. -/
theorem code3_valid : (code 3).valid = true := by
  show FormalRV.QEC.Instances.surface3.valid = true
  rw [FormalRV.QEC.CSSCode.valid, surface3_well_shaped, surface3_css]
  rfl

set_option maxRecDepth 16384 in
theorem code5_well_shaped : (code 5).well_shaped = true := by native_decide

set_option maxRecDepth 16384 in
theorem code5_css : (code 5).css_condition = true := by native_decide

/-- The d = 5 instance of the arbitrary-distance semantics theorem. -/
theorem code5_extraction_measures :
    Round.measuredDataObs
        ((code 5).n + (code 5).hx.length + (code 5).hz.length)
        (code 5).n (extractionRound 5)
      = (code 5).toStabilizers :=
  family_extraction_measures 5 code5_well_shaped

end FormalRV.QEC.Codes.Surface
