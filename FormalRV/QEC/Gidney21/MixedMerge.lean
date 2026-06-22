/-
  FormalRV.QEC.Gidney21.MixedMerge
  ────────────────────────────────
  **(completeness keystone) MIXED cross-patch X/Z joint measurement, via the
  per-patch-ORIENTED composite — reusing the X-surgery wholesale.**

  A joint measurement of a MIXED Pauli where each patch is measured in a
  single type (X̄ on some patches, Z̄ on others — e.g. the CCZ `measureSel2`
  axes `X[a]Z[a+2]`) is realized WITHOUT any new surgery machinery:

    • orient each patch — keep the PRIMAL code for an X-measured patch, take
      the CSS DUAL (`hx ↔ hz`) for a Z-measured patch;
    • direct-sum the oriented codes into one composite;
    • run a single `canonicalXSurgery` measuring the composite's joint
      X-logical (`logicalX` on primal blocks, `logicalZ` on dual blocks).

  On a dual block, the X-logical IS the original patch's Z̄.  So the one
  X-surgery measures `⊗ X̄ ⊗ Z̄` — the mixed operator — and inherits the FULL
  `MergeFullyCorrect` (syndrome extraction + logical measurement) verbatim.
-/
import FormalRV.QEC.Gidney21.SurgerySemantics
import FormalRV.QEC.Gidney21.GadgetScheduleDispatch
import FormalRV.QEC.Codes.Surface.RotatedLogical
import FormalRV.QEC.LatticeSurgery.XSurgeryBuilder
import FormalRV.QEC.CSSCode
import FormalRV.QEC.CodeBuilders

namespace FormalRV.QEC.Gidney21

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.QEC.Codes.Surface
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.LatticeSurgery

/-! ## §1. Per-patch orientation. -/

/-- The CSS dual of a CSS code (swap X- and Z-checks). -/
def cssDualC (c : CSSCode) : CSSCode := ⟨c.n, c.hz, c.hx⟩

/-- Orient one patch for the joint X-surgery: PRIMAL rotated surface for an
X-measured patch, its CSS DUAL for a Z-measured patch. -/
def orientedCSS : MergeAxis → Nat → CSSCode
  | MergeAxis.xAxis, d => rotatedSurface d
  | MergeAxis.zAxis, d => cssDualC (rotatedSurface d)

/-- The per-patch joint-X support: `logicalX` on a primal (X) block,
`logicalZ` on a dual (Z) block (= that block's X-logical). -/
def orientedSupp : MergeAxis → Nat → BoolVec
  | MergeAxis.xAxis, d => logicalX d
  | MergeAxis.zAxis, d => logicalZ d

/-! ## §2. The oriented composite and the mixed merge. -/

/-- The direct-sum composite of the oriented patches. -/
def mixedComposite (axes : List MergeAxis) (d : Nat) : CSSCode :=
  axes.foldr (fun a acc => (orientedCSS a d).directSum acc) ⟨0, [], []⟩

/-- The joint support over the composite: each patch's oriented support,
concatenated (block `i` lives at its direct-sum data offset). -/
def mixedSupport (axes : List MergeAxis) (d : Nat) : BoolVec :=
  axes.foldr (fun a acc => orientedSupp a d ++ acc) []

/-- **THE MIXED CROSS-PATCH MERGE**: one X-surgery on the oriented composite,
measuring `⊗_i (X̄_i if xAxis else Z̄_i)`. -/
def mixedMerge (axes : List MergeAxis) (d tau bound : Nat) : SurgeryGadget :=
  canonicalXSurgery ((mixedComposite axes d).toQECCode 1 d)
    (mixedSupport axes d) tau bound

/-! ## §3. The concrete CCZ shape: X̄₀ ⊗ Z̄₁ at d = 3, fully correct. -/

/-- The CCZ-style mixed axes: patch 0 in X, patch 1 in Z. -/
def xzAxes : List MergeAxis := [MergeAxis.xAxis, MergeAxis.zAxis]

/-- **The X̄₀Z̄₁ mixed merge verifies** (d=3). -/
theorem mixedXZ3_verifies :
    SurgeryGadget.verify_surgery_gadget (mixedMerge xzAxes 3 2 30) = true := by
  decide

/-- **The X̄₀Z̄₁ mixed merge is FULLY SEMANTICALLY CORRECT** — its detailed
syndrome extraction of the merged composite AND its measurement of the joint
mixed logical Pauli are both correct, on the same circuit. -/
theorem mixedXZ3_fully_correct : MergeFullyCorrect (mixedMerge xzAxes 3 2 30) :=
  mergeFullyCorrect_of (mixedMerge xzAxes 3 2 30)

/-- The X̄₀Z̄₁ merge's syndrome extraction measures the merged stabilizers. -/
theorem mixedXZ3_syndrome_correct :
    Round.measuredDataObs
        ((mergedCSS (mixedMerge xzAxes 3 2 30)).n
          + (mergedCSS (mixedMerge xzAxes 3 2 30)).hx.length
          + (mergedCSS (mixedMerge xzAxes 3 2 30)).hz.length)
        (mergedCSS (mixedMerge xzAxes 3 2 30)).n
        (SurgeryGadget.extractionRound (mixedMerge xzAxes 3 2 30))
      = (mergedCSS (mixedMerge xzAxes 3 2 30)).toStabilizers :=
  merge_syndrome_correct (mixedMerge xzAxes 3 2 30) (by decide)

/-- The X̄₀Z̄₁ merge measures its target joint mixed logical, for every
outcome. -/
theorem mixedXZ3_logical_correct (signs : List Bool)
    (hsig : signs.length = (mixedMerge xzAxes 3 2 30).merged_hx.length) :
    selectedSignedProduct (mixedMerge xzAxes 3 2 30).span_witness
        (mixedMerge xzAxes 3 2 30).merged_hx signs
      = signedXRow (selectedParity (mixedMerge xzAxes 3 2 30).span_witness signs)
          (mixedMerge xzAxes 3 2 30).target_pauli :=
  ((mixedXZ3_fully_correct).2 signs hsig mixedXZ3_verifies (by decide) (by decide))

/-- The two oriented supports are GENUINE logicals: `logicalX 3` a valid X of
the primal patch, `logicalZ 3` a valid Z of the original patch — so the merge
measures the true `X̄₀ ⊗ Z̄₁`, not an arbitrary operator. -/
theorem mixedXZ3_supports_genuine :
    isXLogical 3 (logicalX 3) = true ∧ isZLogical 3 (logicalZ 3) = true :=
  ⟨logicalX3_valid, logicalZ3_valid⟩

/-! ## §4. d = 27 — the mixed merge at GE2021 scale. -/

/-- **The X̄₀Z̄₁ mixed merge verifies at d = 27** (composite of two
[[729,1,27]] patches; bound 60 covers the weight-55 connection check). -/
theorem mixedXZ27_verifies :
    SurgeryGadget.verify_surgery_gadget (mixedMerge xzAxes 27 18 60) = true := by
  native_decide

/-- **The d=27 X̄₀Z̄₁ mixed merge is fully semantically correct** — the mixed
cross-patch joint measurement at GE2021 scale, syndrome + logical. -/
theorem mixedXZ27_fully_correct : MergeFullyCorrect (mixedMerge xzAxes 27 18 60) :=
  mergeFullyCorrect_of (mixedMerge xzAxes 27 18 60)

end FormalRV.QEC.Gidney21
