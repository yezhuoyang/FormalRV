/-
  FormalRV.Framework.ZX — spider FUSION for the ZX IR, proven to PRESERVE the
  PPM semantics.

  Spider fusion is THE core ZX rewrite used to OPTIMIZE lattice surgery (reduce
  spacetime volume): two same-colour spiders connected by a wire fuse into one
  spider whose external legs are the symmetric difference of their supports (the
  shared wire qubit cancels — Z·Z = I, X·X = I).  In our PPM grounding (each
  spider = a Pauli-product measurement, `ZXStabilizer`), fusion is exactly
  MULTIPLICATION of the measured Paulis:

      (Z-spider on S₁) ⊕ (Z-spider on S₂)  =  Z-spider on (S₁ ⊕ S₂),
      with   zRow S₁ · zRow S₂ = zRow (S₁ ⊕ S₂)          [`fuseZ_toPauli`]

  So the fused spider's PPM op measures exactly the PRODUCT of what the two
  original spiders measured (`fuse_toStabOp`).  This makes "verify the OPTIMIZED
  lattice surgery" a THEOREM — any volume-reducing rewrite built from spider
  fusion is sound at the PPM layer — rather than a per-instance Stim check.

  The underlying multiplication algebra is already proven in `SurgeryCorrect`
  (`signedZRow_mul`, `signedXRow_mul`); here we package it as the ZX fusion rule
  and connect it to `ZXStabilizer`'s spiders.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.PPM.Rules.ZXStabilizer

namespace FormalRV.Framework.ZX

open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.StabProgram
open FormalRV.Framework.PPMOp
open FormalRV.Framework.PauliSem

/-- Fuse two same-colour spiders: the external legs are the symmetric difference
    (`vec_xor`) of the supports — shared wires cancel.  Colour from `sp1`. -/
def fuse (sp1 sp2 : ZXSpider) : ZXSpider :=
  { color := sp1.color, support := vec_xor sp1.support sp2.support }

/-- **Spider fusion, Z-type (Pauli level).**  Two Z-spiders fuse by XOR-ing their
    supports, and the fused Z-row equals the PRODUCT of the two Z-rows. -/
theorem fuseZ_toPauli (S1 S2 : BoolVec) (h : S1.length = S2.length) :
    (zRow S1).mul (zRow S2) = zRow (vec_xor S1 S2) := by
  rw [zRow_eq_signedZRow_false S1, zRow_eq_signedZRow_false S2,
      signedZRow_mul false false S1 S2 h]
  rfl

/-- **Spider fusion, X-type (Pauli level).** -/
theorem fuseX_toPauli (S1 S2 : BoolVec) (h : S1.length = S2.length) :
    (xRow S1).mul (xRow S2) = xRow (vec_xor S1 S2) := by
  rw [xRow_eq_signedXRow_false S1, xRow_eq_signedXRow_false S2,
      signedXRow_mul false false S1 S2 h]
  rfl

/-- **Spider fusion PRESERVES PPM semantics.**  For two same-colour spiders of
    equal support length, the fused spider measures exactly the PRODUCT of the
    two spiders' Paulis: `(fuse sp1 sp2).toPauli = sp1.toPauli · sp2.toPauli`.
    The ZX fusion rewrite is therefore sound at the PPM layer. -/
theorem fuse_toPauli (sp1 sp2 : ZXSpider) (hc : sp1.color = sp2.color)
    (h : sp1.support.length = sp2.support.length) :
    (fuse sp1 sp2).toPauli = (sp1.toPauli).mul (sp2.toPauli) := by
  unfold ZXSpider.toPauli fuse
  rw [← hc]
  cases sp1.color with
  | Z => exact (fuseZ_toPauli sp1.support sp2.support h).symm
  | X => exact (fuseX_toPauli sp1.support sp2.support h).symm

/-- **Spider fusion at the PPM-op level.**  The fused spider compiles to a single
    PPM that measures the product of the two original measured Paulis — the
    rewrite "two spiders → one" is exactly "two measurements → their product". -/
theorem fuse_toStabOp (sp1 sp2 : ZXSpider) (hc : sp1.color = sp2.color)
    (h : sp1.support.length = sp2.support.length) :
    (fuse sp1 sp2).toStabOp = StabOp.meas ((sp1.toPauli).mul (sp2.toPauli)) := by
  unfold ZXSpider.toStabOp
  rw [fuse_toPauli sp1 sp2 hc h]

/-! ## Concrete smokes: fusion on real spiders -/

/-- Two Z-spiders on `{0,1}` and `{1,2}` fuse to a Z-spider on `{0,2}` (the shared
    leg 1 cancels) — the canonical merge-product. -/
example :
    (fuse { color := ZXColor.Z, support := [true, true, false] }
          { color := ZXColor.Z, support := [false, true, true] }).support
      = [true, false, true] := by decide

/-- The fused spider's measured Pauli is the product, on a concrete instance. -/
example :
    (fuse { color := ZXColor.X, support := [true, false] }
          { color := ZXColor.X, support := [true, true] }).toPauli
      = ((xRow [true, false]).mul (xRow [true, true])) :=
  fuse_toPauli _ _ rfl rfl

end FormalRV.Framework.ZX
