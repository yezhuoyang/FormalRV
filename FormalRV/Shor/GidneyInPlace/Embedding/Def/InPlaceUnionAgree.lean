/-
  FormalRV.Shor.GidneyInPlace.InPlaceUnionAgree — F2 (the no-strengthening core):
  the column-independent UNION bad set and the entry-wise off-union agreement.
  ════════════════════════════════════════════════════════════════════════════

  The controlled-oracle lift (`ControlOracleLift.controlled_shifted_oracle_hintertwine`) consumes
  an ENTRY-WISE matrix identity `hwork_int` off a SINGLE, column-independent `bad_step` Finset, and
  itself performs the arbitrary-superposition extension (by linearity — that part is already
  PROVEN).  T2 (`gidneyInPlaceWithSwap_agree_off_explicit`) gives only COLUMNWISE (per residue `z`)
  agreement off the z-DEPENDENT `inplaceBadSetB z`.

  This file builds the legitimate bridge — NOT an arbitrary-superposition extension, but the
  honest "entry-wise identity off the UNION":

    • `inplaceUnionBad` = `(range N).biUnion (z ↦ inplaceBadSetB z)` — a SINGLE Finset, the union
      of every column's bad set; column-INDEPENDENT (the bad_step `hwork_int` needs).
    • `inplace_agree_off_union` — off this union, T2 holds for EVERY column `z < N` SIMULTANEOUSLY:
      `y ∉ union ⇒ y ∉ inplaceBadSetB z` for the specific `z`, so T2 at column `z` applies.

  This is the audit-critical "no strengthening" step: the per-column z-dependent agreement is made
  column-independent by UNIONING the bad sets (a superset), NOT by extending a single column's bad
  set to arbitrary superpositions.  The remaining F2 bricks (the matrix `hwork_int` wrapping this
  with `workMat`/E₂mat + the `f_ideal` shift-permutation hypothesis + the casts, the E₂
  generalizations of `controlled_shifted_oracle_{hintertwine,hc_local}`, and the `hstep` assembly)
  build ON this lemma.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceAgreeOffExplicit

namespace FormalRV.Shor.GidneyInPlace.InPlaceUnionAgree

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedGate (gidneyInPlaceWithSwap)
open FormalRV.Shor.GidneyInPlace.InPlaceComposedAgree (inplaceBadSetB)
open FormalRV.Shor.GidneyInPlace.InPlaceAgreeOffExplicit (gidneyInPlaceWithSwap_agree_off_explicit)

/-- **The column-independent UNION bad set** `bad_step = ⋃_{z<N} inplaceBadSetB z`.  A SINGLE
    Finset of output basis indices, independent of any column `y2` — the shape `hwork_int`'s
    `bad_step` requires.  (Its Born mass is the F3 accumulation, NOT computed here.) -/
noncomputable def inplaceUnionBad (w bits numWin N cm k : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) : Finset (Fin (2 ^ cosetDim w bits)) :=
  (Finset.range N).biUnion
    (fun z => inplaceBadSetB w bits numWin N cm k z TfamK TfamKinv hw hbits)

/-- **Entry-wise off-union agreement (the F2 no-strengthening core).**  Off the union bad set, the
    in-place gate's exact coset-shift agreement (T2) holds for EVERY canonical column `z < N`
    simultaneously: `y ∉ inplaceUnionBad` forces `y ∉ inplaceBadSetB z` for that specific `z`, so
    T2 at column `z` gives the entry equality.  This is the legitimate column-independent identity
    (entry-wise off the union) — NOT an arbitrary-superposition extension. -/
theorem inplace_agree_off_union
    (w bits numWin N cm k kInv : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hfitAll : ∀ z, z < N → (k * z) % N + (2 ^ cm - 1) * N < 2 ^ bits)
    (y : Fin (2 ^ cosetDim w bits))
    (hy : y ∉ inplaceUnionBad w bits numWin N cm k TfamK TfamKinv hw hbits)
    (z : Nat) (hz : z < N) :
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (gidneyInPlaceWithSwap w bits TfamK TfamKinv numWin))
      * cosetInputVec w bits N cm z 0) y 0
      = cosetInputVec w bits N cm ((k * z) % N) 0 y 0 :=
  gidneyInPlaceWithSwap_agree_off_explicit w bits numWin N cm k kInv z TfamK TfamKinv
    hTfamK hTfamKinv hw hbits hN hz hkkinv (hfitAll z hz) y
    (fun hyz => hy (Finset.mem_biUnion.mpr ⟨z, Finset.mem_range.mpr hz, hyz⟩))

end FormalRV.Shor.GidneyInPlace.InPlaceUnionAgree
