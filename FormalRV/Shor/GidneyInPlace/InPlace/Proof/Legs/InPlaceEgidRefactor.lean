/-
  FormalRV.Shor.GidneyInPlace.InPlaceEgidRefactor
  ───────────────────────────────────────────────────
  THE GO/NO-GO: the two-factorization handoff between pass-1 (eGid data = b-block) and
  pass-2 (eGid data = a-block).  After pass1, register `a` holds `ja`, register `b`
  holds `jb' = (jb + ∑ₖ TfamK k (window w ja k)) % 2^bits`, scratch clean.  This file
  proves that THIS canonical configuration is the SAME register index whether read in
  the pass-1 factorization `eGid(bBase)` (control = a, data = b) or the pass-2
  factorization `eGid(aBase)` (control = b, data = a) — so reverse-pass2 can consume
  pass1's output WITHOUT any cross-register obstruction.

  VERDICT: the handoff LANDS cleanly (no bad set needed at the basis-index level).  The
  reason: at a SINGLE basis branch the config `(a=ja, b=jb', scratch clean)` is a clean
  PRODUCT — viewed through `eGid(bBase)` it is `inplaceAccInput` with acc=b=jb',
  mult=a=ja; viewed through `eGid(aBase)` it is `inplaceAccInput` with acc=a=ja,
  mult=b=jb'; and these two `inplaceAccInput`s are the SAME `Nat → Bool` function
  (`inplaceAccInput_swap`).  The q(j)-staircase cross-register CORRELATION is a property
  of the SUPERPOSITION (the q·N runway, absorbed by the coset window in the
  bad-mass/normSqDist layer), NOT of any individual basis branch — so it does NOT
  obstruct this per-branch refactor.

  Contents:
   • `inplaceAccInput_swap` — the SAME register config under the swapped (acc,mult)
     roles: `inplaceAccInput bBase aBase jb' ja = inplaceAccInput aBase bBase ja jb'`.
   • `eGid_refactor_pass1_to_pass2` — `eGid(bBase)(xCtrlGid_b(ja), ⟨jb'⟩)
     = eGid(aBase)(xCtrlGid_a(jb'), ⟨ja⟩)` (the pure refactor; via Brick 2's
     `assembleEGid_xCtrlGid` + the swap).
   • `pass1_output_as_pass2_branch` — combining Brick 5's pass-1 dynamics with the
     refactor: `gateToPerm pass1 (eGid_b(xCtrlGid_b(ja), ⟨jb⟩)) = eGid_a(xCtrlGid_a(jb'),
     ⟨ja⟩)` — pass1's output, expressed in the pass-2 factorization, ready for
     reverse-pass2 (Brick 7).

  AUDIT.  Branch indices `ja`, `jb'`, `jb` are RAW `Fin (2^bits)` / `Nat` register
  values (NOT residues; NO requirement that `jb' = (k·x)%N` — `jb'` is a raw coset
  branch).  NO `normSqDist`, NO `inplaceReducedLookupCosetMul_shift`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputTwoReg
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceFoldAction

namespace FormalRV.Shor.GidneyInPlace.InPlaceEgidRefactor

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat gateToPerm)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (inplaceAccInput inplaceWorkInput xCtrlGid assembleEGid_xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase)
open FormalRV.Shor.GidneyInPlace.InPlaceFoldAction (gidneyProductAddTOf_pass1_perm_through_eGid)

/-! ## §1. The swap lemma — the same config under swapped (acc, mult) roles. -/

/-- **The two-register config is symmetric in the (acc, mult) roles.**  The register
    function with the b-block as accumulator (`= jb'`) and the a-block as multiplicand
    (`= ja`) is the SAME `Nat → Bool` as the one with the a-block as accumulator
    (`= ja`) and the b-block as multiplicand (`= jb'`): both encode `a-block = ja`,
    `b-block = jb'`, ctrl set, all other scratch clean.  (`aBase = 1+2w`,
    `bBase = 1+2w+bits` are disjoint and adjacent; `numWin·w = bits` aligns the
    multiplicand window with the accumulator block.) -/
theorem inplaceAccInput_swap (w bits numWin ja jb' : Nat) (hbits : numWin * w = bits) :
    inplaceAccInput w bits numWin (bBase w bits) (aBase w) jb' ja
      = inplaceAccInput w bits numWin (aBase w) (bBase w bits) ja jb' := by
  funext p
  unfold inplaceAccInput inplaceWorkInput
  rw [hbits]
  unfold encodeReg aBase bBase ulookup_ctrl_idx
  split_ifs <;> first | rfl | omega

/-! ## §2. The pure refactor: pass-1 factorization index = pass-2 factorization index. -/

/-- **THE REFACTOR (go/no-go).**  The canonical configuration `(a = ja, b = jb',
    scratch clean)` is the SAME `Fin (2^cosetDim)` index in BOTH factorizations: the
    pass-1 `eGid(bBase)` image of `(xCtrlGid_b(ja), ⟨jb'⟩)` (control = a, data = b)
    equals the pass-2 `eGid(aBase)` image of `(xCtrlGid_a(jb'), ⟨ja⟩)` (control = b,
    data = a).  Both reduce (via Brick 2's `assembleEGid_xCtrlGid`) to `funboolNat` of
    the SAME `inplaceAccInput`, identified by `inplaceAccInput_swap`. -/
theorem eGid_refactor_pass1_to_pass2 (w bits numWin : Nat) (hbits : numWin * w = bits)
    (ja jb' : Nat) (hja : ja < 2 ^ bits) (hjb' : jb' < 2 ^ bits) :
    eGid w bits (bBase w bits) (pass1_accfit w bits)
        (xCtrlGid w bits numWin (bBase w bits) (aBase w) ja, ⟨jb', hjb'⟩)
      = eGid w bits (aBase w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (aBase w) (bBase w bits) jb', ⟨ja, hja⟩) := by
  unfold eGid
  rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply]
  unfold eFunGid
  congr 1
  funext i
  rw [assembleEGid_xCtrlGid w bits numWin (bBase w bits) (aBase w) ja jb' i.val
        (pass1_accfit w bits) i.isLt,
      assembleEGid_xCtrlGid w bits numWin (aBase w) (bBase w bits) jb' ja i.val
        (pass2_accfit w bits) i.isLt,
      inplaceAccInput_swap w bits numWin ja jb' hbits]

/-! ## §3. Pass-1 output, expressed in the pass-2 factorization. -/

/-- **Pass-1 output as a pass-2 branch.**  Combining the Brick-5 pass-1 dynamics (which
    sends `eGid_b(xCtrlGid_b(ja), ⟨jb⟩)` to `eGid_b(xCtrlGid_b(ja), ⟨jb'⟩)` with
    `jb' = (jb + ∑ₖ TfamK k (window w ja k)) % 2^bits`) with the refactor, the pass-1
    permutation sends the input branch `(a = ja, b = jb)` to the configuration
    `(a = ja, b = jb')` EXPRESSED in the pass-2 factorization — exactly the form
    reverse-pass2 (Brick 7) consumes.  `jb'` is a RAW coset branch (NOT required to be
    `(k·x)%N`). -/
theorem pass1_output_as_pass2_branch (w bits numWin : Nat) (TfamK : Nat → Nat → Nat)
    (ja jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hja : ja < 2 ^ bits)
    (hjb : jb < 2 ^ bits)
    (hjb' : (jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits)
      (FormalRV.Shor.GidneyInPlace.ProductAddWrapper.gidneyProductAddTOf w bits TfamK
        (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin)) :
    gateToPerm (FormalRV.Shor.GidneyInPlace.ProductAddWrapper.gidneyProductAddTOf w bits TfamK
        (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) (cosetDim w bits) hwt
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits)
            ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits),
            ⟨ja, hja⟩) := by
  rw [gidneyProductAddTOf_pass1_perm_through_eGid w bits numWin TfamK ja jb hw hbits hjb hjb' hwt]
  exact eGid_refactor_pass1_to_pass2 w bits numWin hbits ja
    ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits) hja hjb'

end FormalRV.Shor.GidneyInPlace.InPlaceEgidRefactor
