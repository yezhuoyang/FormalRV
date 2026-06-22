/-
  FormalRV.Shor.GidneyInPlace.InPlaceBranchAction
  ───────────────────────────────────────────────────
  The WHOLE-GATE per-branch action of the in-place coset multiplier — the first
  sub-brick of the capstone assembly.  Composes pass-1 (Brick 5), the two-factorization
  handoff (`pass1_output_as_pass2_branch`), and reverse-pass2 (Brick 7) via a new generic
  `gateToPerm_seq`.  NO agree-off, NO mass bound, NO normSqDist.

  THE MAP.  On the eGid branch `(a = ja, b = jb, scratch clean)` the gate
  `gidneyTwoRegInPlaceCosetMul` acts as:
    jb' := (jb + ∑ₖ TfamK k (window w ja k)) % 2^bits           (pass-1 result, b-block)
    a   ↦ modSub bits ja (∑ₖ TfamKinv k (window w jb' k))       (reverse-pass2, a-block)
  with `modSub` PROPER modular subtraction `(a + 2^bits − S % 2^bits) % 2^bits` (NOT the
  truncated `(a − S) % 2^bits`).  The output is expressed in the pass-2 factorization
  (control = b = jb', data = a).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceEgidRefactor
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceReverseLeg

namespace FormalRV.Shor.GidneyInPlace.InPlaceBranchAction

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (window)
open FormalRV.Shor.GidneyInPlace.GatePerm
  (funboolNat gateToPerm applyFin extendBool funboolEquiv funboolEquiv_val reverse_wellTyped)
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper
  (gidneyProductAddTOf gidneyProductAdd_pass1_wellTyped gidneyProductAdd_pass2_wellTyped)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate
open FormalRV.Shor.GidneyInPlace.InPlaceEgateInput (xCtrlGid)
open FormalRV.Shor.GidneyInPlace.InPlaceReverseLeg (extendBool_applyFin pass2_reverse_through_eGid)
open FormalRV.Shor.GidneyInPlace.InPlaceEgidRefactor (pass1_output_as_pass2_branch)
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  (gidneyTwoRegInPlaceCosetMul pass1 pass2)

/-! ## §1. `gateToPerm` over `Gate.seq` (generic composition). -/

/-- **`gateToPerm` composes over `Gate.seq`.**  `gateToPerm (seq a b) idx = gateToPerm b
    (gateToPerm a idx)`.  Reduces to `applyFin (seq a b) = applyFin b ∘ applyFin a` via
    `gateToPerm_funboolNat` + `extendBool_applyFin` (Brick 7) + `applyNat_seq`. -/
theorem gateToPerm_seq (a b : Gate) (dim : Nat) (ha : Gate.WellTyped dim a)
    (hb : Gate.WellTyped dim b) (hab : Gate.WellTyped dim (Gate.seq a b)) (idx : Fin (2 ^ dim)) :
    gateToPerm (Gate.seq a b) dim hab idx = gateToPerm b dim hb (gateToPerm a dim ha idx) := by
  set φ := (funboolEquiv dim).symm idx with hφ
  have heq : funboolNat dim φ = (funboolEquiv dim) φ := by
    apply Fin.ext
    show funbool_to_nat dim (extendBool dim φ) = ((funboolEquiv dim) φ).val
    rw [funboolEquiv_val]
  have hidx : idx = funboolNat dim φ := by rw [heq, hφ, Equiv.apply_symm_apply]
  rw [hidx, gateToPerm_funboolNat (Gate.seq a b) dim hab φ,
      gateToPerm_funboolNat a dim ha φ,
      gateToPerm_funboolNat b dim hb (applyFin a dim φ)]
  congr 1
  funext i
  show Gate.applyNat (Gate.seq a b) (extendBool dim φ) i.val
    = Gate.applyNat b (extendBool dim (applyFin a dim φ)) i.val
  rw [Gate.applyNat_seq, extendBool_applyFin a dim ha φ]

/-! ## §2. Proper modular subtraction. -/

/-- Modular subtraction on `[0, 2^bits)`: `a ⊖ S = (a + 2^bits − S % 2^bits) % 2^bits`.
    NOT the truncated `(a − S) % 2^bits`. -/
def modSub (bits a S : Nat) : Nat := (a + 2 ^ bits - S % 2 ^ bits) % 2 ^ bits

/-- **The defining identity:** `(a ⊖ S) + S ≡ a` mod `2^bits` (for `a < 2^bits`). -/
theorem modSub_add (bits a S : Nat) (ha : a < 2 ^ bits) :
    (modSub bits a S + S) % 2 ^ bits = a := by
  unfold modSub
  rw [Nat.mod_add_mod]
  have hdm := Nat.div_add_mod S (2 ^ bits)
  have hr : S % 2 ^ bits < 2 ^ bits := Nat.mod_lt _ (by positivity)
  have key : a + 2 ^ bits - S % 2 ^ bits + S = a + 2 ^ bits * (S / 2 ^ bits + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-! ## §3. The whole-gate per-branch action. -/

/-- **The in-place gate's per-branch action.**  On the eGid branch `(a = ja, b = jb)`
    (scratch clean), the whole gate sends it to `(a = modSub bits ja Sinv, b = jb')`
    expressed in the pass-2 factorization, where `jb' = (jb + ∑ₖ TfamK k (window w ja k))
    % 2^bits` and `Sinv = ∑ₖ TfamKinv k (window w jb' k)`.  Composes Brick 5 (pass1),
    `pass1_output_as_pass2_branch` (handoff), and Brick 7 (reverse-pass2) via
    `gateToPerm_seq`.  Raw `Fin (2^bits)` indices; the a-output is genuine modular
    subtraction. -/
theorem gidneyTwoRegInPlace_branch_action (w bits numWin : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (ja jb : Nat) (hw : 0 < w) (hbits : numWin * w = bits) (hja : ja < 2 ^ bits) (hjb : jb < 2 ^ bits)
    (hwt : Gate.WellTyped (cosetDim w bits) (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin)) :
    gateToPerm (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) (cosetDim w bits) hwt
        (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))
      = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits)
              ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits),
            ⟨modSub bits ja (∑ k ∈ Finset.range numWin, TfamKinv k
                (window w ((jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits) k)),
              Nat.mod_lt _ (by positivity)⟩) := by
  set jb' := (jb + ∑ k ∈ Finset.range numWin, TfamK k (window w ja k)) % 2 ^ bits with hjb'def
  have hjb' : jb' < 2 ^ bits := Nat.mod_lt _ (by positivity)
  set Sinv := ∑ k ∈ Finset.range numWin, TfamKinv k (window w jb' k) with hSinvdef
  have hz2 : (modSub bits ja Sinv + Sinv) % 2 ^ bits < 2 ^ bits := by
    rw [modSub_add bits ja Sinv hja]; exact hja
  -- per-pass well-typedness
  have ha : Gate.WellTyped (cosetDim w bits) (pass1 w bits TfamK numWin) :=
    gidneyProductAdd_pass1_wellTyped w bits TfamK numWin hw hbits
  have hb : Gate.WellTyped (cosetDim w bits) (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) :=
    reverse_wellTyped (pass2 w bits TfamKinv numWin) (cosetDim w bits)
      (gidneyProductAdd_pass2_wellTyped w bits TfamKinv numWin hw hbits)
  -- the data `⟨ja, hja⟩` is the B7 pre-image `⟨(modSub + Sinv) % 2^bits, hz2⟩`
  have hdata : (⟨ja, hja⟩ : Fin (2 ^ bits))
      = ⟨(modSub bits ja Sinv + Sinv) % 2 ^ bits, hz2⟩ := Fin.ext (modSub_add bits ja Sinv hja).symm
  calc gateToPerm (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) (cosetDim w bits) hwt
          (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
            (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))
      = gateToPerm (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) (cosetDim w bits) hb
          (gateToPerm (pass1 w bits TfamK numWin) (cosetDim w bits) ha
            (eGid w bits (1 + 2 * w + bits) (pass1_accfit w bits)
              (xCtrlGid w bits numWin (1 + 2 * w + bits) (1 + 2 * w) ja, ⟨jb, hjb⟩))) :=
        gateToPerm_seq (pass1 w bits TfamK numWin) (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin))
          (cosetDim w bits) ha hb hwt _
    _ = gateToPerm (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) (cosetDim w bits) hb
          (eGid w bits (1 + 2 * w) (pass2_accfit w bits)
            (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb', ⟨ja, hja⟩)) :=
        congrArg (gateToPerm (GateReversible.Gate.reverse (pass2 w bits TfamKinv numWin)) (cosetDim w bits) hb)
          (pass1_output_as_pass2_branch w bits numWin TfamK ja jb hw hbits hja hjb hjb' ha)
    _ = eGid w bits (1 + 2 * w) (pass2_accfit w bits)
          (xCtrlGid w bits numWin (1 + 2 * w) (1 + 2 * w + bits) jb', ⟨modSub bits ja Sinv, _⟩) := by
        rw [hdata]
        exact pass2_reverse_through_eGid w bits numWin TfamKinv jb' (modSub bits ja Sinv)
          hw hbits (Nat.mod_lt _ (by positivity)) hz2
          (gidneyProductAdd_pass2_wellTyped w bits TfamKinv numWin hw hbits)

end FormalRV.Shor.GidneyInPlace.InPlaceBranchAction
