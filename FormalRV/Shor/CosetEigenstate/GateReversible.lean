/-
  FormalRV.Shor.CosetEigenstate.GateReversible — reversibility of the gate IR.
  ════════════════════════════════════════════════════════════════════════════

  Every gate in the `Gate` IR (`I/X/CX/CCX/seq`) is built from reversible
  generators, so its Boolean action `Gate.applyNat g` is a BIJECTION on states.
  The three generators are self-inverse INVOLUTIONS (under well-typedness, which
  supplies the control≠target distinctness `CX`/`CCX` need), and `seq` reverses by
  composition.  This gives:

    * `Gate.reverse` — the inverse circuit (reverse the sequence; generators fixed).
    * `applyNat_reverse_cancel` — `applyNat (reverse g) ∘ applyNat g = id`.
    * `applyNat_injective` — `applyNat g` is injective.

  This is the infrastructure the coset-eigenstate work needs: the windowed coset
  multiplier `runwayWindowedMul`, being a real reversible circuit, permutes basis
  states — so its restriction to a coset's encodings is injective, the foundation
  for the orbit-shift `C_j → C_{j+1}`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Correctness

namespace FormalRV.Shor.CosetEigenstate.GateReversible

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-- The inverse circuit: reverse the sequence; each generator is its own inverse. -/
def Gate.reverse : Gate → Gate
  | Gate.I => Gate.I
  | Gate.X q => Gate.X q
  | Gate.CX c t => Gate.CX c t
  | Gate.CCX a b c => Gate.CCX a b c
  | Gate.seq g₁ g₂ => Gate.seq (Gate.reverse g₂) (Gate.reverse g₁)

/-! ## §1. The three generators are involutions. -/

/-- `X` is self-inverse: flipping qubit `q` twice restores the state. -/
theorem applyNat_X_involution (q : Nat) (f : Nat → Bool) :
    Gate.applyNat (Gate.X q) (Gate.applyNat (Gate.X q) f) = f := by
  show update (update f q (!(f q))) q (!((update f q (!(f q))) q)) = f
  rw [update_eq, Bool.not_not, update_idem, update_self]

/-- `CX` is self-inverse (under `c ≠ t`): the control is preserved, so the target
    is XOR-ed with the same control bit twice. -/
theorem applyNat_CX_involution (c t : Nat) (h : c ≠ t) (f : Nat → Bool) :
    Gate.applyNat (Gate.CX c t) (Gate.applyNat (Gate.CX c t) f) = f := by
  show update (update f t (xor (f t) (f c))) t
      (xor ((update f t (xor (f t) (f c))) t) ((update f t (xor (f t) (f c))) c)) = f
  rw [update_eq, update_neq f t c (xor (f t) (f c)) h,
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false, update_idem, update_self]

/-- `CCX` is self-inverse (under `a ≠ c`, `b ≠ c`): both controls are preserved, so
    the target is XOR-ed with `a && b` twice. -/
theorem applyNat_CCX_involution (a b c : Nat) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Nat → Bool) :
    Gate.applyNat (Gate.CCX a b c) (Gate.applyNat (Gate.CCX a b c) f) = f := by
  show update (update f c (xor (f c) (f a && f b))) c
      (xor ((update f c (xor (f c) (f a && f b))) c)
        ((update f c (xor (f c) (f a && f b))) a && (update f c (xor (f c) (f a && f b))) b)) = f
  rw [update_eq, update_neq f c a (xor (f c) (f a && f b)) hac,
      update_neq f c b (xor (f c) (f a && f b)) hbc,
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false, update_idem, update_self]

/-! ## §2. `Gate.reverse` is a left inverse of `Gate.applyNat`. -/

/-- **`applyNat (reverse g) ∘ applyNat g = id`** for well-typed `g`.  Generators by
    their involutions (well-typedness supplies the distinctness); `seq` by reversed
    composition. -/
theorem applyNat_reverse_cancel : ∀ (g : Gate) (dim : Nat), Gate.WellTyped dim g →
    ∀ (f : Nat → Bool), Gate.applyNat (Gate.reverse g) (Gate.applyNat g f) = f := by
  intro g
  induction g with
  | I => intro dim _ f; rfl
  | X q => intro dim _ f; exact applyNat_X_involution q f
  | CX c t => intro dim hwt f; exact applyNat_CX_involution c t hwt.2.2 f
  | CCX a b c =>
      intro dim hwt f
      exact applyNat_CCX_involution a b c hwt.2.2.2.2.1 hwt.2.2.2.2.2 f
  | seq g₁ g₂ ih₁ ih₂ =>
      intro dim hwt f
      show Gate.applyNat (Gate.reverse g₁)
        (Gate.applyNat (Gate.reverse g₂) (Gate.applyNat g₂ (Gate.applyNat g₁ f))) = f
      rw [ih₂ dim hwt.2 (Gate.applyNat g₁ f), ih₁ dim hwt.1 f]

/-! ## §3. `Gate.applyNat g` is injective (a permutation of states). -/

/-- **`applyNat g` is injective** for well-typed `g` — the reversible circuit
    permutes states, so distinct inputs give distinct outputs. -/
theorem applyNat_injective (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g) :
    Function.Injective (Gate.applyNat g) := by
  intro f₁ f₂ h
  have hcancel := applyNat_reverse_cancel g dim hwt
  calc f₁ = Gate.applyNat (Gate.reverse g) (Gate.applyNat g f₁) := (hcancel f₁).symm
    _ = Gate.applyNat (Gate.reverse g) (Gate.applyNat g f₂) := by rw [h]
    _ = f₂ := hcancel f₂

end FormalRV.Shor.CosetEigenstate.GateReversible
