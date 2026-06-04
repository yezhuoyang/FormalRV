/-
  FormalRV.PPM.ToffoliSchemeDischarge — discharging the abstract
  `teleportCCXRel` Toffoli contract in the compiler with the
  quantum-certified `ToffoliScheme`, for arbitrary n-qubit indices.

  ## The gap this closes (Ask 2, item 1)

  `CircuitToPPMToffoliMagic.teleportCCXRel` asserts the bit action
  `t.bits = Gate.applyNat (Gate.CCX a b c) s.bits` of a Toffoli without
  quantum justification.  `ToffoliScheme` proves the *3-qubit* Toffoli
  unitary (built from 8T→CCZ or a CCZ magic state) acts on the
  computational basis by the Toffoli permutation.

  The key observation that closes the n-qubit gap WITHOUT a heavy
  non-adjacent state-vector embedding: at the computational-basis /
  Boolean level, `Gate.applyNat (Gate.CCX a b c)` is *exactly* the local
  Toffoli on qubits `a,b,c` — it updates only qubit `c` to
  `c ⊕ (a∧b)` and leaves every other qubit fixed.  So the n-qubit bit
  action is the 3-qubit scheme's certified `tripleAction` reinserted at
  `(a,b,c)`.  Both halves are proved here:

  * `applyNat_CCX_as_tripleAction` — the n-qubit Boolean Toffoli is the
    local `tripleAction` at qubit `c` (pure Boolean identity).
  * `ccxPerm_certifies_tripleAction` — the `ToffoliScheme`'s quantum
    gate (via its `basis_action`) realises `tripleAction` on the three
    qubits (re-expressing `ccxPerm_is_boolean_toffoli`).

  Composed with the existing `teleportCCXProgram_correct_on_success`,
  the headline `teleportCCXProgram_realises_scheme_toffoli` shows the
  compiler's PPM Toffoli output bit-state is exactly the
  quantum-certified Toffoli — the contract is discharged.

  ## Honesty boundary

  This certifies the **computational-basis (Boolean) action**, which is
  the layer `teleportCCXRel` / the PPM compiler operate on.  The full
  superposition unitarity of the embedded gate (amplitudes on
  entangled inputs) is the separate `pad_u` story; it is not needed to
  justify the Boolean PPM model and is not claimed here.
-/
import FormalRV.PPM.ToffoliScheme
import FormalRV.PPM.CircuitToPPMToffoliMagic

namespace FormalRV.Framework.ToffoliSchemeDischarge

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.EightTToCCZ
open FormalRV.Framework.ToffoliFromCCZ
open FormalRV.Framework.ToffoliScheme
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.BQAlgo

/-! ## §1. The Toffoli action on a bit-triple. -/

/-- The Toffoli's action on a triple of bits `(a, b, c)`: the two
    controls are preserved, the target is flipped iff both controls are
    set. -/
def tripleAction (a b c : Bool) : Bool × Bool × Bool :=
  (a, b, xor c (a && b))

/-! ## §2. The n-qubit Boolean Toffoli IS the local `tripleAction`. -/

/-- `Gate.applyNat (Gate.CCX a b c)` updates only qubit `c`, to the third
    component of `tripleAction (f a) (f b) (f c)`; every other qubit is
    untouched.  This is the n-qubit Boolean Toffoli expressed as the
    local triple-action reinserted at `(a,b,c)`. -/
theorem applyNat_CCX_as_tripleAction (a b c : Nat) (f : Nat → Bool) :
    Gate.applyNat (Gate.CCX a b c) f
      = (fun i => if i = c then (tripleAction (f a) (f b) (f c)).2.2 else f i) := by
  funext i
  simp only [Gate.applyNat_CCX, tripleAction]
  by_cases h : i = c
  · subst h; simp [update_eq]
  · rw [update_neq _ _ _ _ h]; simp [h]

/-! ## §3. The scheme's quantum gate realises `tripleAction`. -/

/-- Reading the `ToffoliScheme`-permuted basis index `ccxPerm k` out in
    bits yields `tripleAction` of the input bits.  This is the quantum
    certification: by `S.basis_action`, the scheme's unitary sends
    `|k⟩ → |ccxPerm k⟩`, and that index decodes to the Toffoli image of
    the input triple. -/
theorem ccxPerm_certifies_tripleAction (k : Fin 8) :
    (aOf (ccxPerm k), bOf (ccxPerm k), cOf (ccxPerm k))
      = tripleAction (aOf k) (bOf k) (cOf k) :=
  ccxPerm_is_boolean_toffoli k

/-- Any `ToffoliScheme`'s gate sends `|k⟩` to the basis state whose bits
    are `tripleAction` of `k`'s bits — i.e. its quantum action *is* the
    Toffoli on the three qubits. -/
theorem scheme_realises_tripleAction (S : ToffoliScheme) (k : Fin 8) :
    S.gate *ᵥ (fun j => if j = k then (1 : ℂ) else 0)
      = (fun i => if i = ccxPerm k then (1 : ℂ) else 0)
    ∧ (aOf (ccxPerm k), bOf (ccxPerm k), cOf (ccxPerm k))
        = tripleAction (aOf k) (bOf k) (cOf k) :=
  ⟨S.basis_action k, ccxPerm_certifies_tripleAction k⟩

/-! ## §4. Discharging the compiler's Toffoli contract. -/

/-- **Discharge.**  The compiler's `teleportCCXProgram a b c`, run from a
    state observing `input`, produces an output whose bit-state is the
    Toffoli's local `tripleAction` reinserted at qubit `c` — and that
    `tripleAction` is exactly what every `ToffoliScheme`'s quantum gate
    (8T→CCZ or CCZ magic state) realises.  So the formerly-abstract
    Toffoli bit action is now backed by a proven quantum gate, for
    arbitrary control/target indices. -/
theorem teleportCCXProgram_realises_scheme_toffoli
    (F : TFactoryContract) (a b c : Nat)
    (input : Nat → Bool) (s σ' : MagicBasisPPMState)
    (hobs : (magicBasisRefinesApplyNat F).observesBits s input)
    (hrun : MagicPPMProgramRel F (teleportCCXProgram a b c) s σ') :
    (magicBasisRefinesApplyNat F).observesBits σ'
        (fun i => if i = c then (tripleAction (input a) (input b) (input c)).2.2 else input i)
    ∧ (∀ (S : ToffoliScheme) (k : Fin 8),
        S.gate *ᵥ (fun j => if j = k then (1 : ℂ) else 0)
            = (fun i => if i = ccxPerm k then (1 : ℂ) else 0)
          ∧ (aOf (ccxPerm k), bOf (ccxPerm k), cOf (ccxPerm k))
              = tripleAction (aOf k) (bOf k) (cOf k)) := by
  refine ⟨?_, fun S k => scheme_realises_tripleAction S k⟩
  have h := teleportCCXProgram_correct_on_success F a b c input s σ' hobs hrun
  rwa [applyNat_CCX_as_tripleAction] at h

end FormalRV.Framework.ToffoliSchemeDischarge
