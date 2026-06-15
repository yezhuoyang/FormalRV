/-
  FormalRV.Shor.CosetEigenstate.GatePerm — the CLASSICAL reversible Gate IR denotes
  basis permutations, hence acts as a `normSqDist`-isometry.
  ════════════════════════════════════════════════════════════════════════════

  The `Gate` IR (`I / X / CX / CCX / seq`) is ENTIRELY the classical reversible
  fragment — there is NO Hadamard / QFT / phase / measurement constructor.  So every
  `WellTyped` `Gate` denotes a permutation of computational basis states
  (`applyNat g` is injective — `applyNat_injective` — and the basis is finite), and
  the corresponding QState action leaves the Born-L1 distance `normSqDist` INVARIANT.

  This discharges the `U_rev` / swap ISOMETRY hypotheses of
  `InPlaceCoset.inPlaceMul_deviation_compose` for the concrete `mulFwd` / `mulInv` /
  `swapReg` circuits (which are exactly `X/CX/CCX/seq` terms).

  ⚠ SCOPE — CLASSICAL FRAGMENT ONLY.  These lemmas hold because `applyNat`
  permutes the basis.  They DO NOT and MUST NOT be applied to non-classical gates
  (H / QFT / phase / measurement) — those live in a different IR (`BaseUCom` /
  SQIR) and are NOT basis permutations; `normSqDist` (an L1-Born / TV-like distance)
  is generally NOT preserved by them.

  ⚠ DIMENSION.  The Gate IR acts on `Fin (2^dim)` (`dim` = number of qubits/bits).
  The permutation is built on the basis-index type `Fin dim → Bool`, then transported
  to `Fin (2^dim)`.  To connect to `wrapShiftState` (mod `dim`) one specializes the
  coset register to `dim = 2^bits` — the physical register size.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp
import FormalRV.Shor.CosetEigenstate.GateReversible

namespace FormalRV.Shor.CosetEigenstate.GatePerm

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.CosetEigenstate.ApproxOp (permState normSqDist_perm_invariant)
open FormalRV.Shor.CosetEigenstate.GateReversible (applyNat_injective)

/-- **Frame lemma.**  A `WellTyped`-in-`dim` gate only touches qubit indices `< dim`,
    so it leaves every index `p ≥ dim` unchanged.  (Induction on the gate, using that
    `WellTyped` bounds every position `< dim` and `update` fixes other positions.) -/
theorem applyNat_frame : ∀ (g : Gate) (dim : Nat), Gate.WellTyped dim g →
    ∀ (f : Nat → Bool) (p : Nat), dim ≤ p → Gate.applyNat g f p = f p := by
  intro g
  induction g with
  | I => intro dim _ f p _; rfl
  | X q =>
      intro dim hwt f p hp
      simp only [Gate.WellTyped] at hwt
      rw [Gate.applyNat_X]
      exact update_neq f q p (!f q) (by omega)
  | CX c t =>
      intro dim hwt f p hp
      simp only [Gate.WellTyped] at hwt
      rw [Gate.applyNat_CX]
      exact update_neq f t p _ (by omega)
  | CCX a b c =>
      intro dim hwt f p hp
      simp only [Gate.WellTyped] at hwt
      rw [Gate.applyNat_CCX]
      exact update_neq f c p _ (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
      intro dim hwt f p hp
      obtain ⟨h1, h2⟩ := hwt
      rw [Gate.applyNat_seq, ih₂ dim h2 _ p hp, ih₁ dim h1 f p hp]

/-- `Gate.reverse` preserves well-typedness (it keeps every generator and only
    reorders `seq`).  Needed so the uncompute leg `reverse mulInv` is a permutation. -/
theorem reverse_wellTyped : ∀ (g : Gate) (dim : Nat), Gate.WellTyped dim g →
    Gate.WellTyped dim (GateReversible.Gate.reverse g) := by
  intro g
  induction g with
  | I => intro _ h; exact h
  | X q => intro _ h; exact h
  | CX c t => intro _ h; exact h
  | CCX a b c => intro _ h; exact h
  | seq g₁ g₂ ih₁ ih₂ =>
      intro dim h
      obtain ⟨h1, h2⟩ := h
      exact ⟨ih₂ dim h2, ih₁ dim h1⟩

/-- Extend a `dim`-bit Boolean function to `Nat → Bool` by `false` outside `[0,dim)`. -/
def extendBool (dim : Nat) (φ : Fin dim → Bool) : Nat → Bool :=
  fun k => if h : k < dim then φ ⟨k, h⟩ else false

/-- The gate's action on `dim`-bit basis functions (extend, apply, restrict). -/
def applyFin (g : Gate) (dim : Nat) (φ : Fin dim → Bool) : Fin dim → Bool :=
  fun i => Gate.applyNat g (extendBool dim φ) i.val

/-- **`applyFin` is injective.**  From `applyNat_injective` (on `Nat → Bool`) plus the
    frame lemma (both extensions agree as `false` outside `[0,dim)`). -/
theorem applyFin_injective (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g) :
    Function.Injective (applyFin g dim) := by
  intro φ ψ h
  have hext : Gate.applyNat g (extendBool dim φ) = Gate.applyNat g (extendBool dim ψ) := by
    funext p
    by_cases hp : p < dim
    · have hpp := congrFun h ⟨p, hp⟩
      simpa [applyFin] using hpp
    · rw [applyNat_frame g dim hwt _ p (by omega), applyNat_frame g dim hwt _ p (by omega)]
      simp [extendBool, hp]
  have hext2 : extendBool dim φ = extendBool dim ψ := applyNat_injective g dim hwt hext
  funext i
  have hi := congrFun hext2 i.val
  simpa [extendBool, i.isLt] using hi

/-- **The classical gate's basis permutation** on `Fin dim → Bool`: `applyFin g`,
    which is injective hence (finite) bijective. -/
noncomputable def gateClassicalPerm (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g) :
    Equiv.Perm (Fin dim → Bool) :=
  Equiv.ofBijective (applyFin g dim) ((applyFin_injective g dim hwt).bijective_of_finite)

/-- Faithfulness: the permutation IS the gate's basis-function action. -/
@[simp] theorem gateClassicalPerm_apply (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (φ : Fin dim → Bool) : gateClassicalPerm g dim hwt φ = applyFin g dim φ := rfl

/-! ### The funbool ENCODING coordinatization (matches `uc_eval`'s `funbool_to_nat`).

    To agree with the literal SQIR semantics (`uc_eval_toUCom_acts_on_basis`, which
    encodes basis states via `funbool_to_nat`), the `Fin (2^dim)` coordinatization
    MUST be the funbool encoding — NOT an arbitrary card-bijection.  The Nat *value*
    `funbool_to_nat dim φ` is exactly the basis-state index used everywhere (and the
    `cosetState` indices `k+j·N` are likewise Nat values), so the endian convention
    is internal to `funbool_to_nat` and the value-based indexing is consistent. -/

/-- Two bit-functions with equal `funbool_to_nat dim` value agree on `[0,dim)`.
    (Uniqueness of binary digits, by induction: `2a+b = 2c+d` with `b,d < 2`.) -/
theorem funbool_to_nat_agree : ∀ (dim : Nat) (f g : Nat → Bool),
    funbool_to_nat dim f = funbool_to_nat dim g → ∀ k, k < dim → f k = g k := by
  intro dim
  induction dim with
  | zero => intro f g _ k hk; omega
  | succ n ih =>
      intro f g h k hk
      rw [funbool_to_nat_succ, funbool_to_nat_succ] at h
      have h1 : (if f n then (1 : Nat) else 0) < 2 := by split <;> omega
      have h2 : (if g n then (1 : Nat) else 0) < 2 := by split <;> omega
      have hAn : funbool_to_nat n f = funbool_to_nat n g := by omega
      have hbit : f n = g n := by
        have hb : (if f n then (1 : Nat) else 0) = (if g n then (1 : Nat) else 0) := by omega
        by_cases hfn : f n <;> by_cases hgn : g n <;> simp_all
      rcases Nat.lt_or_ge k n with hkn | hkn
      · exact ih f g hAn k hkn
      · rw [show k = n by omega]; exact hbit

/-- The funbool encoding of a `dim`-bit function as an index in `Fin (2^dim)`. -/
def funboolNat (dim : Nat) (φ : Fin dim → Bool) : Fin (2 ^ dim) :=
  ⟨funbool_to_nat dim (extendBool dim φ), funbool_to_nat_lt dim _⟩

theorem funboolNat_injective (dim : Nat) : Function.Injective (funboolNat dim) := by
  intro φ ψ h
  have hval : funbool_to_nat dim (extendBool dim φ) = funbool_to_nat dim (extendBool dim ψ) :=
    congrArg Fin.val h
  funext i
  have hi := funbool_to_nat_agree dim _ _ hval i.val i.isLt
  simpa [extendBool, i.isLt] using hi

/-- **The funbool coordinatization** `(Fin dim → Bool) ≃ Fin (2^dim)`: `φ ↦
    funbool_to_nat dim φ` — the SAME encoding `uc_eval` uses on basis states. -/
noncomputable def funboolEquiv (dim : Nat) : (Fin dim → Bool) ≃ Fin (2 ^ dim) :=
  Equiv.ofBijective (funboolNat dim)
    ((Fintype.bijective_iff_injective_and_card (funboolNat dim)).mpr
      ⟨funboolNat_injective dim, by
        simp [Fintype.card_bool, Fintype.card_fin]⟩)

@[simp] theorem funboolEquiv_val (dim : Nat) (φ : Fin dim → Bool) :
    ((funboolEquiv dim) φ : Nat) = funbool_to_nat dim (extendBool dim φ) := rfl

/-- **The classical gate's basis permutation on the register `Fin (2^dim)`**, in the
    funbool coordinatization (so it matches the SQIR semantics — see `UCEvalBridge`). -/
noncomputable def gateToPerm (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g) :
    Equiv.Perm (Fin (2 ^ dim)) :=
  (funboolEquiv dim).permCongr (gateClassicalPerm g dim hwt)

/-- **GATE ACTION IS A `normSqDist`-ISOMETRY (classical fragment).**  The QState
    action of a `WellTyped` classical `Gate` — a basis permutation `permState
    (gateToPerm g)` — leaves the Born-L1 distance INVARIANT.  This discharges the
    `U_rev` / swap isometry hypotheses of `inPlaceMul_deviation_compose` for the
    concrete `X/CX/CCX/seq` circuits.  (Immediate from `normSqDist_perm_invariant`.) -/
theorem gate_normSqDist_perm (g : Gate) (dim : Nat) (hwt : Gate.WellTyped dim g)
    (s₁ s₂ : QState (2 ^ dim)) :
    normSqDist (permState (gateToPerm g dim hwt) s₁) (permState (gateToPerm g dim hwt) s₂)
      = normSqDist s₁ s₂ :=
  normSqDist_perm_invariant (gateToPerm g dim hwt) s₁ s₂

end FormalRV.Shor.CosetEigenstate.GatePerm
