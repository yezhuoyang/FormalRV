/-
  FormalRV.Framework.Semantics — RCIR-level (bit-vector) semantics for
  the `Gate` IR.

  Mirrors SQIR's `bcexec : bccom -> nat -> bv -> bv` (RCIR.v). At this
  semantic level we treat states as classical bit-vectors and gates as
  reversible functions on them — sufficient for proving arithmetic
  subroutines correct (adders, modular multipliers, lookups), which is
  what BQ-Algo needs first.

  The full quantum semantic (gate-as-unitary, state-as-complex-vector)
  is deferred to `Framework/QuantumSemantics.lean` (not yet created) and
  will only be needed once BQ-Algo reasons about QPE-level correctness.

  Note on equality: bare `apply g s = f s` for `s : Fin n → Bool` requires
  `funext` since function equality isn't `decide`-able in Lean core. We
  state correctness pointwise (`∀ i, apply g s i = f s i`) which `decide`
  can dispatch via `Fin n` being a Fintype.
-/

import FormalRV.Core.Gate

namespace FormalRV.Framework

/-! ## Classical (bit-vector) state -/

/-- An n-qubit classical state: a function from qubit index to its
    Boolean value. -/
abbrev State (n : Nat) := Fin n → Bool

namespace State

/-- Read bit `i` from state `s`; out-of-bounds reads return `false`
    (matching SQIR's convention). -/
def getBit (s : State n) (i : Nat) : Bool :=
  if h : i < n then s ⟨i, h⟩ else false

/-- Flip bit `i` in state `s`; out-of-bounds writes are no-ops. -/
def flipBit (s : State n) (i : Nat) : State n :=
  fun j => if j.val = i then !s j else s j

/-- Smoke checks. -/
example : getBit (n := 3) (fun _ => false) 1 = false := by decide
example : getBit (n := 3) (fun _ => true)  1 = true  := by decide
example : getBit (n := 3) (fun _ => true)  5 = false := by decide  -- out of bounds

end State

namespace Gate

/-! ## RCIR semantics: applying a gate to a bit-vector state -/

/-- Apply a `Gate` to a classical state, deterministically.
    All gates here are classical-reversible, so this fully captures
    their action (no superposition needed). -/
def apply (g : Gate) (s : State n) : State n :=
  match g with
  | I            => s
  | X q          => State.flipBit s q
  | CX c t       =>
      if State.getBit s c then State.flipBit s t else s
  | CCX a b t    =>
      if State.getBit s a && State.getBit s b then State.flipBit s t else s
  | seq g₁ g₂    => apply g₂ (apply g₁ s)

/-! ## Smoke checks: gates do what we expect on small concrete states -/

/-- Concrete 3-qubit state with bits `b₀ b₁ b₂`. -/
def mkState3 (b₀ b₁ b₂ : Bool) : State 3 :=
  fun i => match i with
    | ⟨0, _⟩ => b₀
    | ⟨1, _⟩ => b₁
    | ⟨2, _⟩ => b₂

/-- X on qubit 1 flips bit 1, leaves others alone. -/
example : ∀ i, apply (X 1) (mkState3 false true false) i
              = mkState3 false false false i := by
  decide

/-- CX (control 0, target 1) with control set ⇒ target flips. -/
example : ∀ i, apply (CX 0 1) (mkState3 true false false) i
              = mkState3 true true false i := by
  decide

/-- CX with control unset ⇒ target unchanged. -/
example : ∀ i, apply (CX 0 1) (mkState3 false false false) i
              = mkState3 false false false i := by
  decide

/-- CCX with both controls set ⇒ target flips. -/
example : ∀ i, apply (CCX 0 1 2) (mkState3 true true false) i
              = mkState3 true true true i := by
  decide

/-- CCX with one control unset ⇒ target unchanged. -/
example : ∀ i, apply (CCX 0 1 2) (mkState3 true false false) i
              = mkState3 true false false i := by
  decide

/-! ## Correctness predicate: a circuit `g` *implements* a function `f`

    Stated pointwise (∀ i) for `decide`-friendliness. Equivalent to
    full function equality modulo `funext`. -/

/-- `g` implements `f` (as bit-vector functions) iff for every input state
    and every bit index, `apply g s` and `f s` agree at that bit. -/
def implements (g : Gate) (f : State n → State n) : Prop :=
  ∀ (s : State n) (i : Fin n), apply g s i = f s i

/-- The identity gate implements the identity function. -/
example : implements (n := 3) I id := by
  intro s i; rfl

end Gate
end FormalRV.Framework
