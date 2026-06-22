/-
  FormalRV.Framework.PPMOperational — operational
  semantics of Pauli-Product Measurement on stabilizer
  states via the Gottesman update algorithm.

  ## Stabilizer states

  An n-qubit stabilizer state is specified (up to global
  phase) by a list of n commuting `PauliString` generators
  whose group does not contain `-I`.  The state itself is
  the unique simultaneous +1 eigenvector of all generators.

  Examples:
    * |+⟩  ↔ stabilizer { +X }       (1 qubit, 1 generator)
    * |0⟩  ↔ stabilizer { +Z }
    * |Bell⟩ ↔ stabilizer { +XX, +ZZ } (2 qubits, 2 generators)
    * |H⟩  ↔ stabilizer { +XZ, +ZX } (the H-magic state)

  ## Gottesman PPM update

  When we measure the Pauli string `P` on a stabilizer state
  with generators `g_1, …, g_n`:

  **Case A** — `P` commutes with every `g_i`.  Then `±P` is
  already in the stabilizer group; the measurement outcome
  is deterministic.  The post-measurement state has the same
  stabilizer.

  **Case B** — there is some `g_i` with `{P, g_i} = 0`.
  Choose the first such `g_i`.  For every OTHER generator
  `g_j` (j ≠ i) that also anticommutes with `P`, replace
  `g_j` with `g_j · g_i` (which now commutes with `P`).
  Then replace `g_i` itself with `P` (for +1 outcome) or
  `-P` (for -1 outcome).

  This is the standard Gottesman algorithm, decidable in
  pure Bool / Nat / List.

  ## Post-condition theorems

  After `apply_PPM_pos`:
    1. `P` (with phase +) is in the new stabilizer.
    2. All generators in the new state pairwise commute.

  After `apply_PPM_neg`:
    1. `-P` is in the new stabilizer.
    2. All generators pairwise commute.

  Theorems closed on concrete instances by `decide`.

  No Mathlib.  Pure Bool / Nat / List.  Decidable.
-/

import FormalRV.PPM.Syntax.PauliSemantics

namespace FormalRV.Framework.PPMOp

open FormalRV.Framework.PauliSem

/-! ## Stabilizer state representation -/

/-- A stabilizer state on `n` qubits, represented by an
    ordered list of `PauliString` generators (each of
    length `n`).  Length and commutation conditions are
    checked separately via `valid`. -/
abbrev StabilizerState := List PauliString

namespace StabilizerState

/-- All generators have the same length `n`. -/
def valid_length (s : StabilizerState) (n : Nat) : Bool :=
  s.all (fun g => decide (g.ops.length = n))

/-- All generators pairwise commute. -/
def valid_commuting (s : StabilizerState) : Bool :=
  s.all (fun g1 => s.all (fun g2 => g1.commutes g2))

/-- A `StabilizerState` is structurally well-formed on `n`
    qubits iff every generator has length `n` AND all
    generators pairwise commute. -/
def valid (s : StabilizerState) (n : Nat) : Bool :=
  valid_length s n && valid_commuting s

end StabilizerState

/-! ## Gottesman PPM update -/

/-- Helper: find the first index of a generator that
    anticommutes with `P`, or `none` if all commute. -/
def find_anticommuting
    (s : StabilizerState) (P : PauliString) : Option Nat :=
  s.findIdx? (fun g => ! g.commutes P)

/-- The Gottesman update for the +1-outcome branch.

    * If no generator anticommutes with `P`, the state's
      stabilizer is unchanged (the measurement was
      deterministic — `+P` was already in the stabilizer
      group, or the implementer's outcome assignment is
      definitionally consistent).
    * Otherwise, replace the first anticommuting generator
      with `P`, and for every OTHER anticommuting generator
      multiply it by the chosen one (so it commutes with `P`). -/
def apply_PPM_pos
    (s : StabilizerState) (P : PauliString) : StabilizerState :=
  match find_anticommuting s P with
  | none => s
  | some i_anti =>
      match s[i_anti]? with
      | none => s   -- impossible, but keep total
      | some g_anti =>
          (s.zipIdx).map (fun (g, j) =>
            if decide (j = i_anti) then P
            else if g.commutes P then g
            else g.mul g_anti)

/-- The Gottesman update for the -1-outcome branch.
    Identical to `apply_PPM_pos` except the inserted
    generator is `-P` rather than `P`. -/
def apply_PPM_neg
    (s : StabilizerState) (P : PauliString) : StabilizerState :=
  match find_anticommuting s P with
  | none => s
  | some i_anti =>
      match s[i_anti]? with
      | none => s
      | some g_anti =>
          (s.zipIdx).map (fun (g, j) =>
            if decide (j = i_anti) then P.neg
            else if g.commutes P then g
            else g.mul g_anti)

/-! ## Concrete examples: single-qubit PPM -/

/-- |+⟩ state stabilizer: { +X }. -/
def plus_state : StabilizerState := [⟨.plus, [.X]⟩]

/-- |0⟩ state stabilizer: { +Z }. -/
def zero_state : StabilizerState := [⟨.plus, [.Z]⟩]

/-- |1⟩ state stabilizer: { -Z }. -/
def one_state  : StabilizerState := [⟨.minus, [.Z]⟩]

/-- The `Z` measurement on `|+⟩`, +1 outcome, gives `|0⟩`. -/
theorem PPM_Z_on_plus_pos :
    apply_PPM_pos plus_state ⟨.plus, [.Z]⟩
    = [⟨.plus, [.Z]⟩] := by decide

/-- The `Z` measurement on `|+⟩`, -1 outcome, gives `|1⟩`. -/
theorem PPM_Z_on_plus_neg :
    apply_PPM_neg plus_state ⟨.plus, [.Z]⟩
    = [⟨.minus, [.Z]⟩] := by decide

/-- Measuring Z on |0⟩ is deterministic: the +1 branch
    preserves the stabilizer (state unchanged). -/
theorem PPM_Z_on_zero_pos :
    apply_PPM_pos zero_state ⟨.plus, [.Z]⟩ = zero_state := by decide

/-! ## Concrete examples: 2-qubit Bell state and PPM -/

/-- |Bell⟩ stabilizer: { +XX, +ZZ }. -/
def bell_state : StabilizerState :=
  [⟨.plus, [.X, .X]⟩, ⟨.plus, [.Z, .Z]⟩]

theorem bell_state_valid :
    StabilizerState.valid bell_state 2 = true := by decide

/-- Measuring `Z₁` (= Z⊗I) on |Bell⟩ — anticommutes with the
    XX generator, commutes with ZZ.  +1 outcome: replace
    XX with Z⊗I (the new constraint). -/
theorem PPM_Z1_on_bell_pos :
    apply_PPM_pos bell_state ⟨.plus, [.Z, .I]⟩
    = [⟨.plus, [.Z, .I]⟩, ⟨.plus, [.Z, .Z]⟩] := by decide

/-- After the above PPM, the new stabilizer also commutes
    pairwise — preserved invariant. -/
theorem PPM_Z1_on_bell_pos_valid :
    StabilizerState.valid
      (apply_PPM_pos bell_state ⟨.plus, [.Z, .I]⟩) 2 = true := by decide

/-! ## Headline invariant: PPM preserves commutativity

    For every concrete `(state, P)` test below, applying
    PPM preserves the "all pairwise commute" invariant.
    The general theorem (parametric in s and P) would
    require induction on s; for the corpus we verify
    on each concrete instance. -/

theorem PPM_preserves_validity_plus_Z :
    StabilizerState.valid
      (apply_PPM_pos plus_state ⟨.plus, [.Z]⟩) 1 = true := by decide

theorem PPM_preserves_validity_plus_X :
    StabilizerState.valid
      (apply_PPM_pos plus_state ⟨.plus, [.X]⟩) 1 = true := by decide

theorem PPM_preserves_validity_bell_Z1 :
    StabilizerState.valid
      (apply_PPM_pos bell_state ⟨.plus, [.Z, .I]⟩) 2 = true := by decide

theorem PPM_preserves_validity_bell_X2 :
    StabilizerState.valid
      (apply_PPM_pos bell_state ⟨.plus, [.I, .X]⟩) 2 = true := by decide

end FormalRV.Framework.PPMOp
