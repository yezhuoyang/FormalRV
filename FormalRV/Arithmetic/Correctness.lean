/-
  FormalRV.BQAlgo.Correctness — REUSABLE correctness primitives for
  Gate-IR-encoded arithmetic circuits.

  ## Status (2026-05-12)

  This module provides the bridge from `Gate` IR (in `Framework.Gate`)
  to classical-basis-state semantics (in `Framework.PadAction`'s
  `f_to_vec` infrastructure), so that any future arithmetic-circuit
  review can state correctness theorems of the form:

  > on classical input `f : Nat → Bool`, running the circuit produces
  > the basis state corresponding to the expected output function.

  Per CLAUDE.md hard rule "build a reusable framework, not one-off
  proofs", lemmas in this file are stated generically over Gate IR
  constructions. They are then applied to specific circuits
  (`gidney_adder_bit_step`, `prefix_and_step`, ...) in their own files.

  **Reusable primitives (this file):**
  - `gate_ccx_acts_on_basis`: Gate.CCX's classical-state action
  - `gate_cx_acts_on_basis`: Gate.CX's classical-state action
  - `gate_x_acts_on_basis`: Gate.X's classical-state action
  - `gate_seq_acts_on_basis`: sequential composition propagation

  **Application sites (other files):**
  - `BQAlgo/RippleCarryAdder.lean`: `gidney_adder_bit_step` correctness
  - `BQAlgo/UnaryLookup.lean`: `prefix_and_step` correctness
  - (future) Gidney measurement-AND with extended Gate IR
-/
import FormalRV.Core.Gate
import FormalRV.Core.PadAction
import FormalRV.Arithmetic.GateToUCom

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## CCX (Toffoli) classical-state action

    Bridges `Gate.CCX a b c`'s `uc_eval`-derived matrix to the
    Toffoli-on-basis-state semantics. Foundational: every Gate-IR
    circuit using CCX as a primitive can reduce its classical-input
    behavior to this lemma + sequential composition. -/

/-- A `Gate.CCX a b c` applied to a classical basis state `f_to_vec
    dim f` XORs the AND of bits `a` and `b` into bit `c`. This is the
    Gate-IR-level statement of the Toffoli's classical action,
    derived from `Framework.PadAction.f_to_vec_CCX_proved` via
    `Gate.toUCom_CCX`. -/
theorem gate_ccx_acts_on_basis (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.CCX a b c)) * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f a && f b))) := by
  rw [Gate.toUCom_CCX]
  exact f_to_vec_CCX_proved dim a b c ha hb hc hab hac hbc f

/-- Symmetric variant: CCX is unchanged by swapping controls. Just a
    notational convenience using `Bool.and_comm`. -/
theorem gate_ccx_acts_on_basis_symm (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.CCX a b c)) * f_to_vec dim f
      = f_to_vec dim (update f c (xor (f c) (f b && f a))) := by
  rw [gate_ccx_acts_on_basis dim a b c ha hb hc hab hac hbc f]
  rw [Bool.and_comm]

/-! ## CX (CNOT) classical-state action -/

/-- A `Gate.CX c t` applied to a classical basis state XORs bit `c`
    into bit `t`. Derived from `Framework.PadAction.f_to_vec_CNOT_proved`. -/
theorem gate_cx_acts_on_basis (dim c t : Nat)
    (hc : c < dim) (ht : t < dim) (hct : c ≠ t) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.CX c t)) * f_to_vec dim f
      = f_to_vec dim (update f t (xor (f t) (f c))) := by
  rw [Gate.toUCom_CX]
  -- `f_to_vec_CNOT_proved` has signature (n i j : Nat) so dim corresponds
  -- to its `n` parameter (the total number of qubits).
  exact f_to_vec_CNOT_proved dim c t f hc ht hct

/-! ## X (bit-flip) classical-state action

    Listed in the status block as a planned primitive; added here as
    a 2-line lift of `f_to_vec_X_uc_eval` via `Gate.toUCom_X`. Useful
    for Iter 55's faithful Gidney bit-step proofs where X gates
    pre-XOR carry bits into next-bit operands. -/

/-- A `Gate.X n` applied to a classical basis state flips bit `n`.
    Derived from `Framework.PadAction.f_to_vec_X_uc_eval`. -/
theorem gate_x_acts_on_basis (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.X n)) * f_to_vec dim f
      = f_to_vec dim (update f n (!f n)) := by
  rw [Gate.toUCom_X]
  exact f_to_vec_X_uc_eval dim n h f

/-! ## CX involution on basis states

    A pair of identical CX gates is the identity on classical basis
    states. Useful for proving that the explicit reverse-cascade in
    `prefix_and_uncompute` undoes the forward cascade. -/

/-- Applying `Gate.CX c t` twice to a classical basis state restores
    the original state. SQIR/SQIR/Equivalences.v line 109 analog
    (CNOT involution) lifted to the Gate IR / basis-action level.
    Direct lift of `f_to_vec_CNOT_CNOT` from `Framework/PadAction.lean`. -/
theorem gate_cx_cx_id_on_basis (dim c t : Nat)
    (hc : c < dim) (ht : t < dim) (hct : c ≠ t) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.seq (Gate.CX c t) (Gate.CX c t)))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [Gate.toUCom_seq, Gate.toUCom_CX]
  exact f_to_vec_CNOT_CNOT dim c t hc ht hct f

/-- Applying `Gate.CCX a b c` twice to a classical basis state restores
    the original state. SQIR analog: CCX is self-inverse (Toffoli is
    an involution). Direct lift of `f_to_vec_CCX_involutive` via
    `Matrix.mul_assoc` (the SQIR form takes nested multiplication;
    our Gate.seq form takes a single composed CCX-CCX product). -/
theorem gate_ccx_ccx_id_on_basis (dim a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.seq (Gate.CCX a b c) (Gate.CCX a b c)))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [Gate.toUCom_seq, Gate.toUCom_CCX]
  -- uc_eval (seq c₁ c₂) = uc_eval c₂ * uc_eval c₁; for matched gates
  -- this is uc_eval CCX * uc_eval CCX. Re-associate to match
  -- f_to_vec_CCX_involutive's nested-mul form.
  show uc_eval (BaseUCom.CCX a b c : BaseUCom dim) *
         uc_eval (BaseUCom.CCX a b c)
       * f_to_vec dim f = f_to_vec dim f
  rw [Matrix.mul_assoc]
  exact f_to_vec_CCX_involutive dim a b c ha hb hc hab hac hbc f

/-- Applying `Gate.X n` twice to a classical basis state restores the
    original state. SQIR/SQIR/Equivalences.v line 68 analog (X_X_id)
    lifted to the Gate IR / basis-action level. Direct lift of
    `f_to_vec_X_X` from `Framework/PadAction.lean`. Completes the
    three-gate involution family (X, CX, CCX). -/
theorem gate_x_x_id_on_basis (dim n : Nat) (h : n < dim) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim (Gate.seq (Gate.X n) (Gate.X n)))
      * f_to_vec dim f
      = f_to_vec dim f := by
  rw [Gate.toUCom_seq, Gate.toUCom_X]
  exact f_to_vec_X_X dim n h f

/-! ## Sequential composition propagation

    The core compositional lemma: if `g₁` takes `f` to `f'` on basis
    states and `g₂` takes `f'` to `f''`, then `Gate.seq g₁ g₂` takes
    `f` to `f''`. Enables inductive correctness proofs over `Gate.seq`
    chains. -/

/-- Sequential composition acts on basis states by composing the per-
    gate basis-state functions. Derived from `uc_eval_seq` (right-to-
    left matrix multiplication on `seq`). -/
theorem gate_seq_acts_on_basis (dim : Nat) (g₁ g₂ : Gate)
    (f g h : Nat → Bool)
    (h₁ : uc_eval (Gate.toUCom dim g₁) * f_to_vec dim f = f_to_vec dim g)
    (h₂ : uc_eval (Gate.toUCom dim g₂) * f_to_vec dim g = f_to_vec dim h) :
    uc_eval (Gate.toUCom dim (Gate.seq g₁ g₂)) * f_to_vec dim f
      = f_to_vec dim h := by
  rw [Gate.toUCom_seq]
  show uc_eval (Gate.toUCom dim g₂) * uc_eval (Gate.toUCom dim g₁)
        * f_to_vec dim f = f_to_vec dim h
  rw [Matrix.mul_assoc, h₁, h₂]

/-! ## Structural Gate → BaseUCom → basis-state adapter

The single reusable bridge from the Gate IR's Boolean-function
semantics (a transformation `Nat → Bool → Nat → Bool`) to the
matrix-level `uc_eval (Gate.toUCom dim g) * f_to_vec dim f` form
required by `MultiplyCircuitProperty` and the modular-multiplier
axioms (`f_modmult_circuit_MMI`).

Without this adapter, every arithmetic-circuit correctness proof must
hand-roll the structural induction (X, CX, CCX, seq) when lifting from
the Boolean update-based per-gate lemmas to the basis-state action.
With this adapter, any Gate IR circuit `g` whose Boolean-function
behaviour `Gate.applyNat g` is known can be promoted directly to the
`uc_eval`/`basis_vector` form `MultiplyCircuitProperty` demands. -/

/-- Boolean-function semantics of a `Gate` IR term as a transformation
on `Nat → Bool` (the function-form parallel of
`Framework.Semantics.apply` on `Fin n → Bool`). Uses the project's
local `Framework.update`, matching `gate_*_acts_on_basis` exactly. -/
def Gate.applyNat : Gate → (Nat → Bool) → (Nat → Bool)
  | Gate.I,         f => f
  | Gate.X q,       f => update f q (!f q)
  | Gate.CX c t,    f => update f t (xor (f t) (f c))
  | Gate.CCX a b c, f => update f c (xor (f c) (f a && f b))
  | Gate.seq g₁ g₂, f => Gate.applyNat g₂ (Gate.applyNat g₁ f)

@[simp] theorem Gate.applyNat_I (f : Nat → Bool) :
    Gate.applyNat Gate.I f = f := rfl

@[simp] theorem Gate.applyNat_X (q : Nat) (f : Nat → Bool) :
    Gate.applyNat (Gate.X q) f = update f q (!f q) := rfl

@[simp] theorem Gate.applyNat_CX (c t : Nat) (f : Nat → Bool) :
    Gate.applyNat (Gate.CX c t) f
      = update f t (xor (f t) (f c)) := rfl

@[simp] theorem Gate.applyNat_CCX (a b c : Nat) (f : Nat → Bool) :
    Gate.applyNat (Gate.CCX a b c) f
      = update f c (xor (f c) (f a && f b)) := rfl

@[simp] theorem Gate.applyNat_seq (g₁ g₂ : Gate) (f : Nat → Bool) :
    Gate.applyNat (Gate.seq g₁ g₂) f
      = Gate.applyNat g₂ (Gate.applyNat g₁ f) := rfl

/-- **The Gate → BaseUCom → basis-state adapter.** For any well-typed
`Gate` IR term `g`, the matrix action of `uc_eval (Gate.toUCom dim g)`
on the classical basis state `f_to_vec dim f` equals the basis state
of `Gate.applyNat g f`. Proved by structural induction on `g`, using
the existing per-gate basis action lemmas plus
`gate_seq_acts_on_basis` for composition.

**Usage path to `f_modmult_circuit_MMI`**: given a future modular
multiplier `g_modmult : Gate` with a Boolean-function correctness
theorem `Gate.applyNat g_modmult (encode_pair x 0) = encode_pair (a*x%N) 0`,
combine with this adapter and `f_to_vec_eq_basis_padEquiv` (in
`Framework/PadAction.lean`) to obtain the
`uc_eval ... * basis_vector ... = basis_vector ...` shape that
`MultiplyCircuitProperty` requires. -/
theorem uc_eval_toUCom_acts_on_basis (dim : Nat) (g : Gate)
    (h_wt : Gate.WellTyped dim g) (f : Nat → Bool) :
    uc_eval (Gate.toUCom dim g) * f_to_vec dim f
      = f_to_vec dim (Gate.applyNat g f) := by
  induction g generalizing f with
  | I =>
      show uc_eval (BaseUCom.ID 0 : BaseUCom dim) * f_to_vec dim f
        = f_to_vec dim f
      rw [uc_eval_ID_eq_one h_wt, Matrix.one_mul]
  | X q =>
      exact gate_x_acts_on_basis dim q h_wt f
  | CX c t =>
      obtain ⟨hc, ht, hct⟩ := h_wt
      exact gate_cx_acts_on_basis dim c t hc ht hct f
  | CCX a b c =>
      obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h_wt
      exact gate_ccx_acts_on_basis dim a b c ha hb hc hab hac hbc f
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h_wt
      exact gate_seq_acts_on_basis dim g₁ g₂
        f (Gate.applyNat g₁ f) (Gate.applyNat g₂ (Gate.applyNat g₁ f))
        (ih₁ hwt₁ f) (ih₂ hwt₂ (Gate.applyNat g₁ f))

/-- **Index-form Gate → BaseUCom → basis_vector adapter** (the
`MultiplyCircuitProperty`-shaped specialisation).  Given:
* a well-typed `Gate` term `g`,
* a Boolean bit-function `f` that encodes some input as the basis
  state at `inputIndex`, and
* the fact that `Gate.applyNat g f` re-encodes the output as the
  basis state at `outputIndex`,

the matrix action of `uc_eval (Gate.toUCom dim g)` on
`basis_vector (2^dim) inputIndex` yields exactly
`basis_vector (2^dim) outputIndex`.  This is precisely the shape of
`MultiplyCircuitProperty`'s `uc_eval c (basis_vector …) =
basis_vector …` clause; downstream, supply
`inputIndex := x * 2^anc`, `outputIndex := (a * x % N) * 2^anc`, and a
Boolean encoding `f` of `x` in the data register with the ancilla
zeroed. -/
theorem toUCom_acts_on_basis_of_applyNat_index
    {dim : Nat} {g : Gate}
    (h_wt : Gate.WellTyped dim g)
    (inputIndex outputIndex : Nat) (f : Nat → Bool)
    (h_input : f_to_vec dim f = basis_vector (2^dim) inputIndex)
    (h_output : f_to_vec dim (Gate.applyNat g f)
                  = basis_vector (2^dim) outputIndex) :
    uc_eval (Gate.toUCom dim g) * basis_vector (2^dim) inputIndex
      = basis_vector (2^dim) outputIndex := by
  rw [← h_input, uc_eval_toUCom_acts_on_basis dim g h_wt f, h_output]

/-- **Out-of-range preservation of `Gate.applyNat`.** For a `Gate`
that is well-typed at `dim` qubits, `Gate.applyNat g f i = f i` for
every position `i ≥ dim`.  In other words, the gate's Boolean
semantics only touches positions `< dim`; any position beyond the
declared dimension is fixed.

Proved by induction on `g`:
* `I`: identity, trivial.
* `X q`, `CX c t`, `CCX a b c`: `update f _ _ i = f i` whenever `i`
  differs from the updated index, which follows from `i ≥ dim` and
  the corresponding bound from `Gate.WellTyped`.
* `seq g₁ g₂`: chain the two inductive hypotheses.

This is the bit-level analogue of "the gate matrix is padded with
identity on the OOB qubits"; used downstream to satisfy the
out-of-range branch of `eq_encodeDataZeroAnc_of_data_anc_oob` for
modular-multiplier circuits. -/
theorem Gate.applyNat_oob
    {dim : Nat} {g : Gate}
    (h_wt : Gate.WellTyped dim g)
    (f : Nat → Bool)
    {i : Nat} (hi : dim ≤ i) :
    Gate.applyNat g f i = f i := by
  induction g generalizing f with
  | I => rfl
  | X q =>
      have hq : q < dim := h_wt
      have h_neq : i ≠ q := by omega
      rw [Gate.applyNat_X]
      exact update_neq f q i (!f q) h_neq
  | CX c t =>
      obtain ⟨_, ht, _⟩ := h_wt
      have h_neq : i ≠ t := by omega
      rw [Gate.applyNat_CX]
      exact update_neq f t i (xor (f t) (f c)) h_neq
  | CCX a b c =>
      obtain ⟨_, _, hc, _, _, _⟩ := h_wt
      have h_neq : i ≠ c := by omega
      rw [Gate.applyNat_CCX]
      exact update_neq f c i (xor (f c) (f a && f b)) h_neq
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h_wt
      show Gate.applyNat g₂ (Gate.applyNat g₁ f) i = f i
      rw [ih₂ hwt₂ (Gate.applyNat g₁ f)]
      exact ih₁ hwt₁ f

end FormalRV.BQAlgo
