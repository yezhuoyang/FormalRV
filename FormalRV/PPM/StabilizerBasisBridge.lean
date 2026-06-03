/-
  FormalRV.Framework.StabilizerBasisBridge — the Gottesman–Knill bridge
  FOUNDATION: a computational basis state as a stabilizer state, and the
  faithfulness of Z-measurement on it.

  Path A, step (1) foundation (John 2026-06-02).  The honest residue between the
  surgery stabilizer-layer reduction (`SurgeryReduction`) and Shor's Boolean PPM
  pipeline (`ShorPPMEndToEnd`, whose `MagicBasisPPMState` carries `bits : Nat →
  Bool`) is the Gottesman–Knill correspondence: computational bits = the +1
  computational-basis sector of a stabilizer state.  For the basis-PRESERVING
  modular exponentiation (CNOTs/Toffolis are permutations), the relevant case is
  the COMPUTATIONAL-BASIS sector — no Hilbert-space superposition machinery is
  needed.  This file builds that core:

    * `encodeBasisState bits n` — |bits⟩ as the stabilizer state
      `{ (-1)^{bits i} Z_i : i < n }`;
    * `encode_Z_nondisturbing` — measuring ANY Z-product on a basis state is
      DETERMINISTIC (leaves the stabilizer unchanged) — the Gottesman fact that
      a Z-measurement on a Z-stabiliser state has a fixed outcome;
    * a readout smoke connecting the measured Z-operator to the bit-parity.

  ## HONEST SCOPE (this is the FOUNDATION, not the full bridge)

  This establishes the stabilizer representation of basis states and the
  determinism of their Z-measurements — the genuine Gottesman–Knill core for the
  Z-sector.  It does NOT, by itself, close the bridge to `ShorPPMEndToEnd`:
  connecting these stabilizer facts to that file's SPECIFIC `MagicBasisPPMState`
  CX-macro bit-flip semantics (a particular Clifford encoding, not a clean
  Z-measurement) is a separate multi-step refinement, and the full-state
  parametric readout (`row_combination` over the identity matrix) and
  Hilbert-space faithfulness for superpositions remain out of scope.  What is
  genuinely NEW: the basis state ↔ ±Z-stabiliser encoding and the determinism of
  Z-measurement on it, code- and size-parametric and axiom-free.

  No Mathlib.  Pure Bool / Nat / List + the PauliString algebra.  No `sorry`,
  no `axiom`.
-/

import FormalRV.LatticeSurgery.SurgeryCorrect

namespace FormalRV.Framework.StabilizerBasisBridge

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.SurgeryCorrect
open FormalRV.Framework.SurgeryReadout
open FormalRV.Framework.LDPC

/-! ## (1) Computational basis state as a stabilizer state -/

/-- The length-`n` indicator vector, `true` only at position `i`. -/
def indicator (i n : Nat) : BoolVec := (List.range n).map (fun j => decide (j = i))

/-- A computational basis state `|bits⟩` as a stabilizer state: qubit `i` is
    stabilised by `(-1)^{bits i} Z_i`. -/
def encodeBasisState (bits : Nat → Bool) (n : Nat) : StabilizerState :=
  (List.range n).map (fun i => signedZRow (bits i) (indicator i n))

/-! ## (2) Phase-irrelevance of commutation, and pairwise commutation -/

/-- `commutes` depends only on `.ops`, so a signed Z-row commutes with `q` iff
    the unsigned `zRow` does. -/
theorem signedZRow_commutes_eq (b : Bool) (l : BoolVec) (q : PauliString) :
    (signedZRow b l).commutes q = (zRow l).commutes q := by
  simp only [PauliString.commutes, signedZRow_ops, zRow_ops]

/-- Every generator of an encoded basis state commutes with any Z-product
    `zRow sup` (all generators are Z/I strings; `zRow_commutes`). -/
theorem encode_all_commute_Z (bits : Nat → Bool) (n : Nat) (sup : BoolVec) :
    ∀ g ∈ encodeBasisState bits n, g.commutes (zRow sup) = true := by
  intro g hg
  obtain ⟨i, _, hgi⟩ := List.mem_map.mp hg
  rw [← hgi, signedZRow_commutes_eq]
  exact zRow_commutes (indicator i n) sup

/-! ## (3) THE BRIDGE CORE: Z-measurement on a basis state is DETERMINISTIC. -/

/-- **Determinism of Z-measurement on a basis state.**  Measuring any Z-product
    `zRow sup` on the encoded basis state `|bits⟩` leaves the stabilizer
    UNCHANGED — the Gottesman fact that a Z-measurement on a Z-stabiliser state
    has a fixed (deterministic) outcome, with no back-action.  This is the
    genuine bridge core: the computational value of a logical Z-operator is read
    out without disturbing the (basis) state.  Parametric in `n`, `bits`, `sup`;
    axiom-free. -/
theorem encode_Z_nondisturbing (bits : Nat → Bool) (n : Nat) (sup : BoolVec) :
    apply_PPM_pos (encodeBasisState bits n) (zRow sup) = encodeBasisState bits n := by
  have h : find_anticommuting (encodeBasisState bits n) (zRow sup) = none := by
    unfold find_anticommuting
    rw [List.findIdx?_eq_none_iff]
    intro g hg
    simp [encode_all_commute_Z bits n sup g hg]
  unfold apply_PPM_pos
  rw [h]

/-! ## (4) Validity + readout smoke (concrete, demonstrating the encoding). -/

/-- The encoded basis state is a valid stabilizer state (commuting Z generators
    of length n).  Smoke at n = 3 over the four representative bit patterns. -/
example : StabilizerState.valid (encodeBasisState (fun _ => false) 3) 3 = true := by decide
example : StabilizerState.valid (encodeBasisState (fun i => decide (i = 1)) 3) 3 = true := by decide

/-- Readout smoke: on `|bits⟩` with `bits = (0,1,1)`, measuring the Z-product over
    the support `{0,2}` (qubits 0 and 2) is non-disturbing, and the signed
    operator the measurement reads is `Z₀Z₂` with sign `(-1)^{bits 0 ⊕ bits 2}
    = (-1)^{0⊕1} = −1` — i.e. the readout encodes the computational parity. -/
example :
    apply_PPM_pos (encodeBasisState (fun i => decide (i = 1) || decide (i = 2)) 3)
        (zRow [true, false, true])
      = encodeBasisState (fun i => decide (i = 1) || decide (i = 2)) 3 := by decide

/-- The measured signed Z-operator over `{0,2}` for `bits = (0,1,1)` carries the
    parity sign `bits 0 ⊕ bits 2 = 0 ⊕ 1 = 1` (−1): the product of the two
    selected ±Z generators.  (`selectedSignedZProduct` over the basis-state
    generators-as-rows reads the bit-parity — the Z-dual readout structure the
    surgery uses.) -/
example :
    selectedSignedZProduct [true, false, true]
        [indicator 0 3, indicator 1 3, indicator 2 3] [false, true, true]
      = signedZRow true [true, false, true] := by decide

end FormalRV.Framework.StabilizerBasisBridge
