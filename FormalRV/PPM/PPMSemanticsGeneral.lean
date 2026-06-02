/-
  FormalRV.PPM.PPMSemanticsGeneral — GENERAL (parametric)
  laws of the PPM operational semantics.

  `PPMOperational` proves its soundness only on concrete
  instances (`by decide`), and its own header notes that "the
  general theorem (parametric in s and P) would require
  induction".  For a *general verification framework* the
  basic-operation semantics must hold for EVERY stabilizer
  state and EVERY measured Pauli — so a user's arbitrary code +
  PPM gets the laws for free.  This file proves the first such
  parametric laws, sorry-free:

  * `Pauli.commutes_comm` — single-qubit commutation is
    symmetric.
  * `Pauli.commutes_mul` — single-qubit bilinearity of
    commutation over multiplication (the symplectic-form
    bilinearity).
  * `apply_PPM_pos_length` / `apply_PPM_neg_length` — a PPM
    preserves the number of stabilizer generators (so the
    logical dimension / code rank is preserved).
  * `apply_PPM_pos_mem` / `apply_PPM_neg_mem` — projective
    measurement: when `P` anticommutes with a generator, `±P`
    becomes a generator of the post-measurement stabilizer
    (the state is projected onto the corresponding eigenspace).

  ## Honesty boundary

  This is the *symbolic stabilizer* (Gottesman tableau) layer;
  the Gottesman–Knill bridge to ℂ-amplitude state vectors is a
  separate layer.  The remaining general laws — n-qubit `commutes` symmetry,
  bilinearity of `commutes` over `PauliString.mul`, and full
  commutativity preservation — build on `Pauli.commutes_mul`
  (the latter two are gated by `PauliString.mul`'s `foldl`/`let`
  definition, which resists clean parametric rewriting).
-/
import FormalRV.PPM.PPMOperational

namespace FormalRV.Framework.PPMOp

open FormalRV.Framework.PauliSem

/-! ## §1. Commutation is symmetric (general). -/

theorem Pauli.commutes_comm (a b : Pauli) :
    Pauli.commutes a b = Pauli.commutes b a := by
  cases a <;> cases b <;> rfl

/-! ## §2. Single-qubit bilinearity of commutation (general).

    The symplectic-form bilinearity: the product `a·b`
    anticommutes with `c` iff exactly one of `a, b` does.
    Decidable over the 4³ = 64-case Pauli table — this is the
    algebraic fact the Gottesman update relies on (multiplying
    an anticommuting generator by the chosen one restores
    commutation). -/
theorem Pauli.commutes_mul (a b c : Pauli) :
    Pauli.commutes (Pauli.mul a b).2 c
      = (Pauli.commutes a c == Pauli.commutes b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## §3. A PPM preserves the number of stabilizer generators.

    Both Gottesman branches either leave the state unchanged
    (deterministic measurement) or rewrite it by a length-
    preserving `map` over the indexed generators.  Hence the
    generator count — and with it the logical dimension /
    stabilizer rank — is invariant under any PPM. -/

theorem apply_PPM_pos_length (s : StabilizerState) (P : PauliString) :
    (apply_PPM_pos s P).length = s.length := by
  unfold apply_PPM_pos
  split
  · rfl
  · split
    · rfl
    · simp

theorem apply_PPM_neg_length (s : StabilizerState) (P : PauliString) :
    (apply_PPM_neg s P).length = s.length := by
  unfold apply_PPM_neg
  split
  · rfl
  · split
    · rfl
    · simp

/-! ## §4. Projective-measurement membership.

    When the measured Pauli `P` anticommutes with some generator
    (so the outcome is genuinely random and the state is
    projected), `P` (resp. `-P` for the −1 branch) becomes a
    generator of the post-measurement stabilizer — i.e. the
    state is projected onto the corresponding `±1` eigenspace of
    `P`.  This is the defining semantic property of a projective
    Pauli measurement, here parametric in the state and `P`. -/

theorem apply_PPM_pos_mem (s : StabilizerState) (P : PauliString) (i : Nat)
    (hi : find_anticommuting s P = some i) (hlt : i < s.length) :
    P ∈ apply_PPM_pos s P := by
  simp only [apply_PPM_pos, hi, List.getElem?_eq_getElem hlt]
  refine List.mem_map.mpr ⟨(s[i], i), ?_, ?_⟩
  · exact List.mem_iff_getElem.mpr
      ⟨i, by simpa using hlt, by simp [List.getElem_zipIdx]⟩
  · simp

theorem apply_PPM_neg_mem (s : StabilizerState) (P : PauliString) (i : Nat)
    (hi : find_anticommuting s P = some i) (hlt : i < s.length) :
    P.neg ∈ apply_PPM_neg s P := by
  simp only [apply_PPM_neg, hi, List.getElem?_eq_getElem hlt]
  refine List.mem_map.mpr ⟨(s[i], i), ?_, ?_⟩
  · exact List.mem_iff_getElem.mpr
      ⟨i, by simpa using hlt, by simp [List.getElem_zipIdx]⟩
  · simp

end FormalRV.Framework.PPMOp
