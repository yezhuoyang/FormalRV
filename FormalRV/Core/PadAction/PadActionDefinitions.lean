import FormalRV.Core.UnitarySem
import FormalRV.Core.QuantumLib

namespace FormalRV.Framework
open Matrix Complex
open scoped Kronecker




/-! ## The reindex equiv used by `pad_u` -/

/-- The reindex equiv embedded inside `pad_u dim n` (when `n < dim`).
    Decomposes a `Fin (2^dim)` index into a triple `(high, middle, low)` with
    `high : Fin (2^n)`, `middle : Fin 2`, `low : Fin (2^(dim-n-1))`. -/
noncomputable def padEquiv (dim n : Nat) (h : n < dim) :
    (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^dim) :=
  let e₀ : (Fin (2^n) × Fin 2) × Fin (2^(dim-n-1)) ≃ Fin (2^n * 2 * 2^(dim-n-1)) :=
    (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv
  e₀.trans (Fin.castOrderIso (two_pow_split dim n h)).toEquiv

/-! ## Bit-flip on `Fin 2` -/

/-- Flip a `Fin 2` value: 0 ↔ 1. -/
def flipBit : Fin 2 → Fin 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨_+2, h⟩ => absurd h (by omega)

/-! ## S† gate: diagonal phase -i on |1⟩ -/

/-- The S†-gate matrix: `!![1, 0; 0, -I]`. -/
noncomputable def sdagMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -Complex.I]

/-! ## T† gate: diagonal phase exp(-i·π/4), no superposition

    Mirrors T but with negative phase. Faithful translation of SQIR's
    `UnitaryOps.v f_to_vec_TDAG`. -/

/-- The T†-gate matrix: `!![1, 0; 0, exp(-i·π/4)]`. -/
noncomputable def tdagMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (-(Complex.I * (Real.pi / 4)))]

/-! ## CCX_eq_toffoliMatrix: matrix equality from f_to_vec_CCX

    Two 8×8 matrices are equal iff their actions on all 8 basis vectors agree.
    `uc_eval (BaseUCom.CCX 0 1 2)` and `toffoliMatrix` should agree because
    both implement the Toffoli permutation: identity on indices 0-5, and
    swap 6 ↔ 7. -/

/-- The natural-number inverse of `funbool_to_nat`: extracts bit at position
    `n-1-i` of `j`. For `j < 2^n`, `funbool_to_nat n (nat_to_funbool n j) = j`. -/
def nat_to_funbool (n : Nat) (j : Nat) : Nat → Bool :=
  fun i => (j / 2^(n - 1 - i)) % 2 = 1

/-! ## Status / next steps

    What's proven above is sufficient to express how `pad_u dim n M` acts
    on a single basis state `f_to_vec dim f`. Specifically the chain
    `f_to_vec_eq_basis_padEquiv` + `pad_u_σx_on_basis_vector_padEquiv`
    + `padEquiv_val_formula` + `funbool_to_nat_split` shows
    `pad_u dim n σx * f_to_vec dim f` is the basis state at the integer
    obtained by flipping bit at qubit-`n` position.

    The next milestones (not closed in this iteration):

    1. `funbool_to_nat_update_negate`: relate `funbool_to_nat dim (update f n (!f n))`
       back to `funbool_to_nat dim f` with the middle bit flipped. Requires
       a lemma `funbool_to_nat_congr : (∀ i < n, f i = g i) → funbool_to_nat n f = funbool_to_nat n g`
       (induction on n).
    2. Lift to `f`-coordinates: `pad_u_σx_on_f_to_vec`,
       `pad_u_proj0_on_f_to_vec`, `pad_u_proj1_on_f_to_vec`.
    3. Compose for `pad_ctrl`: case-split on `f i` and combine.
    4. Conclude `f_to_vec_CNOT`.

    Each is < 50 LOC of Lean. Total remaining: ~200 LOC for `f_to_vec_CNOT`.
    Then per-gate work for `f_to_vec_H/T/TDAG` (similar size) + chaining
    for `f_to_vec_CCX`. -/

end FormalRV.Framework
