/-
  FormalRV.BQCode.LogicalState — operational infrastructure stub
  for Phase B emergent-action theorem.

  Per Iter 144 reflection: define LogicalState_4_2_2_pair as the
  type for "a quantum state in the +1 eigenspace of all 4 extended
  stabilizers of the 2-patch [[4,2,2]] system". This is step 1 of
  the 4-step infrastructure build-up (Iter 145-148) for the
  operational emergent-action theorem.

  **Status**: stub only. The structural commitments are real, but
  the underlying matrix-level semantics are intentionally
  postponed to future iters (146-147 add MeasurementOutcome +
  apply_PPM + apply_surgery_with_corrections).
-/
import FormalRV.PPM.PPM
import FormalRV.Core.Gate
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Complex.Basic

namespace FormalRV.BQCode

open Matrix Complex

/-! ## Pauli.toMatrix — single-qubit matrix interpretation (Iter 151, 2026-05-13)

    The four single-qubit Paulis as 2×2 complex matrices, using
    the standard textbook convention:
    - I = identity
    - X = !![0, 1; 1, 0] (bit-flip)
    - Y = !![0, -i; i, 0] (bit-flip + phase)
    - Z = !![1, 0; 0, -1] (phase-flip)

    Foundation for the operational tightening of `apply_PPM`
    and `apply_surgery_with_corrections` (Iter 145-148
    placeholders). Future Iter 153 lifts this to PauliString via
    Kronecker product. -/

/-- Single-qubit Pauli matrix interpretation in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def Pauli.toMatrix : Pauli → Matrix (Fin 2) (Fin 2) ℂ
  | .I => !![1, 0; 0, 1]
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, -Complex.I; Complex.I, 0]
  | .Z => !![1, 0; 0, -1]

/-- **Structural sanity** for I: matrix is the 2×2 identity. -/
example : Pauli.toMatrix .I = !![(1:ℂ), 0; 0, 1] := rfl

/-- **Structural sanity** for X at index (0,1): the bit-flip
    matrix has 1 at off-diagonal positions. -/
example : (Pauli.toMatrix .X) 0 1 = 1 := by
  unfold Pauli.toMatrix
  rfl

/-- **Structural sanity** for X at index (1,0). -/
example : (Pauli.toMatrix .X) 1 0 = 1 := by
  unfold Pauli.toMatrix
  rfl

/-- **Structural sanity** for Z at diagonal. -/
example :
    (Pauli.toMatrix .Z) 0 0 = 1
    ∧ (Pauli.toMatrix .Z) 1 1 = -1 := by
  unfold Pauli.toMatrix
  refine ⟨rfl, rfl⟩

/-- **Structural sanity** for Y at off-diagonal entries. -/
example :
    (Pauli.toMatrix .Y) 0 1 = -Complex.I
    ∧ (Pauli.toMatrix .Y) 1 0 = Complex.I := by
  unfold Pauli.toMatrix
  refine ⟨rfl, rfl⟩

/-! ## Pauli.mul ↔ matrix-mul consistency checks (Iter 152, 2026-05-13)

    Verify that the inductive `Pauli.mul` (Iter 30 area) agrees
    with the matrix-multiplication of `Pauli.toMatrix` (Iter 151)
    on specific entries. These act as structural consistency
    checks: they confirm the inductive Pauli phase convention
    matches the standard textbook matrix convention.

    Self-product cases (e.g., X·X = I) are easy. Off-diagonal
    cases (X·Y, Y·Z, Z·X) involve i-phases and exercise the
    full algebra. -/

/-- **X * X = I at entry (0,0)**: matrix product diagonal entry.
    Verifies the bit-flip-squared identity. -/
example : (Pauli.toMatrix .X * Pauli.toMatrix .X) 0 0 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **X * X = I at entry (1,1)**: matrix product diagonal entry. -/
example : (Pauli.toMatrix .X * Pauli.toMatrix .X) 1 1 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **X * X = I at entry (0,1)**: off-diagonal vanishes. -/
example : (Pauli.toMatrix .X * Pauli.toMatrix .X) 0 1 = 0 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Z * Z = I at entry (0,0)**: diagonal-squared. -/
example : (Pauli.toMatrix .Z * Pauli.toMatrix .Z) 0 0 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Z * Z = I at entry (1,1)**: (-1)² = 1. -/
example : (Pauli.toMatrix .Z * Pauli.toMatrix .Z) 1 1 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **X * Z at entry (0,1)**: bit-flip composed with phase-flip
    yields -1 on the upper-right. (Inductive `Pauli.mul .X .Z =
    (.negI, .Y)`, and `-i · Y_{0,1} = -i · -i = -1`. Consistent.) -/
example : (Pauli.toMatrix .X * Pauli.toMatrix .Z) 0 1 = -1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **X * Z at entry (1,0)**: yields 1. (Inductive: negI · Y_{1,0}
    = -i · i = 1.) -/
example : (Pauli.toMatrix .X * Pauli.toMatrix .Z) 1 0 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Z * X at entry (0,1)**: opposite ordering yields +1
    (inductive `Pauli.mul .Z .X = (.posI, .Y)`, posI · Y_{0,1} =
    i · -i = 1). This confirms the anticommutation X·Z = -(Z·X)
    at the matrix level. -/
example : (Pauli.toMatrix .Z * Pauli.toMatrix .X) 0 1 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Y-involving consistency checks (Iter 155, 2026-05-13)

    Extends Iter 152's 8 entry-wise checks with Y-involving cases:
    Y·Y = I (Pauli involution), Y·X = posI Z (i.e., +i Z),
    Y·Z = posI X (i.e., +i X). These are the "missing" pairs from
    the Iter 152 selection. -/

/-- **Y * Y = I at diagonal (0,0)**: Pauli involution `Y² = I`.
    Direct entry check via matrix-mul + Fin sum. Inductive: `Pauli.mul
    .Y .Y = (.pos, .I)`. Both forms agree at (0,0): both give 1. -/
example : (Pauli.toMatrix .Y * Pauli.toMatrix .Y) 0 0 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Y * Y = I at diagonal (1,1)**. Computed: `(i · -i) + (0 · 0)
    = 1`. Confirms full diagonal of Y² = I. -/
example : (Pauli.toMatrix .Y * Pauli.toMatrix .Y) 1 1 = 1 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Y * Y = I at off-diagonal (0,1)**: vanishes (involution
    requires zero off-diagonal). -/
example : (Pauli.toMatrix .Y * Pauli.toMatrix .Y) 0 1 = 0 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Y * X at entry (0,0)**: inductive `Pauli.mul .Y .X = (.negI, .Z)`,
    so `(.negI · Z_{0,0}) = (-i · 1) = -i`. Matrix product:
    `Y_{00}·X_{00} + Y_{01}·X_{10}` = `0·0 + (-i)·1` = `-i`. ✓ -/
example : (Pauli.toMatrix .Y * Pauli.toMatrix .X) 0 0 = -Complex.I := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **X * Y at entry (0,0)**: inductive `Pauli.mul .X .Y = (.posI, .Z)`,
    so `(.posI · Z_{0,0}) = (i · 1) = i`. Confirms opposite-ordering
    sign flip vs Y·X (anticommutation of X with Y). -/
example : (Pauli.toMatrix .X * Pauli.toMatrix .Y) 0 0 = Complex.I := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Y * Z at entry (0,0)**: inductive `Pauli.mul .Y .Z = (.posI, .X)`,
    so `(.posI · X_{0,0}) = (i · 0) = 0`. Matrix: `Y_{00}·Z_{00} +
    Y_{01}·Z_{10}` = `0·1 + (-i)·0` = `0`. ✓ -/
example : (Pauli.toMatrix .Y * Pauli.toMatrix .Z) 0 0 = 0 := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Y * Z at entry (0,1)**: inductive `Pauli.mul .Y .Z = (.posI, .X)`,
    so `(.posI · X_{0,1}) = (i · 1) = i`. Matrix: `Y_{00}·Z_{01} +
    Y_{01}·Z_{11}` = `0·0 + (-i)·(-1)` = `i`. ✓ Both forms agree
    on the Y·Z = iX identity. -/
example : (Pauli.toMatrix .Y * Pauli.toMatrix .Z) 0 1 = Complex.I := by
  unfold Pauli.toMatrix
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## PauliString.toMatrix — multi-qubit lift (Iter 153, 2026-05-13)

    Lift `Pauli.toMatrix` to a `PauliString` (= `List Pauli`) by
    iterated Kronecker product:
        toMatrix [P_0, P_1, ..., P_{n-1}]
          = Pauli.toMatrix P_0 ⊗ Pauli.toMatrix P_1 ⊗ ... ⊗ Pauli.toMatrix P_{n-1}
    yielding a `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`.

    **Status**: signature committed, body SORRIED. The
    dependent-type issue is real — Mathlib's `Matrix.kroneckerMap`
    produces `Matrix (m × m') (n × n')`, but we want
    `Matrix (Fin (2^(k+1))) (Fin (2^(k+1)))` which requires a
    `Fin (2 × 2^k) ↔ Fin (2^(k+1))` reindex. Future tick (likely
    Iter 156 or later) implements via `Matrix.reindex` +
    `finProdFinEquiv`. -/

/-- **Multi-qubit Pauli string as matrix** (Iter 274, 2026-05-14):
    a `Matrix (Fin (2^n)) (Fin (2^n)) ℂ` representing the iterated
    Kronecker product of single-qubit Pauli matrices.

    **Convention**: `(p :: ps).toMatrix = ps.toMatrix ⊗ p.toMatrix`
    (qubit at list-position 0 is the LEAST-significant tensor factor —
    appears on the RIGHT). This is non-standard physics convention,
    but it lets the dependent-type plumbing close cleanly without
    casts because `Nat.pow_succ` reduces `2^(n+1) = 2^n * 2` (right
    multiplication). The matrix-level semantics are well-defined
    either way; downstream operational claims compose with this
    convention.

    Foundation for the operational tightening of `apply_PPM`
    (currently a `rfl`-placeholder identity on `LogicalState_4_2_2_pair`). -/
noncomputable def PauliString.toMatrix : (P : PauliString) →
    Matrix (Fin (2 ^ P.length)) (Fin (2 ^ P.length)) ℂ
  | [] => 1
  | p :: ps =>
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·) (PauliString.toMatrix ps) p.toMatrix)

/-! ### `PauliString.toMatrix` basic properties (Iter 275, 2026-05-14)

    Sanity lemmas validating the recursive Kronecker definition:
    - Empty list gives the 1×1 identity matrix.
    - Cons unfolds to reindex(kroneckerMap(rest, head)).

    These are `rfl`-proofs; their existence establishes that the
    `noncomputable def` from Iter 274 is structurally well-formed
    (no hidden universe / metavariable issues). -/

/-- **Empty Pauli string is the 1×1 identity matrix.** -/
theorem PauliString.toMatrix_nil :
    PauliString.toMatrix [] = (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  rfl

/-- **Cons unfolds via Kronecker + reindex** — the structural recursion
    equation, useful for downstream proofs that need to step into the
    recursion. -/
theorem PauliString.toMatrix_cons (p : Pauli) (ps : PauliString) :
    PauliString.toMatrix (p :: ps)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (PauliString.toMatrix ps) p.toMatrix) :=
  rfl

/-- **Pauli.I as 2×2 matrix is the identity** (Iter 277, 2026-05-14).
    Bridges the `Pauli.I` enum constructor to Mathlib's `(1 : Matrix
    (Fin 2) (Fin 2) ℂ)`. Useful for downstream proofs that need to
    fold strings of all-`Pauli.I` into the n-qubit identity. -/
theorem Pauli.toMatrix_I_eq_one :
    Pauli.toMatrix Pauli.I = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **All-`Pauli.I` PauliString as matrix is the identity** (Iter 278).
    `PauliString.toMatrix (List.replicate n .I) = 1`, where the `1`'s
    type is the implied `Matrix (Fin (2^(List.replicate n .I).length))
    ... ℂ`. Proof by induction on `n`, using:
    - `_nil` (Iter 275) for the base.
    - `_cons` (Iter 275) + IH + `Pauli.toMatrix_I_eq_one` (Iter 277).
    - `Matrix.kroneckerMap_one_one`: kroneckerMap of two identities
      is identity (for multiplicative `f` with zero/one preservation).
    - `Matrix.submatrix_one`: submatrix of identity by an injective
      reindex is identity. -/
theorem PauliString.toMatrix_replicate_I (n : Nat) :
    PauliString.toMatrix (List.replicate n Pauli.I) = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show PauliString.toMatrix (Pauli.I :: List.replicate k Pauli.I) = 1
    rw [PauliString.toMatrix_cons, ih, Pauli.toMatrix_I_eq_one]
    rw [Matrix.kroneckerMap_one_one (· * ·) zero_mul mul_zero (one_mul 1)]
    rw [Matrix.reindex_apply]
    exact Matrix.submatrix_one finProdFinEquiv.symm finProdFinEquiv.symm.injective

/-- **Each Pauli matrix is an involution** (Iter 279): `P · P = I` for
    every `p : Pauli`. Direct case analysis with `Matrix.mul_apply` +
    `Fin.sum_univ_two` to expand the 2×2 product and `simp` for the
    complex arithmetic (`Complex.I * Complex.I = -1`, etc.).

    This is the load-bearing identity for projection-onto-±1-eigenspace
    reasoning downstream: `(I ± P)/2` is idempotent precisely because
    `P² = I`. -/
theorem Pauli.toMatrix_mul_self (p : Pauli) :
    Pauli.toMatrix p * Pauli.toMatrix p = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Pauli.toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- **PauliString is matrix-level involution** (Iter 280, 2026-05-14):
    `P.toMatrix * P.toMatrix = 1` for any `P : PauliString`. Lifts the
    single-qubit Pauli involution (Iter 279) to n qubits via the
    `Matrix.kroneckerMap` recursion.

    **Why it matters**: the PPM projector `(I ± P)/2` is idempotent
    precisely because `P² = I`. With this lemma, the operational
    tightening of `apply_PPM` to a real ±1-eigenspace projection
    becomes structurally possible — the algebraic identity that
    makes projection well-defined is now available at the matrix
    level for arbitrary PauliStrings.

    **Proof structure** (induction on the list):
    - Base `nil`: `toMatrix [] = 1`, so `1 * 1 = 1` by `one_mul`.
    - Step `cons p ps`: unfold via `toMatrix_cons` (Iter 275) and
      `reindex_apply`, then:
      - `Matrix.submatrix_mul_equiv` to combine the two submatrix
        products into a single submatrix of the inner product.
      - `← Matrix.mul_kronecker_mul` (Mathlib): kron mul kron is
        kron of muls.
      - IH (collapses ps factor to 1) and `Pauli.toMatrix_mul_self`
        (collapses p factor to 1).
      - `Matrix.kroneckerMap_one_one`: kron(1, 1) = 1.
      - `Matrix.submatrix_one`: submatrix of 1 by an injective
        reindex is 1.

    **Key trick** (the `show` line): the recursive definition of
    `toMatrix (p :: ps)` has natural type
    `Matrix (Fin (2^ps.length * 2)) ...`, but the goal type uses
    `Matrix (Fin (2^(p :: ps).length)) ...`. These are defeq but
    Lean's `rw` matcher doesn't unfold the `Nat.pow` reduction
    automatically. The explicit `show` forces the goal into the
    `reindex finProdFinEquiv finProdFinEquiv (kroneckerMap ...)`
    form where the subsequent rewrites can fire. -/
theorem PauliString.toMatrix_mul_self (P : PauliString) :
    P.toMatrix * P.toMatrix = 1 := by
  induction P with
  | nil => exact one_mul 1
  | cons p ps ih =>
    show Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * · : ℂ → ℂ → ℂ) (PauliString.toMatrix ps) p.toMatrix)
      * Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (PauliString.toMatrix ps) p.toMatrix)
      = 1
    rw [Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
        ← Matrix.mul_kronecker_mul, ih, Pauli.toMatrix_mul_self,
        Matrix.kroneckerMap_one_one (· * ·) zero_mul mul_zero (one_mul 1)]
    exact Matrix.submatrix_one _ finProdFinEquiv.symm.injective

/-- **Single-qubit Pauli commutation at the matrix level** (Iter 281):
    if `commutes p q = true` (Pauli-algebra commutation), then the
    matrix products commute: `p.toMatrix * q.toMatrix = q.toMatrix *
    p.toMatrix`. Proof by 16-case analysis (`cases p <;> cases q`).
    For the 10 commuting cases (same Pauli, or one of them is `.I`),
    the 2×2 matrix-element equality discharges via `simp` + the
    standard `Matrix.mul_apply` / `Fin.sum_univ_two` expansion. For
    the 6 anti-commuting cases (X/Y, X/Z, Y/Z and their swaps), the
    hypothesis `h : commutes p q = true` reduces to `False` under
    `simp [commutes, Pauli.mul]` and closes by contradiction.

    **Why it matters**: this is the matrix-level instantiation of
    the Pauli-algebra commutation predicate (PPM.lean line 109). It
    is the building block for lifting `PauliString.commutes` (the
    abstract commutation predicate on n-qubit Pauli strings) to a
    real matrix-product commutation — needed for proving that two
    PPMs of mutually commuting Pauli strings can be performed in
    either order with the same operational effect. -/
theorem Pauli.toMatrix_comm_of_commutes (p q : Pauli)
    (h : commutes p q = true) :
    Pauli.toMatrix p * Pauli.toMatrix q
      = Pauli.toMatrix q * Pauli.toMatrix p := by
  cases p <;> cases q <;> (try simp [commutes, Pauli.mul] at h) <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Pauli.toMatrix, Matrix.mul_apply, Fin.sum_univ_two])

/-- **PPM projector idempotency (algebraic form, multi-qubit)** (Iter 282).
    For any PauliString `P`, the unnormalized projector `1 + P.toMatrix`
    onto the `+1` eigenspace satisfies
    `(1 + P) * (1 + P) = 2 • (1 + P)`.

    **Algebraic content**: `(1 + P)² = 1 + 2P + P² = 1 + 2P + 1 =
    2(1 + P)`. The crucial step `P² = 1` is exactly
    `PauliString.toMatrix_mul_self` (Iter 280); the rest is ring
    distribution + abelian group manipulation.

    **Why it matters**: dividing both sides by `4` (over `ℂ`) gives
    `((1 + P)/2)² = (1 + P)/2`, the standard idempotency identity
    of the normalized PPM `+1`-eigenspace projector. This is the
    last algebraic prerequisite before `apply_PPM` can be tightened
    from its `rfl` placeholder to a real projection operator. The
    unnormalized form (with `2 •`) avoids the inverse / division
    machinery and stays inside the commutative-monoid algebra. -/
theorem PauliString.toMatrix_projector_idem_aux (P : PauliString) :
    (1 + P.toMatrix) * (1 + P.toMatrix) = 2 • (1 + P.toMatrix) := by
  rw [add_mul, mul_add, mul_add, PauliString.toMatrix_mul_self]
  simp [two_smul]
  abel

/-- **PPM projector idempotency (algebraic form, `-1` eigenspace)** (Iter 283).
    Sign-flipped twin of Iter 282: for any PauliString `P`, the
    unnormalized `-1`-eigenspace projector `1 - P.toMatrix` satisfies
    `(1 - P) * (1 - P) = 2 • (1 - P)`.

    **Algebraic content**: `(1 - P)² = 1·1 - 1·P - P·1 + P·P
    = 1 - P - P + 1 = 2(1 - P)`. Identical proof shape to Iter 282,
    swap `add_mul` → `sub_mul`, `mul_add` → `mul_sub`.

    **Why it matters**: dividing both sides by 4 over `ℂ` gives the
    normalized identity `((1 - P)/2)² = (1 - P)/2`, the idempotency
    of the `-1`-eigenspace projector. With Iter 282 and this lemma
    together, both PPM measurement outcomes are characterized by
    well-defined projectors. The next algebraic step is orthogonality
    (`(1+P)(1-P) = 0`) and resolution of identity
    (`(1+P) + (1-P) = 2 • 1`). -/
theorem PauliString.toMatrix_projector_idem_aux_minus (P : PauliString) :
    (1 - P.toMatrix) * (1 - P.toMatrix) = 2 • (1 - P.toMatrix) := by
  rw [sub_mul, mul_sub, mul_sub, PauliString.toMatrix_mul_self]
  simp [two_smul]
  abel

/-- **PPM projector orthogonality** (Iter 284). For any PauliString
    `P`, the `+1` and `-1` eigenspace projectors annihilate each
    other: `(1 + P) * (1 - P) = 0` (and by an identical proof
    `(1 - P) * (1 + P) = 0`).

    **Algebraic content**: `(1 + P)(1 - P) = 1·1 - 1·P + P·1 - P·P
    = 1 - P + P - 1 = 0`. The crucial cancellation is `P² = 1`
    (Iter 280), which sets the `-P²` cross term equal to `-1`,
    cancelling the leading `+1`. The remaining `-P + P` cancels by
    additive inverse.

    **Why it matters**: orthogonality is the second of three
    characterizing identities of a projection-valued measure (PVM):
    1. Idempotency (Iter 282, 283). ✓
    2. **Orthogonality (this lemma).** ✓
    3. Resolution of identity (Iter 285 plan).

    Together they certify that `Π₊` and `Π₋` form a complete PVM,
    so a PPM measurement decomposes the state space cleanly into
    two orthogonal eigenspaces — the operational meaning of "Pauli
    measurement". -/
theorem PauliString.toMatrix_projector_orthogonality (P : PauliString) :
    (1 + P.toMatrix) * (1 - P.toMatrix) = 0 := by
  rw [add_mul, mul_sub, mul_sub, PauliString.toMatrix_mul_self]
  simp

/-- **PPM resolution of identity** (Iter 285). For any PauliString
    `P`, the `+1` and `-1` unnormalized projectors sum to twice the
    identity matrix: `(1 + P) + (1 - P) = 2 • 1`. Dividing by 2 over
    `ℂ` gives the standard resolution-of-identity
    `Π₊ + Π₋ = (1 + P)/2 + (1 - P)/2 = 1`.

    **Algebraic content**: `(1 + P) + (1 - P) = 1 + P + 1 - P = 2`.
    This identity does NOT depend on `P² = 1`; it is a pure
    abelian-group identity, so the proof is `rw [two_smul]; abel`.

    **Why it matters**: this is the third (and last) of the three
    PVM characterizing identities:
    1. Idempotency `Π_±² = Π_±` (Iter 282, 283). ✓
    2. Orthogonality `Π₊ · Π₋ = 0` (Iter 284). ✓
    3. **Resolution of identity `Π₊ + Π₋ = 1` (this lemma).** ✓

    With all three in hand, `{Π₊, Π₋}` is a complete PVM in the
    classical operator-algebra sense. A PPM measurement of `P` is
    now a well-defined operational primitive: decompose the state
    space into `Π₊ |ψ⟩ ⊕ Π₋ |ψ⟩` and return the outcome with
    probability proportional to the squared norm of the respective
    component. The next step is to wire these matrix identities
    into the operational `apply_PPM` definition (Iter 286+). -/
theorem PauliString.toMatrix_projector_resolution (P : PauliString) :
    (1 + P.toMatrix) + (1 - P.toMatrix)
      = (2 • 1 : Matrix (Fin (2^P.length)) (Fin (2^P.length)) ℂ) := by
  rw [two_smul]
  abel

/-- **Pointwise commutation predicate** (Iter 286). An inductive
    propositional predicate stating that two PauliStrings `P` and `Q`
    have equal length AND commute position-by-position in the
    underlying Pauli algebra.

    **Why an inductive predicate** (rather than `∀ i, commutes (P.get
    i) (Q.get i) = true`): the inductive form lets us pattern-match
    on it in proofs, recovering both the same-length and the
    head-commutes hypotheses simultaneously. The List-quantified form
    would require carrying a separate `P.length = Q.length`
    hypothesis through every step. -/
inductive PointwisePauliCommutes : PauliString → PauliString → Prop
  | nil : PointwisePauliCommutes [] []
  | cons : ∀ {p q : Pauli} {ps qs : PauliString},
      Pauli.commutes p q = true → PointwisePauliCommutes ps qs →
      PointwisePauliCommutes (p :: ps) (q :: qs)

/-- **Equal-length consequence of pointwise commutation** (Iter 286).
    If `P` and `Q` commute pointwise (as PauliStrings), they must have
    the same length. Proof by induction on the predicate: `nil` matches
    `[]` against `[]`; `cons` adds one to each side, preserving equality.

    Useful both as an invariant of `PointwisePauliCommutes` and as the
    cast needed to type-check `P.toMatrix * Q.toMatrix` (both
    matrices live in `Matrix (Fin (2^length)) ...`, so multiplication
    requires equal-length). -/
theorem PointwisePauliCommutes.length_eq :
    ∀ {P Q : PauliString}, PointwisePauliCommutes P Q → P.length = Q.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) (PointwisePauliCommutes.length_eq h)

/-- **Single-Pauli commutation is symmetric** (Iter 287). `commutes p q
    = commutes q p` for any Paulis `p, q`. Proved by 16-case `decide`. -/
theorem Pauli.commutes_comm (p q : Pauli) :
    Pauli.commutes p q = Pauli.commutes q p := by
  cases p <;> cases q <;> decide

/-- **Every PauliString commutes pointwise with itself** (Iter 287).
    Reflexivity of `PointwisePauliCommutes`: any PauliString trivially
    commutes with itself position-by-position because each Pauli
    commutes with itself (`Pauli.commutes_self` in PPM.lean). -/
theorem PointwisePauliCommutes.self :
    ∀ (P : PauliString), PointwisePauliCommutes P P
  | [] => .nil
  | (p :: ps) =>
      .cons (Pauli.commutes_self p) (PointwisePauliCommutes.self ps)

/-- **Pointwise commutation is symmetric** (Iter 287). If `P` commutes
    with `Q` pointwise, then `Q` commutes with `P` pointwise. Proven
    by recursion on the predicate; uses `Pauli.commutes_comm` for the
    head and the IH for the tail. -/
theorem PointwisePauliCommutes.symm :
    ∀ {P Q : PauliString}, PointwisePauliCommutes P Q →
                            PointwisePauliCommutes Q P
  | _, _, .nil => .nil
  | _, _, .cons hpq h =>
      .cons (by rw [Pauli.commutes_comm]; exact hpq)
            (PointwisePauliCommutes.symm h)

/-- **All-identity Pauli string commutes with anything (left)** (Iter 289).
    If `P` is `List.replicate Q.length Pauli.I` (all-`I` of the right
    length), it commutes pointwise with `Q`. Direct consequence of
    `Pauli.commutes_I_left` (PPM.lean line 128) applied at every
    position. -/
theorem PointwisePauliCommutes.replicate_I_left :
    ∀ (Q : PauliString),
    PointwisePauliCommutes (List.replicate Q.length Pauli.I) Q
  | [] => by exact PointwisePauliCommutes.nil
  | (q :: qs) => by
      show PointwisePauliCommutes
        (Pauli.I :: List.replicate qs.length Pauli.I) (q :: qs)
      exact PointwisePauliCommutes.cons (Pauli.commutes_I_left q)
        (PointwisePauliCommutes.replicate_I_left qs)

/-- **All-identity Pauli string commutes with anything (right)** (Iter 289).
    Symmetric twin of `replicate_I_left`: any `P` commutes pointwise
    with `List.replicate P.length Pauli.I`. Useful when one logical
    operator acts trivially on a sub-register. -/
theorem PointwisePauliCommutes.replicate_I_right :
    ∀ (P : PauliString),
    PointwisePauliCommutes P (List.replicate P.length Pauli.I)
  | [] => by exact PointwisePauliCommutes.nil
  | (p :: ps) => by
      show PointwisePauliCommutes (p :: ps)
        (Pauli.I :: List.replicate ps.length Pauli.I)
      exact PointwisePauliCommutes.cons (Pauli.commutes_I_right p)
        (PointwisePauliCommutes.replicate_I_right ps)

/-- **Pointwise commutation composes via append** (Iter 290). Concatenation
    of two pointwise-commuting pairs is pointwise-commuting:
    `P₁ ~ Q₁ → P₂ ~ Q₂ → (P₁ ++ P₂) ~ (Q₁ ++ Q₂)`.

    **Why it matters**: surgery schedules build PauliString stabilizers
    by concatenating per-patch contributions. With `append`, commutation
    of full stabilizers reduces to commutation of per-patch pieces. The
    [[4,2,2]] CNOT surgery's `Code4Code4_XXXX_L` = `[X, X, X, X] ++
    List.replicate 4 .I` commutes pointwise with `Code4Code4_ZZZZ_R` =
    `List.replicate 4 .I ++ [Z, Z, Z, Z]` because each half-pair is
    either same-pattern (any string vs all-I gives commutation by
    `replicate_I_*`) or trivially equal. -/
theorem PointwisePauliCommutes.append :
    ∀ {P₁ Q₁ P₂ Q₂ : PauliString},
    PointwisePauliCommutes P₁ Q₁ → PointwisePauliCommutes P₂ Q₂ →
    PointwisePauliCommutes (P₁ ++ P₂) (Q₁ ++ Q₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons hpq h₁, h₂ => by
      show PointwisePauliCommutes (_ :: _) (_ :: _)
      exact PointwisePauliCommutes.cons hpq
        (PointwisePauliCommutes.append h₁ h₂)

/-- **Disjoint-support commutation pattern** (Iter 290). The canonical
    instance for surgery schedules: an operator `P` on a left sub-register
    (with identity padding on the right) commutes pointwise with the
    "swapped" pattern (identity padding on the left, operator `Q` on the
    right). Direct corollary of `append` + `replicate_I_*`.

    Concrete use case: `Code4Code4` 2-patch surgery has stabilizers like
    `XXXX_L = XXXX ++ IIII` (acting on qubits 0-3, identity on 4-7) and
    `ZZZZ_R = IIII ++ ZZZZ` (acting on qubits 4-7, identity on 0-3).
    `disjoint_left_right [X,X,X,X] [Z,Z,Z,Z]` directly produces the
    pointwise-commutation witness. -/
theorem PointwisePauliCommutes.disjoint_left_right (P Q : PauliString) :
    PointwisePauliCommutes
      (P ++ List.replicate Q.length Pauli.I)
      (List.replicate P.length Pauli.I ++ Q) :=
  PointwisePauliCommutes.append
    (PointwisePauliCommutes.replicate_I_right P)
    (PointwisePauliCommutes.replicate_I_left Q)

/-- **Pointwise commutation implies abstract Pauli-string commutation**
    (Iter 291). The `PointwisePauliCommutes` predicate is a sufficient
    condition for the abstract symplectic `PauliString.commutes` (PPM.lean
    line 271): if every position commutes pointwise, then the parity of
    anti-commuting positions is zero (trivially even).

    **Note**: the converse is FALSE — `PauliString.commutes` is the
    weaker parity condition (even number of anti-commuting positions
    suffices), so two strings can `commutes` without pointwise-commuting.
    Example: `[X, Y]` and `[Y, X]` both anti-commute pointwise (2
    anti-commuting positions, even total), so they `commutes` but NOT
    `PointwisePauliCommutes`.

    **Why this lemma**: bridges our predicate-level abstraction to the
    pre-existing `PauliString.commutes` symplectic predicate already used
    in PPM.lean's stabilizer-code proofs. Now any consumer that has a
    `PointwisePauliCommutes P Q` witness can also conclude
    `PauliString.commutes P Q = true`. -/
theorem PauliString.commutes_of_pointwise :
    ∀ {P Q : PauliString}, PointwisePauliCommutes P Q →
    PauliString.commutes P Q = true
  | _, _, .nil => rfl
  | _, _, .cons hpq h => by
      have ih := PauliString.commutes_of_pointwise h
      simp only [PauliString.commutes, PauliString.mul,
        Pauli.commutes, decide_eq_true_eq] at hpq ih ⊢
      rw [hpq, ih]

/-- **[[4,2,2]] left/right disjoint-patch stabilizers commute pointwise**
    (Iter 292). Concrete application of the `disjoint_left_right`
    pattern to the 2-patch [[4,2,2]] system's stabilizer pair
    `XXXX_L` (acts on qubits 0-3) and `ZZZZ_R` (acts on qubits 4-7).

    Decomposition: `Code4Code4_XXXX_L = [X, X, X, X] ++ List.replicate 4
    Pauli.I` and `Code4Code4_ZZZZ_R = List.replicate 4 Pauli.I ++ [Z, Z,
    Z, Z]`. The two strings have disjoint Pauli support (one acts only
    on positions 0-3, the other only on 4-7), so every position has at
    least one identity, and pointwise commutation follows directly from
    `PointwisePauliCommutes.disjoint_left_right`.

    **Why this matters as an review deliverable**: this is the FIRST
    concrete application of the Iter 286-291 `PointwisePauliCommutes`
    abstraction layer to a paper-defined surgery stabilizer. With the
    pointwise witness in hand, `PauliString.commutes_of_pointwise`
    (Iter 291) immediately gives `PauliString.commutes Code4Code4_XXXX_L
    Code4Code4_ZZZZ_R = true`. This grounds the abstraction in the
    actual surgery schedule's correctness chain. -/
theorem Code4Code4_XXXX_L_pointwise_commutes_ZZZZ_R :
    PointwisePauliCommutes Code4Code4_XXXX_L Code4Code4_ZZZZ_R := by
  show PointwisePauliCommutes
    ([Pauli.X, .X, .X, .X] ++ List.replicate 4 Pauli.I)
    (List.replicate 4 Pauli.I ++ [Pauli.Z, .Z, .Z, .Z])
  exact PointwisePauliCommutes.disjoint_left_right
    [Pauli.X, .X, .X, .X] [Pauli.Z, .Z, .Z, .Z]

/-- **[[4,2,2]] disjoint-patch: `XXXX_L` commutes with `XXXX_R`** (Iter 293).
    Same proof pattern as `XXXX_L_pointwise_commutes_ZZZZ_R` (Iter 292),
    with `[Z,Z,Z,Z]` swapped to `[X,X,X,X]` on the right-patch side. -/
theorem Code4Code4_XXXX_L_pointwise_commutes_XXXX_R :
    PointwisePauliCommutes Code4Code4_XXXX_L Code4Code4_XXXX_R := by
  show PointwisePauliCommutes
    ([Pauli.X, .X, .X, .X] ++ List.replicate 4 Pauli.I)
    (List.replicate 4 Pauli.I ++ [Pauli.X, .X, .X, .X])
  exact PointwisePauliCommutes.disjoint_left_right
    [Pauli.X, .X, .X, .X] [Pauli.X, .X, .X, .X]

/-- **[[4,2,2]] disjoint-patch: `ZZZZ_L` commutes with `XXXX_R`** (Iter 293). -/
theorem Code4Code4_ZZZZ_L_pointwise_commutes_XXXX_R :
    PointwisePauliCommutes Code4Code4_ZZZZ_L Code4Code4_XXXX_R := by
  show PointwisePauliCommutes
    ([Pauli.Z, .Z, .Z, .Z] ++ List.replicate 4 Pauli.I)
    (List.replicate 4 Pauli.I ++ [Pauli.X, .X, .X, .X])
  exact PointwisePauliCommutes.disjoint_left_right
    [Pauli.Z, .Z, .Z, .Z] [Pauli.X, .X, .X, .X]

/-- **[[4,2,2]] disjoint-patch: `ZZZZ_L` commutes with `ZZZZ_R`** (Iter 293).
    Final entry in the disjoint-patch quadrant of the [[4,2,2]] 4×4
    stabilizer-commutation matrix. -/
theorem Code4Code4_ZZZZ_L_pointwise_commutes_ZZZZ_R :
    PointwisePauliCommutes Code4Code4_ZZZZ_L Code4Code4_ZZZZ_R := by
  show PointwisePauliCommutes
    ([Pauli.Z, .Z, .Z, .Z] ++ List.replicate 4 Pauli.I)
    (List.replicate 4 Pauli.I ++ [Pauli.Z, .Z, .Z, .Z])
  exact PointwisePauliCommutes.disjoint_left_right
    [Pauli.Z, .Z, .Z, .Z] [Pauli.Z, .Z, .Z, .Z]

/-- **Helper for cast threading in cons-case** (added 2026-05-23).
    Pushes the outer length cast on `toMatrix (q :: qs)` through the
    `reindex finProdFinEquiv finProdFinEquiv (kron ...)` structure
    to expose an inner cast on `qs.toMatrix`. Proof: `subst` on the
    length equality (after `generalize`ing `ps.length` to a free Nat)
    makes both sides definitionally equal. -/
private lemma toMatrix_cons_cast {q : Pauli} {qs ps : PauliString}
    (hsym : qs.length = ps.length) :
    (congrArg (· + 1) hsym ▸ PauliString.toMatrix (q :: qs)
      : Matrix (Fin (2^(ps.length + 1))) (Fin (2^(ps.length + 1))) ℂ)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·)
            (hsym ▸ PauliString.toMatrix qs
              : Matrix (Fin (2^ps.length)) (Fin (2^ps.length)) ℂ)
            q.toMatrix) := by
  generalize _hN : ps.length = N at hsym
  subst hsym
  rfl

/-- **PauliString commutation at the matrix level via pointwise**
    (Iter 286, **closed 2026-05-23**).
    If every position of `P` and `Q` commutes (and lengths match —
    both implied by `PointwisePauliCommutes P Q`), then the n-qubit
    matrices commute as operators.

    **Statement note**: the matrix product `P.toMatrix * Q.toMatrix`
    requires `P.length = Q.length` to type-check. The predicate
    enforces this, but Lean's elaborator doesn't see the equality
    until pattern-matching. We thread the `length_eq` cast explicitly
    via `h.length_eq.symm ▸ Q.toMatrix`, turning `Q.toMatrix`'s type
    from `Matrix (Fin (2^Q.length)) ...` into `Matrix (Fin (2^P.length))
    ...`. After this cast, the multiplication type-checks.

    **Proof structure**: structural recursion on the predicate.
    - `nil` case: both toMatrix's are `(1 : Matrix (Fin 1) (Fin 1) ℂ)`,
      cast is identity, closes by `simp`.
    - `cons p q ps qs hpq h_tail` case:
      1. Apply IH to get commutation on `ps`/`qs`.
      2. Use `toMatrix_cons_cast` helper to push the outer cast
         (`(cons _ _).length_eq.symm`) inward to a cast on `qs.toMatrix`.
      3. `simp only [Matrix.reindex_apply]` converts reindex to submatrix.
      4. `submatrix_mul_equiv` (×2) combines factors under shared middle equiv.
      5. `← Matrix.mul_kronecker_mul` (×2) factors kron of muls.
      6. `IH` and `Pauli.toMatrix_comm_of_commutes` swap the inner factors.

    **Why it matters**: this is the general PauliString-level
    commutation lift. The PPM measurement-order independence theorem
    needs this. The pointwise specialization (every position commutes
    outright) sidesteps the parity argument required by full
    `PauliString.commutes` (PPM.lean line 271) but covers
    practically-important cases:
    - Disjoint-support stabilizers (`XXXX_L` and `XXXX_R` on
      qubits 0-3 and 4-7).
    - Stabilizer-with-identity commutation. -/
theorem PauliString.toMatrix_comm_of_pointwise :
    ∀ {P Q : PauliString} (h : PointwisePauliCommutes P Q),
      PauliString.toMatrix P *
          (h.length_eq.symm ▸ PauliString.toMatrix Q
            : Matrix (Fin (2^P.length)) _ ℂ)
        = (h.length_eq.symm ▸ PauliString.toMatrix Q
            : Matrix (Fin (2^P.length)) _ ℂ) * PauliString.toMatrix P
  | [], [], _ => by simp [PauliString.toMatrix]
  | (p :: ps), (q :: qs), .cons hpq h_tail => by
    have IH := PauliString.toMatrix_comm_of_pointwise h_tail
    have step1 : ((PointwisePauliCommutes.cons hpq h_tail).length_eq.symm
                    ▸ PauliString.toMatrix (q :: qs)
                  : Matrix (Fin (2^(ps.length + 1))) _ ℂ)
                = Matrix.reindex finProdFinEquiv finProdFinEquiv
                    (Matrix.kroneckerMap (· * ·)
                      (h_tail.length_eq.symm ▸ PauliString.toMatrix qs)
                      q.toMatrix) :=
      toMatrix_cons_cast (hsym := h_tail.length_eq.symm)
    rw [step1]
    show Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (· * ·) (PauliString.toMatrix ps) p.toMatrix)
          * Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kroneckerMap (· * ·)
                (h_tail.length_eq.symm ▸ PauliString.toMatrix qs) q.toMatrix)
        = Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kroneckerMap (· * ·)
                (h_tail.length_eq.symm ▸ PauliString.toMatrix qs) q.toMatrix)
          * Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kroneckerMap (· * ·) (PauliString.toMatrix ps) p.toMatrix)
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
        Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        IH, Pauli.toMatrix_comm_of_commutes p q hpq]

/-! ## LogicalState_4_2_2_pair — type stub

    The 2-patch [[4,2,2]] system uses 8 physical qubits (4 per
    patch). A `LogicalState_4_2_2_pair` represents a quantum
    state in the joint codespace — i.e., a 2^8 = 256-dimensional
    complex vector that is a +1 eigenvector of all 4 extended
    stabilizers:
    - `Code4Code4_XXXX_L` (XXXX on qubits 0-3)
    - `Code4Code4_ZZZZ_L` (ZZZZ on qubits 0-3)
    - `Code4Code4_XXXX_R` (XXXX on qubits 4-7)
    - `Code4Code4_ZZZZ_R` (ZZZZ on qubits 4-7)

    The codespace has dimension 2^4 = 16 (4 logical qubits: 2 per
    patch × 2 patches). Logical states live in this 16-dimensional
    subspace.

    **Stub form**: the record carries a 256-dim vector + a placeholder
    proof of codespace membership. Future iters will tighten the
    `in_codespace` predicate once PauliString → Matrix conversion
    is added. -/

/-- A 2^8 = 256-dimensional complex column vector. Concrete shape
    for the joint [[4,2,2]] ⊗ [[4,2,2]] 8-qubit system. -/
abbrev JointStateVector := Matrix (Fin (2^8)) (Fin 1) ℂ

/-- **Placeholder predicate** for "vector is in the +1 eigenspace
    of all 4 extended stabilizers". Future iter 146 will tighten
    this to an actual matrix-action constraint once
    `PauliString.toMatrix` is available. For now it's abstract,
    accepting any vector. -/
def in_Code4Code4_codespace (_v : JointStateVector) : Prop := True

/-- **LogicalState of the 2-patch [[4,2,2]] joint system**: a
    256-dim vector with a proof it lies in the joint codespace.
    The codespace itself has dimension 16 (4 logical qubits).
    Future iters will refine the `in_codespace` predicate. -/
structure LogicalState_4_2_2_pair where
  vector : JointStateVector
  in_codespace : in_Code4Code4_codespace vector

/-- **Structural sanity**: the codespace predicate is currently
    trivially satisfied. This decide-witness confirms `True`
    holds, anchoring the stub at the right type. -/
example (v : JointStateVector) : in_Code4Code4_codespace v := trivial

/-- Constructor from a vector (using the trivial placeholder
    predicate). After Iter 146 tightens the predicate, callers
    must provide a real proof. -/
def LogicalState_4_2_2_pair.mk_trivial (v : JointStateVector) :
    LogicalState_4_2_2_pair :=
  { vector := v, in_codespace := trivial }

/-! ## Logical-gate actions on `LogicalState_4_2_2_pair` (Iter 295, 2026-05-14)

    Per goal.md (refreshed 2026-05-14 by John): connect the abstract
    `Gate` IR (used by arithmetic gadgets in BQAlgo) to the codespace
    operational layer. The first concrete bridge is the logical
    CNOT acting on the 2-patch [[4,2,2]] codespace.

    **What "logical CNOT" means concretely**: for a state `|ψ⟩` in
    the joint codespace (a `+1`-eigenvector of all 4 extended
    stabilizers), the logical CNOT from L1_left (control) to L1_right
    (target) acts as
    $$\\mathrm{CNOT} = \\Pi_0^{L_1} \\otimes I + \\Pi_1^{L_1} \\otimes X^{R_1}$$
    where `Π_0^{L_1} = (I + Z̄_{L_1})/2` projects on the `|0⟩` logical
    eigenstate of `L_1`, and `X̄^{R_1}` is the logical X on `R_1`.
    Expanded: `CNOT = (1/2) · (I + Z̄_{L_1} + X̄^{R_1} − Z̄_{L_1} · X̄^{R_1})`.

    This is the `apply_logical_gate (Gate.CX 0 1)` action that the
    bridge theorem `surgery_CNOT_implements_gate_CX` (sub-deliverable 5
    of the Iter 294 goal refresh) targets. -/

/-- **Logical-CNOT unitary on the [[4,2,2]] 2-patch codespace** (Iter 295).
    The 256×256 complex matrix that implements the logical CNOT from
    `L1_left` (control) to `L1_right` (target). Built from:

    - `Z_L1 := Code4Code4_Z_L1_left.toMatrix` — logical Z on the left
      patch's L1 qubit, embedded in the 256-dim joint space.
    - `X_R1 := Code4Code4_X_L1_right.toMatrix` — logical X on the right
      patch's L1 qubit.

    Formula: `(1/2) · (I + Z_L1 + X_R1 − Z_L1 · X_R1)`.

    **Type-coercion note**: each PauliString in the 2-patch system has
    length 8 (e.g., `Code4Code4_Z_L1_left = [.Z, .I, .Z, .I, .I, .I, .I, .I]`),
    so `toMatrix` produces `Matrix (Fin (2 ^ 8)) (Fin (2 ^ 8)) ℂ`.
    The let-bindings carry explicit type annotations to force the
    coercion (`length` doesn't reduce to `8` automatically in all
    elaboration contexts). -/
noncomputable def Code4Code4_CNOT_L1L_R1_matrix :
    Matrix (Fin (2^8)) (Fin (2^8)) ℂ :=
  let Z_L1 : Matrix (Fin (2^8)) (Fin (2^8)) ℂ :=
    Code4Code4_Z_L1_left.toMatrix
  let X_R1 : Matrix (Fin (2^8)) (Fin (2^8)) ℂ :=
    Code4Code4_X_L1_right.toMatrix
  (1/2 : ℂ) • (1 + Z_L1 + X_R1 - Z_L1 * X_R1)

/-- **Apply an abstract logical gate to a `LogicalState_4_2_2_pair`** (Iter 295).
    Pattern-matches on the `Gate` constructor. Currently only `Gate.CX 0 1`
    (logical CNOT from L1_left to L1_right) has a non-trivial action; all
    other gates return the input state unchanged. Future iters extend
    coverage to `Gate.X`, `Gate.CCX` (via magic-state injection at LP
    scale), and other gates from the `Gate` IR.

    **Review role**: this is the LEFT side of the bridge theorem
    `surgery_CNOT_implements_gate_CX`. The right side is the
    `apply_PPM_schedule + classical_pauli_feedback` on
    `Code4Code4_CNOT_surgery_schedule`. The bridge theorem (sub-deliverable
    5 of Iter 294 goal refresh) is the load-bearing claim that these two
    sides agree on the codespace. -/
noncomputable def apply_logical_gate (g : Framework.Gate)
    (s : LogicalState_4_2_2_pair) : LogicalState_4_2_2_pair :=
  match g with
  | Framework.Gate.CX 0 1 =>
    { vector := Code4Code4_CNOT_L1L_R1_matrix * s.vector,
      in_codespace := trivial }
  | _ => s

/-! ## MeasurementOutcome and apply_PPM (Iter 146, 2026-05-13)

    Step 2/4 of the Phase B operational infrastructure build-up.
    A PPM (parallel Pauli-product measurement) on a state produces
    a binary outcome (±1) and projects the state onto the
    corresponding eigenspace. For PPMs that commute with all
    stabilizers, both outcomes preserve LogicalState membership. -/

/-- **Measurement outcome** of a single PPM: ±1 eigenvalue. -/
inductive MeasurementOutcome
  | plus    -- +1 eigenvalue
  | minus   -- -1 eigenvalue
  deriving DecidableEq, Repr

/-- **Numerical eigenvalue** of a measurement outcome: `plus → 1`,
    `minus → -1`. Connects the inductive `MeasurementOutcome` to its
    Complex-number interpretation, needed for any future tightening
    of `apply_PPM` to its operational matrix definition (projector
    `(I + λ·P)/2` for eigenvalue `λ`). -/
def MeasurementOutcome.toComplex : MeasurementOutcome → ℂ
  | .plus  => 1
  | .minus => -1

/-- **Cumulative outcome sign**: product of `toComplex` over a list
    of outcomes. Useful for tracking measurement-frame Pauli
    corrections — when the surgery's correction function consumes
    `n` outcomes, the cumulative sign decides whether an overall
    Pauli is applied vs. not. -/
def outcome_product : List MeasurementOutcome → ℂ
  | [] => 1
  | x :: xs => x.toComplex * outcome_product xs

/-- **Structural sanity**: `plus.toComplex = 1`. -/
example : MeasurementOutcome.plus.toComplex = 1 := rfl

/-- **Structural sanity**: `minus.toComplex = -1`. -/
example : MeasurementOutcome.minus.toComplex = -1 := rfl

/-- **Outcome product empty list = 1** (multiplicative identity). -/
example : outcome_product [] = 1 := rfl

/-- **Outcome product on all-plus list = 1**. Five `plus` outcomes
    (matching the 5-PPM surgery schedule) yield product = 1. -/
example :
    outcome_product [.plus, .plus, .plus, .plus, .plus] = 1 := by
  simp only [outcome_product, MeasurementOutcome.toComplex]
  ring

/-- **Outcome product with one `minus` = -1**. Confirms a single
    minus outcome flips the cumulative sign — the structural
    foundation for measurement-frame Pauli corrections. -/
example :
    outcome_product [.plus, .minus, .plus, .plus, .plus] = -1 := by
  simp only [outcome_product, MeasurementOutcome.toComplex]
  ring

/-- **Outcome product with two `minus` = +1**. Even number of
    minus outcomes restores the positive cumulative sign. -/
example :
    outcome_product [.minus, .plus, .minus, .plus, .plus] = 1 := by
  simp only [outcome_product, MeasurementOutcome.toComplex]
  ring

/-- **Apply a PPM to a LogicalState**: produces a measurement
    outcome and a post-measurement state. Implementation requires
    `PauliString.toMatrix` (projection operators `(I ± P)/2`),
    which is sorried until a future tick adds that infrastructure.

    **Specification** (`TODO_apply_PPM_specification`):
    1. When the PPM operator commutes with all 4 extended
       stabilizers of `Code4Code4`, the post-state remains in
       the codespace (preserves `in_codespace`).
    2. The two outcomes correspond to the ±1 eigenprojectors of
       the PPM's measurement operator.
    3. Outcome probabilities are determined by Born's rule on
       the input vector.

    For now: returns `(plus, trivial-state)` regardless of input —
    a placeholder that type-checks but has no operational
    content. Future iter 147+ tightens this. -/
def apply_PPM (s : LogicalState_4_2_2_pair) (_ppm : PPM) :
    MeasurementOutcome × LogicalState_4_2_2_pair :=
  -- TODO_apply_PPM_specification: implement via PauliString.toMatrix
  -- projections (I ± P)/2 applied to s.vector, with outcome chosen
  -- by Born's rule sample (or refactored to be a relation, not function).
  (MeasurementOutcome.plus, s)

/-- **Apply a PPM projector with given outcome** (Iter 296, 2026-05-14).
    Operational primitive for the PPM-arithmetic bridge: applies the
    `+1`- or `-1`-eigenspace projector of a Pauli measurement operator
    to the joint state vector.

    **Signature design**: takes an EXPLICIT `outcome` parameter rather
    than computing it from Born's rule. This decouples the projector
    application (deterministic matrix multiplication) from outcome
    selection (probabilistic, requires norm calculation). Downstream
    proofs enumerate over outcomes via pattern match; for the bridge
    theorem `surgery_CNOT_implements_gate_CX` (Iter 299 plan), the
    correction function makes the per-outcome state match the logical
    gate's action regardless of outcome.

    **Operator form** (from Iter 282-283 PVM characterization):
    - `outcome = .plus`:  projector `(I + P)/2`
    - `outcome = .minus`: projector `(I - P)/2`

    **Type-coercion design**: takes the measurement matrix `P` as a
    pre-coerced `Matrix (Fin (2^8)) (Fin (2^8)) ℂ`. The caller is
    responsible for `ppm.measure.toMatrix` with explicit length-cast.
    This sidesteps the `PauliString.length` defeq issue in
    elaboration.

    Codespace preservation: when `P` commutes with all stabilizers,
    the projected state remains in the codespace. Currently
    `in_codespace` is the trivial `True` predicate; future tightening
    (Iter 298+) connects this lemma. -/
noncomputable def apply_PPM_projector
    (s : LogicalState_4_2_2_pair)
    (P : Matrix (Fin (2^8)) (Fin (2^8)) ℂ)
    (outcome : MeasurementOutcome) :
    LogicalState_4_2_2_pair :=
  let projector : Matrix (Fin (2^8)) (Fin (2^8)) ℂ :=
    match outcome with
    | .plus  => (1/2 : ℂ) • (1 + P)
    | .minus => (1/2 : ℂ) • (1 - P)
  { vector := projector * s.vector, in_codespace := trivial }

/-- **Structural sanity for outcomes**: `plus ≠ minus`. Provides a
    decidable inequality witness for downstream proofs. -/
example : (MeasurementOutcome.plus = MeasurementOutcome.minus) = False := by decide

/-- **Apply_PPM placeholder structural check**: applying a PPM to
    any logical state yields a result of type
    `MeasurementOutcome × LogicalState_4_2_2_pair`. Trivial type
    sanity at this stage of the infrastructure build-up. -/
example (s : LogicalState_4_2_2_pair) (ppm : PPM) :
    let result := apply_PPM s ppm
    result.1 = MeasurementOutcome.plus := by rfl

/-! ## apply_surgery_with_corrections (Iter 147, 2026-05-13)

    Step 3/4 of the Phase B operational infrastructure build-up.

    **The picture**: a surgery schedule is a list of PPMs (Iter
    41 / Code4Code4_CNOT_surgery_schedule). Applying it to a
    LogicalState yields:
    1. A sequence of measurement outcomes (one per PPM).
    2. A post-measurement state, before any classical post-
       processing.

    To make the surgery DETERMINISTIC at the logical level (i.e.,
    a unitary on the codespace), the measurement outcomes are
    consumed by a **correction function** that produces a Pauli
    string to apply to the post-state. For the 5-PPM CNOT surgery,
    the standard literature correction is:

    - Outcome of merge PPM (XL⊗ZR): if `minus`, apply `Z_L1·Z_R1`
      to flip the sign of `Z_L1` (target-Z correction).
    - Outcomes of stabilizer checks (Z_L, X_R): standard syndrome
      processing; in the ideal-decoder limit these are absorbed
      by the codespace projection.
    - Outcomes of split PPMs (X_L, Z_R): if either is `minus`, an
      additional Pauli correction is needed to align the split
      codes' logicals.

    This iter defines the function TYPE for the corrected
    surgery; the body is a placeholder. -/

/-- **Correction function** for the 5-PPM CNOT surgery: maps the
    5 measurement outcomes (one per PPM in
    `Code4Code4_CNOT_surgery_schedule`) to the Pauli string that
    must be applied to bring the post-measurement state into the
    canonical logical-CNOT image. The specific function is
    derived from the surgery literature; placeholder here. -/
def Code4Code4_CNOT_correction_fn (_outcomes : List MeasurementOutcome) :
    PauliString :=
  -- TODO_correction_fn_specification: derive from surgery literature.
  -- Standard form: case-analysis on outcome list maps to one of
  -- {I⊗8, Z_L1·Z_R1, X_L1·X_R1, Y_L1·Y_R1} (Pauli-frame correction
  -- for the 4 possible logical Pauli corrections after CNOT).
  PauliString.id 8

/-- **Apply a sequence of PPMs to a LogicalState**, collecting
    outcomes left-to-right. Iterated `apply_PPM`. -/
def apply_schedule (s : LogicalState_4_2_2_pair) :
    List PPM → List MeasurementOutcome × LogicalState_4_2_2_pair
  | [] => ([], s)
  | ppm :: rest =>
      let (out_head, s_after_head) := apply_PPM s ppm
      let (outs_rest, s_final) := apply_schedule s_after_head rest
      (out_head :: outs_rest, s_final)

/-- **Apply surgery with corrections**: applies the schedule,
    collects outcomes, computes the correction Pauli string,
    and applies it to the post-state.

    **Specification** (`TODO_apply_surgery_specification`):
    1. The output state lies in the joint codespace
       (`in_codespace` preserved).
    2. For input `s` representing a tensor-product logical state
       `|ψ_L⟩ ⊗ |φ_R⟩`, the output represents
       `CNOT_L1,R1 (|ψ_L⟩ ⊗ |φ_R⟩)`.
    3. Outcome 1 above is the structural commitment; outcome 2
       is the operational claim verified by Iter 148's
       `Code4Code4_surgery_implements_logical_CNOT`.

    For now: applies the schedule (collecting outcomes), then
    returns the post-state UNCORRECTED — the correction-function
    multiplication needs `PauliString.toMatrix` + matrix
    multiplication, deferred. -/
def apply_surgery_with_corrections (s : LogicalState_4_2_2_pair)
    (schedule : List PPM)
    (_correction_fn : List MeasurementOutcome → PauliString) :
    LogicalState_4_2_2_pair :=
  -- TODO_apply_surgery_specification: combine apply_schedule's
  -- post-state with the Pauli correction from correction_fn (via
  -- PauliString.toMatrix, not yet available).
  (apply_schedule s schedule).2

/-- **Structural sanity for the 5-PPM schedule**: applying
    `Code4Code4_CNOT_surgery_schedule` collects exactly 5
    outcomes. Decide-witness of the structural commitment. -/
example (s : LogicalState_4_2_2_pair) :
    (apply_schedule s Code4Code4_CNOT_surgery_schedule).1.length = 5 := by
  unfold Code4Code4_CNOT_surgery_schedule
  rfl

/-- **Correction function placeholder structural check**: at any
    outcome list, the placeholder returns the 8-qubit identity
    string. -/
example (outs : List MeasurementOutcome) :
    Code4Code4_CNOT_correction_fn outs = PauliString.id 8 := rfl

/-! ## Operational emergent-action theorem (Iter 148, 2026-05-13)

    Step 4/4 of the Phase B operational infrastructure build-up.

    **The headline claim**: the 5-PPM CNOT surgery schedule, when
    applied to a tensor-product LogicalState with the standard
    Pauli correction function, implements a **logical CNOT** on
    the encoded logical qubits.

    Stated using the Iter 145-147 infrastructure
    (`LogicalState_4_2_2_pair`, `apply_surgery_with_corrections`,
    `Code4Code4_CNOT_correction_fn`). The proof requires the
    operational specifications of each placeholder
    (`TODO_apply_PPM_specification`,
    `TODO_apply_surgery_specification`,
    `TODO_correction_fn_specification`) to be tightened to their
    actual matrix-level semantics, which itself requires
    `PauliString.toMatrix`. -/

/-- **Abstract logical-CNOT image on the joint LogicalState**:
    placeholder for the function `|ψ⟩ ↦ CNOT_L1,R1 |ψ⟩` on
    LogicalStates. Returns the input unchanged for now (a
    placeholder identity). Real implementation requires the
    logical-CNOT matrix on the 16-dim codespace. -/
def logical_CNOT_L1_R1 (s : LogicalState_4_2_2_pair) : LogicalState_4_2_2_pair :=
  -- TODO_logical_CNOT_specification: implement via codespace-restricted
  -- CNOT matrix on the 16-dim subspace of JointStateVector.
  s

/-- **THE PHASE B OPERATIONAL EMERGENT-ACTION THEOREM** (Iter 148):
    applying the 5-PPM CNOT surgery schedule with the standard
    correction function to a joint LogicalState yields the same
    state as applying the logical CNOT directly.

    **Status**: stated using Iter 145-147 infrastructure. Holds
    by `rfl` AT THE PLACEHOLDER LAYER — both
    `apply_surgery_with_corrections` and `logical_CNOT_L1_R1` are
    currently identities on `s`, so they trivially agree.

    The operational content emerges as the placeholders are
    tightened to their real matrix-level definitions via
    `PauliString.toMatrix` infrastructure. The theorem's
    **structural shape** is now committed; future work fills in
    the operational semantics underneath, after which this
    theorem will be a real (non-trivial) claim. -/
theorem Code4Code4_surgery_implements_logical_CNOT
    (s : LogicalState_4_2_2_pair) :
    apply_surgery_with_corrections s
        Code4Code4_CNOT_surgery_schedule
        Code4Code4_CNOT_correction_fn
      = logical_CNOT_L1_R1 s := by
  -- Both sides are placeholders that return `s`. Holds by rfl;
  -- becomes the real operational claim once placeholders tighten.
  -- TODO_emergent_CNOT_operational: real proof requires
  --   (a) PauliString.toMatrix and matrix-level apply_PPM,
  --   (b) Pauli correction multiplication on JointStateVector,
  --   (c) reduction of the post-corrected schedule to logical_CNOT.
  rfl

/-! ## Phase B operational infrastructure — STATUS after Iter 148

    All 4 infrastructure pieces in place:
    - `LogicalState_4_2_2_pair` (Iter 145)
    - `MeasurementOutcome` + `apply_PPM` (Iter 146)
    - `apply_schedule` + `apply_surgery_with_corrections` +
      `Code4Code4_CNOT_correction_fn` (Iter 147)
    - `logical_CNOT_L1_R1` + the emergent-action theorem (Iter 148, this)

    **The Phase B operational claim is SCOPED**: the theorem
    `Code4Code4_surgery_implements_logical_CNOT` is stated
    precisely using all required infrastructure, and currently
    holds by `rfl` at the placeholder layer. As infrastructure
    tightens (via `PauliString.toMatrix`), the theorem becomes
    progressively a real claim — at which point it may either
    continue to hold (closing the Phase B emergent-action
    direction) or fail (revealing a structural error to
    investigate).

    This is the **specification-first** completion pattern:
    state the theorem with all dependencies, run the
    rfl-proof, and let future infrastructure work tighten the
    claim. -/

/-! ## Operational infrastructure roadmap (Iter 145-148 plan)

    | Iter | Deliverable |
    |---|---|
    | 145 (this) | `LogicalState_4_2_2_pair` type + abstract `in_codespace` predicate |
    | 146 | `MeasurementOutcome` enum + `apply_PPM` (with `TODO_apply_PPM_specification`) |
    | 147 | `apply_surgery_with_corrections` for the 5-PPM schedule (with `TODO_apply_surgery_specification`) |
    | 148 | `Code4Code4_surgery_implements_logical_CNOT` operational theorem statement (likely sorried with `TODO_emergent_CNOT_operational`) |

    After Iter 148, the Phase B operational claim is **scoped** —
    all infrastructure defined, theorem stated precisely. The
    proof itself remains open but the specification is complete. -/

end FormalRV.BQCode
