/-
  FormalRV.PauliRotation.Semantics.CommBridge
  ─────────────────────────────────
  THE COMMUTATION BRIDGE — closing the layer's known gap 1:

      `commF P Q = true  →  axisMat n P * axisMat n Q = axisMat n Q * axisMat n P`

  i.e. the SYNTACTIC commutation test (even anticommuting-overlap count,
  kernel-decidable) implies MATRIX commutation of the axes.  This is the
  exchange engine every reorder/parallelization transform rests on: combined
  with the proven `rotOf_comm`, it yields the program-level exchange lemma
  `Rot.denote_swap` (adjacent rotations with `commF`-commuting axes swap
  without changing the denotation).

  Proof route (all mechanical):
    §1  single-qubit: `p·q = ±q·p` with the sign decided by `pauliAC`
        (16-case matrix computation);
    §2  the Kronecker SIGN theorem: `opsMat n f * opsMat n g =
        (−1)^|{i < n | AC(f i, g i)}| • (opsMat n g * opsMat n f)`
        (induction on `n`, one Kronecker factor at a time);
    §3  the sparse↔dense count bridge: for canonical `P` of width ≤ n the
        dense mismatch count over `range n` IS `acCount P Q`;
    §4  assembly: `commF` says the count is even, `(−1)^even = 1`.

  Width hypotheses are NECESSARY: a factor at qubit ≥ n is invisible to the
  `n`-qubit matrix, so the sparse and dense parities can disagree.
-/
import FormalRV.PauliRotation.Semantics.Core
import FormalRV.PPM.Syntax.PauliAlgebra

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Single-qubit commutation sign. -/

/-- Do two single-qubit Paulis anticommute?  (Exactly the six mixed pairs of
distinct non-identity Paulis.) -/
def pauliAC : Pauli → Pauli → Bool
  | .X, .Y => true
  | .Y, .X => true
  | .X, .Z => true
  | .Z, .X => true
  | .Y, .Z => true
  | .Z, .Y => true
  | _,  _  => false

/-- Single-qubit Paulis commute or anticommute, with the sign decided by
`pauliAC` — by direct 2×2 matrix computation in all 16 cases. -/
theorem pauli_mul_sign (p q : Pauli) :
    p.toMatrix * q.toMatrix
      = (if pauliAC p q then (-1 : ℂ) else 1) • (q.toMatrix * p.toMatrix) := by
  cases p <;> cases q <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Pauli.toMatrix, pauliAC, Matrix.mul_apply, Fin.sum_univ_two])

/-! ## §2. The Kronecker sign theorem. -/

@[simp] theorem opsMat_zero (f : Nat → Pauli) : opsMat 0 f = 1 := rfl

theorem opsMat_succ (n : Nat) (f : Nat → Pauli) :
    opsMat (n + 1) f
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (opsMat n (fun i => f (i + 1)))
            (f 0).toMatrix) := rfl

theorem reindexKron_mul {n : Nat}
    (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (a b : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * · : ℂ → ℂ → ℂ) A a)
      * Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) B b)
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (A * B) (a * b)) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
      Matrix.mul_kronecker_mul]

private theorem countP_map_succ (p : Nat → Bool) (l : List Nat) :
    (l.map Nat.succ).countP p = l.countP (fun i => p (i + 1)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.countP_cons, ih]

private theorem countP_range_succ_shift (p : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).countP p
      = (List.range n).countP (fun i => p (i + 1)) + (if p 0 then 1 else 0) := by
  rw [List.range_succ_eq_map, List.countP_cons, countP_map_succ]

/-- **The Kronecker sign theorem**: two dense Pauli assignments commute up to
the sign `(−1)^(number of anticommuting positions)`. -/
theorem opsMat_mul_sign (n : Nat) (f g : Nat → Pauli) :
    opsMat n f * opsMat n g
      = ((-1 : ℂ) ^ ((List.range n).countP (fun i => pauliAC (f i) (g i)))) •
          (opsMat n g * opsMat n f) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
      show Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (· * · : ℂ → ℂ → ℂ)
              (opsMat n (fun i => f (i + 1))) (f 0).toMatrix)
          * Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kroneckerMap (· * ·)
                (opsMat n (fun i => g (i + 1))) (g 0).toMatrix)
          = ((-1 : ℂ) ^ ((List.range (n + 1)).countP (fun i => pauliAC (f i) (g i)))) •
              (Matrix.reindex finProdFinEquiv finProdFinEquiv
                (Matrix.kroneckerMap (· * ·)
                  (opsMat n (fun i => g (i + 1))) (g 0).toMatrix)
              * Matrix.reindex finProdFinEquiv finProdFinEquiv
                  (Matrix.kroneckerMap (· * ·)
                    (opsMat n (fun i => f (i + 1))) (f 0).toMatrix))
      rw [reindexKron_mul, reindexKron_mul, ih, pauli_mul_sign,
          Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
      rw [show ∀ (c : ℂ) (M : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ),
            Matrix.reindex finProdFinEquiv finProdFinEquiv (c • M)
              = c • Matrix.reindex finProdFinEquiv finProdFinEquiv M
          from fun _ _ => rfl]
      rw [countP_range_succ_shift]
      congr 1
      by_cases h : pauliAC (f 0) (g 0) = true <;>
        simp [h, pow_succ]

/-! ## §3. The sparse ↔ dense mismatch-count bridge. -/

theorem width_le_factor_lt {P : PauliProduct} {n : Nat}
    (h : PauliProduct.width P ≤ n) : ∀ f ∈ P, f.qubit < n := by
  induction P with
  | nil => intro f hf; cases hf
  | cons a t ih =>
      intro f hf
      simp only [PauliProduct.width] at h
      rcases List.mem_cons.mp hf with rfl | hf
      · omega
      · exact ih (by omega) f hf

theorem kindFn_cons_self (f : PFactor) (t : PauliProduct) :
    kindFn (f :: t) f.qubit = pkindToBQ f.kind := by
  simp [kindFn, List.find?_cons_of_pos]

theorem kindFn_cons_ne (f : PFactor) (t : PauliProduct) (i : Nat)
    (h : f.qubit ≠ i) : kindFn (f :: t) i = kindFn t i := by
  have : (f.qubit == i) = false := by simpa using h
  simp [kindFn, List.find?_cons_of_neg, this]

theorem kindFn_eq_I_of_lt_lbound {lo : Nat} {P : PauliProduct}
    (h : lbound lo P = true) {i : Nat} (hi : i < lo) : kindFn P i = .I := by
  induction P with
  | nil => rfl
  | cons f t ih =>
      simp only [lbound, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [kindFn_cons_ne f t i (by omega)]
      exact ih h.2

/-- `pauliAC` against a sparse lookup IS the syntactic `overlapMismatch`. -/
theorem pauliAC_kind_lookup (k : PKind) (Q : PauliProduct) (i : Nat) :
    pauliAC (pkindToBQ k) (kindFn Q i) = overlapMismatch Q ⟨i, k⟩ := by
  unfold kindFn overlapMismatch
  cases hq : Q.find? (fun g => g.qubit == i) with
  | none => cases k <;> rfl
  | some g => rcases g with ⟨gq, gk⟩; cases k <;> cases gk <;> rfl

private theorem countP_congr' {p q : Nat → Bool} :
    ∀ {l : List Nat}, (∀ a ∈ l, p a = q a) → l.countP p = l.countP q := by
  intro l h
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.countP_cons, List.countP_cons, h a (.head _),
          ih (fun b hb => h b (.tail _ hb))]

private theorem countP_range_split (n a : Nat) (ha : a < n) (p q : Nat → Bool)
    (heq : ∀ j, j ≠ a → q j = p j) (hpa : p a = false) :
    (List.range n).countP q = (List.range n).countP p + (if q a then 1 else 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.countP_append, List.countP_append]
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add]
      by_cases han : a = n
      · subst han
        have h1 : (List.range a).countP q = (List.range a).countP p :=
          countP_congr' (fun j hj => heq j (by have := List.mem_range.mp hj; omega))
        rw [h1, hpa]
        simp
      · have han' : a < n := by omega
        rw [ih han', heq n (by omega)]
        omega

/-- **The count bridge**: for a canonical sparse product of width ≤ n, the
dense anticommuting-position count over `range n` is exactly the syntactic
`acCount`. -/
theorem acCount_dense (n : Nat) (P Q : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n) :
    (List.range n).countP (fun i => pauliAC (kindFn P i) (kindFn Q i))
      = acCount P Q := by
  induction P with
  | nil =>
      have h0 : ∀ i ∈ List.range n,
          pauliAC (kindFn ([] : PauliProduct) i) (kindFn Q i) = false := by
        intro i _
        cases hk : kindFn Q i <;> rfl
      rw [countP_congr' h0]
      simp [acCount]
  | cons fc t ih =>
      have hlt : fc.qubit < n := width_le_factor_lt hw fc (.head _)
      have hst := sorted_cons_tail hs
      have hlb := sorted_cons_lbound hs
      have hwt : PauliProduct.width t ≤ n := by
        simp only [PauliProduct.width] at hw; omega
      have heq : ∀ j, j ≠ fc.qubit →
          pauliAC (kindFn (fc :: t) j) (kindFn Q j)
            = pauliAC (kindFn t j) (kindFn Q j) := by
        intro j hj
        rw [kindFn_cons_ne fc t j (fun h => hj h.symm)]
      have hpa : pauliAC (kindFn t fc.qubit) (kindFn Q fc.qubit) = false := by
        rw [kindFn_eq_I_of_lt_lbound hlb (by omega)]
        cases hk : kindFn Q fc.qubit <;> rfl
      rw [countP_range_split n fc.qubit hlt _ _ heq hpa, ih hst hwt,
          kindFn_cons_self fc t, pauliAC_kind_lookup]
      show acCount t Q + _ = acCount (fc :: t) Q
      simp only [acCount, List.countP_cons]

/-! ## §4. Assembly: the bridge and the exchange lemma. -/

/-- **THE COMMUTATION BRIDGE**: syntactically commuting axes (`commF`) have
commuting matrices.  (`P` canonical and within width — the width bound is
necessary, since out-of-range factors are invisible to the matrix.) -/
theorem axisMat_comm_of_commF (n : Nat) {P Q : PauliProduct}
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (h : commF P Q = true) :
    axisMat n P * axisMat n Q = axisMat n Q * axisMat n P := by
  have hsign := opsMat_mul_sign n (kindFn P) (kindFn Q)
  rw [acCount_dense n P Q hs hw] at hsign
  have heven : Even (acCount P Q) := by
    simp only [commF, beq_iff_eq] at h
    exact Nat.even_iff.mpr h
  unfold axisMat
  rw [hsign, Even.neg_one_pow heven, one_smul]

/-- **THE EXCHANGE LEMMA**: adjacent rotations whose axes commute
syntactically swap without changing the denotation — the engine behind every
reorder/parallelization transform.  Only ONE side needs to be canonical and
in-width. -/
theorem Rot.denote_swap (n : Nat) (r s : Rot)
    (hs : sortedStrict s.axis = true) (hw : PauliProduct.width s.axis ≤ n)
    (h : commF s.axis r.axis = true) :
    Rot.denote n r * Rot.denote n s = Rot.denote n s * Rot.denote n r := by
  unfold Rot.denote
  exact rotOf_comm (axisMat_comm_of_commF n hs hw h).symm _ _

/-! ## §5. Smoke: the bridge applied to a concrete overlapping pair. -/

example :  -- X₀X₁ and Z₀Z₁ overlap everywhere yet commute — now at the MATRIX level
    axisMat 2 [⟨0, .x⟩, ⟨1, .x⟩] * axisMat 2 [⟨0, .z⟩, ⟨1, .z⟩]
      = axisMat 2 [⟨0, .z⟩, ⟨1, .z⟩] * axisMat 2 [⟨0, .x⟩, ⟨1, .x⟩] :=
  axisMat_comm_of_commF 2 (by decide) (by decide) (by decide)

end FormalRV.PauliRotation
