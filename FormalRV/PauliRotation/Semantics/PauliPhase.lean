/-
  FormalRV.PauliRotation.Semantics.PauliPhase
  ─────────────────────────────────
  **THE PHASE-TRACKED PAULI PRODUCT — the optimization keystone.**

  The frame product `mulF` (PPM/Syntax/PauliAlgebra) multiplies sparse Pauli
  products MOD PHASE.  This file supplies the missing phase and welds the
  pair to the matrix semantics:

      axisMat n P * axisMat n Q = i^(phaseF P Q) • axisMat n (mulF P Q)

  for canonical `P` within width and canonical `Q`.  This single theorem is
  what turns Litinski-style Clifford pushing (`rot_quarter_push`, which
  conjugates axes as MATRICES) into verified SYNTACTIC rewrites on the
  rotation IR — the new axis is `mulF P Q` and the sign lands in the `neg`
  flag (anticommuting products always carry phase ±i).

  Build mirrors the proven CommBridge architecture exactly:
    §1  dense single-qubit product with phase (`bqMul`/`bqPhase`,
        `pauli_mul_full` — 16-case 2×2 computation);
    §2  the Kronecker lift (`opsMat_mul_full` — induction via
        `reindexKron_mul`, phases add);
    §3  sparse ↔ dense bridges (`phaseF_dense` mirrors `acCount_dense`;
        `kindFn_mulF` is the pointwise kind law over the sorted merge);
    §4  THE KEYSTONE `axisMat_mulF` + parity corollaries reconciling
        `phaseF` with `commF`/`acCount`.
-/
import FormalRV.PauliRotation.Semantics.CommBridge

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. The dense single-qubit product with phase. -/

/-- Single-qubit Pauli product, kind component (`I` absorbs; equal kinds
cancel; distinct kinds give the third). -/
def bqMul : Pauli → Pauli → Pauli
  | .I, q => q
  | p, .I => p
  | .X, .X => .I
  | .Y, .Y => .I
  | .Z, .Z => .I
  | .X, .Y => .Z
  | .Y, .X => .Z
  | .Y, .Z => .X
  | .Z, .Y => .X
  | .Z, .X => .Y
  | .X, .Z => .Y

/-- Single-qubit Pauli product, phase exponent: `p·q = i^(bqPhase p q)·(bqMul p q)`.
Cyclic order `X→Y→Z` gives `+i` (exponent 1), reversed gives `−i` (exponent 3). -/
def bqPhase : Pauli → Pauli → ℕ
  | .X, .Y => 1
  | .Y, .Z => 1
  | .Z, .X => 1
  | .Y, .X => 3
  | .Z, .Y => 3
  | .X, .Z => 3
  | _, _ => 0

@[simp] theorem bqMul_I_left (q : Pauli) : bqMul .I q = q := rfl

@[simp] theorem bqMul_I_right (p : Pauli) : bqMul p .I = p := by
  cases p <;> rfl

@[simp] theorem bqPhase_I_left (q : Pauli) : bqPhase .I q = 0 := by
  cases q <;> rfl

@[simp] theorem bqPhase_I_right (p : Pauli) : bqPhase p .I = 0 := by
  cases p <;> rfl

/-- **The 2×2 phase-tracked product**: every pair of single-qubit Paulis
multiplies to `i^(bqPhase)` times the `bqMul` kind — all 16 cases by direct
matrix computation. -/
theorem pauli_mul_full (p q : Pauli) :
    p.toMatrix * q.toMatrix
      = (Complex.I ^ bqPhase p q) • (bqMul p q).toMatrix := by
  cases p <;> cases q <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Pauli.toMatrix, bqMul, bqPhase, Matrix.mul_apply,
        Fin.sum_univ_two, pow_succ])

/-! ## §2. The Kronecker lift: phases add across qubits. -/

private theorem map_sum_range_succ (h : Nat → ℕ) (n : Nat) :
    ((List.range (n + 1)).map h).sum
      = ((List.range n).map (fun i => h (i + 1))).sum + h 0 := by
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]
  omega

/-- **The Kronecker product theorem**: dense Pauli assignments multiply
pointwise, with the phase exponents SUMMING across qubits. -/
theorem opsMat_mul_full (n : Nat) (f g : Nat → Pauli) :
    opsMat n f * opsMat n g
      = (Complex.I ^ (((List.range n).map (fun i => bqPhase (f i) (g i))).sum))
          • opsMat n (fun i => bqMul (f i) (g i)) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
      show Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (· * · : ℂ → ℂ → ℂ)
              (opsMat n (fun i => f (i + 1))) (f 0).toMatrix)
          * Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kroneckerMap (· * ·)
                (opsMat n (fun i => g (i + 1))) (g 0).toMatrix)
          = (Complex.I
              ^ (((List.range (n + 1)).map
                  (fun i => bqPhase (f i) (g i))).sum)) •
              Matrix.reindex finProdFinEquiv finProdFinEquiv
                (Matrix.kroneckerMap (· * ·)
                  (opsMat n (fun i => bqMul (f (i + 1)) (g (i + 1))))
                  (bqMul (f 0) (g 0)).toMatrix)
      rw [reindexKron_mul, ih, pauli_mul_full (f 0) (g 0),
          Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
          show ∀ (c : ℂ) (M : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ),
            Matrix.reindex finProdFinEquiv finProdFinEquiv (c • M)
              = c • Matrix.reindex finProdFinEquiv finProdFinEquiv M
          from fun _ _ => rfl,
          ← pow_add, map_sum_range_succ (fun i => bqPhase (f i) (g i)) n]

/-! ## §3. Sparse ↔ dense bridges. -/

/-- The per-factor phase of `f` against the product `Q` (0 off `Q`'s
support). -/
def phaseAt (Q : PauliProduct) (f : PFactor) : ℕ :=
  match Q.find? (fun g => g.qubit == f.qubit) with
  | some g => bqPhase (pkindToBQ f.kind) (pkindToBQ g.kind)
  | none   => 0

/-- **The product phase exponent**: the sum of per-factor phases of `P`
against `Q` — `i^(phaseF P Q)` is the phase of `P·Q` relative to
`mulF P Q`. -/
def phaseF (P Q : PauliProduct) : ℕ := (P.map (phaseAt Q)).sum

@[simp] theorem phaseF_nil (Q : PauliProduct) : phaseF [] Q = 0 := rfl

theorem phaseF_cons (f : PFactor) (P Q : PauliProduct) :
    phaseF (f :: P) Q = phaseAt Q f + phaseF P Q := by
  simp [phaseF]

/-- `bqPhase` against a sparse lookup IS the syntactic `phaseAt`. -/
theorem bqPhase_kind_lookup (k : PKind) (Q : PauliProduct) (i : Nat) :
    bqPhase (pkindToBQ k) (kindFn Q i) = phaseAt Q ⟨i, k⟩ := by
  unfold kindFn phaseAt
  cases hq : Q.find? (fun g => g.qubit == i) with
  | none => cases k <;> rfl
  | some g => rfl

private theorem sum_range_split (n a : Nat) (ha : a < n) (p q : Nat → ℕ)
    (heq : ∀ j, j ≠ a → q j = p j) (hpa : p a = 0) :
    ((List.range n).map q).sum = ((List.range n).map p).sum + q a := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append,
          List.sum_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases han : a = n
      · subst han
        have h1 : ((List.range a).map q).sum = ((List.range a).map p).sum := by
          congr 1
          exact List.map_congr_left
            (fun j hj => heq j (by have := List.mem_range.mp hj; omega))
        rw [h1, hpa]
        omega
      · rw [ih (by omega), heq n (by omega)]
        omega

/-- **The phase bridge**: for canonical `P` within width, the dense phase
sum over `range n` IS the syntactic `phaseF`. -/
theorem phaseF_dense (n : Nat) (P Q : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n) :
    ((List.range n).map (fun i => bqPhase (kindFn P i) (kindFn Q i))).sum
      = phaseF P Q := by
  induction P with
  | nil =>
      have h0 : ∀ i ∈ List.range n,
          bqPhase (kindFn ([] : PauliProduct) i) (kindFn Q i) = 0 := by
        intro i _
        exact bqPhase_I_left _
      rw [List.map_congr_left h0]
      simp
  | cons fc t ih =>
      have hlt : fc.qubit < n := width_le_factor_lt hw fc (.head _)
      have hst := sorted_cons_tail hs
      have hlb := sorted_cons_lbound hs
      have hwt : PauliProduct.width t ≤ n := by
        simp only [PauliProduct.width] at hw; omega
      have heq : ∀ j, j ≠ fc.qubit →
          bqPhase (kindFn (fc :: t) j) (kindFn Q j)
            = bqPhase (kindFn t j) (kindFn Q j) := by
        intro j hj
        rw [kindFn_cons_ne fc t j (fun h => hj h.symm)]
      have hpa : bqPhase (kindFn t fc.qubit) (kindFn Q fc.qubit) = 0 := by
        rw [kindFn_eq_I_of_lt_lbound hlb (by omega)]
        exact bqPhase_I_left _
      rw [sum_range_split n fc.qubit hlt _ _ heq hpa, ih hst hwt,
          kindFn_cons_self fc t, bqPhase_kind_lookup, phaseF_cons]
      show phaseF t Q + phaseAt Q fc = phaseAt Q fc + phaseF t Q
      omega

/-! ### The pointwise kind law over the sorted merge. -/

theorem bqMul_of_mulK_none {a b : PKind} (h : PKind.mulK a b = none) :
    bqMul (pkindToBQ a) (pkindToBQ b) = .I := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [PKind.mulK])

theorem bqMul_of_mulK_some {a b k : PKind} (h : PKind.mulK a b = some k) :
    bqMul (pkindToBQ a) (pkindToBQ b) = pkindToBQ k := by
  cases a <;> cases b <;>
    simp only [PKind.mulK, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

theorem kindFn_eq_I_of_not_lt {P : PauliProduct} {lo i : Nat}
    (hlb : lbound lo P = true) (hi : i < lo) : kindFn P i = .I :=
  kindFn_eq_I_of_lt_lbound hlb hi

/-- **The pointwise kind law**: the sorted-merge product looks up, qubit by
qubit, as the dense single-qubit product of the factors' lookups. -/
theorem kindFn_mulF (P Q : PauliProduct)
    (hsP : sortedStrict P = true) (hsQ : sortedStrict Q = true) (i : Nat) :
    kindFn (mulF P Q) i = bqMul (kindFn P i) (kindFn Q i) := by
  induction P, Q using mulF.induct with
  | case1 Q =>
      rw [mulF_nil_left]
      show kindFn Q i = bqMul (kindFn [] i) (kindFn Q i)
      rfl
  | case2 P h =>
      rw [mulF_nil_right]
      show kindFn P i = bqMul (kindFn P i) (kindFn [] i)
      rw [show kindFn ([] : PauliProduct) i = Pauli.I from rfl, bqMul_I_right]
  | case3 a P b Q hab ih =>
      rw [mulF_cons_lt P Q hab]
      by_cases hi : a.qubit = i
      · subst hi
        rw [kindFn_cons_self, kindFn_cons_self,
            kindFn_cons_ne b Q a.qubit (by omega),
            kindFn_eq_I_of_lt_lbound (sorted_cons_lbound hsQ) (by omega),
            bqMul_I_right]
      · rw [kindFn_cons_ne _ _ _ hi, kindFn_cons_ne _ _ _ hi,
            ih (sorted_cons_tail hsP) hsQ]
  | case4 a P b Q hab hba ih =>
      rw [mulF_cons_gt P Q hba]
      by_cases hi : b.qubit = i
      · subst hi
        rw [kindFn_cons_self, kindFn_cons_self,
            kindFn_cons_ne a P b.qubit (by omega),
            kindFn_eq_I_of_lt_lbound (sorted_cons_lbound hsP) (by omega)]
        rfl
      · rw [kindFn_cons_ne _ _ _ hi, kindFn_cons_ne _ _ _ hi,
            ih hsP (sorted_cons_tail hsQ)]
  | case5 a P b Q hab hba hk ih =>
      rw [mulF_cons_cancel P Q hab hba hk]
      have hq : b.qubit = a.qubit := by omega
      by_cases hi : a.qubit = i
      · subst hi
        rw [kindFn_cons_self,
            show kindFn (b :: Q) a.qubit = pkindToBQ b.kind from by
              rw [← hq]; exact kindFn_cons_self b Q,
            kindFn_eq_I_of_lt_lbound
              (mulF_lbound (a.qubit + 1) P Q (sorted_cons_lbound hsP)
                (hq ▸ sorted_cons_lbound hsQ)) (by omega),
            bqMul_of_mulK_none hk]
      · rw [kindFn_cons_ne _ _ _ hi,
            kindFn_cons_ne b Q i (by omega),
            ih (sorted_cons_tail hsP) (sorted_cons_tail hsQ)]
  | case6 a P b Q hab hba k hk ih =>
      rw [mulF_cons_combine P Q hab hba hk]
      have hq : b.qubit = a.qubit := by omega
      by_cases hi : a.qubit = i
      · subst hi
        rw [show kindFn (⟨a.qubit, k⟩ :: mulF P Q) a.qubit = pkindToBQ k from
              kindFn_cons_self ⟨a.qubit, k⟩ (mulF P Q),
            kindFn_cons_self,
            show kindFn (b :: Q) a.qubit = pkindToBQ b.kind from by
              rw [← hq]; exact kindFn_cons_self b Q,
            bqMul_of_mulK_some hk]
      · rw [show kindFn (⟨a.qubit, k⟩ :: mulF P Q) i = kindFn (mulF P Q) i from
              kindFn_cons_ne ⟨a.qubit, k⟩ (mulF P Q) i hi,
            kindFn_cons_ne _ _ _ hi,
            kindFn_cons_ne b Q i (by omega),
            ih (sorted_cons_tail hsP) (sorted_cons_tail hsQ)]

/-! ## §4. THE KEYSTONE. -/

/-- **THE PHASE-TRACKED PRODUCT THEOREM**: the matrix product of two
canonical axes is `i^(phaseF P Q)` times the axis of the frame product
`mulF P Q`.  This welds the phase-free frame algebra to the matrix
semantics and is the engine of verified Clifford pushing. -/
theorem axisMat_mulF (n : Nat) (P Q : PauliProduct)
    (hsP : sortedStrict P = true) (hwP : PauliProduct.width P ≤ n)
    (hsQ : sortedStrict Q = true) :
    axisMat n P * axisMat n Q
      = (Complex.I ^ phaseF P Q) • axisMat n (mulF P Q) := by
  show opsMat n (kindFn P) * opsMat n (kindFn Q) = _
  rw [opsMat_mul_full, phaseF_dense n P Q hsP hwP]
  congr 1
  show opsMat n _ = opsMat n (kindFn (mulF P Q))
  congr 1
  funext i
  exact (kindFn_mulF P Q hsP hsQ i).symm

/-! ### Parity corollaries: `phaseF` against `commF`/`acCount`. -/

theorem phaseAt_parity (Q : PauliProduct) (f : PFactor) :
    phaseAt Q f % 2 = (if overlapMismatch Q f then 1 else 0) := by
  obtain ⟨fq, fk⟩ := f
  unfold phaseAt overlapMismatch
  cases hq : Q.find? (fun g => g.qubit == fq) with
  | none => rfl
  | some g =>
      rcases g with ⟨gq, gk⟩
      cases fk <;> cases gk <;> simp [bqPhase, pkindToBQ]

/-- The phase parity IS the anticommutation parity. -/
theorem phaseF_parity (P Q : PauliProduct) :
    phaseF P Q % 2 = acCount P Q % 2 := by
  induction P with
  | nil => rfl
  | cons f t ih =>
      rw [phaseF_cons]
      show _ = (f :: t).countP (overlapMismatch Q) % 2
      rw [List.countP_cons]
      have h1 := phaseAt_parity Q f
      have h2 : acCount t Q = t.countP (overlapMismatch Q) := rfl
      rw [h2] at ih
      omega

/-- Commuting axes have an EVEN phase (`i^phaseF = ±1`). -/
theorem phaseF_even_of_commF {P Q : PauliProduct}
    (h : commF P Q = true) : phaseF P Q % 2 = 0 := by
  unfold commF at h
  have := phaseF_parity P Q
  simp only [beq_iff_eq] at h
  omega

/-- Anticommuting axes have an ODD phase (`i^phaseF = ±i`) — the sign that
Clifford pushing folds into the `neg` flag. -/
theorem phaseF_odd_of_not_commF {P Q : PauliProduct}
    (h : commF P Q = false) : phaseF P Q % 2 = 1 := by
  unfold commF at h
  have := phaseF_parity P Q
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  omega

/-- `i^k` only depends on `k % 4`. -/
theorem I_pow_mod (k : Nat) : Complex.I ^ k = Complex.I ^ (k % 4) := by
  conv_lhs => rw [← Nat.div_add_mod k 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

end FormalRV.PauliRotation
