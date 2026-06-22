/-
  FormalRV.PauliRotation.Semantics.BasisAction
  ──────────────────────────────────
  D1, THE BASIS-ACTION CORE: what the axis matrices DO to computational
  basis states, in bit arithmetic — the lemmas that convert the operator
  forms of `GateRows.lean` into `Gate.applyNat` permutation matrices.

  Index convention (pinned by `finProdFinEquiv (i₁, i₂) = i₂ + 2·i₁`):
  qubit 0 is the LEAST-SIGNIFICANT BIT; basis state `j : Fin (2^n)` assigns
  qubit `k` the bit `(j : Nat).testBit k`.

    §1  `opsMat_one`, `opsMat_succ_apply` — the entry-level recursion.
    §2  Index bridges: bits and XOR through the Kronecker pair split.
    §3  **`axisMat_single_z_apply`** — `Z_q` is the bit-parity diagonal:
        entry `(i,j) = [i = j] · (−1)^{bit q of j}`.
        **`axisMat_single_x_apply`** — `X_q` is the bit-flip permutation:
        entry `(i,j) = [i = j XOR 2^q]`.
    §4  `applyMat` — `Gate.applyNat` as a permutation matrix — and
        **`xGate_rots_applyNat`: THE FIRST END-TO-END ROW** against the
        repo's Boolean gate semantics: the dictionary's X-rotation denotes
        `(−i) · applyMat n (X q)`.
-/
import FormalRV.PauliRotation.Correctness.GateRows
import FormalRV.Arithmetic.Correctness

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open FormalRV.BQAlgo
open FormalRV.Framework (update update_apply)
open Matrix

/-! ## §1. The entry-level recursion. -/

theorem opsMat_one (n : Nat) : opsMat n (fun _ => Pauli.I) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [opsMat_succ, ih, Pauli.toMatrix_I_eq_one,
          Matrix.kroneckerMap_one_one (· * ·) zero_mul mul_zero (one_mul 1),
          Matrix.reindex_apply]
      exact Matrix.submatrix_one _ finProdFinEquiv.symm.injective

theorem opsMat_succ_apply (n : Nat) (f : Nat → Pauli)
    (i₁ j₁ : Fin (2 ^ n)) (i₂ j₂ : Fin 2) :
    opsMat (n + 1) f (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv (j₁, j₂))
      = opsMat n (fun i => f (i + 1)) i₁ j₁ * (f 0).toMatrix i₂ j₂ := by
  rw [opsMat_succ]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-! ## §2. Index bridges through the pair split. -/

/-- `Fin.val` is type-ascription-blind across the defeq `2^(n+1) = 2^n·2`
(the recurring trap of this development, made explicit once). -/
theorem val_coe {n : Nat} (x : Fin (2 ^ n * 2)) :
    @Fin.val (2 ^ (n + 1)) x = @Fin.val (2 ^ n * 2) x := rfl

theorem pair_val {n : Nat} (i₁ : Fin (2 ^ n)) (i₂ : Fin 2) :
    ((finProdFinEquiv (i₁, i₂) : Fin (2 ^ n * 2)) : Nat)
      = (i₂ : Nat) + 2 * (i₁ : Nat) :=
  finProdFinEquiv_apply_val _

theorem pair_testBit_zero {n : Nat} (i₁ : Fin (2 ^ n)) (i₂ : Fin 2) :
    ((finProdFinEquiv (i₁, i₂) : Fin (2 ^ n * 2)) : Nat).testBit 0
      = decide ((i₂ : Nat) = 1) := by
  rw [pair_val, Nat.testBit_zero, decide_eq_decide]
  have := i₂.isLt
  omega

theorem pair_testBit_succ {n : Nat} (i₁ : Fin (2 ^ n)) (i₂ : Fin 2) (k : Nat) :
    ((finProdFinEquiv (i₁, i₂) : Fin (2 ^ n * 2)) : Nat).testBit (k + 1)
      = (i₁ : Nat).testBit k := by
  rw [pair_val, Nat.testBit_add_one]
  congr 1
  have := i₂.isLt
  omega

/-- XOR with `1` on the 2-adic split flips the low component. -/
theorem xor_one_split (a b : Nat) (hb : b < 2) :
    (b + 2 * a) ^^^ 1 = (1 - b) + 2 * a := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero,
          Nat.testBit_zero]
      obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
      · simp [Nat.mul_mod_right]
      · simp [Nat.add_mul_mod_self_left]
  | succ k =>
      rw [Nat.testBit_xor, Nat.testBit_add_one, Nat.testBit_add_one,
          Nat.testBit_add_one,
          show (b + 2 * a) / 2 = a from by omega,
          show ((1 - b) + 2 * a) / 2 = a from by omega,
          show (1 : Nat) / 2 = 0 from rfl]
      simp

/-- XOR with `2^(q+1)` on the 2-adic split acts on the high component. -/
theorem xor_pow_succ_split (a b : Nat) (hb : b < 2) (q : Nat) :
    (b + 2 * a) ^^^ 2 ^ (q + 1) = b + 2 * (a ^^^ 2 ^ q) := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero,
          show 2 ^ (q + 1) % 2 = 0 from by rw [pow_succ]; omega]
      have h1 : (b + 2 * a) % 2 = (b + 2 * (a ^^^ 2 ^ q)) % 2 := by omega
      simp [h1]
  | succ k =>
      rw [Nat.testBit_xor, Nat.testBit_add_one, Nat.testBit_add_one,
          Nat.testBit_add_one,
          show (b + 2 * a) / 2 = a from by omega,
          show (b + 2 * (a ^^^ 2 ^ q)) / 2 = a ^^^ 2 ^ q from by omega,
          show 2 ^ (q + 1) / 2 = 2 ^ q from by rw [pow_succ]; omega,
          Nat.testBit_xor]

/-! ## §3. The single-qubit basis actions. -/

private theorem opsMat_single_z (n : Nat) :
    ∀ (q : Nat), q < n → ∀ (i j : Fin (2 ^ n)),
      opsMat n (fun k => if q = k then Pauli.Z else Pauli.I) i j
        = if (i : Nat) = (j : Nat)
          then (if (j : Nat).testBit q then -1 else 1) else 0 := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
      intro q hq i j
      obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
      rw [opsMat_succ_apply]
      simp only [val_coe]
      cases q with
      | zero =>
          rw [show (fun i => if (0 : Nat) = i + 1 then Pauli.Z else Pauli.I)
                = (fun _ => Pauli.I) from by funext i; simp,
              opsMat_one, Matrix.one_apply,
              show ((finProdFinEquiv (j₁, j₂) : Fin (2 ^ n * 2)) : Nat).testBit 0
                = decide ((j₂ : Nat) = 1) from pair_testBit_zero j₁ j₂]
          by_cases h1 : i₁ = j₁ <;>
            fin_cases i₂ <;> fin_cases j₂ <;>
              simp [h1, Pauli.toMatrix] <;> omega
      | succ q' =>
          rw [show (fun i => if q' + 1 = i + 1 then Pauli.Z else Pauli.I)
                = (fun k => if q' = k then Pauli.Z else Pauli.I) from by
                  funext i; simp,
              ih q' (by omega),
              show (if q' + 1 = 0 then Pauli.Z else Pauli.I) = Pauli.I from rfl,
              Pauli.toMatrix_I_eq_one, Matrix.one_apply,
              show ((finProdFinEquiv (j₁, j₂) : Fin (2 ^ n * 2)) : Nat).testBit (q' + 1)
                = (j₁ : Nat).testBit q' from pair_testBit_succ j₁ j₂ q']
          have hi₂ := i₂.isLt
          have hj₂ := j₂.isLt
          by_cases h1 : (i₁ : Nat) = (j₁ : Nat) <;> by_cases h2 : i₂ = j₂ <;>
            simp [h1, h2] <;> omega

private theorem opsMat_single_x (n : Nat) :
    ∀ (q : Nat), q < n → ∀ (i j : Fin (2 ^ n)),
      opsMat n (fun k => if q = k then Pauli.X else Pauli.I) i j
        = if (i : Nat) = (j : Nat) ^^^ 2 ^ q then 1 else 0 := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
      intro q hq i j
      obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
      rw [opsMat_succ_apply]
      simp only [val_coe]
      cases q with
      | zero =>
          rw [show (fun i => if (0 : Nat) = i + 1 then Pauli.X else Pauli.I)
                = (fun _ => Pauli.I) from by funext i; simp,
              opsMat_one, Matrix.one_apply, pow_zero]
          have hvi : (↑(finProdFinEquiv (i₁, i₂)) : Nat)
              = (i₂ : Nat) + 2 * (i₁ : Nat) := pair_val i₁ i₂
          have hvj : (↑(finProdFinEquiv (j₁, j₂)) : Nat)
              = (j₂ : Nat) + 2 * (j₁ : Nat) := pair_val j₁ j₂
          simp only [hvi, hvj, xor_one_split (j₁ : Nat) (j₂ : Nat) j₂.isLt]
          have hi₂ := i₂.isLt
          have hj₂ := j₂.isLt
          by_cases h1 : (i₁ : Nat) = (j₁ : Nat) <;>
            fin_cases i₂ <;> fin_cases j₂ <;>
              simp [h1, Pauli.toMatrix, Fin.ext_iff] <;> omega
      | succ q' =>
          rw [show (fun i => if q' + 1 = i + 1 then Pauli.X else Pauli.I)
                = (fun k => if q' = k then Pauli.X else Pauli.I) from by
                  funext i; simp,
              ih q' (by omega),
              show (if q' + 1 = 0 then Pauli.X else Pauli.I) = Pauli.I from rfl,
              Pauli.toMatrix_I_eq_one, Matrix.one_apply]
          have hvi : (↑(finProdFinEquiv (i₁, i₂)) : Nat)
              = (i₂ : Nat) + 2 * (i₁ : Nat) := pair_val i₁ i₂
          have hvj : (↑(finProdFinEquiv (j₁, j₂)) : Nat)
              = (j₂ : Nat) + 2 * (j₁ : Nat) := pair_val j₁ j₂
          simp only [hvi, hvj,
            xor_pow_succ_split (j₁ : Nat) (j₂ : Nat) j₂.isLt q']
          have hi₂ := i₂.isLt
          have hj₂ := j₂.isLt
          by_cases h1 : (i₁ : Nat) = (j₁ : Nat) ^^^ 2 ^ q' <;>
            by_cases h2 : (i₂ : Nat) = (j₂ : Nat) <;>
              simp [h1, h2, Fin.ext_iff] <;> omega

/-- **`Z_q` is the bit-parity diagonal.** -/
theorem axisMat_single_z_apply (n q : Nat) (hq : q < n) (i j : Fin (2 ^ n)) :
    axisMat n [(⟨q, .z⟩ : PFactor)] i j
      = if (i : Nat) = (j : Nat)
        then (if (j : Nat).testBit q then -1 else 1) else 0 := by
  unfold axisMat
  rw [show kindFn [(⟨q, .z⟩ : PFactor)]
        = (fun k => if q = k then Pauli.Z else Pauli.I) from by
      funext k
      rw [kindFn_single]
      by_cases h : q = k <;> simp [h, pkindToBQ]]
  exact opsMat_single_z n q hq i j

/-- **`X_q` is the bit-flip permutation.** -/
theorem axisMat_single_x_apply (n q : Nat) (hq : q < n) (i j : Fin (2 ^ n)) :
    axisMat n [(⟨q, .x⟩ : PFactor)] i j
      = if (i : Nat) = (j : Nat) ^^^ 2 ^ q then 1 else 0 := by
  unfold axisMat
  rw [show kindFn [(⟨q, .x⟩ : PFactor)]
        = (fun k => if q = k then Pauli.X else Pauli.I) from by
      funext k
      rw [kindFn_single]
      by_cases h : q = k <;> simp [h, pkindToBQ]]
  exact opsMat_single_x n q hq i j

/-! ## §4. `Gate.applyNat` as a matrix, and the first end-to-end row. -/

/-- **The repo's Boolean gate semantics as a permutation matrix** at width
`n` (basis state `j` assigns qubit `k` the bit `testBit k`). -/
noncomputable def applyMat (n : Nat) (g : FormalRV.Framework.Gate) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j =>
    if ∀ k, k < n →
        (i : Nat).testBit k
          = Gate.applyNat g (fun b => (j : Nat).testBit b) k
    then 1 else 0

/-- The X gate's matrix is the bit-flip permutation. -/
theorem applyMat_X (n q : Nat) (hq : q < n) (i j : Fin (2 ^ n)) :
    applyMat n (.X q) i j
      = if (i : Nat) = (j : Nat) ^^^ 2 ^ q then 1 else 0 := by
  unfold applyMat
  congr 1
  rw [eq_iff_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    · rw [h k hk, Gate.applyNat_X, update_apply, Nat.testBit_xor,
          Nat.testBit_two_pow]
      by_cases hkq : k = q
      · simp [hkq, Bool.xor_comm]
      · rw [if_neg hkq, decide_eq_false (fun hh => hkq hh.symm)]
        simp
    · have hi : (i : Nat).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hj : (j : Nat).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le j.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hi, Nat.testBit_xor, hj, Nat.testBit_two_pow,
          decide_eq_false (by omega)]
      rfl
  · intro h k hk
    rw [h, Gate.applyNat_X, update_apply, Nat.testBit_xor,
        Nat.testBit_two_pow]
    by_cases hkq : k = q
    · simp [hkq, Bool.xor_comm]
    · rw [if_neg hkq, decide_eq_false (fun hh => hkq hh.symm)]
      simp

/-- **THE FIRST END-TO-END ROW vs `Gate.applyNat`**: at any wire `q < n`,
the dictionary's X-rotation denotes the gate's Boolean semantics as a
matrix, with the explicit global phase `−i`. -/
theorem xGate_rots_applyNat (n q : Nat) (hq : q < n) :
    seqDenote n (gateRots (.X q)) = (-Complex.I) • applyMat n (.X q) := by
  show 1 * Rot.denote n ⟨false, .piHalf, [⟨q, .x⟩]⟩ = _
  rw [Matrix.one_mul]
  show rotOf (Rot.theta ⟨false, .piHalf, [⟨q, .x⟩]⟩) (axisMat n [⟨q, .x⟩]) = _
  simp only [Rot.theta, RAngle.val, Bool.false_eq_true, if_false]
  rw [rotOf_pi_div_two]
  congr 1
  ext i j
  rw [axisMat_single_x_apply n q hq, applyMat_X n q hq]

/-! ## §5. The CX row, end-to-end. -/

/-- `Z_c` in `Matrix.diagonal` form (products collapse against it). -/
theorem axisMat_single_z_diag (n c : Nat) (hc : c < n) :
    axisMat n [(⟨c, .z⟩ : PFactor)]
      = Matrix.diagonal (fun k : Fin (2 ^ n) =>
          if (k : Nat).testBit c then (-1 : ℂ) else 1) := by
  ext a b
  rw [axisMat_single_z_apply n c hc, Matrix.diagonal_apply]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Fin.val_inj]

/-- Flipping bit `t` preserves any other bit `c`. -/
theorem testBit_xor_other {c t : Nat} (hct : c ≠ t) (m : Nat) :
    (m ^^^ 2 ^ t).testBit c = m.testBit c := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow,
      decide_eq_false (fun h => hct h.symm)]
  simp

/-- Flipping bit `t` moves the state: `m XOR 2^t ≠ m`. -/
theorem xor_two_pow_ne (m t : Nat) : m ^^^ 2 ^ t ≠ m := by
  intro hh
  have h1 : (m ^^^ 2 ^ t).testBit t = !m.testBit t := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.xor_true]
  rw [hh] at h1
  simp at h1

/-- The CX gate's matrix: flip bit `t` exactly when bit `c` is set. -/
theorem applyMat_CX (n c t : Nat) (hct : c ≠ t) (ht : t < n)
    (i j : Fin (2 ^ n)) :
    applyMat n (.CX c t) i j
      = if (i : Nat) = (if (j : Nat).testBit c
            then (j : Nat) ^^^ 2 ^ t else (j : Nat))
        then 1 else 0 := by
  unfold applyMat
  congr 1
  rw [eq_iff_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    · rw [h k hk, Gate.applyNat_CX, update_apply]
      by_cases hcj : (j : Nat).testBit c
      · rw [if_pos hcj]
        by_cases hkt : k = t
        · subst hkt
          rw [if_pos rfl, Nat.testBit_xor, Nat.testBit_two_pow_self]
          simp [hcj]
        · rw [if_neg hkt, Nat.testBit_xor, Nat.testBit_two_pow,
              decide_eq_false (fun hh => hkt hh.symm)]
          simp
      · rw [if_neg hcj]
        by_cases hkt : k = t
        · subst hkt
          rw [if_pos rfl]
          simp [hcj]
        · rw [if_neg hkt]
    · have hi : (i : Nat).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hj2 : (if (j : Nat).testBit c
          then (j : Nat) ^^^ 2 ^ t else (j : Nat)) < 2 ^ n := by
        by_cases hcj : (j : Nat).testBit c
        · rw [if_pos hcj]
          exact Nat.xor_lt_two_pow j.isLt
            (Nat.pow_lt_pow_right (by norm_num) ht)
        · rw [if_neg hcj]
          exact j.isLt
      rw [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hj2
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h k hk
    rw [h, Gate.applyNat_CX, update_apply]
    by_cases hcj : (j : Nat).testBit c
    · rw [if_pos hcj]
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos rfl, Nat.testBit_xor, Nat.testBit_two_pow_self]
        simp [hcj]
      · rw [if_neg hkt, Nat.testBit_xor, Nat.testBit_two_pow,
            decide_eq_false (fun hh => hkt hh.symm)]
        simp
    · rw [if_neg hcj]
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos rfl]
        simp [hcj]
      · rw [if_neg hkt]

/-- **THE CX ROW, END-TO-END vs `Gate.applyNat`**: at any distinct wires
`c, t < n`, the dictionary's three rotations denote the CNOT's Boolean
semantics as a matrix, with the explicit global phase `e^{iπ/4}`. -/
theorem cnot_rots_applyNat (n c t : Nat) (hct : c ≠ t) (hc : c < n)
    (ht : t < n) :
    seqDenote n (gateRots (.CX c t))
      = phaseC (Real.pi / 4) • applyMat n (.CX c t) := by
  rw [cnot_rots_denote n c t hct (by omega)]
  congr 1
  ext i j
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply,
      Matrix.one_apply, axisMat_single_z_diag n c hc, Matrix.diagonal_mul,
      Matrix.diagonal_apply, axisMat_single_x_apply n t ht,
      applyMat_CX n c t hct ht]
  have hxx : (j : Nat) ^^^ 2 ^ t ≠ (j : Nat) := xor_two_pow_ne _ t
  have hpres : ((j : Nat) ^^^ 2 ^ t).testBit c = (j : Nat).testBit c :=
    testBit_xor_other hct _
  by_cases hcj : (j : Nat).testBit c <;>
    by_cases hij : i = j <;>
      by_cases hijx : (i : Nat) = (j : Nat) ^^^ 2 ^ t <;>
        simp [hcj, hij, hijx, hpres, Fin.val_inj, Ne.symm hxx] <;>
        first
          | omega
          | norm_num

/-! ## §6. The Y_q basis action (for the selective-destruction branch). -/

private theorem opsMat_single_y (n : Nat) :
    ∀ (q : Nat), q < n → ∀ (i j : Fin (2 ^ n)),
      opsMat n (fun k => if q = k then Pauli.Y else Pauli.I) i j
        = if (i : Nat) = (j : Nat) ^^^ 2 ^ q
          then (if (j : Nat).testBit q then -Complex.I else Complex.I)
          else 0 := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
      intro q hq i j
      obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
      rw [opsMat_succ_apply]
      simp only [val_coe]
      cases q with
      | zero =>
          rw [show (fun i => if (0 : Nat) = i + 1 then Pauli.Y else Pauli.I)
                = (fun _ => Pauli.I) from by funext i; simp,
              opsMat_one, Matrix.one_apply, pow_zero]
          have hvi : (↑(finProdFinEquiv (i₁, i₂)) : Nat)
              = (i₂ : Nat) + 2 * (i₁ : Nat) := pair_val i₁ i₂
          have hvj : (↑(finProdFinEquiv (j₁, j₂)) : Nat)
              = (j₂ : Nat) + 2 * (j₁ : Nat) := pair_val j₁ j₂
          simp only [hvi, hvj, xor_one_split (j₁ : Nat) (j₂ : Nat) j₂.isLt,
            Nat.testBit_zero]
          have hi₂ := i₂.isLt
          have hj₂ := j₂.isLt
          by_cases h1 : (i₁ : Nat) = (j₁ : Nat) <;>
            fin_cases i₂ <;> fin_cases j₂ <;>
              simp [h1, Pauli.toMatrix, Fin.ext_iff] <;> omega
      | succ q' =>
          rw [show (fun i => if q' + 1 = i + 1 then Pauli.Y else Pauli.I)
                = (fun k => if q' = k then Pauli.Y else Pauli.I) from by
                  funext i; simp,
              ih q' (by omega),
              show (if q' + 1 = 0 then Pauli.Y else Pauli.I) = Pauli.I from rfl,
              Pauli.toMatrix_I_eq_one, Matrix.one_apply]
          have hvi : (↑(finProdFinEquiv (i₁, i₂)) : Nat)
              = (i₂ : Nat) + 2 * (i₁ : Nat) := pair_val i₁ i₂
          have hvj : (↑(finProdFinEquiv (j₁, j₂)) : Nat)
              = (j₂ : Nat) + 2 * (j₁ : Nat) := pair_val j₁ j₂
          have hbit : ((j₂ : Nat) + 2 * (j₁ : Nat)).testBit (q' + 1)
              = (j₁ : Nat).testBit q' := by
            rw [Nat.testBit_add_one]
            congr 1
            have := j₂.isLt
            omega
          simp only [hvi, hvj,
            xor_pow_succ_split (j₁ : Nat) (j₂ : Nat) j₂.isLt q', hbit]
          have hi₂ := i₂.isLt
          have hj₂ := j₂.isLt
          by_cases h1 : (i₁ : Nat) = (j₁ : Nat) ^^^ 2 ^ q' <;>
            by_cases h2 : (i₂ : Nat) = (j₂ : Nat) <;>
              simp [h1, h2, Fin.ext_iff] <;> omega

/-- **Y_q is the bit-flip permutation with the +-i phases.** -/
theorem axisMat_single_y_apply (n q : Nat) (hq : q < n) (i j : Fin (2 ^ n)) :
    axisMat n [(⟨q, .y⟩ : PFactor)] i j
      = if (i : Nat) = (j : Nat) ^^^ 2 ^ q
        then (if (j : Nat).testBit q then -Complex.I else Complex.I)
        else 0 := by
  unfold axisMat
  rw [show kindFn [(⟨q, .y⟩ : PFactor)]
        = (fun k => if q = k then Pauli.Y else Pauli.I) from by
      funext k
      rw [kindFn_single]
      by_cases h : q = k <;> simp [h, pkindToBQ]]
  exact opsMat_single_y n q hq i j

end FormalRV.PauliRotation
