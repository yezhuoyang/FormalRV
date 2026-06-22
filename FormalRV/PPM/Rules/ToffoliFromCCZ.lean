/-
  FormalRV.PPM.Rules.ToffoliFromCCZ — the Clifford reduction `CCX = H·CCZ·H`,
  turning the 8T→CCZ identity into the actual Toffoli gate, sorry-free.

  Combined with `EightTToCCZScheme.tDecompMat_eq_cczMat` (the seven-T
  phase polynomial equals `CCZ`), this proves that the Toffoli unitary
  is implemented by `H_c · (8T→CCZ) · H_c`, and that its action on a
  computational basis state is exactly the Boolean Toffoli permutation
  (flip the target iff both controls are set).

  ## Technique

  To avoid `√2` arithmetic inside a 64-entry matrix proof, we factor the
  Hadamard on the target qubit as `H = (1/√2)·H̄` with `H̄ = [[1,1],[1,-1]]`
  (integer entries).  Then

      H̄_c · CCZ · H̄_c = 2 · P     (P = the Toffoli permutation matrix)

  is a pure integer/ℂ identity proved by `fin_cases` + `simp`/`norm_num`
  (no `√2`), and the normalised statement follows by peeling the single
  scalar fact `(1/√2)² = 1/2`.
-/
import FormalRV.PPM.Rules.EightTToCCZScheme

namespace FormalRV.Framework.ToffoliFromCCZ

open scoped Matrix
open FormalRV.Framework.EightTToCCZ

/-! ## §1. The Toffoli permutation matrix on 3 qubits.

    Index `k = 4a+2b+c` (big-endian).  The Toffoli flips the low bit `c`
    iff both control bits `a,b` are set, i.e. it is the transposition of
    indices `6 = |110⟩` and `7 = |111⟩`. -/

/-- The Toffoli permutation on a 3-bit index: swap 6 ↔ 7, else identity. -/
def ccxPerm (k : Fin 8) : Fin 8 :=
  if k = 6 then 7 else if k = 7 then 6 else k

/-- The Toffoli permutation matrix (8×8 0/1 matrix). -/
noncomputable def ccxPermMat : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of (fun i j => if i = ccxPerm j then 1 else 0)

/-! ## §2. The unnormalised Hadamard on the target qubit. -/

/-- `H̄ = [[1,1],[1,-1]]` applied to the low (target) qubit of a 3-qubit
    register: `H̄_c (k,k') = [k/2 = k'/2] · H̄(k%2, k'%2)`. -/
noncomputable def Hbar3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of (fun k k' =>
    if k.val / 2 = k'.val / 2 then
      (if k.val % 2 = 1 ∧ k'.val % 2 = 1 then -1 else 1)
    else 0)

/-! ## §3. The integer core: `H̄·CCZ·H̄ = 2·P` (no √2). -/

theorem Hbar3_ccz_Hbar3 :
    Hbar3 * cczMat * Hbar3 = (2 : ℂ) • ccxPermMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Hbar3, cczMat, ccxPermMat, ccxPerm,
          Matrix.diagonal, Matrix.of_apply, Fin.sum_univ_eight] <;> norm_num

/-! ## §4. The normalised Clifford reduction `CCX = H·CCZ·H`. -/

/-- The real Hadamard on the target qubit, `H_c = (1/√2)·H̄_c`. -/
noncomputable def Had3 : Matrix (Fin 8) (Fin 8) ℂ :=
  ((1 : ℂ) / Real.sqrt 2) • Hbar3

theorem inv_sqrt2_sq : ((1 : ℂ) / Real.sqrt 2) * ((1 : ℂ) / Real.sqrt 2) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul]
  rw [show ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = ((Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) by
        push_cast; ring]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **`CCX = H_c · CCZ · H_c`.**  The Toffoli permutation matrix is the
    Hadamard-conjugated `CCZ`. -/
theorem had_ccz_had_eq_ccxPermMat :
    Had3 * cczMat * Had3 = ccxPermMat := by
  unfold Had3
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, inv_sqrt2_sq,
      Hbar3_ccz_Hbar3, smul_smul, show ((1:ℂ) / 2) * 2 = 1 by norm_num, one_smul]

/-- **8T→CCZ → Toffoli.**  The seven-T phase-polynomial gate, conjugated
    by Hadamards on the target, equals the Toffoli permutation.  This is
    the full chain: 8 T-gates ⟹ CCZ ⟹ (with two Cliffords) Toffoli. -/
theorem had_tDecomp_had_eq_ccxPermMat :
    Had3 * tDecompMat * Had3 = ccxPermMat := by
  rw [tDecompMat_eq_cczMat, had_ccz_had_eq_ccxPermMat]

/-! ## §5. Computational-basis action: the Toffoli permutation IS the
       Boolean Toffoli update. -/

/-- The decode `aOf/bOf/cOf` of `ccxPerm k` realises the Boolean Toffoli
    update on the three bits: the low bit `c` is flipped iff `a ∧ b`. -/
theorem ccxPerm_is_boolean_toffoli (k : Fin 8) :
    (aOf (ccxPerm k), bOf (ccxPerm k), cOf (ccxPerm k))
      = (aOf k, bOf k, xor (cOf k) (aOf k && bOf k)) := by
  fin_cases k <;> rfl

/-- The Toffoli permutation matrix sends basis vector `|k⟩` to
    `|ccxPerm k⟩` — i.e. it permutes computational basis states by the
    Toffoli map. -/
theorem ccxPermMat_mulVec_basis (k : Fin 8) :
    ccxPermMat *ᵥ (fun j => if j = k then (1 : ℂ) else 0)
      = (fun i => if i = ccxPerm k then (1 : ℂ) else 0) := by
  funext i
  simp only [Matrix.mulVec, ccxPermMat, Matrix.of_apply, dotProduct]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

end FormalRV.Framework.ToffoliFromCCZ
