/-
  FormalRV.SQIRPort.Eigenstate — modular-multiplier eigenstate
  infrastructure for the QPE orbit decomposition (Phase 4.A + 4.C).

  This module hosts the discrete-Fourier machinery that underlies the
  Shor orbit decomposition

      |1⟩_n  =  (1/√r) · ∑_{k<r} ψ_k                              (†)

  where the ψ_k are joint eigenstates of the modular-multiplier family
  `{U_{a^{2^i}}}` with phases `(2^i · k / r) mod 1`. The forward
  direction (4.A: building the ψ_k) and the inversion direction (4.C:
  recovering |1⟩_n from the ψ_k) both rely on the same finite-group
  Fourier orthogonality fact:

      ∑_{k<r} exp(2πi · j · k / r)  =  if j ≡ 0 mod r then r else 0.

  This file establishes that fact (`fourier_orthogonality_fin`) and
  derives the column-sum corollary that drives (†). Both are pure
  mathlib + complex analysis — no QuantumLib infrastructure required.
  Downstream consumers in `SQIRPort/Shor.lean` will use these to close
  the `h_orbit_exists` existential of
  `QPE_MMI_correct_assuming_orbit_factorization`.
-/

import Mathlib
import Mathlib.Logic.Equiv.Fin.Rotate
import FormalRV.Core.QuantumLib

namespace FormalRV.SQIRPort

open FormalRV.Framework

/-- **Finite Fourier orthogonality on `Fin r`** (Phase 4.C foundation).

For any `r ≥ 1` and any `j : Fin r`, the discrete-Fourier sum of
`r`-th roots of unity at character index `j` collapses:

    ∑_{k : Fin r} exp(2πi · j · k / r)  =  r  if  j = 0
                                          =  0  otherwise.

Standard finite-group Fourier orthogonality, specialized to the
cyclic group `Z/rZ`. The proof routes through `geom_sum_eq` (mathlib's
geometric-series closed form) plus three classical observations:

1. The character `z = exp(2πi · j / r)` is a non-trivial `r`-th root of
   unity when `0 < j < r` (so `z ≠ 1`).
2. `z^r = exp(2πi · j) = 1` for any natural `j`.
3. Therefore `∑_{k=0}^{r-1} z^k = (z^r - 1)/(z - 1) = 0/(z - 1) = 0`.

The `j = 0` branch is trivial — every summand is `exp(0) = 1`, sum is
`r` by `Fin.sum_const`. -/
theorem fourier_orthogonality_fin (r : Nat) (h_r : 0 < r) (j : Fin r) :
    (∑ k : Fin r, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                                (j.val * k.val : ℂ) / (r : ℂ)))
      = if j.val = 0 then (r : ℂ) else 0 := by
  by_cases h_j : j.val = 0
  · simp [h_j]
  · rw [if_neg h_j]
    set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                              (j.val : ℂ) / (r : ℂ)) with hz_def
    have h_r_C_ne : (r : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h_r
      exact_mod_cast this.ne'
    -- Step 1: each summand is z^k.val
    have h_summand : ∀ k : Fin r,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                     (j.val * k.val : ℂ) / (r : ℂ))
          = z ^ k.val := by
      intro k
      rw [hz_def, ← Complex.exp_nat_mul]
      congr 1
      field_simp
    simp_rw [h_summand]
    rw [Fin.sum_univ_eq_sum_range (fun k => z ^ k)]
    -- Step 2: z ≠ 1
    have h_z_ne : z ≠ 1 := by
      rw [hz_def]
      intro h_eq
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h_eq
      have h_pi_I_ne : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h_div : (j.val : ℂ) / (r : ℂ) = (n : ℂ) := by
        have : 2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) / (r : ℂ))
             = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
          calc 2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) / (r : ℂ))
              = 2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ) := by ring
            _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
            _ = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by ring
        exact mul_left_cancel₀ h_pi_I_ne this
      have h_jr : (j.val : ℂ) = (n : ℂ) * (r : ℂ) := by
        field_simp at h_div; linear_combination h_div
      have h_jr_Z : (j.val : ℤ) = n * r := by exact_mod_cast h_jr
      have h_j_pos : 0 < j.val := Nat.pos_of_ne_zero h_j
      have h_j_lt : j.val < r := j.isLt
      have h_rZ : (0 : ℤ) < r := by exact_mod_cast h_r
      rcases lt_trichotomy n 0 with h_neg | h_zero | h_pos
      · have h1 : n * r ≤ -1 * r :=
          Int.mul_le_mul_of_nonneg_right (by omega) h_rZ.le
        omega
      · subst h_zero; simp at h_jr_Z; omega
      · have h1 : 1 * r ≤ n * r :=
          Int.mul_le_mul_of_nonneg_right (by omega) h_rZ.le
        omega
    -- Step 3: z^r = 1
    have h_z_pow_r : z ^ r = 1 := by
      rw [hz_def, ← Complex.exp_nat_mul]
      have h_eq : ((r : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I *
                                    (j.val : ℂ) / (r : ℂ))
                = ((j.val : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
      rw [h_eq, Complex.exp_nat_mul_two_pi_mul_I]
    -- Step 4: geometric series collapses to 0
    rw [geom_sum_eq h_z_ne r, h_z_pow_r, sub_self, zero_div]

/-! ## Character-vector building blocks for the modular-multiplier eigenstates

The Shor eigenstate ψ_k is constructed as a sum-weighted basis-state
combination

    ψ_k(y)  =  (1/√r) · ∑_{j<r}  exp(-2πi·jk/r) · [y = a^j mod N]

over the modular orbit `{a^j mod N : j < r}`. Its orthonormality
properties decompose into two layers:

1. The **character vectors** `e_k : Fin r → ℂ`,
   `e_k(j) := (1/√r) · exp(-2πi·jk/r)`, form an orthonormal family
   under the standard ℓ² inner product on `Fin r`.
2. The orbit `{a^j mod N : j < r}` consists of `r` distinct values
   (under coprimality + `Order a r N`), turning the basis-state sum
   into a pointwise-disjoint family.

This section establishes layer (1) — the abstract character-vector
orthonormality — independent of the modular-orbit structure. Layer
(2) and the final eigenstate assembly are deferred to later ticks.

This tick (2026-05-24 16:35) closes the **diagonal case** `k = k'`:
each character vector has unit ℓ²-norm. The proof reduces to
`|exp(iθ)| = 1` plus the trivial sum `r · (1/r) = 1`. The
off-diagonal case (`k ≠ k'` ⟹ `⟨e_k|e_k'⟩ = 0`) reduces to
`fourier_orthogonality_fin` above and is the next-tick deliverable. -/

/-- **Character vector** `e_k(j) := (1/√r) · exp(-2πi·jk/r)`.
This is the `j`-th component of the `k`-th Shor character vector,
to be combined later with the orbit `[y = a^j mod N]` indicator
to form the full modular-multiplier eigenstate `ψ_k(y)`. -/
noncomputable def character_vector (r : Nat) (k j : Fin r) : ℂ :=
  (1 / (Real.sqrt r : ℂ)) *
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j.val * k.val : ℂ)) /
                 (r : ℂ))

/-- **Diagonal orthonormality of the character vectors** (Phase 4.A,
diagonal case).

For each `k : Fin r` with `r > 0`, the ℓ²-norm of `character_vector r k`
on `Fin r` equals 1:

    ∑_{j : Fin r}  ‖e_k(j)‖²  =  1.

Proof: every summand has `‖exp(-2πi·jk/r)‖² = 1` (the exponent is
purely imaginary), so the summand collapses to `1/r`, and the sum
of `r` copies of `1/r` is `1`. Uses `Complex.norm_exp_I_mul_ofReal`. -/
theorem character_vector_diagonal_norm_sum
    (r : Nat) (h_r : 0 < r) (k : Fin r) :
    (∑ j : Fin r, Complex.normSq (character_vector r k j))
      = 1 := by
  unfold character_vector
  have h_rR : (0 : ℝ) < r := by exact_mod_cast h_r
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr h_rR
  have h_sqrt_ne : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_pos.ne'
  have h_normSq_sqrt : Complex.normSq ((Real.sqrt r : ℝ) : ℂ) = r := by
    rw [Complex.normSq_ofReal]
    exact Real.mul_self_sqrt h_rR.le
  have h_summand : ∀ j : Fin r,
      Complex.normSq
        (((1 / (Real.sqrt r : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k.val : ℂ)) / (r : ℂ))))
        = 1 / (r : ℝ) := by
    intro j
    have h_arg : -(2 * (Real.pi : ℂ) * Complex.I * (j.val * k.val : ℂ)) /
                 (r : ℂ)
                 = Complex.I *
                   ((-(2 * Real.pi * (j.val * k.val : ℝ) / r) : ℝ) : ℂ) := by
      push_cast; ring
    rw [map_mul, h_arg]
    have h_exp_normSq :
        Complex.normSq
          (Complex.exp (Complex.I *
            ((-(2 * Real.pi * (j.val * k.val : ℝ) / r) : ℝ) : ℂ))) = 1 := by
      rw [show Complex.normSq _ = ‖Complex.exp (Complex.I *
            ((-(2 * Real.pi * (j.val * k.val : ℝ) / r) : ℝ) : ℂ))‖^2 from
            (Complex.sq_norm _).symm]
      rw [Complex.norm_exp_I_mul_ofReal, one_pow]
    rw [h_exp_normSq, mul_one, map_div₀, map_one, h_normSq_sqrt]
  rw [Finset.sum_congr rfl (fun j _ => h_summand j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Negative-character Fourier orthogonality** (Phase 4.A off-diagonal
support). Companion to `fourier_orthogonality_fin`:

    ∑_{k : Fin r} exp(-2πi · j · k / r) = if j.val = 0 then r else 0.

Same statement as the positive-character form with the sign flipped on
the exponent. Proof: rewrite each summand as the complex conjugate of
the positive-character summand (via `Complex.exp_conj` + `Complex.conj_I`),
pull the conjugate out of the sum (`map_sum`), and apply
`fourier_orthogonality_fin`. The case split on `j.val = 0` handles
`conj r = r` vs `conj 0 = 0`. -/
theorem fourier_orthogonality_fin_neg (r : Nat) (h_r : 0 < r) (j : Fin r) :
    (∑ k : Fin r, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                                  (j.val * k.val : ℂ) / (r : ℂ))))
      = if j.val = 0 then (r : ℂ) else 0 := by
  have h_conj : ∀ k : Fin r,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                      (j.val * k.val : ℂ) / (r : ℂ)))
        = starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                                       (j.val * k.val : ℂ) / (r : ℂ))) := by
    intro k
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I, Complex.conj_ofNat]
    ring
  simp_rw [h_conj, ← map_sum]
  rw [fourier_orthogonality_fin r h_r j]
  by_cases h_j : j.val = 0 <;> simp [h_j]

/-- **Off-diagonal orthogonality of the character vectors** (Phase 4.A,
off-diagonal case).

For distinct `k ≠ k' : Fin r`, the ℓ² inner product `⟨e_k' | e_k⟩`
vanishes:

    ∑_{j : Fin r}  conj(e_k'(j)) · e_k(j)  =  0.

Combined with `character_vector_diagonal_norm_sum`, this establishes
the full orthonormality of the family `{e_k : k : Fin r}` — the
abstract Layer-(1) prerequisite for the Shor eigenstate construction.

Proof outline:
1. Pull out the `(1/r)` prefactor and combine each summand's two
   exponentials into a single `exp(2πi · j · (k' - k) / r)` via
   `Complex.exp_conj` (handles the conj on `e_k'`) plus `Complex.exp_add`.
2. Case-split on `sign(k.val - k'.val)`:
   - `k.val < k'.val`: let `d := k'.val - k.val ∈ (0, r)`. Apply
     `fourier_orthogonality_fin` at `⟨d, _⟩` to conclude the inner
     sum is `0`.
   - `k.val > k'.val`: let `d := k.val - k'.val ∈ (0, r)`. Rewrite the
     summand as `exp(-2πi · j · d / r)` and apply
     `fourier_orthogonality_fin_neg`.

Total length ~70 lines; the bulk is algebraic manipulation of the
conjugate + prefactor combination. -/
theorem character_vector_orthogonality (r : Nat) (h_r : 0 < r)
    (k k' : Fin r) (h_ne : k ≠ k') :
    (∑ j : Fin r, starRingEnd ℂ (character_vector r k' j) *
                  character_vector r k j) = 0 := by
  unfold character_vector
  have h_rR : (0 : ℝ) < r := by exact_mod_cast h_r
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr h_rR
  have h_sqrt_ne : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_pos.ne'
  have h_sqrt_sq : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    norm_cast; exact Real.mul_self_sqrt h_rR.le
  -- Step 1: collapse each summand to (1/r) · exp(2πi · j · (k' - k) / r).
  have h_each : ∀ j : Fin r,
      starRingEnd ℂ ((1 / (Real.sqrt r : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k'.val : ℂ)) / (r : ℂ))) *
        ((1 / (Real.sqrt r : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k.val : ℂ)) / (r : ℂ)))
        = (1 / (r : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                                        ((j.val * k'.val : ℂ) -
                                         (j.val * k.val : ℂ)) /
                                        (r : ℂ)) := by
    intro j
    rw [map_mul, map_div₀, map_one, Complex.conj_ofReal,
        ← Complex.exp_conj]
    have h_conj_arg :
        starRingEnd ℂ (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k'.val : ℂ)) / (r : ℂ))
          = 2 * (Real.pi : ℂ) * Complex.I * (j.val * k'.val : ℂ) /
            (r : ℂ) := by
      simp [Complex.conj_I, Complex.conj_ofNat, Complex.conj_ofReal]
    rw [h_conj_arg]
    have h_combine :
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                      (j.val * k'.val : ℂ) / (r : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k.val : ℂ)) / (r : ℂ))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                          ((j.val * k'.val : ℂ) -
                           (j.val * k.val : ℂ)) / (r : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h_prefactor :
        (1 / (Real.sqrt r : ℂ)) * (1 / (Real.sqrt r : ℂ)) = 1 / (r : ℂ) := by
      rw [div_mul_div_comm, mul_one, h_sqrt_sq]
    calc (1 / (Real.sqrt r : ℂ)) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k'.val : ℂ) / (r : ℂ)) *
          ((1 / (Real.sqrt r : ℂ)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ)) / (r : ℂ)))
        = ((1 / (Real.sqrt r : ℂ)) * (1 / (Real.sqrt r : ℂ))) *
            (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k'.val : ℂ) / (r : ℂ)) *
             Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ)) / (r : ℂ))) := by ring
      _ = (1 / (r : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                                         ((j.val * k'.val : ℂ) -
                                          (j.val * k.val : ℂ)) /
                                         (r : ℂ)) := by
              rw [h_prefactor, h_combine]
  rw [Finset.sum_congr rfl (fun j _ => h_each j), ← Finset.mul_sum]
  -- Step 2: case split on sign(k.val - k'.val) and apply Fourier orthog.
  have h_kne : k.val ≠ k'.val := fun h => h_ne (Fin.ext h)
  rcases lt_or_gt_of_ne h_kne with h_lt | h_gt
  · set d : Nat := k'.val - k.val with hd_def
    have h_d_pos : 0 < d := Nat.sub_pos_of_lt h_lt
    have h_d_lt : d < r := Nat.lt_of_le_of_lt (Nat.sub_le _ _) k'.isLt
    have h_replace : ∀ j : Fin r,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                      ((j.val * k'.val : ℂ) - (j.val * k.val : ℂ)) /
                      (r : ℂ))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                          ((d : ℕ) * j.val : ℂ) / (r : ℂ)) := by
      intro j
      congr 1
      have h_d_C : ((d : ℕ) : ℂ) = (k'.val : ℂ) - (k.val : ℂ) := by
        rw [hd_def]; exact Nat.cast_sub h_lt.le
      rw [h_d_C]; ring
    rw [Finset.sum_congr rfl (fun j _ => h_replace j)]
    rw [fourier_orthogonality_fin r h_r ⟨d, h_d_lt⟩]
    simp [h_d_pos.ne']
  · set d : Nat := k.val - k'.val with hd_def
    have h_d_pos : 0 < d := Nat.sub_pos_of_lt h_gt
    have h_d_lt : d < r := Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt
    have h_replace : ∀ j : Fin r,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                      ((j.val * k'.val : ℂ) - (j.val * k.val : ℂ)) /
                      (r : ℂ))
          = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            ((d : ℕ) * j.val : ℂ) / (r : ℂ))) := by
      intro j
      congr 1
      have h_d_C : ((d : ℕ) : ℂ) = (k.val : ℂ) - (k'.val : ℂ) := by
        rw [hd_def]; exact Nat.cast_sub h_gt.le
      rw [show ((j.val * k'.val : ℂ) - (j.val * k.val : ℂ))
            = -((k.val : ℂ) - (k'.val : ℂ)) * j.val from by ring]
      rw [← h_d_C]; ring
    rw [Finset.sum_congr rfl (fun j _ => h_replace j)]
    rw [fourier_orthogonality_fin_neg r h_r ⟨d, h_d_lt⟩]
    simp [h_d_pos.ne']

/-! ## Modular-multiplier eigenstate construction (Phase 4.A)

With the abstract character-vector orthonormality (`character_vector_*`
lemmas above) now in place, we assemble the Shor eigenstate

    ψ_k(y)  =  (1/√r) · ∑_{j<r}  exp(-2πi·jk/r) · [y = a^j mod N]
            =  ∑_{j<r}  character_vector r k j · [y = a^j mod N]

This is a `Matrix (Fin (2^n)) (Fin 1) ℂ` column vector for the
`n`-qubit data register. Its full orthonormality

    ⟨ψ_k | ψ_k'⟩  =  δ_{kk'}

reduces to two pieces:

1. **Character orthonormality** (`character_vector_diagonal_norm_sum`
   + `character_vector_orthogonality`): the coefficient family
   `{e_k(·) : k : Fin r}` is orthonormal as a family of `ℂ`-valued
   functions on `Fin r`. — *Closed in earlier ticks (2026-05-24 16:28
   and 16:44).*
2. **Orbit distinctness**: the modular orbit `{a^j mod N : j : Fin r}`
   consists of `r` distinct elements when `Order a r N` and
   `gcd(a, N) = 1` hold. — *Future tick.*

This tick (2026-05-24 16:48) delivers piece (0): the **definition**
of `modmult_eigenstate` and its trivial **off-orbit support** lemma
— `ψ_k(y) = 0` whenever `y` is not in the orbit, regardless of
orbit-distinctness. Two future ticks will (a) prove orbit distinctness
from `Order a r N`, (b) combine with character orthonormality to
deliver the headline `modmult_eigenstate_orthonormal` theorem. -/

/-- **Modular-multiplier (Shor) eigenstate** `ψ_k` on the `n`-qubit
data register.

For each `k : Fin r`, the `y`-th amplitude is the sum over the orbit
of `a` mod `N` of the `k`-th character weighting:

    ψ_k(y) := ∑_{j : Fin r} character_vector r k j · [y = a^j mod N].

When the orbit `{a^j mod N : j : Fin r}` is non-degenerate, this is
a joint eigenstate of the modular-multiplier family `U_{a^{2^i}}` with
eigenvalue `exp(2πi · 2^i · k / r)`. The non-degeneracy hypothesis is
encoded downstream via the user's `Order a r N` assumption rather
than baked into the def. -/
noncomputable def modmult_eigenstate (a r N n : Nat) (k : Fin r) :
    Matrix (Fin (2^n)) (Fin 1) ℂ :=
  fun y _ =>
    ∑ j : Fin r, character_vector r k j *
      (if y.val = a^j.val % N then 1 else 0)

/-- **Off-orbit support**: if `y` is not in the modular orbit (i.e., for
no `j : Fin r` does `y.val = a^j mod N`), then `ψ_k(y) = 0`.

Trivial consequence of the definition: every summand is zero because
its indicator is `0`. Does NOT depend on `Order a r N` or orbit
distinctness — purely structural. -/
theorem modmult_eigenstate_off_orbit_zero
    (a r N n : Nat) (k : Fin r) (y : Fin (2^n)) (j_dummy : Fin 1)
    (h_off : ∀ j : Fin r, y.val ≠ a^j.val % N) :
    modmult_eigenstate a r N n k y j_dummy = 0 := by
  unfold modmult_eigenstate
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (h_off j), mul_zero]

/-- **On-orbit unique-match support**: if `y = a^{j0} mod N` for some
`j0 : Fin r` AND `j0` is the unique such index in `Fin r` (no other
`j : Fin r` satisfies `y = a^j mod N`), then `ψ_k(y) = character_vector
r k j0`.

This lemma factors the value of `ψ_k` on the orbit through the
single character-vector coefficient at the orbit-index position. The
uniqueness hypothesis is the natural shape produced by the orbit-
distinctness lemma (forthcoming): under `Order a r N` + `gcd(a, N) = 1`,
the orbit has exactly `r` distinct elements, so each `y` in the orbit
matches a unique `j : Fin r`. -/
theorem modmult_eigenstate_on_orbit_unique
    (a r N n : Nat) (k : Fin r) (y : Fin (2^n)) (j_dummy : Fin 1)
    (j0 : Fin r) (h_match : y.val = a^j0.val % N)
    (h_unique : ∀ j : Fin r, y.val = a^j.val % N → j = j0) :
    modmult_eigenstate a r N n k y j_dummy = character_vector r k j0 := by
  unfold modmult_eigenstate
  rw [Finset.sum_eq_single j0]
  · rw [if_pos h_match, mul_one]
  · intros j _ h_j_ne
    by_cases h : y.val = a^j.val % N
    · exact absurd (h_unique j h) h_j_ne
    · rw [if_neg h, mul_zero]
  · intro h_no
    exact absurd (Finset.mem_univ j0) h_no

/-! ## Orbit distinctness (Phase 4.A layer-2)

Under the multiplicative order hypothesis `Order a r N`
(unpacked here as `h_arN : a^r % N = 1` + minimality), the modular
orbit `{a^j mod N : j : Fin r}` consists of `r` distinct elements.
This is the second prerequisite (Layer 2) for the full
`modmult_eigenstate` orthonormality theorem; combined with the
already-closed Layer 1 (character_vector orthonormality), it will
discharge `⟨ψ_k | ψ_k'⟩ = δ_{kk'}`. -/

/-- **Coprimality of `a` and `N` from the order hypothesis.**

If `a^r % N = 1` with `r > 0`, then `gcd(a, N) = 1`. Standard:
`gcd a N ∣ a` and `gcd a N ∣ N`, so `gcd a N ∣ a^r`, hence
`gcd a N ∣ a^r % N = 1`. -/
theorem coprime_of_pow_mod_eq_one (a r N : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1) :
    Nat.gcd a N = 1 := by
  have h1 : Nat.gcd a N ∣ a := Nat.gcd_dvd_left a N
  have h2 : Nat.gcd a N ∣ N := Nat.gcd_dvd_right a N
  have h3 : Nat.gcd a N ∣ a^r := dvd_pow h1 (Nat.pos_iff_ne_zero.mp h_r_pos)
  have h4 : Nat.gcd a N ∣ a^r % N := (Nat.dvd_mod_iff h2).mpr h3
  rw [h_arN] at h4
  exact Nat.eq_one_of_dvd_one h4

/-- **Modular orbit injectivity** (Phase 4.A layer-2).

Under the order hypothesis `Order a r N` (unpacked into `h_r_pos`,
`h_arN`, `h_min`) and `1 < N`, the modular-orbit map
`j : Fin r ↦ a^j.val % N` is injective.

Proof: WLOG `j.val ≤ j'.val`. From `a^j ≡ a^j' [MOD N]`, multiply
both sides by `1 = (a^j) · (a^j)⁻¹` (which exists in `ZMod N`
because `gcd a N = 1`) to derive `a^(j'-j) ≡ 1 [MOD N]`. Then
either `j' = j` (the desired conclusion), or `0 < j' - j < r` —
contradicting the minimality clause `h_min` of the `Order`
hypothesis. -/
theorem modmult_orbit_injective (a r N : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1) (h_N : 1 < N) :
    Function.Injective (fun j : Fin r => a^j.val % N) := by
  have h_coprime_aN : Nat.gcd a N = 1 :=
    coprime_of_pow_mod_eq_one a r N h_r_pos h_arN
  -- Reduction: from a^k ≡ a^k' [MOD N] with k ≤ k', derive a^(k'-k) ≡ 1.
  have h_reduce : ∀ k k' : Nat, k ≤ k' →
      a^k % N = a^k' % N → a^(k' - k) % N = 1 := by
    intros k k' h_le h_eq
    have h_split : a^k' = a^k * a^(k' - k) := by
      rw [← pow_add, Nat.add_sub_cancel' h_le]
    have h_modeq : a^k * 1 ≡ a^k * a^(k' - k) [MOD N] := by
      rw [mul_one, h_split.symm]; exact h_eq
    have h_coprime_pow : Nat.gcd N (a^k) = 1 := by
      rw [Nat.gcd_comm]
      exact Nat.Coprime.pow_left k h_coprime_aN
    have h_cancel : 1 ≡ a^(k' - k) [MOD N] :=
      Nat.ModEq.cancel_left_of_coprime h_coprime_pow h_modeq
    have h_mod : a^(k' - k) % N = 1 % N := h_cancel.symm
    rw [Nat.one_mod_eq_one.mpr h_N.ne'] at h_mod
    exact h_mod
  intros j j' h_eq
  simp only at h_eq
  rcases le_total j.val j'.val with h_le | h_le
  · set d := j'.val - j.val
    have h_d_pow : a^d % N = 1 :=
      h_reduce j.val j'.val h_le h_eq
    by_cases h_d_zero : d = 0
    · apply Fin.ext; omega
    · exact absurd h_d_pow (h_min d (Nat.pos_of_ne_zero h_d_zero)
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _) j'.isLt))
  · set d := j.val - j'.val
    have h_d_pow : a^d % N = 1 :=
      h_reduce j'.val j.val h_le h_eq.symm
    by_cases h_d_zero : d = 0
    · apply Fin.ext; omega
    · exact absurd h_d_pow (h_min d (Nat.pos_of_ne_zero h_d_zero)
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt))

/-! ## Orthonormality assembly helpers (Phase 4.A finale)

These helpers package the indicator-sum + orbit-injectivity step that
appears inside the headline `modmult_eigenstate_orthonormal` proof.
Pulled out as named lemmas so the headline assembly stays readable. -/

/-- **Indicator-product sum on `Fin (2^n)`**: for any `v < 2^n` and
arbitrary `v'`,

    ∑_{y : Fin (2^n)}  [y = v] · [y = v']  =  if v = v' then 1 else 0.

If `v = v'`, only `y = ⟨v, _⟩` contributes (giving `1·1 = 1`). If
`v ≠ v'`, no `y` matches both indicators, so the sum is `0`. -/
theorem indicator_product_sum_pow_two (n v v' : Nat) (h_v_lt : v < 2^n) :
    (∑ y : Fin (2^n), (if y.val = v then (1 : ℂ) else 0) *
                      (if y.val = v' then (1 : ℂ) else 0))
      = if v = v' then 1 else 0 := by
  by_cases h_eq : v = v'
  · subst h_eq
    rw [Finset.sum_eq_single (⟨v, h_v_lt⟩ : Fin (2^n))]
    · simp
    · intros y _ h_ne
      have : y.val ≠ v := fun h => h_ne (Fin.ext h)
      rw [if_neg this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg h_eq]
    apply Finset.sum_eq_zero
    intros y _
    by_cases h1 : y.val = v
    · have h2 : y.val ≠ v' := fun heq => h_eq (h1 ▸ heq)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **Orbit-indicator bilinear orthogonality** (composite of
`indicator_product_sum_pow_two` and `modmult_orbit_injective`):

    ∑_{y : Fin (2^n)}  [y = a^j%N] · [y = a^{j'}%N]
        =  if j = j' then 1 else 0    (for j, j' : Fin r).

Combines the pure indicator-product sum with the orbit-distinctness
fact that `a^j%N = a^{j'}%N ⟺ j = j'` under `Order a r N`. This is
the inner-sum identity that drives the headline
`modmult_eigenstate_orthonormal` proof — pulled out so the assembly
stays under one screenful. -/
theorem orbit_indicator_bilinear_orth (a r N n : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n)
    (j j' : Fin r) :
    (∑ y : Fin (2^n),
      (if y.val = a^j.val % N then (1 : ℂ) else 0) *
      (if y.val = a^j'.val % N then (1 : ℂ) else 0))
      = if j = j' then 1 else 0 := by
  have h_j_lt : a^j.val % N < 2^n := by
    calc a^j.val % N < N := Nat.mod_lt _ (by omega : 0 < N)
      _ ≤ 2^n := h_N_lt
  rw [indicator_product_sum_pow_two n (a^j.val % N) (a^j'.val % N) h_j_lt]
  have h_inj := modmult_orbit_injective a r N h_r_pos h_arN h_min h_N
  by_cases h : j = j'
  · simp [h]
  · have h_ne : a^j.val % N ≠ a^j'.val % N := fun h_eq => h (h_inj h_eq)
    simp [h, h_ne]

/-! ## Headline: `modmult_eigenstate_orthonormal` (Phase 4.A complete)

The family `{ψ_k : k : Fin r}` of Shor eigenstates is orthonormal as
column vectors on the `n`-qubit data register, under the standing
hypotheses

  • `Order a r N`: the order of `a` mod `N` is exactly `r`,
  • `1 < N` (rules out the degenerate modulus),
  • `N ≤ 2^n` (the orbit fits inside the `n`-qubit register).

The proof structure (per the docstring of `modmult_eigenstate`):

  1. Pointwise rewrite ⟨ψ_k'(y) | ψ_k(y)⟩ as a `Fintype.sum_mul_sum`
     bilinear expansion over the two `Fin r` summation indices, with
     the indicator-pair `[y = a^j%N] · [y = a^{j'}%N]` as the inner
     factor.
  2. Swap the order `∑_y ∑_j ∑_{j'} → ∑_j ∑_{j'} ∑_y` via
     `Finset.sum_comm` twice; pull the `y`-independent factor
     `conj(e_{k'}(j)) · e_k(j')` out of the inner sum via
     `Finset.mul_sum`.
  3. Reduce the inner `∑_y [y=a^j%N][y=a^{j'}%N]` to `[j = j']` via
     `orbit_indicator_bilinear_orth`.
  4. Collapse `∑_{j'} (...) · [j = j']` to its `j' = j` value.
  5. Final `∑_j conj(e_{k'}(j)) · e_k(j) = δ_{kk'}` from
     `character_vector_diagonal_norm_sum` (k = k' case) or
     `character_vector_orthogonality` (k ≠ k' case). -/

/-- **Modular-multiplier eigenstate orthonormality** (Phase 4.A
headline / Layer-(1) × Layer-(2) combined):

    ⟨ψ_{k'} | ψ_k⟩_{Fin (2^n)}  =  if k = k' then 1 else 0.

Assembles the character-vector orthonormality (`character_vector_*`)
with the orbit-distinctness fact (`modmult_orbit_injective`) via the
bilinear-indicator helper (`orbit_indicator_bilinear_orth`). This is
the column-vector / data-register version; the combined-register
extension (kron with ancilla) is the next-tick deliverable. -/
theorem modmult_eigenstate_orthonormal (a r N n : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n)
    (k k' : Fin r) :
    (∑ y : Fin (2^n), starRingEnd ℂ (modmult_eigenstate a r N n k' y 0) *
                      modmult_eigenstate a r N n k y 0)
      = if k = k' then 1 else 0 := by
  -- Step 1: pointwise expansion of each ⟨ψ_k'(y) | ψ_k(y)⟩.
  have h_pointwise : ∀ y : Fin (2^n),
      starRingEnd ℂ (modmult_eigenstate a r N n k' y 0) *
      modmult_eigenstate a r N n k y 0
        = ∑ j : Fin r, ∑ j' : Fin r,
            (starRingEnd ℂ (character_vector r k' j) *
             character_vector r k j') *
            ((if y.val = a^j.val % N then (1 : ℂ) else 0) *
             (if y.val = a^j'.val % N then (1 : ℂ) else 0)) := by
    intro y
    unfold modmult_eigenstate
    rw [map_sum]
    have h_conj_summand : ∀ j : Fin r,
        starRingEnd ℂ (character_vector r k' j *
                       (if y.val = a^j.val % N then (1 : ℂ) else 0))
          = starRingEnd ℂ (character_vector r k' j) *
            (if y.val = a^j.val % N then (1 : ℂ) else 0) := by
      intro j
      rw [map_mul]
      congr 1
      by_cases h : y.val = a^j.val % N
      · simp [h]
      · simp [h]
    simp_rw [h_conj_summand]
    rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    ring
  -- Step 2: rewrite the outer goal using pointwise + swap orders.
  rw [show (∑ y : Fin (2^n),
            starRingEnd ℂ (modmult_eigenstate a r N n k' y 0) *
            modmult_eigenstate a r N n k y 0)
        = ∑ j : Fin r, ∑ j' : Fin r,
            (starRingEnd ℂ (character_vector r k' j) *
             character_vector r k j') *
            (∑ y : Fin (2^n),
              (if y.val = a^j.val % N then (1 : ℂ) else 0) *
              (if y.val = a^j'.val % N then (1 : ℂ) else 0)) from ?_]
  · -- Step 3: apply orbit_indicator_bilinear_orth pointwise.
    have h_inner : ∀ j j' : Fin r,
        (∑ y : Fin (2^n),
          (if y.val = a^j.val % N then (1 : ℂ) else 0) *
          (if y.val = a^j'.val % N then (1 : ℂ) else 0))
          = if j = j' then 1 else 0 :=
      fun j j' =>
        orbit_indicator_bilinear_orth a r N n
          h_r_pos h_arN h_min h_N h_N_lt j j'
    simp_rw [h_inner]
    -- Step 4: collapse the ∑_{j'} with [j = j'] indicator.
    have h_collapse : ∀ j : Fin r,
        (∑ j' : Fin r,
          starRingEnd ℂ (character_vector r k' j) *
          character_vector r k j' *
          (if j = j' then (1 : ℂ) else 0))
          = starRingEnd ℂ (character_vector r k' j) *
            character_vector r k j := by
      intro j
      rw [Finset.sum_eq_single j]
      · simp
      · intros j' _ h_ne
        rw [if_neg (Ne.symm h_ne), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun j _ => h_collapse j)]
    -- Step 5: final reduction to character orthonormality.
    by_cases h_kk : k = k'
    · subst h_kk
      rw [if_pos rfl]
      have h_eq : (∑ j : Fin r,
          starRingEnd ℂ (character_vector r k j) *
          character_vector r k j)
          = ∑ j : Fin r, (Complex.normSq (character_vector r k j) : ℂ) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [mul_comm]
        exact Complex.mul_conj _
      rw [h_eq]
      exact_mod_cast character_vector_diagonal_norm_sum r h_r_pos k
    · rw [if_neg h_kk]
      exact character_vector_orthogonality r h_r_pos k k' h_kk
  · -- The swap-step rewrite assembly:
    -- ∑_y ⟨ψ_k'(y) | ψ_k(y)⟩ = ∑_j ∑_{j'} ... · (∑_y indicator)
    rw [Finset.sum_congr rfl (fun y _ => h_pointwise y)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [← Finset.mul_sum]

/-! ## Combined-register extension (Phase 4.A → β family for h_orbit_exists)

The data-register eigenstate `modmult_eigenstate a r N n k` is combined
with the all-zeros ancilla state `kron_zeros anc` to produce a vector
on the full `(n + anc)`-qubit register. This is the exact shape needed
for the `β` family in
`QPE_MMI_correct_assuming_orbit_factorization`'s `h_orbit_exists`
existential.

The combined-register orthonormality follows by tensor-product
bilinearity: `⟨ψ_k' ⊗ |0⟩ | ψ_k ⊗ |0⟩⟩ = ⟨ψ_k' | ψ_k⟩ · ⟨0|0⟩
= δ_{kk'} · 1 = δ_{kk'}`. Two small helpers (`kron_vec_inner_split`
and `kron_zeros_self_inner_eq_one`) capture the bilinearity step; the
headline combines them with `modmult_eigenstate_orthonormal`. -/

/-- **Combined-register Shor eigenstate** `ψ_k ⊗ |0...0⟩_anc`. The
data-register eigenstate `modmult_eigenstate a r N n k` extended to
the full `(n + anc)`-qubit register by tensoring with the all-zeros
ancilla state. Provides the `β k` family for `h_orbit_exists`. -/
noncomputable def modmult_eigenstate_combined (a r N n anc : Nat) (k : Fin r) :
    Matrix (Fin (2^(n+anc))) (Fin 1) ℂ :=
  kron_vec (modmult_eigenstate a r N n k) (kron_zeros anc)

/-- **Tensor-product inner-product factorization**: the bilinear inner
product over `Fin (2^(a+b))` of two kron_vec products factors as the
product of inner products on `Fin (2^a)` and `Fin (2^b)`. Standard
`⟨α'⊗β' | α⊗β⟩ = ⟨α'|α⟩ · ⟨β'|β⟩`.

Proof uses the `kronEquiv` reindexing + `Fintype.sum_prod_type` +
`Finset.sum_mul_sum`. -/
theorem kron_vec_inner_split {a b : Nat}
    (α α' : Matrix (Fin (2^a)) (Fin 1) ℂ)
    (β β' : Matrix (Fin (2^b)) (Fin 1) ℂ) :
    (∑ i : Fin (2^(a+b)),
      starRingEnd ℂ (kron_vec α' β' i 0) * kron_vec α β i 0)
      = (∑ j : Fin (2^a), starRingEnd ℂ (α' j 0) * α j 0) *
        (∑ k : Fin (2^b), starRingEnd ℂ (β' k 0) * β k 0) := by
  have reindex : ∑ i : Fin (2^(a+b)),
        starRingEnd ℂ (kron_vec α' β' i 0) * kron_vec α β i 0
      = ∑ p : Fin (2^a) × Fin (2^b),
          starRingEnd ℂ (kron_vec α' β' (kron_vec_combine p.1 p.2) 0) *
          kron_vec α β (kron_vec_combine p.1 p.2) 0 :=
    (Fintype.sum_equiv (kronEquiv a b) _ _ (fun _ => rfl)).symm
  rw [reindex]
  simp_rw [kron_vec_apply_combine, map_mul]
  rw [Fintype.sum_prod_type]
  refine Eq.trans ?_ (Finset.sum_mul_sum _ _ _ _).symm
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

/-- **Self-inner-product of `kron_zeros anc` equals 1**: the all-zeros
basis state is unit-norm. `∑_k ‖[k=0]‖² = 1` collapses via
`Finset.sum_eq_single` at the single nonzero index. -/
theorem kron_zeros_self_inner_eq_one (anc : Nat) :
    (∑ k : Fin (2^anc),
      starRingEnd ℂ (kron_zeros anc k 0) * kron_zeros anc k 0) = 1 := by
  unfold kron_zeros
  rw [Finset.sum_eq_single (⟨0, Nat.two_pow_pos anc⟩ : Fin (2^anc))]
  · simp [basis_vector]
  · intros k _ h_ne
    have h_k_ne : k.val ≠ 0 := fun h => h_ne (Fin.ext h)
    rw [basis_vector_apply_ne _ _ _ _ h_k_ne, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Combined-register eigenstate orthonormality** (Phase 4.A combined
form). The β family for `h_orbit_exists` is orthonormal on
`Fin (2^(n+anc))`:

    ⟨β_{k'} | β_k⟩  =  δ_{kk'}

where `β_k = modmult_eigenstate a r N n k ⊗ kron_zeros anc`.

Proof: bilinear inner-product factorization via `kron_vec_inner_split`,
then collapse the ancilla factor via `kron_zeros_self_inner_eq_one`,
then dispatch to `modmult_eigenstate_orthonormal` for the data-register
factor. Three-line proof. -/
theorem modmult_eigenstate_combined_orthonormal (a r N n anc : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n)
    (k k' : Fin r) :
    (∑ i : Fin (2^(n+anc)),
      starRingEnd ℂ (modmult_eigenstate_combined a r N n anc k' i 0) *
      modmult_eigenstate_combined a r N n anc k i 0)
      = if k = k' then 1 else 0 := by
  unfold modmult_eigenstate_combined
  rw [kron_vec_inner_split, kron_zeros_self_inner_eq_one, mul_one,
      modmult_eigenstate_orthonormal a r N n h_r_pos h_arN h_min h_N
        h_N_lt k k']

/-! ## Orbit decomposition (Phase 4.C)

The headline of Phase 4.C: the basis state `|1⟩_n` admits the inverse-
Fourier decomposition

    |1⟩_n  =  (1/√r) · ∑_{k : Fin r}  ψ_k

over the modular-multiplier eigenstates `ψ_k`. The proof is a discrete
Fourier inversion: combining the `(1/√r)` weights of the outer sum
and the eigenstate construction yields `(1/r) · ∑_j [y=a^j%N] · ∑_k
exp(-2πi·jk/r)`; the inner `∑_k` collapses via
`fourier_orthogonality_fin_neg` to `r · [j=0]`; the surviving `j=0`
term gives `[y = a^0 % N] = [y = 1]` (using `N > 1`).

The review chain uses this to express the Shor input state
`basis_vector (2^n) 1` (the integer-1 basis state on the `n`-qubit
data register) as a sum of orbit eigenstates — the FORWARD direction
of the orbit-eigenstate / circuit-eigenstate equivalence. -/

/-- **Pointwise orbit decomposition** (Phase 4.C, pointwise form).

For each data-register basis index `y : Fin (2^n)`, the weighted
sum over the modular orbit eigenstates evaluates to the indicator
of `y = 1`:

    (1/√r) · ∑_{k : Fin r}  ψ_k(y)  =  basis_vector (2^n) 1 y 0.

Proof outline:
1. Pull `(1/√r)` inside; combine with character_vector's own `(1/√r)`
   factor to produce a `(1/r)` prefactor and remaining `exp(-2πi·jk/r)`
   factor.
2. Swap `∑_k ∑_j → ∑_j ∑_k`; pull the `y`-independent prefactor and
   the `[y=a^j%N]` indicator out of the inner `∑_k`.
3. Apply `fourier_orthogonality_fin_neg` to reduce
   `∑_k exp(-2πi·jk/r) = r · [j=0]`.
4. The `(1/r) · r = 1` cancels; the `[j=0]` collapse leaves only the
   `j = ⟨0, h_r_pos⟩` summand, giving `[y = a^0 % N] = [y = 1 % N]
   = [y = 1]` (using `h_N : 1 < N`).

The full Order hypotheses (`h_arN`, `h_min`) and `h_N_lt` are NOT used
in this lemma — kept in the signature for API consistency with the
companion `modmult_eigenstate_orthonormal`. -/
theorem orbit_decomposition_pointwise (a r N n : Nat)
    (h_r_pos : 0 < r) (_h_arN : a^r % N = 1)
    (_h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (_h_N_lt : N ≤ 2^n)
    (y : Fin (2^n)) :
    (1 / (Real.sqrt r : ℂ)) *
      (∑ k : Fin r, modmult_eigenstate a r N n k y 0)
      = basis_vector (2^n) 1 y 0 := by
  unfold modmult_eigenstate
  have h_rR : (0 : ℝ) < r := by exact_mod_cast h_r_pos
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr h_rR
  have h_sqrt_ne : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast h_sqrt_pos.ne'
  have h_sqrt_sq : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    norm_cast; exact Real.mul_self_sqrt h_rR.le
  have h_r_C_ne : (r : ℂ) ≠ 0 := by
    rw [← h_sqrt_sq]; exact mul_ne_zero h_sqrt_ne h_sqrt_ne
  rw [Finset.mul_sum]
  -- Step 1: pull (1/√r) inside, combine with character's (1/√r) into (1/r).
  have h_each_k : ∀ k : Fin r,
      (1 / (Real.sqrt r : ℂ)) *
        (∑ j : Fin r, character_vector r k j *
          (if y.val = a^j.val % N then (1 : ℂ) else 0))
        = ∑ j : Fin r,
            ((1 / (r : ℂ)) *
             Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ) / (r : ℂ)))) *
            (if y.val = a^j.val % N then (1 : ℂ) else 0) := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold character_vector
    have h_prefactor :
        (1 / (Real.sqrt r : ℂ)) * (1 / (Real.sqrt r : ℂ)) = 1 / (r : ℂ) := by
      rw [div_mul_div_comm, mul_one, h_sqrt_sq]
    have h_exp_eq :
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                        (j.val * k.val : ℂ)) / (r : ℂ))
          = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ) / (r : ℂ))) := by
      congr 1; ring
    calc (1 / (Real.sqrt r : ℂ)) *
            ((1 / (Real.sqrt r : ℂ)) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                              (j.val * k.val : ℂ)) / (r : ℂ)) *
              (if y.val = a^j.val % N then (1 : ℂ) else 0))
        = ((1 / (Real.sqrt r : ℂ)) * (1 / (Real.sqrt r : ℂ))) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ)) / (r : ℂ)) *
            (if y.val = a^j.val % N then (1 : ℂ) else 0) := by ring
      _ = (1 / (r : ℂ)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ) / (r : ℂ))) *
            (if y.val = a^j.val % N then (1 : ℂ) else 0) := by
              rw [h_prefactor, h_exp_eq]
  simp_rw [h_each_k]
  -- Step 2: swap ∑_k ∑_j → ∑_j ∑_k; pull indicator out of inner ∑_k.
  rw [Finset.sum_comm]
  have h_inner : ∀ j : Fin r,
      (∑ k : Fin r,
        (1 / (r : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k.val : ℂ) / (r : ℂ))) *
          (if y.val = a^j.val % N then (1 : ℂ) else 0))
        = ((1 / (r : ℂ)) *
           (∑ k : Fin r,
             Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                            (j.val * k.val : ℂ) / (r : ℂ))))) *
          (if y.val = a^j.val % N then (1 : ℂ) else 0) := by
    intro j
    rw [← Finset.sum_mul]
    rw [show (∑ k : Fin r,
          (1 / (r : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                          (j.val * k.val : ℂ) / (r : ℂ))))
            = (1 / (r : ℂ)) *
              (∑ k : Fin r,
                Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
                                (j.val * k.val : ℂ) / (r : ℂ))))
            from (Finset.mul_sum _ _ _).symm]
  simp_rw [h_inner]
  -- Step 3: apply fourier_orthogonality_fin_neg to inner ∑_k.
  simp_rw [fourier_orthogonality_fin_neg r h_r_pos]
  -- Step 4: cancel (1/r)·r = 1, collapse [j=0].
  have h_simp_factor : ∀ j : Fin r,
      ((1 / (r : ℂ)) * (if j.val = 0 then (r : ℂ) else 0)) *
      (if y.val = a^j.val % N then (1 : ℂ) else 0)
        = (if j.val = 0 then (1 : ℂ) else 0) *
          (if y.val = a^j.val % N then (1 : ℂ) else 0) := by
    intro j
    by_cases h : j.val = 0
    · simp [h]; field_simp
    · simp [h]
  simp_rw [h_simp_factor]
  rw [Finset.sum_eq_single (⟨0, h_r_pos⟩ : Fin r)]
  · simp [pow_zero, Nat.one_mod_eq_one.mpr h_N.ne', basis_vector]
  · intros j _ h_ne
    have : j.val ≠ 0 := fun h => h_ne (Fin.ext h)
    rw [if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Combined-register orbit decomposition** (Phase 4.C combined form).

For each combined-register basis index `i : Fin (2^(n+anc))`:

    kron_vec |1⟩_n |0⟩_anc  =  (1/√r) · ∑_{k : Fin r}  ψ_k^{combined}

where `ψ_k^{combined} = modmult_eigenstate_combined a r N n anc k`.

Proof: pull the y-independent `kron_zeros anc (kron_vec_low i) 0`
factor out of the inner `∑_k`, then apply
`orbit_decomposition_pointwise` to the data-register sum.

This is the orbit-side analog of `modmult_eigenstate_combined_orthonormal`:
the data-register results (4.C pointwise + 4.A orthonormality) lifted
to the combined `(n+anc)`-qubit register that QPE_var acts on. Together
they discharge the orbit-side requirements of `h_orbit_exists` in
`QPE_MMI_correct_assuming_orbit_factorization` (modulo the still-blocked
QPE circuit-semantics step 4.B). -/
theorem orbit_decomposition_combined_pointwise (a r N n anc : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n)
    (i : Fin (2^(n+anc))) :
    (kron_vec (basis_vector (2^n) 1) (kron_zeros anc) i 0 : ℂ)
      = (1 / (Real.sqrt r : ℂ)) *
          (∑ k : Fin r,
            modmult_eigenstate_combined a r N n anc k i 0) := by
  unfold modmult_eigenstate_combined
  rw [kron_vec_apply]
  -- Pull the kron_zeros factor out of the inner ∑_k.
  have h_sum_factor :
      (∑ k : Fin r,
        kron_vec (modmult_eigenstate a r N n k) (kron_zeros anc) i 0)
        = (∑ k : Fin r,
            modmult_eigenstate a r N n k (kron_vec_high i) 0) *
          kron_zeros anc (kron_vec_low i) 0 := by
    simp_rw [kron_vec_apply]
    rw [← Finset.sum_mul]
  rw [h_sum_factor]
  -- Reassociate the (1/√r) prefactor and apply the data-register
  -- pointwise decomposition.
  rw [show (1 / (Real.sqrt r : ℂ)) *
        ((∑ k : Fin r, modmult_eigenstate a r N n k (kron_vec_high i) 0) *
         kron_zeros anc (kron_vec_low i) 0)
      = ((1 / (Real.sqrt r : ℂ)) *
         (∑ k : Fin r, modmult_eigenstate a r N n k (kron_vec_high i) 0)) *
        kron_zeros anc (kron_vec_low i) 0 from by ring]
  rw [orbit_decomposition_pointwise a r N n h_r_pos h_arN h_min h_N h_N_lt
        (kron_vec_high i)]

/-! ## Character-vector shift identity (toward LSB modmult eigenvalue theorem)

The first algebraic atom toward `modmult_eigenstate_combined_eigen_lsb`:
shifting the orbit index `j` by `s` (modulo `r`) in `character_vector r k`
introduces a phase factor `exp(-2π·I · s · k / r)`. The proof has two
pieces:

- `exp_mod_r_shift`: periodicity of `exp(-2π·I · n · k / r)` in `n` modulo
  `r` (the integer multiple of `2π·I · k` differs by a multiple of `r`,
  which cancels via `Complex.exp_int_mul_two_pi_mul_I`).
- `character_vector_shift_identity`: the shift identity itself, derived
  from the periodicity plus `Complex.exp_add`. -/

/-- **Periodicity of `exp(-2π·I · n · k / r)` in `n` modulo `r`.** The
exponent differs by an integer multiple of `2π·I · k` when `n` is
replaced by `n % r`, so the exponential is unchanged. -/
theorem exp_mod_r_shift (r : Nat) (h_r_pos : 0 < r) (k : Fin r) (n : Nat) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n % r : Nat) * k.val : ℂ)) / (r : ℂ))
    = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n * k.val : ℂ)) / (r : ℂ)) := by
  have h_r_ne : (r : ℂ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  set p := n % r with hp
  set q := n / r with hq
  have h_n_split : n = p + r * q := by
    simp [hp, hq]; rw [Nat.add_comm]; exact (Nat.div_add_mod n r).symm
  have h_n_cC : (n : ℂ) = (p : ℂ) + (r : ℂ) * (q : ℂ) := by exact_mod_cast h_n_split
  rw [h_n_cC]
  have h_split : -(2 * (Real.pi : ℂ) * Complex.I * (((p : ℂ) + (r : ℂ) * (q : ℂ)) * (k.val : ℂ))) / (r : ℂ)
              = -(2 * (Real.pi : ℂ) * Complex.I * ((p : ℂ) * (k.val : ℂ))) / (r : ℂ)
                + (((-(q * k.val : Nat) : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h_qk : (((-(q * k.val : Nat) : ℤ)) : ℂ) = -((q : ℂ) * (k.val : ℂ)) := by
      push_cast; ring
    rw [h_qk]; field_simp; ring
  rw [h_split, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Cyclic-shift sum reindexing on `Fin r`**: for any `s : Nat`,
summing `g` over `Fin r` equals summing `g ∘ (shift by s mod r)` over
`Fin r`. Direct corollary of `Equiv.sum_comp` applied to `finCycle k`
where `k = ⟨s % r, _⟩`. The shift is `j ↦ ⟨(j.val + s) % r, _⟩`,
matching the orbit reindexing `j ↦ (j + 2^i) mod r` needed for the
modular-multiplier eigenstate eigenvalue theorem. -/
theorem sum_fin_add_mod {α : Type*} [AddCommMonoid α]
    (r : Nat) (h_r_pos : 0 < r) (s : Nat) (g : Fin r → α) :
    ∑ j : Fin r, g j = ∑ j : Fin r, g ⟨(j.val + s) % r, Nat.mod_lt _ h_r_pos⟩ := by
  let k : Fin r := ⟨s % r, Nat.mod_lt _ h_r_pos⟩
  rw [← Equiv.sum_comp (finCycle k) g]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [finCycle_apply]
  apply Fin.ext
  show (j.val + (⟨s % r, Nat.mod_lt _ h_r_pos⟩ : Fin r).val) % r = (j.val + s) % r
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- **Periodicity of `a^n mod N` in `n` modulo `r`**, when `a^r % N = 1`.
Direct consequence of `a^(n%r + r*(n/r)) = a^(n%r) * (a^r)^(n/r)` and
`(a^r % N = 1) → (a^r)^k % N = 1`. Needed for the basis-vector orbit
position rewrite in `modmult_eigenstate_combined_eigen_lsb`:
`a^(j + 2^i) % N = a^((j + 2^i) % r) % N`. -/
theorem a_pow_mod_periodic_in_n (a N r n : Nat) (h_arN : a^r % N = 1) :
    a^(n % r) % N = a^n % N := by
  have h_N_ne_one : N ≠ 1 := by
    intro hN; rw [hN] at h_arN
    rw [Nat.mod_one] at h_arN
    exact (by omega : (0 : Nat) ≠ 1) h_arN
  have h_eq : n = (n % r) + r * (n / r) := by
    have := Nat.div_add_mod n r; omega
  conv_rhs => rw [h_eq]
  rw [pow_add, Nat.mul_mod, pow_mul]
  have h_pow : (a^r)^(n/r) % N = 1 := by
    rw [Nat.pow_mod, h_arN, one_pow]
    rcases Nat.eq_zero_or_pos N with h_N | h_N
    · subst h_N; show 1 % 0 = 1; simp
    · exact Nat.one_mod_eq_one.mpr h_N_ne_one
  rw [h_pow, mul_one, Nat.mod_mod]

/-- **Modular-multiplier eigenstate as a sum**: the pointwise definition
`ψ_k(y) = ∑_j character_vector r k j · [y = a^j mod N]` admits the matrix
form `ψ_k = ∑_j character_vector r k j • basis_vector (2^n) (a^j mod N)`.
Trivial pointwise unfolding via `Matrix.sum_apply` + `Matrix.smul_apply`
+ `basis_vector_apply`. Needed to apply `Matrix.mul_sum` / `Matrix.mul_smul`
linearity in the upcoming `modmult_eigenstate_eigen_lsb` proof. -/
theorem modmult_eigenstate_as_sum (a r N n : Nat) (k : Fin r) :
    modmult_eigenstate a r N n k
    = ∑ j : Fin r, character_vector r k j • basis_vector (2^n) (a^j.val % N) := by
  ext y col
  unfold modmult_eigenstate
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.smul_apply, basis_vector_apply, smul_eq_mul]

/-- **Positive-sign variant of `exp_mod_r_shift`.** Same statement but
with `+` in the exponent instead of `-`. Identical proof structure;
needed for the eigenvalue extraction in `modmult_eigenstate_combined_eigen_lsb`
where the phase factor has POSITIVE sign (the inverse of `character_vector`'s
negative-sign convention). -/
theorem exp_mod_r_shift_pos (r : Nat) (h_r_pos : 0 < r) (k : Fin r) (n : Nat) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * ((n % r : Nat) * k.val : ℂ)) / (r : ℂ))
    = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n * k.val : ℂ)) / (r : ℂ)) := by
  have h_r_ne : (r : ℂ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  set p := n % r with hp
  set q := n / r with hq
  have h_n_split : n = p + r * q := by
    simp [hp, hq]; rw [Nat.add_comm]; exact (Nat.div_add_mod n r).symm
  have h_n_cC : (n : ℂ) = (p : ℂ) + (r : ℂ) * (q : ℂ) := by exact_mod_cast h_n_split
  rw [h_n_cC]
  have h_split : 2 * (Real.pi : ℂ) * Complex.I *
                    (((p : ℂ) + (r : ℂ) * (q : ℂ)) * (k.val : ℂ)) / (r : ℂ)
              = 2 * (Real.pi : ℂ) * Complex.I * ((p : ℂ) * (k.val : ℂ)) / (r : ℂ)
                + (((q * k.val : Nat) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h_qk : (((q * k.val : Nat) : ℤ) : ℂ) = (q : ℂ) * (k.val : ℂ) := by
      push_cast; ring
    rw [h_qk]; field_simp
  rw [h_split, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Character-vector shift identity**: shifting the orbit index `j` by
`s` (modulo `r`) in `character_vector r k` introduces a phase factor
`exp(-2π·I · s · k / r)`. Direct corollary of `exp_mod_r_shift` plus
`Complex.exp_add`. -/
theorem character_vector_shift_identity
    (r : Nat) (h_r_pos : 0 < r) (k : Fin r) (j : Fin r) (s : Nat) :
    character_vector r k ⟨(j.val + s) % r, Nat.mod_lt _ h_r_pos⟩
    = character_vector r k j
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (s * k.val : ℂ)) / (r : ℂ)) := by
  unfold character_vector
  rw [show (⟨(j.val + s) % r, Nat.mod_lt _ h_r_pos⟩ : Fin r).val = (j.val + s) % r from rfl]
  rw [exp_mod_r_shift r h_r_pos k (j.val + s)]
  have h_r_ne : (r : ℂ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((↑j.val + s : ℕ) * k.val : ℂ)) / (r : ℂ)
        = -(2 * (Real.pi : ℂ) * Complex.I * (j.val * k.val : ℂ)) / (r : ℂ)
          + -(2 * (Real.pi : ℂ) * Complex.I * (s * k.val : ℂ)) / (r : ℂ) from by
      push_cast; field_simp; ring]
  rw [Complex.exp_add]
  ring

end FormalRV.SQIRPort
