/-
  FormalRV.Shor.OrderFinding.FourierEigenstate — the BASIS-GENERIC cyclic-shift
  orbit eigenstate.
  ════════════════════════════════════════════════════════════════════════════

  The standard-Shor eigenvalue proof (`modmult_eigenstate_combined_eigen_lsb`)
  used exactly one encoding-specific fact — the single-orbit SHIFT action
  `uc_eval (f i) · |a^j mod N⟩ = |a^(2^i+j) mod N⟩` — and then ran pure `Fin r`
  Fourier algebra (reindex `sum_fin_add_mod`, phase extraction
  `character_vector_shift_identity`).  This file FACTORS that algebra out, once,
  parametric over an ARBITRARY orbit basis `φ : Fin r → QState d`:

      if a linear operator `M` cyclically shifts the orbit basis by `s`
          (`M · φ_j = φ_{(s+j) mod r}`),
      then the Fourier eigenstate `Σ_j character_vector(r,k,j) · φ_j` is an
      eigenstate of `M` with eigenvalue `exp(2π·i · s · k / r)`.

  `modmult_eigenstate_combined_eigen_lsb` is then a ONE-LINE instantiation
  (`φ_j = |a^j mod N⟩|0⟩_anc`, `M = uc_eval (f i)`, `s = 2^i`), and so is the
  GE2021 coset eigenstate (`φ_j = |coset(a^j mod N)⟩`).  The hard phase algebra is
  proven HERE, once, and reused.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.OrderFinding.Eigenstate

namespace FormalRV.SQIRPort

open FormalRV.Framework

/-- **The Fourier eigenstate over an arbitrary orbit basis** `φ : Fin r → QState d`:
    the `k`-th character-weighted superposition `Σ_j character_vector(r,k,j) · φ_j`.
    With `φ_j = |a^j mod N⟩|0⟩` this is the standard Shor eigenstate. -/
noncomputable def fourierEigenstate {d : Nat} (r : Nat)
    (φ : Fin r → Matrix (Fin d) (Fin 1) ℂ) (k : Fin r) :
    Matrix (Fin d) (Fin 1) ℂ :=
  ∑ j : Fin r, character_vector r k j • φ j

/-- **BASIS-GENERIC eigenvalue theorem.**  If `M` cyclically shifts the orbit
    basis `φ` by `s` (`M · φ_j = φ_{(s+j) mod r}`), then the Fourier eigenstate is
    an eigenstate of `M` with the LSB-first eigenvalue `exp(2π·i · s · k / r)`.

    The proof is the standard-Shor `modmult_eigenstate_combined_eigen_lsb` with
    the basis abstracted: term-by-term action via `h_shift`, reindex by
    `sum_fin_add_mod` (shift `t = r − s%r`), phase extraction via
    `character_vector_shift_identity` + `exp_mod_r_shift_pos`, and the integer
    phase `exp(−2π·i·k) = 1` via `Complex.exp_int_mul_two_pi_mul_I`. -/
theorem fourierEigenstate_eigen_lsb {d : Nat} {r : Nat} (h_r_pos : 0 < r)
    (φ : Fin r → Matrix (Fin d) (Fin 1) ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) (s : Nat) (k : Fin r)
    (h_shift : ∀ j : Fin r, M * φ j = φ ⟨(s + j.val) % r, Nat.mod_lt _ h_r_pos⟩) :
    M * fourierEigenstate r φ k
      = Complex.exp
          (((2 * Real.pi * (s : ℝ) * (k.val : ℝ) / (r : ℝ) : ℝ) : ℂ) * Complex.I)
        • fourierEigenstate r φ k := by
  -- Step 1 — `M` acts term-by-term, shifting each orbit position by `s`.
  have h_action : M * fourierEigenstate r φ k
      = ∑ j : Fin r, character_vector r k j
          • φ ⟨(s + j.val) % r, Nat.mod_lt _ h_r_pos⟩ := by
    unfold fourierEigenstate
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.mul_smul, h_shift j]
  rw [h_action]
  -- Step 2 — reindex by the inverse shift `t = r − s%r`.
  set t := r - s % r with ht
  rw [sum_fin_add_mod r h_r_pos t
        (fun j => character_vector r k j
          • φ ⟨(s + j.val) % r, Nat.mod_lt _ h_r_pos⟩)]
  -- Step 3 — unfold the target eigenstate and factor the scalar phase.
  unfold fourierEigenstate
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- The reindexed orbit position collapses back to `j`.
  have h_arith : (s + ((j.val + t) % r)) % r = j.val := by
    have h_jr : j.val < r := j.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h_eq : s + (j.val + t) = j.val + r * (s / r + 1) := by
      have h_decomp : s = s % r + r * (s / r) := by
        have := Nat.div_add_mod s r; omega
      have h_sr : s % r ≤ r := le_of_lt (Nat.mod_lt _ h_r_pos)
      show s + (j.val + (r - s % r)) = j.val + r * (s / r + 1)
      have h_split : r * (s / r + 1) = r * (s / r) + r := by ring
      omega
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h_jr
  show character_vector r k ⟨(j.val + t) % r, Nat.mod_lt _ h_r_pos⟩
        • φ ⟨(s + ((⟨(j.val + t) % r, Nat.mod_lt _ h_r_pos⟩ : Fin r).val)) % r,
              Nat.mod_lt _ h_r_pos⟩
      = Complex.exp _ • (character_vector r k j • φ j)
  rw [show ((⟨(j.val + t) % r, Nat.mod_lt _ h_r_pos⟩ : Fin r).val : Nat)
        = (j.val + t) % r from rfl]
  have hfin : (⟨(s + ((j.val + t) % r)) % r, Nat.mod_lt _ h_r_pos⟩ : Fin r) = j :=
    Fin.ext h_arith
  rw [hfin, character_vector_shift_identity r h_r_pos k j t, smul_smul]
  congr 1
  rw [mul_comm]
  congr 1
  have h_r_ne : (r : ℂ) ≠ 0 := by exact_mod_cast h_r_pos.ne'
  have h_s_mod_lt : s % r ≤ r := le_of_lt (Nat.mod_lt _ h_r_pos)
  have h_t_cast : (t : ℂ) = (r : ℂ) - (s % r : Nat) := by
    show ((r - s % r : Nat) : ℂ) = (r : ℂ) - (s % r : Nat)
    push_cast
    rw [Nat.cast_sub h_s_mod_lt]
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * (t * k.val : ℂ)) / (r : ℂ)
        = ((-(k.val : Nat) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          + 2 * (Real.pi : ℂ) * Complex.I * ((s % r : Nat) * k.val : ℂ) / (r : ℂ) from by
      rw [h_t_cast]; push_cast; field_simp; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [exp_mod_r_shift_pos r h_r_pos k s]
  push_cast
  ring_nf

end FormalRV.SQIRPort
