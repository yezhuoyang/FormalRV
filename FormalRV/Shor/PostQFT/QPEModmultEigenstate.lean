/-
  FormalRV.Shor.PostQFT.QPEModmultEigenstate
  ──────────────────────────────────────────
  The MODULAR-EXPONENTIATION instantiation of the black-box QPE correctness:
  the controlled modular-multiplier family is a QPE oracle whose combined
  eigenstate carries the LSB-first eigenvalue `exp(2πi · 2^i · k/r)`, so QPE
  recovers the phase `k/r`.

  Relocated here (2026-06-10) out of `QFT/IQFTRecursiveArbitrary.lean`: these
  are Shor-specific (they reference `ModMulImpl`, `modmult_eigenstate_combined`,
  `a^j % N`), so they belong in Shor, NOT in the QFT or QPE folders.  They build
  on the QPE-generic headline `QPE_var_lsb_on_eigenstate_from_real_QFTinv`
  (now in `QPE/QPECorrectness.lean`) by discharging its eigenvalue hypothesis
  via `modmult_eigenstate_combined_eigen_lsb`.
-/
import FormalRV.QPE.QPECorrectness
import FormalRV.Shor.OrderFinding.FourierEigenstate

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom
/-! ### Combined-register modmult eigenstate sum form

Lifts `modmult_eigenstate_as_sum` from the data register to the combined
data+ancilla register via `kron_vec_sum_left` + `kron_vec_smul_left` +
pointwise basis-vector match. Cannot live in `Eigenstate.lean` because
the `kron_vec_sum_left` helper lives in `PhaseKickback.lean` (which is
imported by `PostQFT` but not by `Eigenstate`). -/

/-- **Combined-register modmult eigenstate sum form**: the combined
eigenstate `kron_vec ψ_k |0⟩_anc` admits the basis-vector decomposition
`∑_j character_vector r k j • basis_vector (2^(n+anc)) (a^j%N · 2^anc)`,
matching the orbit basis vectors (data-register orbit index times
`2^anc` for the zero ancilla). Proven by combining
`modmult_eigenstate_as_sum` with `kron_vec_sum_left` /
`kron_vec_smul_left`, then a pointwise basis match using
`kron_vec_apply` + the `kron_vec_high`/`kron_vec_low` index decomposition. -/
theorem modmult_eigenstate_combined_as_sum (a r N n anc : Nat) (k : Fin r) :
    modmult_eigenstate_combined a r N n anc k
    = ∑ j : Fin r, character_vector r k j •
        FormalRV.Framework.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc) := by
  unfold modmult_eigenstate_combined
  rw [modmult_eigenstate_as_sum, kron_vec_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [kron_vec_smul_left]
  congr 1
  ext i col
  rw [kron_vec_apply, basis_vector_apply, basis_vector_apply]
  unfold kron_zeros
  rw [basis_vector_apply]
  have h_decomp : i.val = (kron_vec_high i).val * 2^anc + (kron_vec_low i).val := by
    unfold kron_vec_high kron_vec_low
    show i.val = i.val / 2^anc * 2^anc + i.val % 2^anc
    rw [Nat.div_add_mod' i.val (2^anc)]
  by_cases hH : (kron_vec_high i).val = a^j.val % N
  · by_cases hL : (kron_vec_low i).val = 0
    · rw [if_pos hH, if_pos hL, mul_one]
      have h_i_eq : i.val = a^j.val % N * 2^anc := by
        rw [h_decomp, hH, hL, Nat.add_zero]
      rw [if_pos h_i_eq]
    · rw [if_neg hL, mul_zero]
      have h_i_ne : i.val ≠ a^j.val % N * 2^anc := by
        intro heq
        apply hL
        show i.val % 2^anc = 0
        rw [heq, Nat.mul_mod_left]
      rw [if_neg h_i_ne]
  · rw [if_neg hH, zero_mul]
    have h_i_ne : i.val ≠ a^j.val % N * 2^anc := by
      intro heq
      apply hH
      show i.val / 2^anc = a^j.val % N
      rw [heq, Nat.mul_div_cancel _ (Nat.two_pow_pos anc)]
    rw [if_neg h_i_ne]

/-- **Modmult action as orbit sum (intermediate step toward eigenvalue
theorem)**: applying `uc_eval (f i)` to `ψ_k^combined` and using the
`a^r % N = 1` periodicity gives a sum over `Fin r` where the basis
vector index is `a^((2^i + j.val) % r) % N · 2^anc` (the orbit position
reduced mod r). The next step (reindexing via `sum_fin_add_mod` + phase
extraction via `character_vector_shift_identity`) gives the eigenvalue
form `exp(2π·I · 2^i · k / r) • ψ_k^combined`. -/
theorem modmult_combined_action_as_orbit_sum
    (a r N n anc i : Nat) (k : Fin r)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_arN : a^r % N = 1)
    (h_N_pos : 0 < N) :
    FormalRV.Framework.uc_eval (f i)
      * modmult_eigenstate_combined a r N n anc k
    = ∑ j : Fin r, character_vector r k j •
        FormalRV.Framework.basis_vector (2^(n+anc))
          (a^((2^i + j.val) % r) % N * 2^anc) := by
  rw [modmult_eigenstate_combined_as_sum, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul]
  congr 1
  show FormalRV.SQIRPort.uc_eval (f i)
        (FormalRV.SQIRPort.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc))
      = FormalRV.SQIRPort.basis_vector (2^(n+anc))
          (a^((2^i + j.val) % r) % N * 2^anc)
  rw [MultiplyCircuitProperty_acts_on_orbit_basis a N n anc i j.val f h_modmul h_N_pos]
  congr 2
  exact (a_pow_mod_periodic_in_n a N r (2^i + j.val) h_arN).symm

/-- **HEADLINE: Modmult eigenstate eigenvalue theorem (LSB form)**. The
combined-register modular-multiplier eigenstate `ψ_k^combined` is an
eigenstate of each `f i = U^{a^{2^i}}` (from `ModMulImpl`) with
eigenvalue `exp(2π·I · 2^i · k / r)` — the standard LSB-first
QPE-eigenvalue convention.

Proof: build on `modmult_combined_action_as_orbit_sum` (which reduces
`uc_eval (f i) * ψ_k_combined` to a sum over `Fin r` with basis-vector
index `a^((2^i + j.val) % r) % N · 2^anc`). Reindex via `sum_fin_add_mod`
with shift `s = r - 2^i % r` (the inverse shift). The basis vector index
simplifies to `a^j.val % N · 2^anc` via Nat arithmetic. The
`character_vector` picks up a phase factor `exp(-2π·I · s · k / r) =
exp(-2π·I · k) · exp(+2π·I · (2^i % r) · k / r) = 1 · exp(+2π·I · 2^i · k / r)`
(via `Complex.exp_int_mul_two_pi_mul_I` + `exp_mod_r_shift_pos`).
Finally `Finset.smul_sum` factors the phase out of the reassembled sum.

This is the LSB-form eigenvalue compatible with `QPE_var_lsb`. Use
together with `QPE_var_lsb_on_eigenstate_from_real_QFTinv` to obtain
the per-orbit QPE action on `modmult_eigenstate_combined`. -/
theorem modmult_eigenstate_combined_eigen_lsb
    (a r N n anc i : Nat) (k : Fin r)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_r_pos : 0 < r)
    (h_arN : a^r % N = 1)
    (h_N_pos : 0 < N) :
    FormalRV.Framework.uc_eval (f i)
      * modmult_eigenstate_combined a r N n anc k
    = Complex.exp
        (((2 * Real.pi * ((2^i : Nat) : ℝ) * (k.val : ℝ) / (r : ℝ) : ℝ) : ℂ) * Complex.I)
      • modmult_eigenstate_combined a r N n anc k := by
  -- REFACTORED (2026-06-13): this is now a ONE-LINE instantiation of the
  -- BASIS-GENERIC `fourierEigenstate_eigen_lsb`.  The orbit basis is
  -- `φ_j = |a^j mod N⟩|0⟩_anc`; the single encoding-specific fact is the orbit
  -- shift `uc_eval (f i) · φ_j = φ_{(2^i+j) mod r}` (= the verified
  -- `MultiplyCircuitProperty_acts_on_orbit_basis` + periodicity).  All the
  -- Fourier phase/reindex algebra lives once in `fourierEigenstate_eigen_lsb`.
  have heq : modmult_eigenstate_combined a r N n anc k
      = fourierEigenstate r
          (fun j => FormalRV.Framework.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc)) k :=
    modmult_eigenstate_combined_as_sum a r N n anc k
  rw [heq]
  exact fourierEigenstate_eigen_lsb h_r_pos
    (fun j => FormalRV.Framework.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc))
    (FormalRV.Framework.uc_eval (f i)) (2^i) k
    (fun j => by
      show FormalRV.SQIRPort.uc_eval (f i)
            (FormalRV.SQIRPort.basis_vector (2^(n+anc)) (a^j.val % N * 2^anc))
          = FormalRV.SQIRPort.basis_vector (2^(n+anc))
              (a^((2^i + j.val) % r) % N * 2^anc)
      rw [MultiplyCircuitProperty_acts_on_orbit_basis a N n anc i j.val f h_modmul h_N_pos]
      congr 2
      exact (a_pow_mod_periodic_in_n a N r (2^i + j.val) h_arN).symm)

/-- **HEADLINE: Per-orbit QPE action on the modmult eigenstate.**
Applying `QPE_var_lsb m (n+anc) f` to `|0⟩_m ⊗ ψ_k^combined` yields
`qpe_phase_state m (k.val / r) ⊗ ψ_k^combined`. Direct application of
`QPE_var_lsb_on_eigenstate_from_real_QFTinv` with the LSB eigenvalue
hypothesis discharged via `modmult_eigenstate_combined_eigen_lsb`. This
is the per-orbit step needed by the orbit-sum linearity that drives
the final Shor measurement-probability theorem. -/
theorem QPE_var_lsb_on_modmult_eigenstate
    {m n anc : Nat} (a r N : Nat) (k : Fin r)
    (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1) (h_N_pos : 0 < N)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (h_modmul : ModMulImpl a N n anc f)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i)) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * kron_vec (FormalRV.Framework.kron_zeros m)
          (modmult_eigenstate_combined a r N n anc k)
    = kron_vec (qpe_phase_state m ((k.val : ℝ) / (r : ℝ)))
        (modmult_eigenstate_combined a r N n anc k) := by
  apply QPE_var_lsb_on_eigenstate_from_real_QFTinv hmanc hm f
        (modmult_eigenstate_combined a r N n anc k)
        ((k.val : ℝ) / (r : ℝ)) h_wt_all
  intro i _
  rw [modmult_eigenstate_combined_eigen_lsb a r N n anc i k f h_modmul
        h_r_pos h_arN h_N_pos]
  congr 1
  congr 1
  push_cast
  ring

/-! ### Toward `Shor_final_state_lsb_eq_shor_orbit_state`

The headline state-equality theorem connecting the LSB-compatible
Shor circuit output to the `shor_orbit_state` closed form. This
section sets up two pieces: a matrix-level orbit decomposition
(lifting the existing pointwise version), and the definition of
`Shor_final_state_lsb` itself. The full state equality is a
follow-up combining these with `QPE_var_lsb_on_modmult_eigenstate`
+ linearity over the orbit sum. -/

/-- **Matrix-level orbit decomposition.** Lifts the pointwise
`orbit_decomposition_combined_pointwise` to a Matrix equality:
`kron_vec |1⟩_n |0⟩_anc = (1/√r) • ∑_k modmult_eigenstate_combined ... k`.
Direct `Matrix.ext` + `Matrix.smul_apply` + `Matrix.sum_apply` chain. -/
theorem orbit_decomposition_combined_matrix
    (a r N n anc : Nat)
    (h_r_pos : 0 < r) (h_arN : a^r % N = 1)
    (h_min : ∀ s, 0 < s → s < r → a^s % N ≠ 1)
    (h_N : 1 < N) (h_N_lt : N ≤ 2^n) :
    kron_vec (FormalRV.Framework.basis_vector (2^n) 1)
             (FormalRV.Framework.kron_zeros anc)
    = (1 / (Real.sqrt r : ℂ)) •
        ∑ k : Fin r, modmult_eigenstate_combined a r N n anc k := by
  ext i col
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  exact orbit_decomposition_combined_pointwise a r N n anc h_r_pos h_arN h_min h_N h_N_lt i

end FormalRV.SQIRPort
