/-
  FormalRV.Shor.CosetOrbitEngine — the ABSTRACT orbit engine: the real QPE
  circuit evaluates ANY oracle-with-eigenfamily to the orbit superposition.
  ════════════════════════════════════════════════════════════════════════════

  This generalizes the canonical `QPE_var_lsb_on_orbit_sum` /
  `QPE_var_lsb_on_Shor_initial_raw` (which are hard-wired to the canonical
  modmult eigenstate `modmult_eigenstate_combined`) to an ARBITRARY eigenstate
  family `ψ : Fin r → QState (2^(n+anc))`.  The proof is identical — it threads
  the generic, oracle-black-box `QPE_var_lsb_on_eigenstate_from_real_QFTinv`
  through the orbit sum by `kron`-linearity.

  WHY.  The GE2021 coset multiplier has the SAME eigenvalue structure as the
  canonical multiplier (its orbit is the canonical orbit with each residue moved
  to its coset representative), so its eigenfamily is the canonical one with the
  data register permuted.  Feeding THAT family to this engine evaluates the real
  QPE on the real coset family — no axiom, no substituted middle.  The remaining
  inputs (the per-iterate eigenvalue equation and the orbit decomposition) become
  gadget/permutation facts, discharged elsewhere.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.PostQFT.PostQFTCompletion

namespace FormalRV.Shor.CosetOrbitEngine

open FormalRV.SQIRPort
open FormalRV.Framework

/-- **The abstract orbit engine.**  For ANY eigenstate family `ψ` such that
    (a) each `ψ k` is an eigenstate of every oracle iterate `f i` (`i < m`) with
    the LSB-first eigenvalue `exp(2πi · 2^i · k/r)`, and (b) the initial data
    state `|1⟩_n ⊗ |0⟩_anc` decomposes as `(1/√r)·∑_k ψ k`, the real QPE circuit
    `QPE_var_lsb m (n+anc) f` carries the Shor initial state to the orbit
    superposition `(1/√r)·∑_k (qpe_phase_state m (k/r) ⊗ ψ k)`.

    The proof mirrors `QPE_var_lsb_on_orbit_sum` exactly, but uses the generic
    `QPE_var_lsb_on_eigenstate_from_real_QFTinv` (black-box in `f` and `ψ`) per
    orbit index `k`, so it holds for the coset family as well as the canonical
    one. -/
theorem qpe_var_lsb_on_eigenfamily_initial
    {m n anc r : Nat} (hmanc : 0 < m + (n + anc)) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (ψ : Fin r → Matrix (Fin (2 ^ (n + anc))) (Fin 1) ℂ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped (n + anc) (f i))
    (h_eig : ∀ k : Fin r, ∀ i, i < m →
        FormalRV.Framework.uc_eval (f i) * ψ k
          = Complex.exp (((2 * Real.pi * ((2 ^ i : Nat) : ℝ)
              * ((k.val : ℝ) / (r : ℝ)) : ℝ) : ℂ) * Complex.I) • ψ k)
    (h_decomp : kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1)
          (FormalRV.Framework.kron_zeros anc)
        = (1 / (Real.sqrt r : ℂ)) • ∑ k : Fin r, ψ k) :
    FormalRV.Framework.uc_eval (QPE_var_lsb m (n + anc) f)
      * (kron_vec (FormalRV.Framework.kron_zeros m)
           (kron_vec (FormalRV.Framework.basis_vector (2 ^ n) 1)
                     (FormalRV.Framework.kron_zeros anc))
          : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)
    = (1 / (Real.sqrt r : ℂ)) • ∑ k : Fin r,
        kron_vec (qpe_phase_state m ((k.val : ℝ) / (r : ℝ))) (ψ k) := by
  rw [h_decomp, kron_vec_smul_right, kron_vec_sum_right, Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact QPE_var_lsb_on_eigenstate_from_real_QFTinv hmanc hm f (ψ k)
    ((k.val : ℝ) / (r : ℝ)) h_wt_all (h_eig k)

end FormalRV.Shor.CosetOrbitEngine
