import FormalRV.Shor.MainAlgorithm.SuccessProbability.Tier3AxiomsAndLinearity

namespace FormalRV.SQIRPort

/-! ## §11. `QPE_var_on_eigenstate` — semantic foundation for QPE correctness

The hook directive (2026-05-24) asked for the central QPE semantic
theorem: for an eigenstate `ψ` of the family `f` with phase `θ` (i.e.,
`uc_eval (f i) * ψ = exp(2πi · 2^i · θ) • ψ`), evaluating `QPE_var m anc f`
on `|0^m⟩ ⊗ ψ` yields `kron_vec (qpe_phase_state m θ) ψ`.

This is the inner semantic step of SQIR's `QPE_semantics_full`
(`QPEGeneral.v` line 105, ~180 LOC of Coq + multi-file `QuantumLib`
support). Implementing it in Lean requires:

  1. **CRITICAL (primary blocker)**: replacing the current `control` STUB
     at `Framework/UnitaryOps.lean:972`. The stub definition is

         control q (UCom.app1 _ _) = SKIP

     which means `control q U` does NOT represent controlled-U when `U`
     contains single-qubit gates — instead it deletes them. Since QPE's
     `controlled_powers (lifted f)` is built from `control i (lifted (f i))`
     and the `f i` family contains the modular-multiplier circuit (which
     necessarily has single-qubit gates), this stub makes the entire
     QPE phase-estimation mechanism semantically vacuous for any `f` that
     isn't a pure-CNOT circuit. A correct implementation requires the
     full controlled-`R(θ,φ,λ)` Toffoli-style decomposition flagged
     `TODO(BQAlgo)` at line 962.
  2. Replacing the `QFTinv n = npar_H n` stub at `Framework/QPE.lean:36`
     with the real inverse QFT circuit.
  3. Proving inverse-QFT-on-superposition correctness (the
     `(1/√2^k) · ∑_x exp(2πi · x · θ) |x⟩ ↦ qpe_phase_state k θ` step).
  4. Proving the `controlled_powers` cascade: on input
     `(npar_H k ⊗ I) (|0^k⟩ ⊗ ψ)`, output is
     `(1/√2^k) · ∑_x exp(2πi · x · θ) |x⟩ ⊗ ψ`. Needs (1).
  5. Tensor / `pad_u` linearity over `kron_vec` summands. The framework
     currently has ZERO `pad_u`-on-`kron_vec` interaction lemmas (grep
     `Framework/` for `pad_u.*kron_vec`).
  6. The `map_qubits (·+m) ∘ f` shift's preservation of eigenstate action
     on the `ψ` register (via `pad_u` block-disjoint commutativity).

Per the hook's fallback clause ("If the full theorem is too hard, prove
the smallest kernel-clean semantic helper and report the exact blocker"),
this tick delivers the **m = 0 base case** — the ONLY case where the
theorem can be settled with the current framework, because:

- At `m = 0`, the `controlled_powers (lifted f) 0 = SKIP` by
  `controlled_powers_zero` — the stubbed `control` is never invoked.
- The `QFTinv 0 = SKIP` and `npar_H 0 = SKIP`, so the QFTinv stub is
  also bypassed.
- The eigenstate hypothesis is vacuously satisfied: the circuit never
  touches `ψ`.

For any `m ≥ 1`, the stubbed `control` (item 1) is invoked at the
`(lifted f) 0` step of `controlled_powers`, and the proof becomes
unsound (it would conclude that `QPE_var 1 anc f * (|0⟩ ⊗ ψ) =
(H ⊗ I) * (kron_zeros 1 ⊗ ψ)` regardless of `f`'s eigenphase, which
contradicts the conclusion `kron_vec (qpe_phase_state 1 θ) ψ` for
nonzero θ). This is not an "infrastructure missing" gap — it's an
"infrastructure deliberately wrong" gap. **Item 1 must close before
any m ≥ 1 case is even well-posed.**

**Strict-honesty summary**: The general-m `QPE_var_on_eigenstate`
theorem **cannot be proven** in this framework as it currently stands —
not because the proof is hard, but because the `control` primitive
does not implement what its docstring claims. Any attempt would either
add `axiom`s (forbidden by the directive) or use `sorry` (forbidden by
the directive). The only honest, sorry-free, axiom-free deliverable
is the m = 0 case below, plus this explicit infrastructure-bug report.

Estimated scope to close items 1–6 per `Framework/QPE.lean:357`:
~1500 LOC (items 1–2 being pure circuit constructions, items 3–6 being
the multi-file proof body). -/

/-- **QPE_var at m = 0 evaluates to the identity matrix** (when the
data register is non-empty). Direct unfolding: `QPE_var 0 anc f` is
`seq (npar_H 0) (seq (controlled_powers c 0) (QFTinv 0))`, and all
three components are `SKIP`, evaluating to the `dim = anc` identity. -/
theorem QPE_var_zero_eq_one (anc : Nat) (h : 0 < anc)
    (f : Nat → BaseUCom anc) :
    FormalRV.Framework.uc_eval (QPE_var 0 anc f) =
      (1 : FormalRV.Framework.Square (0 + anc)) := by
  unfold QPE_var
  rw [FormalRV.Framework.BaseUCom.uc_eval_QPE]
  have hd : 0 < 0 + anc := by omega
  rw [FormalRV.Framework.BaseUCom.uc_eval_QFTinv_zero_eq_one hd,
      FormalRV.Framework.BaseUCom.uc_eval_controlled_powers_zero_eq_one _ hd,
      FormalRV.Framework.BaseUCom.uc_eval_npar_H_zero_eq_one hd,
      Matrix.one_mul, Matrix.one_mul]

/-- **QPE_var_on_eigenstate — m = 0 base case** (the smallest kernel-clean
semantic helper per the hook directive).

For any data-register state `ψ` and phase `θ`, evaluating `QPE_var 0 anc f`
on `kron_vec (kron_zeros 0) ψ` yields `kron_vec (qpe_phase_state 0 θ) ψ`.
The eigenstate hypothesis on `f` is not required at `m = 0` because the
zero-precision QPE circuit is the identity and never invokes `f`.

Proof: `QPE_var 0 anc f` evaluates to the identity (via
`QPE_var_zero_eq_one`), so the LHS simplifies to
`kron_vec (kron_zeros 0) ψ`. Pointwise, both `kron_zeros 0` and
`qpe_phase_state 0 θ` are the single-entry matrix with value `1` at
index `0 : Fin 1` — the former by `basis_vector` definition, the latter
because `qpe_amp 0 0 θ = 1` (the empty `Fin 1`-sum collapses to
`exp(0) = 1`). The two kron_vecs are therefore pointwise equal. -/
theorem QPE_var_on_eigenstate_zero (anc : Nat) (h : 0 < anc)
    (f : Nat → BaseUCom anc) (θ : ℝ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) :
    FormalRV.Framework.uc_eval (QPE_var 0 anc f) *
        (FormalRV.Framework.kron_vec
          (FormalRV.Framework.kron_zeros 0) ψ :
         Matrix (Fin (2^(0 + anc))) (Fin 1) ℂ)
      = FormalRV.Framework.kron_vec
          (FormalRV.Framework.qpe_phase_state 0 θ) ψ := by
  rw [QPE_var_zero_eq_one anc h f, Matrix.one_mul]
  ext i j
  rw [FormalRV.Framework.kron_vec_apply,
      FormalRV.Framework.kron_vec_apply]
  have h_idx :
      (FormalRV.Framework.kron_vec_high i :
        Fin (2^0)).val = 0 := by
    have hlt := (FormalRV.Framework.kron_vec_high i :
                 Fin (2^0)).isLt
    have h2 : (2^0 : Nat) = 1 := pow_zero 2
    omega
  have h_zeros :
      FormalRV.Framework.kron_zeros 0
        (FormalRV.Framework.kron_vec_high i) 0 = 1 := by
    unfold FormalRV.Framework.kron_zeros
    exact FormalRV.Framework.basis_vector_apply_eq _ _ _ _ h_idx
  have h_phase :
      FormalRV.Framework.qpe_phase_state 0 θ
        (FormalRV.Framework.kron_vec_high i) 0 = 1 := by
    rw [FormalRV.Framework.qpe_phase_state_apply, h_idx]
    unfold FormalRV.Framework.qpe_amp
    simp [pow_zero]
  rw [h_zeros, h_phase]

/-! ## §12. Dim-cast bridge (Phase 4.E)

Two helpers for the dim-equality `2^(m + (n + anc)) = 2^m * 2^n * 2^anc`
that bridges between `QPE_var`'s natural output dimension and
`Shor_final_state`'s product-form `QState` type. The first is the bare
Nat equality; the second shows that `prob_partial_meas` is invariant
under `QState.cast` over any dim equality.

Together they let the user of `QPE_MMI_correct_assuming_orbit_factorization`
discharge the third conjunct of `h_orbit_exists` (the probability
equality between `Shor_final_state` and the orbit-superposition
`actual_state`) by exhibiting `actual_state` as a cast of a vector
on `Fin (2^(m + (n + anc)))`. -/

/-- **Dim-equality bridge** for the Shor combined-register product
form: `2^(m + (n + anc)) = 2^m * 2^n * 2^anc`. Pure Nat fact: two
applications of `pow_add` + `mul_assoc`. -/
theorem dim_assoc_eq (m n anc : Nat) :
    2^(m + (n + anc)) = 2^m * 2^n * 2^anc := by
  rw [pow_add, pow_add, mul_assoc]

/-- **`prob_partial_meas` is invariant under `QState.cast`**: for any
dim equality `h_eq : a = b`, the partial-measurement probability of
the cast vector equals that of the original. The proof uses `subst`
to reduce the cast to the identity (modulo `Subsingleton.elim` on
the `Fin 1` row index).

Used in the review chain to swap between `QState (2^(m + (n + anc)))`
(the natural output dimension of `uc_eval (QPE_var ...)`) and
`QState (2^m * 2^n * 2^anc)` (the product form used by
`Shor_final_state`'s signature). -/
theorem prob_partial_meas_cast {m_dim a b : Nat} (h_eq : a = b)
    (ψ : QState m_dim) (φ : QState a) :
    prob_partial_meas ψ (QState.cast h_eq φ : QState b)
      = prob_partial_meas ψ φ := by
  subst h_eq
  have h_eq_state : (QState.cast rfl φ : QState a) = φ := by
    unfold QState.cast
    funext i j
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hj]; simp
  rw [h_eq_state]

/-! ## §13. Tightened conditional: `QPE_MMI_correct_modulo_qpe_semantics`

`QPE_MMI_correct_assuming_orbit_factorization` (§10.x) takes the entire
`h_orbit_exists` existential as a single hypothesis, packaging both
the (now-proven) orbit-side requirements and the (still-blocked) QPE
circuit-semantics step.

With Phase 4.A/4.C/4.D/4.E complete (the orbit-side infrastructure in
`SQIRPort/Eigenstate.lean`), we can substitute the proven β family
(`modmult_eigenstate_combined`) and the orbit-superposition state
(`shor_orbit_state` below) into the existential, leaving only the
single state-equality hypothesis `h_qpe_semantics` — which IS the
4.B circuit-semantics step. This narrows the "what's left to prove"
surface to one named identity. -/

/-- **Shor orbit-superposition state**: the closed-form
`(1/√r) · ∑_{k<r} qpe_phase_state_m(k/r) ⊗ ψ_k^{combined}` that the
QPE_var circuit IDEALLY outputs on input `|0^m⟩ ⊗ |1⟩_n ⊗ |0⟩_anc`.

Used as the `actual_state` witness in the tighter
`QPE_MMI_correct_modulo_qpe_semantics` conditional. -/
noncomputable def shor_orbit_state (a r N m n anc : Nat) :
    Matrix (Fin (2^(m + (n + anc)))) (Fin 1) ℂ :=
  fun i j => (1 / (Real.sqrt r : ℂ)) *
    ((∑ j_idx : Fin r,
       FormalRV.Framework.kron_vec
         (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
         (modmult_eigenstate_combined a r N n anc j_idx))
      i j)

/-- **`QPE_MMI_correct_modulo_qpe_semantics`** (Phase 4 tightened
conditional): strictly stronger than
`QPE_MMI_correct_assuming_orbit_factorization` because it discharges
the orbit-side conjuncts (orthonormality + state factorization) using
the now-proven `modmult_eigenstate_combined` + its orthonormality
theorem.

The only remaining hypothesis is the genuine 4.B QPE circuit-semantics
step: the equality
`prob_partial_meas Shor_final_state = prob_partial_meas shor_orbit_state`,
i.e., that QPE_var applied to the Shor input state actually produces
the orbit-superposition closed form (modulo measurement-probability
equivalence).

This is the maximal closure achievable WITHOUT fixing the `control`
stub at `Framework/UnitaryOps.lean:972`. Closing the `h_qpe_semantics`
hypothesis ⟹ closing `QPE_MMI_correct`. -/
theorem QPE_MMI_correct_modulo_qpe_semantics
    (a r N m n anc k : Nat) (f : Nat → BaseUCom (n + anc))
    (h_basic : BasicSetting a r N m n)
    (h_mmi : ModMulImpl a N n anc f)
    (h_wt : ∀ i, i < m → uc_well_typed (f i))
    (h_k_lt : k < r)
    (h_qpe_semantics :
      prob_partial_meas (basis_vector (2^m) (s_closest m k r))
          (Shor_final_state m n anc f)
        = prob_partial_meas (basis_vector (2^m) (s_closest m k r))
              (shor_orbit_state a r N m n anc)) :
    prob_partial_meas (basis_vector (2^m) (s_closest m k r))
        (Shor_final_state m n anc f)
      ≥ 4 / (Real.pi^2 * (r : ℝ)) := by
  apply QPE_MMI_correct_assuming_orbit_factorization a r N m n anc k f
    h_basic h_mmi h_wt h_k_lt
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, _, h_n_bounds⟩ := h_basic
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  have h_N_gt_one : 1 < N := by omega
  have h_N_lt_pow : N ≤ 2^n := h_n_bounds.1.le
  refine ⟨modmult_eigenstate_combined a r N n anc,
          shor_orbit_state a r N m n anc, ?_, rfl, h_qpe_semantics⟩
  intros j j'
  exact modmult_eigenstate_combined_orthonormal a r N n anc h_r_pos h_arN h_min
    h_N_gt_one h_N_lt_pow j j'

end FormalRV.SQIRPort
