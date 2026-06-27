/- PhaseKickback — Part1 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.QPE.ControlledGates
import FormalRV.Shor.MainAlgorithm

namespace FormalRV.SQIRPort
open FormalRV.Framework
open FormalRV.Framework.BaseUCom

/-! ## Shifted-data-register lemmas -/

/-- **Shifted freshness.** Any control qubit `q < m` is fresh in the
shift-lifted circuit `map_qubits (fun x => m + x) c`, because every gate's
qubit index becomes `m + n ≥ m > q`. -/
theorem is_fresh_map_qubits_shift {m anc q : Nat}
    (c : BaseUCom anc) (hq : q < m) :
    is_fresh q (map_qubits (fun x => m + x) c : BaseUCom (m + anc)) := by
  induction c with
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | app1 _ n => show q ≠ m + n; omega
  | app2 _ a b => exact ⟨by show q ≠ m + a; omega, by show q ≠ m + b; omega⟩
  | app3 _ a b c =>
      exact ⟨by show q ≠ m + a; omega,
             by show q ≠ m + b; omega,
             by show q ≠ m + c; omega⟩

/-- **Shifted well-typedness.** A circuit well-typed on `anc` qubits
becomes well-typed on `m + anc` after shifting every index by `+m`. -/
theorem wellTyped_map_qubits_shift {m anc : Nat}
    (c : BaseUCom anc) (h_wt : UCom.WellTyped anc c) :
    UCom.WellTyped (m + anc)
      (map_qubits (fun x => m + x) c : BaseUCom (m + anc)) := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      cases h_wt with
      | seq h₁ h₂ => exact UCom.WellTyped.seq (ih₁ h₁) (ih₂ h₂)
  | app1 _ n =>
      cases h_wt with
      | app1 hn => exact UCom.WellTyped.app1 (show m + n < m + anc by omega)
  | app2 _ a b =>
      cases h_wt with
      | app2 ha hb hab =>
        exact UCom.WellTyped.app2
          (show m + a < m + anc by omega)
          (show m + b < m + anc by omega)
          (show m + a ≠ m + b by omega)
  | app3 _ a b d =>
      cases h_wt with
      | app3 ha hb hd hab hbd had =>
        exact UCom.WellTyped.app3
          (show m + a < m + anc by omega)
          (show m + b < m + anc by omega)
          (show m + d < m + anc by omega)
          (show m + a ≠ m + b by omega)
          (show m + b ≠ m + d by omega)
          (show m + a ≠ m + d by omega)

/-- **Block-disjoint commutation.** For any control-register qubit
`q < m`, the matrix `pad_u (m + anc) q U` commutes with the matrix
semantics of a shift-lifted data-register circuit. This is the crucial
lemma validating the `h_comm_all` hypothesis of the abstract cascade
theorem for QPE's specific block layout.

Proof by induction on `c`:
- `seq`: by IH on both sides + reassociation;
- `app1 (R θ φ λ) n`: shifted target `m + n` satisfies `q < m ≤ m + n`,
  so `pad_u_disjoint_comm'` applies;
- `app2 CNOT a b`: shifted targets `m + a`, `m + b` both `> q`, so
  `pad_u_pad_ctrl_disjoint_comm` applies;
- `app3`: vacuous since `BaseUnitary 3` is empty. -/
theorem uc_eval_map_qubits_shift_commutes_pad_u {m anc q : Nat}
    (c : BaseUCom anc) (hq : q < m) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    pad_u (m + anc) q U *
        FormalRV.Framework.uc_eval
          (map_qubits (fun x => m + x) c : BaseUCom (m + anc))
      = FormalRV.Framework.uc_eval
          (map_qubits (fun x => m + x) c : BaseUCom (m + anc)) *
          pad_u (m + anc) q U := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      show pad_u (m + anc) q U *
            (FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₂ : BaseUCom (m + anc)) *
              FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₁ : BaseUCom (m + anc)))
            = (FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₂ : BaseUCom (m + anc)) *
              FormalRV.Framework.uc_eval
                (map_qubits (fun x => m + x) c₁ : BaseUCom (m + anc))) *
              pad_u (m + anc) q U
      rw [← Matrix.mul_assoc, ih₂, Matrix.mul_assoc, ih₁, ← Matrix.mul_assoc]
  | app1 u n =>
      cases u with
      | R θ φ lam =>
        show pad_u (m + anc) q U * pad_u (m + anc) (m + n) (rotation θ φ lam) = _
        exact pad_u_disjoint_comm' (m + anc) q (m + n) U (rotation θ φ lam)
                (by omega)
  | app2 u a b =>
      cases u
      show pad_u (m + anc) q U * pad_ctrl (m + anc) (m + a) (m + b) σx = _
      exact pad_u_pad_ctrl_disjoint_comm (m + anc) q (m + a) (m + b) U σx
              (by omega) (by omega)
  | app3 u _ _ _ => cases u

/-! ## QPE-shifted cascade theorem -/

/-- **QPE-SHIFTED CASCADE THEOREM.** The full controlled-powers
phase-kickback identity, specialized to QPE's shift-lifted oracle
family `i ↦ map_qubits (fun x => m + x) (f i)`. All commutation,
freshness, and well-typedness hypotheses of the abstract cascade
theorem are discharged automatically using the three lemmas above;
the caller need only supply the per-oracle well-typedness and the
common eigenstate relation. -/
theorem uc_eval_controlled_powers_shifted_on_common_eigenstate
    {m anc : Nat} (hd : 0 < m + anc)
    (f : Nat → BaseUCom anc)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (ψ : Matrix (Fin (2^(m + anc))) (Fin 1) ℂ) (ζ : Nat → ℂ)
    (h_eig : ∀ i, i < m →
        FormalRV.Framework.uc_eval
          (map_qubits (fun x => m + x) (f i) : BaseUCom (m + anc)) * ψ
          = ζ i • ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun x => m + x) (f i) : BaseUCom (m + anc))) m) * ψ
      = @phase_projector_product (m + anc) ζ m * ψ := by
  let g : Nat → BaseUCom (m + anc) :=
    fun i => map_qubits (fun x => m + x) (f i)
  apply uc_eval_controlled_powers_on_common_eigenstate_recursive hd g ψ ζ m
  · intro i hi; omega
  · intro i hi; exact is_fresh_map_qubits_shift (f i) hi
  · intro i hi; exact wellTyped_map_qubits_shift (f i) (h_wt_all i hi)
  · intro i j hi _ U; exact uc_eval_map_qubits_shift_commutes_pad_u (f j) hi U
  · exact h_eig

/-! ## Pre-QFT QPE composition (conditional)

The next layer up is the pre-QFT composition: H on the control
register, followed by `controlled_powers`, on a common eigenstate.

This composition depends on two pieces of `pad_u`/`kron_vec` interaction
infrastructure that the framework currently lacks:

1. **`KronVecShiftHyp`** — the shifted oracle's action on `kron_vec χ ψ`
   factors through `ψ`: it acts as `f` on the data register and leaves
   the control register `χ` untouched.

2. **`NparHKronZerosUniformHyp`** — `npar_H m` on `kron_zeros m ⊗ᵥ ψ`
   produces the uniform-superposition state on the control register
   while leaving the data register `ψ` untouched.

Both reduce to the same fundamental `pad_u`-on-`kron_vec` interaction
lemma (flagged at `Shor.lean:4843-4845` as a known multi-file gap).
Once that infrastructure is in place, both hypotheses become provable
auxiliary lemmas; until then they are exposed as explicit hypotheses
on the conditional theorems below. -/

/-- **The shifted-oracle / kron-vec interaction hypothesis.**

`pad_u`/`pad_ctrl` on the data-register block `[m, m + anc)` should
act on a `kron_vec` state by leaving the control component `χ`
unchanged and applying the unshifted oracle to the data component `ψ`.

This abbreviation packages the statement so the conditional
theorems below can require it as an explicit hypothesis. Proving it
unconditionally (i.e., for every `f : BaseUCom anc`) requires the
`pad_u`-on-`kron_vec` interaction infrastructure (a known
multi-file gap in the framework). -/
abbrev KronVecShiftHyp (m anc : Nat) (f : FormalRV.Framework.BaseUCom anc)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) : Prop :=
  FormalRV.Framework.uc_eval
      (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
    * kron_vec χ ψ
    = kron_vec χ (FormalRV.Framework.uc_eval f * ψ)

/-- **Conditional eigen-on-kron-control.** Given the kron-vec
interaction hypothesis and the data-register eigen-relation, the
combined `χ ⊗ᵥ ψ` is an eigenstate of the shifted oracle with the
same eigenvalue. The proof is one rewrite + a scalar pull-out
(`kron_vec_smul_right`). -/
theorem lifted_oracle_eigen_on_kron_control_conditional
    {m anc : Nat}
    (f : FormalRV.Framework.BaseUCom anc)
    (χ : Matrix (Fin (2^m)) (Fin 1) ℂ)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ)
    (ζ : ℂ)
    (h_eig : FormalRV.Framework.uc_eval f * ψ = ζ • ψ)
    (h_shift_kron : KronVecShiftHyp m anc f χ ψ) :
    FormalRV.Framework.uc_eval
        (map_qubits (fun q => m + q) f : FormalRV.Framework.BaseUCom (m + anc))
        * kron_vec χ ψ
      = ζ • kron_vec χ ψ := by
  unfold KronVecShiftHyp at h_shift_kron
  rw [h_shift_kron, h_eig, kron_vec_smul_right]

/-- **The H-on-zeros / uniform-superposition hypothesis.** The
column of Hadamards `npar_H m` applied to `kron_vec (kron_zeros m) ψ`
produces the uniform superposition `(1/√2^m) · ∑_x |x⟩ ⊗ ψ` on
the control register, leaving the data register `ψ` untouched. -/
abbrev NparHKronZerosUniformHyp (m anc : Nat)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) : Prop :=
  FormalRV.Framework.uc_eval
      (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
    * kron_vec (kron_zeros m) ψ
    = ((1 : ℂ) / Real.sqrt (2 ^ m)) •
        ∑ x : Fin (2^m),
          kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ

/-- **CONDITIONAL pre-QFT QPE composition on a common eigenstate.**

Composes `npar_H m` (Hadamard layer on control register) with the
shifted controlled-powers cascade. The eigenvalue carries to the
phase-projector-product form on the uniform-superposition state.

This is the pre-QFT half of QPE; combining it with `QFTinv k` on the
phase-projector-product form yields the `qpe_phase_state k θ ⊗ ψ`
that QPE measurement projects against.

The conditional version takes two explicit hypotheses for the missing
`pad_u`/`kron_vec` infrastructure:

- `h_npar_H : NparHKronZerosUniformHyp m anc ψ` — the H-on-zeros step;
- `h_shift_kron_eig_uniform` — the shifted-oracle eigen-relation on
  the uniform-superposition state. (The latter would follow from
  `h_eig_data` + a `KronVecShiftHyp` lemma for the uniform sum;
  exposed here as a single hypothesis for the conditional form.)

Once the `pad_u`-on-`kron_vec` infrastructure lands, both hypotheses
become provable and the conditional becomes unconditional. -/
theorem QPE_pre_QFT_on_eigenstate_conditional
    {m anc : Nat} (hmanc : 0 < m + anc)
    (f : Nat → FormalRV.Framework.BaseUCom anc)
    (ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ) (ζ : Nat → ℂ)
    (h_wt_all : ∀ i, i < m → UCom.WellTyped anc (f i))
    (h_shift_kron_eig_uniform : ∀ i, i < m →
      FormalRV.Framework.uc_eval
          (map_qubits (fun q => m + q) (f i) :
            FormalRV.Framework.BaseUCom (m + anc))
        * (((1 : ℂ) / Real.sqrt (2 ^ m)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
        = ζ i • (((1 : ℂ) / Real.sqrt (2 ^ m)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ))
    (h_npar_H : NparHKronZerosUniformHyp m anc ψ) :
    FormalRV.Framework.uc_eval (controlled_powers
        (fun i => (map_qubits (fun q => m + q) (f i) :
          FormalRV.Framework.BaseUCom (m + anc))) m)
      * (FormalRV.Framework.uc_eval
            (npar_H m : FormalRV.Framework.BaseUCom (m + anc))
          * kron_vec (kron_zeros m) ψ)
      = @phase_projector_product (m + anc) ζ m
        * (((1 : ℂ) / Real.sqrt (2 ^ m)) •
            ∑ x : Fin (2^m),
              kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ) := by
  unfold NparHKronZerosUniformHyp at h_npar_H
  rw [h_npar_H]
  exact uc_eval_controlled_powers_shifted_on_common_eigenstate hmanc f h_wt_all
    (((1 : ℂ) / Real.sqrt (2 ^ m)) •
      ∑ x : Fin (2^m),
        kron_vec (FormalRV.Framework.basis_vector (2^m) x.val) ψ)
    ζ h_shift_kron_eig_uniform

/-! ## Toward the unconditional pad_u-on-kron_vec interaction

The current obstacle to unconditional pre-QFT QPE: prove

    pad_u (m + anc) (m + n) M * kron_vec χ ψ
      = kron_vec χ (pad_u anc n M * ψ)

for arbitrary `χ : Matrix (Fin (2^m)) (Fin 1) ℂ` and
`ψ : Matrix (Fin (2^anc)) (Fin 1) ℂ`. This is hard because:

- `pad_u` is defined via `Matrix.kronecker` + a 3-way `padEquiv` reindex
  splitting `Fin (2^(m+anc))` into `(Fin (2^(m+n)) × Fin 2) × Fin (2^(anc-n-1))`.
- `kron_vec` is defined via a 2-way `kronEquiv` reindex splitting
  `Fin (2^(m+anc))` into `Fin (2^m) × Fin (2^anc)`.
- The two reindexings are compatible but expressing the compatibility
  requires explicit index arithmetic.

The cleanest path forward leverages `Matrix.mul_kronecker_mul`
(`(A ⊗ₖ B) * (v ⊗ₖ w) = (A v) ⊗ₖ (B w)`):

1. Prove `pad_u (m + anc) (m + n) M = reindex_e (Iₙ (2^m) ⊗ₖ pad_u anc n M)`
   for some explicit equiv `e` — the "shifted-pad_u decomposition".
2. Prove `kron_vec χ ψ = reindex_e (χ ⊗ₖ ψ)` for the same `e`.
3. Apply `Matrix.mul_kronecker_mul` and the reindex identity.

Estimated scope: comparable to existing `pad_u_pad_u_disjoint_decomp`
chains in `UnitarySem.lean` (~200-500 LOC of mathlib Kronecker /
reindex work).

Single-deliverable seed proved here: the explicit-basis form of the
kron-of-basis identity, which feeds into the future entry-wise proof. -/

/-- **Kron of two basis vectors = basis of combined index.** The
elementary fact that `|x⟩ ⊗ |y⟩` (on `m + anc` qubits) is the standard
basis vector for the combined index `kron_vec_combine x y`. Used
downstream when the QPE proof reduces actions on `kron_vec` to actions
on individual basis states. -/
theorem kron_vec_basis_eq_basis_combine (a b : Nat) (x : Fin (2^a)) (y : Fin (2^b)) :
    kron_vec (FormalRV.Framework.basis_vector (2^a) x.val)
             (FormalRV.Framework.basis_vector (2^b) y.val)
      = FormalRV.Framework.basis_vector (2^(a+b)) (kron_vec_combine x y).val := by
  ext i col
  fin_cases col
  rw [kron_vec_apply,
      FormalRV.Framework.basis_vector_apply,
      FormalRV.Framework.basis_vector_apply,
      FormalRV.Framework.basis_vector_apply]
  by_cases hi : i = kron_vec_combine x y
  · rw [hi, kron_vec_high_combine, kron_vec_low_combine]
    simp
  · have hi_val : (i : Nat) ≠ (kron_vec_combine x y : Nat) := fun h => hi (Fin.ext h)
    rw [if_neg hi_val]
    by_cases hH : (kron_vec_high i : Nat) = (x : Nat)
    · by_cases hL : (kron_vec_low i : Nat) = (y : Nat)
      · exfalso
        apply hi
        apply kron_vec_high_low_inj
        · apply Fin.ext; rw [kron_vec_high_combine]; exact hH
        · apply Fin.ext; rw [kron_vec_low_combine]; exact hL
      · rw [if_neg hL]; ring
    · rw [if_neg hH]; ring


end FormalRV.SQIRPort
