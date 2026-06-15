/-
  FormalRV.Shor.MeasuredANDUncompute — Gidney's measurement-based AND-uncompute
  at the LOGICAL layer (density-matrix semantics on `Com`/`c_eval`).

  Gidney (arXiv:1709.06648 §"temporary AND"; arXiv:1905.07682 Fig. 4, l.200–227):
  to uncompute an AND ancilla `c` holding `f a ∧ f b`, instead of paying a second
  Toffoli, MEASURE the ancilla in the X basis and apply a classically-controlled
  `CZ a b` phase fixup (then reset the ancilla).  This file proves, at the
  density-matrix layer, that the channel is the PERFECT uncompute on every state
  of the "computed family" (finite superpositions whose ancilla bit equals the
  AND of the two control bits):

      `c_eval (measANDUncompute dim a b c) (ψ ⬝ ψᴴ) = ψ' ⬝ ψ'ᴴ`

  where `ψ = Σ_x α_x |x⟩` with `x c = (x a && x b)` on the support, and
  `ψ' = Σ_x α_x |x with bit c cleared⟩`.

  Modelling: the X-measurement is `H c` followed by a Z-basis `meas`; outcome 1
  (post-state has `c = |1⟩`) triggers the fixup `CZ a b ; X c` (phase fix + reset
  so the ancilla is released as `|0⟩`); outcome 0 needs no fixup.

  Per-branch content (the real mathematics, at the state-vector level):
    * outcome 0:  `P₀ (H_c ψ) = (√2/2) • ψ'`                  (`measAND_branch0`)
    * outcome 1:  `(X_c · CZ_ab) (P₁ (H_c ψ)) = (√2/2) • ψ'`  (`measAND_branch1`)
  Each branch contributes `(1/2) • ψ'ψ'ᴴ` to the channel output; they sum to
  `ψ'ψ'ᴴ` (`measANDUncompute_perfect`).

  T-count note: the channel contains only `H`, `CZ`, `X` and a computational-basis
  measurement — all Clifford, NO T gates.  (The repo has no T-counter at the
  `UCom`/`Com` layer — `Gate.tcount` lives in the classical reversible IR and
  `EGate.tcount` in `Shor.MeasUncompute` — so the Clifford claim is recorded here
  rather than as a counted theorem; the structural 0-Toffoli accounting for the
  measurement-based uncompute is `Shor.MeasUncompute.tcount_mzList` et al.)

  Precedent (structural only, no semantics): `FormalRV.PPM.Magic.GidneyAND`.
  This file is the first semantic (density/channel-level) verification of the
  pattern in the repo.
-/
import FormalRV.Core.DensitySem
import FormalRV.Core.GateDecompositions

namespace FormalRV.Shor.MeasuredANDUncompute

open FormalRV.Framework
open FormalRV.Framework.BaseCom
open FormalRV.Framework.BaseUCom (proj)
open Matrix

noncomputable section

/-! ## The channel

    `H c ; meas c (CZ a b ; X c) skip` — X-measure the AND ancilla `c`;
    on outcome 1 apply the `CZ a b` phase fixup and reset `c` with `X c`
    (the measured qubit is in `|1⟩`, so `X` releases it as `|0⟩`);
    on outcome 0 do nothing. -/

/-- Gidney's measurement-based AND-uncompute as a `Com` program:
    `H c ; meas c (CZ a b ; X c) skip`. -/
def measANDUncompute (dim a b c : Nat) : BaseCom dim :=
  Com.useq (Com.embedU (BaseUCom.H c))
    (Com.meas c
      (Com.useq (Com.embedU (BaseUCom.CZ a b)) (Com.embedU (BaseUCom.X c)))
      Com.cskip)

/-! ## Scalar helpers: the Hadamard weight `√2/2` -/

/-- `(√2/2)·(√2/2) = 1/2` — the Hadamard weight squares to the branch probability. -/
theorem sqrt2_half_mul_self :
    (Real.sqrt 2 / 2 : ℂ) * (Real.sqrt 2 / 2 : ℂ) = 1 / 2 := by
  rw [div_mul_div_comm, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- `√2/2` is real, hence self-conjugate. -/
theorem star_sqrt2_half :
    star (Real.sqrt 2 / 2 : ℂ) = (Real.sqrt 2 / 2 : ℂ) := by
  have h : (Real.sqrt 2 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.star_def, Complex.conj_ofReal]

/-- `(√2/2)·conj(√2/2) = 1/2` — the squared norm of the Hadamard weight. -/
theorem sqrt2_half_mul_star :
    (Real.sqrt 2 / 2 : ℂ) * star (Real.sqrt 2 / 2 : ℂ) = 1 / 2 := by
  rw [star_sqrt2_half, sqrt2_half_mul_self]

/-! ## CZ on a computational basis state

    No CZ action lemma existed in Core; we derive it from the `H·CNOT·H`
    definition of `CZ` via the existing H/CNOT basis-action lemmas. -/

/-- **`CZ` is a pure phase on basis states**: `CZ_{m,n} |f⟩ = (-1)^{f m ∧ f n} |f⟩`. -/
theorem f_to_vec_CZ (dim m n : Nat) (hm : m < dim) (hn : n < dim) (hmn : m ≠ n)
    (f : Nat → Bool) :
    uc_eval (BaseUCom.CZ m n : BaseUCom dim) * f_to_vec dim f
      = (if f m && f n then (-1 : ℂ) else 1) • f_to_vec dim f := by
  have hseq : uc_eval (BaseUCom.CZ m n : BaseUCom dim)
      = uc_eval (BaseUCom.H n : BaseUCom dim)
        * uc_eval (BaseUCom.CNOT m n : BaseUCom dim)
        * uc_eval (BaseUCom.H n : BaseUCom dim) := rfl
  rw [hseq, Matrix.mul_assoc, Matrix.mul_assoc,
      f_to_vec_H_uc_eval dim n hn f,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      f_to_vec_CNOT_proved dim m n (update f n false) hm hn hmn,
      f_to_vec_CNOT_proved dim m n (update f n true) hm hn hmn]
  simp only [update_idem, update_eq, update_neq _ n m _ hmn,
             Bool.false_xor, Bool.true_xor]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      f_to_vec_H_uc_eval dim n hn (update f n (f m)),
      f_to_vec_H_uc_eval dim n hn (update f n (!f m))]
  simp only [update_idem, update_eq]
  have hupd0 : f n = false → update f n false = f := fun h => by
    rw [← h]; exact update_self f n
  have hupd1 : f n = true → update f n true = f := fun h => by
    rw [← h]; exact update_self f n
  cases hfm : f m <;> cases hfn : f n
  · rw [hupd0 hfn]; norm_num
    simp only [smul_smul]; rw [sqrt2_half_mul_self]; module
  · rw [hupd1 hfn]; norm_num
    simp only [smul_smul]; rw [sqrt2_half_mul_self]; module
  · rw [hupd0 hfn]; norm_num
    simp only [smul_smul]; rw [sqrt2_half_mul_self]; module
  · rw [hupd1 hfn]; norm_num
    simp only [smul_smul]; rw [sqrt2_half_mul_self]; module

/-! ## The two measurement branches on a single computed basis state -/

/-- **Branch 0 (outcome 0, no fixup)**: projecting the Hadamard-rotated ancilla
    onto `|0⟩` already yields the cleaned state, with amplitude `√2/2`.
    (Holds for every basis state — the AND constraint is not even needed here.) -/
theorem measAND_branch0_basis {dim : Nat} (c : Nat) (hc : c < dim) (f : Nat → Bool) :
    proj c dim false * (uc_eval (BaseUCom.H c : BaseUCom dim) * f_to_vec dim f)
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f c false) := by
  rw [f_to_vec_H_uc_eval dim c hc f, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      proj_false_on_f_to_vec dim c hc, proj_false_on_f_to_vec dim c hc]
  simp [update_eq]

/-- **Branch 1 (outcome 1, `CZ a b ; X c` fixup)**: projecting onto `|1⟩` leaves
    the phase `(-1)^{f c} = (-1)^{f a ∧ f b}` (this is where the AND constraint
    enters); the classically-controlled `CZ a b` cancels it and `X c` resets the
    ancilla — net result: the same cleaned state with amplitude `√2/2`. -/
theorem measAND_branch1_basis {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Nat → Bool) (hf : f c = (f a && f b)) :
    uc_eval (BaseUCom.X c : BaseUCom dim)
        * (uc_eval (BaseUCom.CZ a b : BaseUCom dim)
          * (proj c dim true * (uc_eval (BaseUCom.H c : BaseUCom dim) * f_to_vec dim f)))
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f c false) := by
  rw [f_to_vec_H_uc_eval dim c hc f, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      proj_true_on_f_to_vec dim c hc, proj_true_on_f_to_vec dim c hc]
  simp only [update_eq, Bool.false_eq_true, if_true, if_false, smul_zero, zero_add]
  rw [Matrix.mul_smul, f_to_vec_CZ dim a b ha hb hab (update f c true)]
  simp only [update_neq _ c a _ hac, update_neq _ c b _ hbc]
  rw [Matrix.mul_smul, Matrix.mul_smul, f_to_vec_X_uc_eval dim c hc (update f c true)]
  simp only [update_idem, update_eq, Bool.not_true]
  rw [hf, smul_smul]
  cases h : f a && f b <;> simp

/-! ## The two measurement branches on finite superpositions (HEADLINE, vector level)

    The computed family: `ψ = Σ_{i ∈ s} α_i |g i⟩` with `g i c = g i a ∧ g i b`
    on the support.  Both branches map `ψ` to `(√2/2) • ψ'`, where
    `ψ' = Σ_{i ∈ s} α_i |g i with bit c cleared⟩` is the perfect uncompute. -/

/-- **Outcome-0 branch on a computed superposition**: `P₀ (H_c ψ) = (√2/2) • ψ'`. -/
theorem measAND_branch0 {dim : Nat} {ι : Type*} (c : Nat) (hc : c < dim)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool) :
    proj c dim false * (uc_eval (BaseUCom.H c : BaseUCom dim)
        * ∑ i ∈ s, α i • f_to_vec dim (g i))
      = (Real.sqrt 2 / 2 : ℂ) • ∑ i ∈ s, α i • f_to_vec dim (update (g i) c false) := by
  rw [Matrix.mul_sum, Matrix.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.mul_smul, measAND_branch0_basis c hc (g i)]
  exact smul_comm _ _ _

/-- **Outcome-1 branch on a computed superposition**:
    `(CZ a b ; X c) (P₁ (H_c ψ)) = (√2/2) • ψ'` — the classically-controlled
    fixup makes the outcome-1 post-state IDENTICAL to the outcome-0 one. -/
theorem measAND_branch1 {dim : Nat} {ι : Type*} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hAND : ∀ i ∈ s, g i c = (g i a && g i b)) :
    uc_eval (UCom.seq (BaseUCom.CZ a b) (BaseUCom.X c) : BaseUCom dim)
        * (proj c dim true * (uc_eval (BaseUCom.H c : BaseUCom dim)
            * ∑ i ∈ s, α i • f_to_vec dim (g i)))
      = (Real.sqrt 2 / 2 : ℂ) • ∑ i ∈ s, α i • f_to_vec dim (update (g i) c false) := by
  rw [uc_eval_seq, Matrix.mul_assoc, Matrix.mul_sum, Matrix.mul_sum, Matrix.mul_sum,
      Matrix.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      measAND_branch1_basis a b c ha hb hc hab hac hbc (g i) (hAND i hi)]
  exact smul_comm _ _ _

/-! ## Density-matrix assembly -/

/-- Conjugating a pure-state density matrix: `M (ψψᴴ) Mᴴ = (Mψ)(Mψ)ᴴ`. -/
theorem conj_outer_product {dim : Nat} (M : Square dim)
    (ψ : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    M * (ψ * ψᴴ) * Mᴴ = (M * ψ) * (M * ψ)ᴴ := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Outer product of a scaled vector: `(k•ψ)(k•ψ)ᴴ = (k·k̄) • ψψᴴ`. -/
theorem smul_outer_product {dim : Nat} (k : ℂ)
    (u : Matrix (Fin (2^dim)) (Fin 1) ℂ) :
    (k • u) * (k • u)ᴴ = (k * star k) • (u * uᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Channel plumbing: if both measurement branches send the (vector) state `ψ`
    to `(√2/2) • ψ'`, then the channel sends the density matrix `ψψᴴ` exactly to
    `ψ'ψ'ᴴ` — each branch contributes probability 1/2, and the two halves add up
    to the full pure target state. -/
theorem measANDUncompute_pure_step {dim : Nat} (a b c : Nat)
    (ψ ψ' : Matrix (Fin (2^dim)) (Fin 1) ℂ)
    (h0 : proj c dim false * (uc_eval (BaseUCom.H c : BaseUCom dim) * ψ)
            = (Real.sqrt 2 / 2 : ℂ) • ψ')
    (h1 : uc_eval (BaseUCom.X c : BaseUCom dim)
            * (uc_eval (BaseUCom.CZ a b : BaseUCom dim)
              * (proj c dim true * (uc_eval (BaseUCom.H c : BaseUCom dim) * ψ)))
            = (Real.sqrt 2 / 2 : ℂ) • ψ') :
    c_eval (measANDUncompute dim a b c) (ψ * ψᴴ) = ψ' * ψ'ᴴ := by
  simp only [measANDUncompute, c_eval_useq, c_eval_meas, c_eval_embedU, c_eval_skip]
  rw [conj_outer_product (uc_eval (BaseUCom.H c)) ψ,
      conj_outer_product (proj c dim true) (uc_eval (BaseUCom.H c : BaseUCom dim) * ψ),
      conj_outer_product (proj c dim false) (uc_eval (BaseUCom.H c : BaseUCom dim) * ψ),
      conj_outer_product (uc_eval (BaseUCom.CZ a b))
        (proj c dim true * (uc_eval (BaseUCom.H c : BaseUCom dim) * ψ)),
      conj_outer_product (uc_eval (BaseUCom.X c))
        (uc_eval (BaseUCom.CZ a b : BaseUCom dim)
          * (proj c dim true * (uc_eval (BaseUCom.H c : BaseUCom dim) * ψ))),
      h0, h1, smul_outer_product, sqrt2_half_mul_star, ← add_smul]
  norm_num

/-- **HEADLINE (density level)**: Gidney's measurement-based AND-uncompute is the
    PERFECT uncompute on the computed family.  For every finite superposition
    `ψ = Σ_{i ∈ s} α_i |g i⟩` whose ancilla bit satisfies `g i c = g i a ∧ g i b`,

        `c_eval (measANDUncompute dim a b c) (ψψᴴ) = ψ'ψ'ᴴ`

    where `ψ' = Σ_{i ∈ s} α_i |g i with bit c cleared⟩`: the data register is
    untouched (coefficients `α` intact) and the ancilla is released as `|0⟩` —
    with NO Toffoli/T gate (the channel is H, CZ, X, measurement: all Clifford). -/
theorem measANDUncompute_perfect {dim : Nat} {ι : Type*} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hAND : ∀ i ∈ s, g i c = (g i a && g i b)) :
    c_eval (measANDUncompute dim a b c)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (update (g i) c false))
          * (∑ i ∈ s, α i • f_to_vec dim (update (g i) c false))ᴴ := by
  have h1 := measAND_branch1 a b c ha hb hc hab hac hbc s α g hAND
  rw [uc_eval_seq, Matrix.mul_assoc] at h1
  exact measANDUncompute_pure_step a b c _ _
    (measAND_branch0 c hc s α g) h1

/-! ## Single-basis-state corollary and concrete smoke checks -/

/-- The single computed basis state `|f⟩` (with `f c = f a ∧ f b`) is mapped to
    `|f with bit c cleared⟩` — coefficient concentrated on one `x`. -/
theorem measANDUncompute_basis {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Nat → Bool) (hf : f c = (f a && f b)) :
    c_eval (measANDUncompute dim a b c)
        (f_to_vec dim f * (f_to_vec dim f)ᴴ)
      = f_to_vec dim (update f c false) * (f_to_vec dim (update f c false))ᴴ := by
  have h := measANDUncompute_perfect (ι := Unit) a b c ha hb hc hab hac hbc
      Finset.univ (fun _ => (1 : ℂ)) (fun _ => f) (fun _ _ => hf)
  simpa using h

/-- Smoke check (AND = 1): `|111⟩` on `(a,b,c) = (0,1,2)` — ancilla holds
    `1 = 1 ∧ 1` — is uncomputed to `|c cleared⟩` with the data bits intact. -/
theorem measANDUncompute_smoke_and_true :
    c_eval (measANDUncompute 3 0 1 2)
        (f_to_vec 3 (fun _ => true) * (f_to_vec 3 (fun _ => true))ᴴ)
      = f_to_vec 3 (update (fun _ => true) 2 false)
          * (f_to_vec 3 (update (fun _ => true) 2 false))ᴴ :=
  measANDUncompute_basis 0 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ rfl

/-- Smoke check (AND = 0): `|x⟩` with `x = (a:1, b:0, c:0)` — ancilla holds
    `0 = 1 ∧ 0` — is a fixed point up to the (trivial) bit-c clear. -/
theorem measANDUncompute_smoke_and_false :
    c_eval (measANDUncompute 3 0 1 2)
        (f_to_vec 3 (fun n => decide (n = 0)) * (f_to_vec 3 (fun n => decide (n = 0)))ᴴ)
      = f_to_vec 3 (update (fun n => decide (n = 0)) 2 false)
          * (f_to_vec 3 (update (fun n => decide (n = 0)) 2 false))ᴴ :=
  measANDUncompute_basis 0 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ rfl

end -- noncomputable section

end FormalRV.Shor.MeasuredANDUncompute
