/-
  FormalRV.Shor.CFS.ApproxPeriodFinding — the bridge from the modular-deviation bound to APPROXIMATE
  PERIODICITY, the first half of "deviation → success" (Gidney 2025, §"Approximate Period Finding",
  main.tex line 432–440).

  Per "semantic proof BEFORE resource proof".  The previous layers proved the CFS approximate modexp
  `f̃` deviates from the exact `f(x) = g^x mod N` by a bounded amount (`TruncatedAccumulation`).  Shor's
  algorithm needs PERIODICITY; `f̃` is only APPROXIMATELY periodic.  The paper's eq:438 states

      ∀ x y : Δ_N( f̃(x + yP) − f̃(x) ) ≤ ε.

  This file PROVES that — approximate periodicity follows from (a) exact periodicity of `f` and (b) the
  pointwise deviation bound, via the `Δ_N` triangle inequality.  It also proves the exact modexp IS
  periodic, so the hypotheses are real.

    * `modexp_periodic` — `x ↦ g^x mod N` is exactly periodic with period `r` whenever `g^r ≡ 1`.
    * `periodic_mul`    — exact periodicity extends to all multiples `yP`.
    * `approx_periodic` — **APPROXIMATE PERIODICITY**: if `f` is exactly periodic and `Δ_N(f,f̃) ≤ ε`
      pointwise, then `Δ_N(f̃(x+yP) − f̃(x)) ≤ 2ε` (paper eq:438; the factor 2 = the two endpoints).

  ## HONEST remaining links of "deviation → success" (the deep QUANTUM half, documented not faked)

  After approximate periodicity, the paper's success argument is:
    1. (eq:max-infidelity, line 503) superposition masking with a width-`⌈SN⌉` mask makes the actual
       pre-measurement state `|ψ̃₁⟩` overlap the ideal `|ψ₁⟩` with infidelity `≤ ε/S`.  This is a
       QUANTUM state-overlap bound (amplitudes of two offset uniform superpositions) — not yet
       formalised; it needs the masked-state inner product.
    2. period finding on the IDEAL state `|ψ₁⟩` succeeds — this is the standard (exact) analysis,
       anchored by `FormalRV.SQIRPort.probability_of_success` (the ported SQIR Shor bound).
    3. Ekerå–Håstad post-processing (main.tex §"Ekerå–Håstad Period Finding") turns the recovered
       frequency into the factorisation.
  Steps 1–3 are the quantum/number-theoretic residue; step 2 already exists for the exact case.
  This file closes the purely-arithmetic entry point (1's classical premise: bounded deviation ⟹
  approximate periodicity).
-/
import FormalRV.Shor.CFS.ModularDeviation

namespace FormalRV.CFS

/-- An exactly-periodic function modulo `N`: `f(x+P) ≡ f(x)`. -/
def Periodic (N P : ℕ) (f : ℕ → ℕ) : Prop := ∀ x, f (x + P) ≡ f x [MOD N]

/-- The modular exponentiation `x ↦ g^x mod N` is exactly periodic with any period `r` for which
    `g^r ≡ 1 (mod N)` (in particular the multiplicative order of `g`). -/
theorem modexp_periodic (N g r : ℕ) (hr : g ^ r ≡ 1 [MOD N]) :
    Periodic N r (fun x => g ^ x % N) := by
  intro x
  show g ^ (x + r) % N ≡ g ^ x % N [MOD N]
  have h : g ^ (x + r) ≡ g ^ x [MOD N] := by
    calc g ^ (x + r) = g ^ x * g ^ r := by rw [pow_add]
      _ ≡ g ^ x * 1 [MOD N] := Nat.ModEq.mul_left _ hr
      _ = g ^ x := by ring
  exact (Nat.mod_modEq _ _).trans (h.trans (Nat.mod_modEq _ _).symm)

/-- Exact periodicity extends to all integer multiples of the period: `f(x + y·P) ≡ f(x)`. -/
theorem periodic_mul (N P : ℕ) (f : ℕ → ℕ) (hf : Periodic N P f) :
    ∀ y x, f (x + y * P) ≡ f x [MOD N]
  | 0, x => by simp [Nat.ModEq]
  | y + 1, x => by
      have hrw : x + (y + 1) * P = (x + y * P) + P := by ring
      rw [hrw]
      exact (hf _).trans (periodic_mul N P f hf y x)

/-- **Approximate periodicity** (Gidney 2025 eq:438).  If `f` is exactly periodic mod `N` and the
    approximation `f̃` deviates from `f` by at most `ε` at every point, then `f̃` is approximately
    periodic with deviation at most `2ε`: `Δ_N( f̃(x+yP) − f̃(x) ) ≤ 2ε`.  Proof: the `Δ_N` triangle
    inequality through the two exactly-periodic anchors `f(x+yP) = f(x)`. -/
theorem approx_periodic (N P : ℕ) (hN : 0 < N) (f ftil : ℕ → ℕ) (ε : ℕ)
    (hper : Periodic N P f) (hdev : ∀ x, modDev N (f x) (ftil x) ≤ ε) (x y : ℕ) :
    modDev N (ftil (x + y * P)) (ftil x) ≤ 2 * ε := by
  have h0 : modDev N (f (x + y * P)) (f x) = 0 :=
    (modDev_eq_zero_iff N _ _ hN).mpr (periodic_mul N P f hper y x)
  calc modDev N (ftil (x + y * P)) (ftil x)
      ≤ modDev N (ftil (x + y * P)) (f (x + y * P)) + modDev N (f (x + y * P)) (ftil x) :=
        modDev_triangle N _ _ _ hN
    _ ≤ modDev N (ftil (x + y * P)) (f (x + y * P))
          + (modDev N (f (x + y * P)) (f x) + modDev N (f x) (ftil x)) := by
        gcongr; exact modDev_triangle N _ _ _ hN
    _ = modDev N (ftil (x + y * P)) (f (x + y * P)) + modDev N (f x) (ftil x) := by rw [h0]; ring
    _ ≤ ε + ε := by
        gcongr
        · rw [modDev_comm]; exact hdev _
        · exact hdev _
    _ = 2 * ε := by ring

/-! ### The masked-state infidelity bound (eq:max-infidelity) — its classical/combinatorial core.

    The quantum step treats the actual state `|ψ̃₁⟩` as the ideal `|ψ₁⟩` at the cost of an infidelity
    `≤ ε/S` (line 503).  For each exponent `e`, the two conditioned states are uniform superpositions
    over two width-`⌈SN⌉` integer windows offset by `≤ Nε` (line 498).  Their fidelity is the
    normalised overlap `|A∩B|/W`.  The two lemmas below are the rigorous CLASSICAL core: the overlap
    count and the ratio bound `d/W ≤ ε/S`.  (The amplitude identity `|⟨ψ₁|ψ̃₁⟩| = |A∩B|/W` for uniform
    superpositions over `A`, `B` is the remaining quantum step.) -/

open scoped BigOperators in
/-- Overlap of two equal-width integer windows offset by `d ≤ W`: the ideal vs approximate masked
    output ranges (line 498) overlap in `W − d` values. -/
theorem window_overlap_card (a W d : ℕ) (hd : d ≤ W) :
    (Finset.Ico a (a + W) ∩ Finset.Ico (a + d) (a + d + W)).card = W - d := by
  rw [Finset.Ico_inter_Ico, show max a (a + d) = a + d by omega,
      show min (a + W) (a + d + W) = a + W by omega, Nat.card_Ico]
  omega

/-- **The infidelity bound's quantitative core** (eq:max-infidelity).  With offset `d ≤ N·ε` (the
    deviation) and mask width `W ≥ S·N`, the overlap ratio is `d/W ≤ ε/S`.  Combined with
    `window_overlap_card` and the uniform-superposition fidelity `|A∩B|/W`, this is the `ε/S`
    infidelity the paper trades for. -/
theorem infidelity_ratio_bound (N S eps d W : ℕ) (hN : 0 < N) (hS : 0 < S)
    (hd : d ≤ N * eps) (hW : S * N ≤ W) :
    (d : ℚ) / W ≤ (eps : ℚ) / S := by
  have hWc : ((S * N : ℕ) : ℚ) ≤ (W : ℚ) := by exact_mod_cast hW
  have hSNpos : (0 : ℚ) < ((S * N : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos hS hN
  have hWpos : (0 : ℚ) < W := lt_of_lt_of_le hSNpos hWc
  have hSpos : (0 : ℚ) < S := by exact_mod_cast hS
  have hdc : (d : ℚ) ≤ (N * eps : ℕ) := by exact_mod_cast hd
  rw [div_le_div_iff₀ hWpos hSpos]
  calc (d : ℚ) * S ≤ ((N * eps : ℕ) : ℚ) * S := by nlinarith [hdc, hSpos]
    _ = (eps : ℚ) * ((S * N : ℕ) : ℚ) := by push_cast; ring
    _ ≤ (eps : ℚ) * W := by nlinarith [hWc, Nat.cast_nonneg (α := ℚ) eps]

open scoped ComplexConjugate in
/-- Uniform superposition over a finite index set `A` of size `W`: amplitude `1/√W` on `A`, else 0
    (the conditioned masked output state of the period-finding register). -/
noncomputable def unifSuper {d : ℕ} (W : ℕ) (A : Finset (Fin d)) : Fin d → ℂ :=
  fun x => if x ∈ A then ((Real.sqrt W : ℂ))⁻¹ else 0

open scoped BigOperators ComplexConjugate in
/-- **The amplitude identity** — the only genuinely-quantum step of the masked-state infidelity
    bound.  The inner product of two uniform superpositions equals the normalised overlap of their
    supports: `⟨u_A | u_B⟩ = |A ∩ B| / W`.  So the conditioned fidelity IS the window overlap. -/
theorem unifSuper_inner {d : ℕ} (W : ℕ) (hW : 0 < W) (A B : Finset (Fin d)) :
    (∑ x, conj (unifSuper W A x) * unifSuper W B x) = ((A ∩ B).card : ℂ) / W := by
  have hWc : (Real.sqrt W : ℂ) ^ 2 = (W : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; norm_cast
  have key : ∀ x : Fin d, conj (unifSuper W A x) * unifSuper W B x
      = if x ∈ A ∩ B then ((Real.sqrt W : ℂ))⁻¹ ^ 2 else 0 := by
    intro x
    unfold unifSuper
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
      simp [hA, hB, Finset.mem_inter, map_inv₀, Complex.conj_ofReal, sq]
  simp_rw [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, inv_pow, hWc]
  field_simp

open scoped BigOperators ComplexConjugate in
/-- **The masked-state fidelity equals `(W − d)/W`** (eq:max-infidelity, combining the amplitude
    identity with `window_overlap_card`): two width-`W` masked windows whose supports overlap in
    `W − d` values have conditioned fidelity `⟨u_A|u_B⟩ = (W − d)/W`, hence infidelity `d/W` (which
    `infidelity_ratio_bound` caps at `ε/S`).  This closes the masked-state overlap argument; the
    remaining quantum links are global-fidelity-from-conditioned, QPE, and Ekerå–Håstad. -/
theorem masked_fidelity {D : ℕ} (W d : ℕ) (hW : 0 < W) (A B : Finset (Fin D))
    (hov : (A ∩ B).card = W - d) :
    (∑ x, conj (unifSuper W A x) * unifSuper W B x) = ((W - d : ℕ) : ℂ) / W := by
  rw [unifSuper_inner W hW A B, hov]

open scoped BigOperators ComplexConjugate in
/-- **Global fidelity from conditioned fidelities** (paper line 501: "true for every condition, and
    so also bounds the total infidelity").  For states block-structured by the input register `e`
    (orthogonal `|e⟩` sectors), the global overlap is the SUM of the per-`e` conditioned overlaps, so
    if every conditioned overlap has real part `≥ c` then the global overlap has real part `≥ M·c`.
    Dividing by the `M` normalisation lifts the per-`e` fidelity `(W−d)/W ≥ 1−ε/S` to the whole
    state — completing the structure of eq:max-infidelity. -/
theorem global_fidelity_ge {M d : ℕ} (U V : Fin M → Fin d → ℂ) (c : ℝ)
    (hcond : ∀ e, c ≤ (∑ x, conj (U e x) * V e x).re) :
    (M : ℝ) * c ≤ (∑ p : Fin M × Fin d, conj (U p.1 p.2) * V p.1 p.2).re := by
  rw [Fintype.sum_prod_type, Complex.re_sum]
  calc (M : ℝ) * c
      = ∑ _e : Fin M, c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ e, (∑ x, conj (U e x) * V e x).re := Finset.sum_le_sum (fun e _ => hcond e)

/-! ## The approximate-periodicity + infidelity theorems pass the VERIFIER gate (axiom-clean). -/

#verify_clean modexp_periodic
#verify_clean approx_periodic
#verify_clean window_overlap_card
#verify_clean infidelity_ratio_bound
#verify_clean unifSuper_inner
#verify_clean masked_fidelity
#verify_clean global_fidelity_ge

end FormalRV.CFS
