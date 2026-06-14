/-
  FormalRV.Shor.CosetEigenstate.PhysEmbedMarginal — the physical/interleaved data
  embedding E_phys (`|z⟩ ↦ physCosetState N m z`) and its CANONICAL-RESIDUE isometry:
  the direct spread-support facts that wire physCosetState into the marginal frontier.
  ════════════════════════════════════════════════════════════════════════════

  To make the downstream phase-marginal frontier talk about the SAME object the literal
  cuccaro gate produces (`physCosetState`, the interleaved/spread coset state) rather than
  the contiguous `cosetState`, we need the physical embedding `E_phys : |z⟩ ↦
  physCosetState N m z` to PRESERVE the phase marginal.  The honest fact:

  ⚠ THE FULL isometry (`DataLocal.isom` for ALL `φ`) is PROVABLY FALSE — the windows of
  `z` and `z+N` overlap, so the embedding columns are NOT all orthonormal.  E_phys is an
  isometry ONLY on CANONICAL RESIDUES `z < N` (distinct residues ⟹ DISJOINT spread
  windows), which is exactly where the ideal Shor data lives.  This file proves that
  canonical-subspace isometry by the DIRECT spread-support argument (the user-chosen
  route), NOT a (false) blanket `DataLocal` instance:

    * `spreadIdx_inj` — the spread index is injective on values `< 2^bits`.
    * `physWindow_card` — each spread window has exactly `2^m` elements.
    * `physWindow_disjoint` — DISTINCT canonical residues `z ≠ z' < N` have DISJOINT
      spread windows (the orthogonality engine).
    * `physCosetState_normalized` — each `physCosetState` carries unit Born mass.
    * `physCosetEmbed_isometry` — **THE DELIVERABLE**: `‖∑_{w<N} α_w · physCosetState w‖²
      = ∑_{w<N} |α_w|²`.  The embedding is an isometry on canonical-residue-supported
      data; cross terms vanish by window disjointness, each diagonal term contributes
      `|α_w|²·(card/2^m) = |α_w|²`.  Hence E_phys preserves the phase marginal of the
      (canonical-supported) ideal Shor data — the marginal frontier may use
      `physCosetState` in place of the contiguous `cosetState`.

  INTERFACE NOTE (honest): `physCosetState` lives on the hardware register `Fin (2^dim)`;
  the marginal frontier sums over the abstract Shor `jointIdx` data register.  The Born
  facts here are register-agnostic (disjointness + cardinality), so the per-branch
  marginal preservation transfers under the layout identification (arithmetic register =
  data part of the Shor split) — the one remaining layout interface, which is
  marginal-invariant.

  Proof de-risked via 3 parallel verified attempts.  Kernel-clean: no `sorry`, no
  `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset

namespace FormalRV.Shor.CosetEigenstate.PhysEmbedMarginal

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.GatePerm
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.CosetEigenstate.CuccaroPhysCoset (spreadIdx physWindow physCosetState)

/-- **(1) Spread-index injectivity on canonical residues.** Distinct values below
    `2^bits` give distinct spread indices, provided the register fits. -/
theorem spreadIdx_inj (dim bits q_start v v' : Nat)
    (hv : v < 2 ^ bits) (hv' : v' < 2 ^ bits) (hdim : q_start + 2 * bits + 1 ≤ dim)
    (h : spreadIdx dim q_start v = spreadIdx dim q_start v') : v = v' := by
  -- funboolNat injective ⟹ the underlying Bool-functions agree.
  have hfun : (fun (l : Fin dim) => cuccaro_input_F q_start false 0 v l.val)
            = (fun (l : Fin dim) => cuccaro_input_F q_start false 0 v' l.val) :=
    funboolNat_injective dim h
  -- The testBits agree for all k.
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k bits with hk | hk
  · -- k < bits : read out at position q_start + 2*k + 1.
    have hpos : q_start + 2 * k + 1 < dim := by omega
    have := congrFun hfun ⟨q_start + 2 * k + 1, hpos⟩
    simp only [] at this
    rw [cuccaro_input_F_at_b q_start k false 0 v, cuccaro_input_F_at_b q_start k false 0 v'] at this
    exact this
  · -- k ≥ bits : both testbits are false.
    have hvk : v.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hk))
    have hv'k : v'.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv' (Nat.pow_le_pow_right (by norm_num) hk))
    rw [hvk, hv'k]

/-- **(2) Physical window cardinality** = `2^m` (the `2^m` reps `k+j·N` are distinct). -/
theorem physWindow_card (dim N m bits q_start k : Nat)
    (hN : 0 < N) (hMN : 2 ^ m * N ≤ 2 ^ bits) (hk : k < N) (hdim : q_start + 2 * bits + 1 ≤ dim) :
    (physWindow dim N m q_start k).card = 2 ^ m := by
  unfold physWindow
  rw [Finset.card_image_of_injOn, Finset.card_range]
  -- InjOn: for j, j' < 2^m, spreadIdx (k+j*N) = spreadIdx (k+j'*N) ⟹ j = j'.
  intro j hj j' hj' heq
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  have hxj : k + j * N < 2 ^ bits := by
    have h1 : (j + 1) * N ≤ 2 ^ m * N := Nat.mul_le_mul_right N (by omega)
    have h2 : (j + 1) * N = j * N + N := by ring
    omega
  have hxj' : k + j' * N < 2 ^ bits := by
    have h1 : (j' + 1) * N ≤ 2 ^ m * N := Nat.mul_le_mul_right N (by omega)
    have h2 : (j' + 1) * N = j' * N + N := by ring
    omega
  have hval : k + j * N = k + j' * N := spreadIdx_inj dim bits q_start _ _ hxj hxj' hdim heq
  have hjN : j * N = j' * N := by omega
  exact Nat.eq_of_mul_eq_mul_right hN hjN

/-- **(3) Disjoint windows for distinct canonical residues** — the orthogonality engine. -/
theorem physWindow_disjoint (dim N m bits q_start z z' : Nat)
    (_hN : 0 < N) (hMN : 2 ^ m * N ≤ 2 ^ bits) (hz : z < N) (hz' : z' < N) (hne : z ≠ z')
    (hdim : q_start + 2 * bits + 1 ≤ dim) :
    Disjoint (physWindow dim N m q_start z) (physWindow dim N m q_start z') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  unfold physWindow at hi hi'
  rw [Finset.mem_image] at hi hi'
  obtain ⟨j, hj, hji⟩ := hi
  obtain ⟨j', hj', hji'⟩ := hi'
  rw [Finset.mem_range] at hj hj'
  have hxz : z + j * N < 2 ^ bits := by
    have h1 : (j + 1) * N ≤ 2 ^ m * N := Nat.mul_le_mul_right N (by omega)
    have h2 : (j + 1) * N = j * N + N := by ring
    omega
  have hxz' : z' + j' * N < 2 ^ bits := by
    have h1 : (j' + 1) * N ≤ 2 ^ m * N := Nat.mul_le_mul_right N (by omega)
    have h2 : (j' + 1) * N = j' * N + N := by ring
    omega
  -- i = spreadIdx (z+j*N) = spreadIdx (z'+j'*N).
  have heq : spreadIdx dim q_start (z + j * N) = spreadIdx dim q_start (z' + j' * N) := by
    rw [hji, hji']
  have hval : z + j * N = z' + j' * N := spreadIdx_inj dim bits q_start _ _ hxz hxz' hdim heq
  -- z ≡ z' (mod N) ⟹ z = z'.
  have hmod : (z + j * N) % N = (z' + j' * N) % N := by rw [hval]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hz'] at hmod
  exact hne hmod

/-- **(4) Each canonical coset state is normalized.** -/
theorem physCosetState_normalized (dim N m bits q_start k : Nat)
    (hN : 0 < N) (hMN : 2 ^ m * N ≤ 2 ^ bits) (hk : k < N) (hdim : q_start + 2 * bits + 1 ≤ dim) :
    bornWeightOn (physCosetState dim N m q_start k) Finset.univ = 1 := by
  unfold bornWeightOn physCosetState
  have hnsq : ∀ i : Fin (2 ^ dim),
      Complex.normSq (if i ∈ physWindow dim N m q_start k then ((1 / Real.sqrt (2 ^ m) : ℝ) : ℂ) else 0)
        = if i ∈ physWindow dim N m q_start k then (1 / 2 ^ m : ℝ) else 0 := by
    intro i
    by_cases h : i ∈ physWindow dim N m q_start k
    · rw [if_pos h, if_pos h, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
          Real.mul_self_sqrt (by positivity)]
    · rw [if_neg h, if_neg h, Complex.normSq_zero]
  rw [Finset.sum_congr rfl (fun i _ => hnsq i),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      physWindow_card dim N m bits q_start k hN hMN hk hdim, nsmul_eq_mul, mul_one_div]
  push_cast
  exact div_self (by positivity)

/-- **(5) MAIN — canonical-residue isometry of the physical coset embedding `E_phys`.**
    The embedding `∑_{w<N} α_w · physCosetState w` preserves total Born mass `∑_w |α_w|²`
    — so `E_phys : |z⟩ ↦ physCosetState N m z` preserves the phase marginal of the
    canonical-supported ideal Shor data. -/
theorem physCosetEmbed_isometry (dim N m bits q_start : Nat) (α : Nat → ℂ)
    (hN : 0 < N) (hMN : 2 ^ m * N ≤ 2 ^ bits) (hdim : q_start + 2 * bits + 1 ≤ dim) :
    bornWeightOn
        (fun (i : Fin (2 ^ dim)) (_ : Fin 1) =>
          ∑ w ∈ Finset.range N, α w * physCosetState dim N m q_start w i 0) Finset.univ
      = ∑ w ∈ Finset.range N, Complex.normSq (α w) := by
  unfold bornWeightOn
  -- f i = ∑ w < N, α w * physCosetState w i 0.
  set f : Fin (2 ^ dim) → ℂ :=
    fun i => ∑ w ∈ Finset.range N, α w * physCosetState dim N m q_start w i 0 with hf
  -- Per-entry orthogonality: normSq (f i) = ∑ w<N, normSq (α w) * (indicator window w).
  have hper : ∀ i : Fin (2 ^ dim),
      Complex.normSq (f i)
        = ∑ w ∈ Finset.range N,
            Complex.normSq (α w) * (if i ∈ physWindow dim N m q_start w then (1 / 2 ^ m : ℝ) else 0) := by
    intro i
    by_cases hex : ∃ w ∈ Finset.range N, i ∈ physWindow dim N m q_start w
    · obtain ⟨w0, hw0r, hw0mem⟩ := hex
      rw [Finset.mem_range] at hw0r
      -- f i = α w0 * (1/√2^m): only the w0 term survives.
      have hfi : f i = α w0 * ((1 / Real.sqrt (2 ^ m) : ℝ) : ℂ) := by
        rw [hf]
        simp only []
        rw [Finset.sum_eq_single w0]
        · simp only [physCosetState, if_pos hw0mem]
        · intro w hw hwne
          rw [Finset.mem_range] at hw
          have hdisj := physWindow_disjoint dim N m bits q_start w0 w hN hMN hw0r hw (Ne.symm hwne) hdim
          have hnotin : i ∉ physWindow dim N m q_start w := by
            rw [Finset.disjoint_left] at hdisj
            exact hdisj hw0mem
          simp only [physCosetState, if_neg hnotin, mul_zero]
        · intro hcontra; rw [Finset.mem_range] at hcontra; exact absurd hw0r hcontra
      rw [hfi]
      -- RHS: only w0 term survives.
      rw [Finset.sum_eq_single w0]
      · rw [if_pos hw0mem, Complex.normSq_mul, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
            Real.mul_self_sqrt (by positivity)]
      · intro w hw hwne
        rw [Finset.mem_range] at hw
        have hdisj := physWindow_disjoint dim N m bits q_start w0 w hN hMN hw0r hw (Ne.symm hwne) hdim
        have hnotin : i ∉ physWindow dim N m q_start w := by
          rw [Finset.disjoint_left] at hdisj
          exact hdisj hw0mem
        rw [if_neg hnotin, mul_zero]
      · intro hcontra; rw [Finset.mem_range] at hcontra; exact absurd hw0r hcontra
    · -- i in no window: f i = 0, RHS = 0.
      simp only [not_exists, not_and] at hex
      have hfi : f i = 0 := by
        rw [hf]
        simp only []
        apply Finset.sum_eq_zero
        intro w hw
        have hnotin : i ∉ physWindow dim N m q_start w := hex w hw
        simp only [physCosetState, if_neg hnotin, mul_zero]
      rw [hfi, Complex.normSq_zero]
      symm
      apply Finset.sum_eq_zero
      intro w hw
      have hnotin : i ∉ physWindow dim N m q_start w := hex w hw
      rw [if_neg hnotin, mul_zero]
  -- Sum over i, swap sums.
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.mem_range] at hw
  -- ∑ i, normSq(α w) * (indicator window w) = normSq(α w) * (card window w / 2^m) = normSq(α w).
  rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      physWindow_card dim N m bits q_start w hN hMN hw hdim, nsmul_eq_mul, mul_one_div]
  rw [show ((2 ^ m : ℕ) : ℝ) / 2 ^ m = 1 by
        push_cast; exact div_self (by positivity)]
  rw [mul_one]

end FormalRV.Shor.CosetEigenstate.PhysEmbedMarginal
