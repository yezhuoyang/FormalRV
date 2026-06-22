/-
  FormalRV.Shor.GidneyInPlace.ApproxOp — the APPROXIMATE ENCODED OPERATION
  interface at the coset-state level (Zalka/Gidney arXiv:1905.08488).
  ════════════════════════════════════════════════════════════════════════════

  Rather than instantiate an EXACT in-place `hchain` for the runway/coset
  multiplier (which is false — the reps only match mod N), we build the coset-level
  APPROXIMATE interface:

    * `cosetState N m k` — the uniform superposition `(1/√2^m) ∑_{j<2^m} |k + j·N⟩`
      (amplitude `1/√2^m`, support the fixed `2^m`-window); normalized, support
      injective.
    * the SINGLE-ADDITION DEVIATION theorem: ordinary NON-modular `+c` carries
      `cosetState N m k` to within `2/2^m` (in `normSqDist`) of the reduced target
      `cosetState N m ((k+c) % N)` — the deviation being the ONE boundary
      representative that crosses the `N`-fold (Gidney Thm 3.2).  Proved by the
      combinatorial support-overlap (`2^m − 1` shared reps, `1` bad each), lifted to
      the vector `normSqDist` via `normSqDist_le_of_agree_off`.

  These compose (later) into `cosetMulOutOfPlace` and `inPlaceMul_coset_correct`
  whose scratch postcondition is `cosetState N m 0`, NOT exact basis zero.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Primitives.Def.CosetState

namespace FormalRV.Shor.GidneyInPlace.ApproxOp

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn normSqDist_le_of_agree_off)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)

/-- The Zalka/Gidney coset state `|Coset_m(k)⟩ = (1/√2^m) ∑_{j<2^m} |k+j·N⟩`:
    amplitude `1/√2^m` on the fixed `2^m`-window, `0` elsewhere. -/
noncomputable def cosetState (dim N m k : Nat) : QState dim :=
  fun i _ => if i ∈ cosetWindow dim N m k then ((1 / Real.sqrt (2 ^ m) : ℝ) : ℂ) else 0

/-- Per-entry Born mass: `1/2^m` on the window, `0` off it. -/
theorem cosetState_normSq (dim N m k : Nat) (i : Fin dim) :
    Complex.normSq (cosetState dim N m k i 0)
      = if i ∈ cosetWindow dim N m k then (1 / 2 ^ m : ℝ) else 0 := by
  rw [cosetState]
  by_cases h : i ∈ cosetWindow dim N m k
  · rw [if_pos h, if_pos h, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
        Real.mul_self_sqrt (by positivity)]
  · rw [if_neg h, if_neg h, Complex.normSq_zero]

/-- **Support injectivity.**  The `2^m` representatives `k + j·N` (`j < 2^m`) are
    distinct, so the window has exactly `2^m` elements (the support of the state). -/
theorem cosetState_support_card (dim N m k : Nat) (hN : 0 < N)
    (hfit : k + (2 ^ m - 1) * N < dim) :
    (cosetWindow dim N m k).card = 2 ^ m :=
  cosetWindow_card dim N m k hN hfit

/-- **Normalization.**  `‖cosetState‖² = 1` (total Born weight) when all `2^m`
    representatives fit the register. -/
theorem cosetState_normalized (dim N m k : Nat) (hN : 0 < N)
    (hfit : k + (2 ^ m - 1) * N < dim) :
    bornWeightOn (cosetState dim N m k) Finset.univ = 1 := by
  unfold bornWeightOn
  rw [Finset.sum_congr rfl (fun i _ => cosetState_normSq dim N m k i),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      cosetWindow_card dim N m k hN hfit, nsmul_eq_mul, mul_one_div]
  push_cast
  exact div_self (by positivity)

/-- **`normSqDist` triangle inequality** — the foundation of deviation
    SUBADDITIVITY (Gidney Thms 2.11–2.12): composing `t` approximate steps costs at
    most the sum of the per-step deviations. -/
theorem normSqDist_triangle {dim : Nat} (s₁ s₂ s₃ : QState dim) :
    normSqDist s₁ s₃ ≤ normSqDist s₁ s₂ + normSqDist s₂ s₃ := by
  unfold normSqDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_sub_le _ _ _)

/-- **Deviation SUBADDITIVITY (the chain bound).**  If a chain of `t` states has
    each consecutive pair within `d`, the endpoints are within `t·d`.  This is how
    `t` approximate additions accumulate to total deviation `t·(2/2^m)`. -/
theorem normSqDist_chain {dim : Nat} (s : Nat → QState dim) (d : ℝ) :
    ∀ t, (∀ i, i < t → normSqDist (s i) (s (i + 1)) ≤ d) →
      normSqDist (s 0) (s t) ≤ (t : ℝ) * d := by
  intro t
  induction t with
  | zero =>
      intro _
      have h0 : normSqDist (s 0) (s 0) = 0 := by unfold normSqDist; simp
      simp [h0]
  | succ n ih =>
      intro hstep
      calc normSqDist (s 0) (s (n + 1))
          ≤ normSqDist (s 0) (s n) + normSqDist (s n) (s (n + 1)) := normSqDist_triangle _ _ _
        _ ≤ (n : ℝ) * d + d := by
            have h1 := ih (fun i hi => hstep i (by omega))
            have h2 := hstep n (by omega)
            linarith
        _ = ((n + 1 : Nat) : ℝ) * d := by push_cast; ring

/-- Apply a basis permutation `σ` to a state. -/
noncomputable def permState {dim : Nat} (σ : Equiv.Perm (Fin dim)) (s : QState dim) : QState dim :=
  fun i z => s (σ i) z

/-- **Non-expansiveness / hybrid lemma (the composition justification).**  A basis
    permutation `σ` — e.g. `uc_eval` of any reversible gate, which permutes the
    basis indices — leaves `normSqDist` INVARIANT (it just reindexes the Born
    distributions identically on both states).  This is what justifies the LINEAR
    accumulation `t·d` of the chain bound across the controlled-addition
    composition: the surrounding reversible ops preserve the per-step deviation, so
    `normSqDist(s_i, s_{i+1})` equals the single-op deviation, not something larger. -/
theorem normSqDist_perm_invariant {dim : Nat} (σ : Equiv.Perm (Fin dim))
    (s₁ s₂ : QState dim) :
    normSqDist (permState σ s₁) (permState σ s₂) = normSqDist s₁ s₂ :=
  Equiv.sum_comp σ (fun i => |Complex.normSq (s₁ i 0) - Complex.normSq (s₂ i 0)|)

/-! ## §2. The single-addition deviation (the combinatorial support-overlap, lifted). -/

/-- **Adjacent-window deviation (the combinatorial core).**  The window at `s+N`
    and the window at `s` share `2^m − 1` representatives and differ on exactly ONE
    each (the bottom `s` and the top `s + 2^m·N`).  So `normSqDist ≤ 2/2^m`.  This is
    the vector-norm lift of the one-boundary-term overlap (Gidney Thm 3.2). -/
theorem cosetState_adjacent_deviation (dim N m s : Nat) (hN : 0 < N)
    (hfit : s + 2 ^ m * N < dim) :
    normSqDist (cosetState dim N m (s + N)) (cosetState dim N m s) ≤ 2 / 2 ^ m := by
  have hs : s < dim := by omega
  have hpow : 0 < 2 ^ m := Nat.two_pow_pos m
  have hsub : (2 ^ m - 1) * N = 2 ^ m * N - N := Nat.sub_one_mul _ _
  have hNle : N ≤ 2 ^ m * N := Nat.le_mul_of_pos_left N hpow
  -- the two boundary representatives, with their values pinned
  set x : Fin dim := ⟨s, hs⟩ with hx
  set y : Fin dim := ⟨s + 2 ^ m * N, hfit⟩ with hy
  have hxv : (x : Nat) = s := by rw [hx]
  have hyv : (y : Nat) = s + 2 ^ m * N := by rw [hy]
  have hxy : x ≠ y := fun he => by have := congrArg Fin.val he; rw [hxv, hyv] at this; omega
  set B : Finset (Fin dim) := {x, y} with hB
  have hmpow : 2 ^ m - 1 < 2 ^ m := by omega
  have hx_notin_sN : x ∉ cosetWindow dim N m (s + N) := by
    rw [mem_cosetWindow dim N m (s + N) hN]; rintro ⟨j, _, hj⟩; rw [hxv] at hj; omega
  have hy_in_sN : y ∈ cosetWindow dim N m (s + N) := by
    rw [mem_cosetWindow dim N m (s + N) hN]
    refine ⟨2 ^ m - 1, hmpow, ?_⟩; rw [hyv]; omega
  have hx_in_s : x ∈ cosetWindow dim N m s := by
    rw [mem_cosetWindow dim N m s hN]; exact ⟨0, hpow, by rw [hxv]; ring⟩
  have hy_notin_s : y ∉ cosetWindow dim N m s := by
    rw [mem_cosetWindow dim N m s hN]; rintro ⟨j, hj, he⟩; rw [hyv] at he
    have : j = 2 ^ m := Nat.eq_of_mul_eq_mul_right hN (by omega); omega
  -- agreement off B (the support equivalence)
  have hagree : ∀ i, i ∉ B → cosetState dim N m (s + N) i 0 = cosetState dim N m s i 0 := by
    intro i hiB
    rw [hB, Finset.mem_insert, Finset.mem_singleton, not_or] at hiB
    obtain ⟨hix, hiy⟩ := hiB
    have hne_x : (i : Nat) ≠ s := fun he => hix (Fin.ext (by rw [hxv]; exact he))
    have hne_y : (i : Nat) ≠ s + 2 ^ m * N := fun he => hiy (Fin.ext (by rw [hyv]; exact he))
    have hiff : (i ∈ cosetWindow dim N m (s + N)) ↔ (i ∈ cosetWindow dim N m s) := by
      rw [mem_cosetWindow dim N m (s + N) hN, mem_cosetWindow dim N m s hN]
      constructor
      · rintro ⟨j, hj, he⟩
        rcases Nat.lt_or_ge (j + 1) (2 ^ m) with h | h
        · exact ⟨j + 1, h, by rw [he]; ring⟩
        · exfalso
          apply hne_y
          have hj1 : j + 1 = 2 ^ m := by omega
          rw [he, show s + N + j * N = s + (j + 1) * N by ring, hj1]
      · rintro ⟨j, hj, he⟩
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · exfalso; apply hne_x; rw [he, hj0]; ring
        · refine ⟨j - 1, by omega, ?_⟩
          rw [he]
          have h2 : N ≤ j * N := Nat.le_mul_of_pos_left N hj0
          have h3 : (j - 1) * N = j * N - N := Nat.sub_one_mul _ _
          omega
    rw [cosetState, cosetState]
    by_cases h : i ∈ cosetWindow dim N m (s + N)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  -- the two wrap Born weights, each = 1/2^m
  have hw_sN : bornWeightOn (cosetState dim N m (s + N)) B ≤ 1 / 2 ^ m := by
    rw [hB, bornWeightOn, Finset.sum_pair hxy,
        cosetState_normSq, cosetState_normSq, if_neg hx_notin_sN, if_pos hy_in_sN, zero_add]
  have hw_s : bornWeightOn (cosetState dim N m s) B ≤ 1 / 2 ^ m := by
    rw [hB, bornWeightOn, Finset.sum_pair hxy,
        cosetState_normSq, cosetState_normSq, if_pos hx_in_s, if_neg hy_notin_s, add_zero]
  calc normSqDist (cosetState dim N m (s + N)) (cosetState dim N m s)
      ≤ 2 * (1 / 2 ^ m) :=
        normSqDist_le_of_agree_off _ _ B (1 / 2 ^ m) hagree hw_sN hw_s
    _ = 2 / 2 ^ m := by ring

/-- The NON-modular add-constant on a register state: `|v⟩ ↦ |v+c⟩`. -/
noncomputable def shiftState (dim c : Nat) (s : QState dim) : QState dim :=
  fun i _ => if c ≤ (i : Nat) then s ⟨(i : Nat) - c, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ 0 else 0

/-- **Adding `c` (non-modularly) shifts the coset WINDOW** by `c`: `addConst c`
    carries `cosetState N m k` to `cosetState N m (k+c)` exactly (the amplitude
    `1/√2^m` is constant, so the shift just relocates the support). -/
theorem shiftState_cosetState (dim N m k c : Nat) (hN : 0 < N) :
    shiftState dim c (cosetState dim N m k) = cosetState dim N m (k + c) := by
  funext i z
  have hz : z = 0 := Subsingleton.elim z 0
  subst hz
  have hiff : (c ≤ (i : Nat) ∧
      (⟨(i : Nat) - c, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin dim)
        ∈ cosetWindow dim N m k) ↔ i ∈ cosetWindow dim N m (k + c) := by
    rw [mem_cosetWindow dim N m k hN, mem_cosetWindow dim N m (k + c) hN]
    constructor
    · rintro ⟨hc, j, hj, he⟩
      have he' : (i : Nat) - c = k + j * N := he
      exact ⟨j, hj, by omega⟩
    · rintro ⟨j, hj, he⟩
      refine ⟨by omega, j, hj, ?_⟩
      show (i : Nat) - c = k + j * N
      omega
  simp only [shiftState, cosetState]
  by_cases h : i ∈ cosetWindow dim N m (k + c)
  · obtain ⟨hc, hmem⟩ := hiff.mpr h
    rw [if_pos hc, if_pos hmem, if_pos h]
  · rw [if_neg h]
    by_cases hc : c ≤ (i : Nat)
    · rw [if_pos hc, if_neg (fun hmem => h (hiff.mp ⟨hc, hmem⟩))]
    · rw [if_neg hc]

/-- **`shiftState` is NON-EXPANSIVE in `normSqDist`.**  The non-modular add-constant
    `|v⟩ ↦ |v+c⟩` is an INJECTION on register indices (values that fall off the top
    are simply dropped), so applying it to both states can only SHRINK the Born-L1
    distance.  This is the surrounding-op step that lets the per-addition deviation
    accumulate ADDITIVELY in the fold (against the ideal reduced chain) — and it is
    UNCONDITIONAL: overflow in the actual chain is absorbed here, so the fold needs
    only the per-step fit, never a running-sum fit. -/
theorem shiftState_normSqDist_nonexpansive {dim : Nat} (c : Nat) (s₁ s₂ : QState dim) :
    normSqDist (shiftState dim c s₁) (shiftState dim c s₂) ≤ normSqDist s₁ s₂ := by
  classical
  unfold normSqDist
  set F : Fin dim → ℝ := fun i =>
    |Complex.normSq (shiftState dim c s₁ i 0) - Complex.normSq (shiftState dim c s₂ i 0)| with hF
  set G : Fin dim → ℝ := fun j =>
    |Complex.normSq (s₁ j 0) - Complex.normSq (s₂ j 0)| with hG
  set S : Finset (Fin dim) := Finset.univ.filter (fun i => c ≤ (i : Nat)) with hS
  set φ : Fin dim → Fin dim :=
    fun i => ⟨(i : Nat) - c, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ with hφ
  have hF0 : ∀ i ∉ S, F i = 0 := by
    intro i hi
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    simp only [hF, shiftState, if_neg (by omega : ¬ c ≤ (i : Nat))]
    simp
  have hFG : ∀ i ∈ S, F i = G (φ i) := by
    intro i hi
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hF, hG, hφ, shiftState, if_pos hi]
  have hφinj : ∀ i ∈ S, ∀ i' ∈ S, φ i = φ i' → i = i' := by
    intro i hi i' hi' he
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    have hv : (i : Nat) - c = (i' : Nat) - c := congrArg Fin.val he
    exact Fin.ext (by omega)
  calc ∑ i, F i
      = ∑ i ∈ S, F i := (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hF0 i hi)).symm
    _ = ∑ i ∈ S, G (φ i) := Finset.sum_congr rfl hFG
    _ = ∑ j ∈ S.image φ, G j := (Finset.sum_image hφinj).symm
    _ ≤ ∑ j, G j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => abs_nonneg _)

/-- The genuine WRAPPING add-constant — the REAL reversible adder's basis
    permutation on a `2^bits`-register of size `dim`: `|v⟩ ↦ |(v+c) mod dim⟩`,
    norm-PRESERVING (a permutation, unlike the truncating `shiftState`).  In
    amplitude form the value at `i` comes from `(i−c) mod dim = (i+dim−c) mod dim`. -/
noncomputable def wrapShiftState (dim c : Nat) (s : QState dim) : QState dim :=
  fun i _ => s ⟨((i : Nat) + (dim - c)) % dim,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ 0

/-- **THE OVERFLOW-FAITHFULNESS CERTIFICATE (audit #3 — truncation hides nothing).**
    Under the per-window fit `k + c + (2^m−1)·N < dim`, the TRUNCATING `shiftState`
    coincides EXACTLY with the genuine WRAPPING reversible-adder gate `wrapShiftState`
    on the coset state.  In this regime `shiftState` drops NOTHING the real gate keeps,
    AND the real gate wraps nothing to a wrong place — there is simply no overflow to
    hide.  Off the fit the two genuinely differ (drop vs wrap-around), which is exactly
    why the FOLD needs the running-sum fit (every partial window `< dim`) to stay
    faithful to the physical gate: non-expansiveness alone would silently absorb the
    dropped mass that the real gate would instead have wrapped. -/
theorem shiftState_eq_wrapState_on_coset (dim N m k c : Nat) (hN : 0 < N)
    (hfit : k + c + (2 ^ m - 1) * N < dim) :
    shiftState dim c (cosetState dim N m k) = wrapShiftState dim c (cosetState dim N m k) := by
  funext i z
  have hz : z = 0 := Subsingleton.elim z 0
  subst hz
  simp only [shiftState, wrapShiftState]
  by_cases hci : c ≤ (i : Nat)
  · rw [if_pos hci]
    congr 2
    have h1 : (i : Nat) + (dim - c) = ((i : Nat) - c) + dim := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hci]
    set j : Fin dim := ⟨((i : Nat) + (dim - c)) % dim,
      Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ with hj
    have hjval : (j : Nat) = (i : Nat) + (dim - c) := by
      rw [hj]; exact Nat.mod_eq_of_lt (by omega)
    have hjnot : j ∉ cosetWindow dim N m k := by
      rw [mem_cosetWindow dim N m k hN]
      rintro ⟨a, ha, heq⟩
      rw [hjval] at heq
      have : a * N ≤ (2 ^ m - 1) * N := Nat.mul_le_mul_right N (by omega)
      omega
    show (0 : ℂ) = cosetState dim N m k j 0
    rw [cosetState, if_neg hjnot]

/-- The real wrapping gate also realizes the coset shift, under the fit: combining
    `shiftState_cosetState` with the coincidence certificate, the GENUINE reversible
    adder carries `cosetState N m k` to `cosetState N m (k+c)` exactly when the window
    fits — and only then (off the fit the wrap lands the top rep wrong). -/
theorem wrapShiftState_cosetState (dim N m k c : Nat) (hN : 0 < N)
    (hfit : k + c + (2 ^ m - 1) * N < dim) :
    wrapShiftState dim c (cosetState dim N m k) = cosetState dim N m (k + c) := by
  rw [← shiftState_eq_wrapState_on_coset dim N m k c hN hfit, shiftState_cosetState dim N m k c hN]

/-- **THE SINGLE-ADDITION DEVIATION THEOREM (Gidney arXiv:1905.08488).**  Ordinary
    NON-modular `addConst c` (for canonical `c < N`) carries `cosetState N m k` to
    within `2/2^m` (in `normSqDist`) of the reduced target `cosetState N m ((k+c)%N)`.
    No wrap (`k+c < N`) ⇒ exact; wrap (`k+c ≥ N`) ⇒ one boundary representative
    crosses, giving the `≤ 2/2^m` via `cosetState_adjacent_deviation`. -/
theorem cosetState_addConst_deviation (dim N m k c : Nat) (hN : 0 < N) (hk : k < N) (hc : c < N)
    (hfit : N + 2 ^ m * N ≤ dim) :
    normSqDist (shiftState dim c (cosetState dim N m k)) (cosetState dim N m ((k + c) % N))
      ≤ 2 / 2 ^ m := by
  rw [shiftState_cosetState dim N m k c hN]
  rcases Nat.lt_or_ge (k + c) N with h | h
  · rw [Nat.mod_eq_of_lt h]
    have h0 : normSqDist (cosetState dim N m (k + c)) (cosetState dim N m (k + c)) = 0 := by
      unfold normSqDist; simp
    rw [h0]; positivity
  · set s := (k + c) % N with hs
    have hsN : s < N := by rw [hs]; exact Nat.mod_lt _ hN
    have hmod : (k + c) % N = k + c - N := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    have hkc : k + c = s + N := by rw [hs, hmod]; omega
    have hfit' : s + 2 ^ m * N < dim := by omega
    rw [hkc]
    exact cosetState_adjacent_deviation dim N m s hN hfit'

end FormalRV.Shor.GidneyInPlace.ApproxOp
