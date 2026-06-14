/-
  FormalRV.Shor.CosetEigenstate.ApproxOp — the APPROXIMATE ENCODED OPERATION
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
import FormalRV.Shor.CosetEigenstate.CosetState

namespace FormalRV.Shor.CosetEigenstate.ApproxOp

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn normSqDist_le_of_agree_off)
open FormalRV.Shor.CosetEigenstate.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)

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

end FormalRV.Shor.CosetEigenstate.ApproxOp
