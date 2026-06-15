/-
  FormalRV.Shor.CosetEigenstate.CosetEmbedStep — the per-addition coset-embedding
  agreement: off the boundary, `cosetState (z+c)` equals `E_data` of the canonical
  residue `(z+c) % N`.
  ════════════════════════════════════════════════════════════════════════════

  The concrete runway multiplier's per-window operation is an ordinary (non-modular)
  add-constant.  On the runway-initialized scratch (a coset superposition), one such
  add carries `cosetState N m z` to `cosetState N m (z+c)` (`shiftState_cosetState`).
  This file proves the EMBEDDING-AGREEMENT form requested (NOT `normSqDist`):

      OFF a boundary bad set `B`,  cosetState N m (z+c)  =  cosetState N m ((z+c) % N),

  i.e. the shifted coset state equals `E_data` applied to the CANONICAL residue
  `(z+c) % N` (`E_data |w⟩ = cosetState N m w`) — exactly off wrap, with the boundary
  Born mass `≤ 1/2^m` each (the ≤ 2 wrapping representatives), to be accumulated by
  `PhaseMarginalOracle.dataBornMass_union_le`.

  This is the atomic step the controlled windowed fold composes to realize
  `actual = (I_phase ⊗ E_data) ideal` off the accumulated wrap set
  (`PhaseMarginalEmbed`).  Branchwise: no-wrap ⇒ EXACT (`B = ∅`); wrap ⇒ agree off the
  single boundary, bound the Born mass.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp

namespace FormalRV.Shor.CosetEigenstate.CosetEmbedStep

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState cosetState_normSq)
open FormalRV.Shor.CosetEigenstate.CosetClass (cosetWindow mem_cosetWindow)

/-- **Adjacent-window AGREEMENT (off the boundary), with the boundary Born bounds.**
    The shifted window at `s+N` equals the window at `s` off the two boundary
    representatives (the bottom `s` and the top `s+2^m·N`), each carrying Born mass
    `1/2^m`.  The off-bad / bounded-Born form of `cosetState_adjacent_deviation`. -/
theorem cosetState_adjacent_agree_off (dim N m s : Nat) (hN : 0 < N)
    (hfit : s + 2 ^ m * N < dim) :
    ∃ B : Finset (Fin dim),
      (∀ i, i ∉ B → cosetState dim N m (s + N) i 0 = cosetState dim N m s i 0)
      ∧ bornWeightOn (cosetState dim N m (s + N)) B ≤ 1 / 2 ^ m
      ∧ bornWeightOn (cosetState dim N m s) B ≤ 1 / 2 ^ m := by
  have hs : s < dim := by omega
  have hpow : 0 < 2 ^ m := Nat.two_pow_pos m
  have hsub : (2 ^ m - 1) * N = 2 ^ m * N - N := Nat.sub_one_mul _ _
  have hNle : N ≤ 2 ^ m * N := Nat.le_mul_of_pos_left N hpow
  set x : Fin dim := ⟨s, hs⟩ with hx
  set y : Fin dim := ⟨s + 2 ^ m * N, hfit⟩ with hy
  have hxv : (x : Nat) = s := by rw [hx]
  have hyv : (y : Nat) = s + 2 ^ m * N := by rw [hy]
  have hxy : x ≠ y := fun he => by have := congrArg Fin.val he; rw [hxv, hyv] at this; omega
  refine ⟨{x, y}, ?_, ?_, ?_⟩
  · -- agreement off the boundary pair
    intro i hiB
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hiB
    obtain ⟨hix, hiy⟩ := hiB
    have hne_x : (i : Nat) ≠ s := fun he => hix (Fin.ext (by rw [hxv]; exact he))
    have hne_y : (i : Nat) ≠ s + 2 ^ m * N := fun he => hiy (Fin.ext (by rw [hyv]; exact he))
    have hiff : (i ∈ cosetWindow dim N m (s + N)) ↔ (i ∈ cosetWindow dim N m s) := by
      rw [mem_cosetWindow dim N m (s + N) hN, mem_cosetWindow dim N m s hN]
      constructor
      · rintro ⟨j, hj, he⟩
        rcases Nat.lt_or_ge (j + 1) (2 ^ m) with h | h
        · exact ⟨j + 1, h, by rw [he]; ring⟩
        · exfalso; apply hne_y
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
  · -- Born weight of cosetState (s+N) on the boundary pair
    have hx_notin_sN : x ∉ cosetWindow dim N m (s + N) := by
      rw [mem_cosetWindow dim N m (s + N) hN]; rintro ⟨j, _, hj⟩; rw [hxv] at hj; omega
    have hy_in_sN : y ∈ cosetWindow dim N m (s + N) := by
      rw [mem_cosetWindow dim N m (s + N) hN]
      refine ⟨2 ^ m - 1, by omega, ?_⟩; rw [hyv]; omega
    rw [bornWeightOn, Finset.sum_pair hxy, cosetState_normSq, cosetState_normSq,
        if_neg hx_notin_sN, if_pos hy_in_sN, zero_add]
  · -- Born weight of cosetState s on the boundary pair
    have hx_in_s : x ∈ cosetWindow dim N m s := by
      rw [mem_cosetWindow dim N m s hN]; exact ⟨0, hpow, by rw [hxv]; ring⟩
    have hy_notin_s : y ∉ cosetWindow dim N m s := by
      rw [mem_cosetWindow dim N m s hN]; rintro ⟨j, hj, he⟩; rw [hyv] at he
      have : j = 2 ^ m := Nat.eq_of_mul_eq_mul_right hN (by omega); omega
    rw [bornWeightOn, Finset.sum_pair hxy, cosetState_normSq, cosetState_normSq,
        if_pos hx_in_s, if_neg hy_notin_s, add_zero]

/-- **THE PER-ADDITION COSET-EMBEDDING STEP (off wrap).**  For canonical `z, c < N`,
    the shifted coset state `cosetState N m (z+c)` (what one ordinary add produces on
    `cosetState N m z`) equals `E_data` of the CANONICAL residue `(z+c) % N`
    (`cosetState N m ((z+c) % N)`) OFF a boundary bad set `B`, with each side's Born
    mass on `B` bounded by `1/2^m`.  No-wrap ⇒ `B = ∅` (exact); wrap ⇒ the single
    boundary.  This is the `EmbedAgree`-shaped atomic step (off-bad agreement + bounded
    bad mass), NOT mere decoded-value correctness. -/
theorem cosetState_addConst_embed_off (dim N m z c : Nat) (hN : 0 < N)
    (hz : z < N) (hc : c < N) (hfit : N + 2 ^ m * N ≤ dim) :
    ∃ B : Finset (Fin dim),
      (∀ i, i ∉ B → cosetState dim N m (z + c) i 0 = cosetState dim N m ((z + c) % N) i 0)
      ∧ bornWeightOn (cosetState dim N m (z + c)) B ≤ 1 / 2 ^ m
      ∧ bornWeightOn (cosetState dim N m ((z + c) % N)) B ≤ 1 / 2 ^ m := by
  rcases Nat.lt_or_ge (z + c) N with h | h
  · -- no wrap: (z+c) % N = z+c, exact agreement, empty bad set
    rw [Nat.mod_eq_of_lt h]
    exact ⟨∅, fun i _ => rfl, by simp [bornWeightOn], by simp [bornWeightOn]⟩
  · -- wrap: s = (z+c) % N = z+c−N, and z+c = s+N
    set s := (z + c) % N with hs_def
    have hsN : s < N := by rw [hs_def]; exact Nat.mod_lt _ hN
    have hmod : s = z + c - N := by
      rw [hs_def, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    have hzc : z + c = s + N := by omega
    have hfit' : s + 2 ^ m * N < dim := by omega
    rw [hzc]
    exact cosetState_adjacent_agree_off dim N m s hN hfit'

end FormalRV.Shor.CosetEigenstate.CosetEmbedStep
