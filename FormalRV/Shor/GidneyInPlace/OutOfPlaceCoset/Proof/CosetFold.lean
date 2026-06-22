/-
  FormalRV.Shor.GidneyInPlace.CosetFold — the fold-level coset-embedding agreement:
  `cosetState (r + q·N)` (unreduced) agrees with `E_data` of the canonical `cosetState r`
  off the symmetric-difference bad set, with TIGHT per-side Born mass `≤ q/2^m`.
  ════════════════════════════════════════════════════════════════════════════

  The concrete runway multiplier applies ordinary (non-modular) additions to the coset
  accumulator.  Off wrap, the unreduced result `cosetState (r + q·N)` (where `q` is the
  number of wraps `≤ T`) agrees with `E_data` of the canonical residue `cosetState r`,
  with each side's Born mass on the bad set `≤ q/2^m`.

    * `agree_off_trans` — the chaining primitive (off-bad agreements compose by union).
    * `cosetState_bornWeightOn_eq` — the coset Born weight on `B` is `|B ∩ window|/2^m`.
    * `windowDiff_card_le` / `windowDiff_card_le'` — THE BOUNDARY COUNT: the one-sided
      window difference has cardinality `≤ q` (the `q` non-shared boundary reps), by an
      injection of the `Fin`-values into `(Finset.Ico (2^m) (q+2^m)).image (·↦r+·N)`
      (resp. `(Finset.range q).image`).
    * `cosetState_multiWrap_agree_off` — `cosetState (r+q·N) = cosetState r` off the
      window symmetric difference, each side's Born mass `≤ q/2^m` (tight, via the
      boundary count).

  Combined with `CosetTableSum.idealAcc_cosetWindowConst` / `windowedLookupFold_eq_modmul`
  (where `q ≤ numWin`), this is the windowed multiplier embedding `cosetState z ↦
  E_data ((a·z) % N)` off bad, with bad mass `≤ numWin/2^m` per side.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Primitives.Def.ApproxOp

namespace FormalRV.Shor.GidneyInPlace.CosetFold

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState cosetState_normSq)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)

/-- **Off-bad agreement TRANSITIVITY (the chaining primitive).**  If `A = B` off
    `bad1` and `B = C` off `bad2`, then `A = C` off `bad1 ∪ bad2` — so per-step
    boundary sets accumulate by union. -/
theorem agree_off_trans {dim : Nat} (A B C : QState dim) (bad1 bad2 : Finset (Fin dim))
    (h1 : ∀ i, i ∉ bad1 → A i 0 = B i 0) (h2 : ∀ i, i ∉ bad2 → B i 0 = C i 0) :
    ∀ i, i ∉ bad1 ∪ bad2 → A i 0 = C i 0 := by
  intro i hi
  rw [Finset.mem_union, not_or] at hi
  rw [h1 i hi.1, h2 i hi.2]

/-- The coset Born weight on a set `B` is `|B ∩ window| / 2^m`. -/
theorem cosetState_bornWeightOn_eq {dim N m a : Nat} (B : Finset (Fin dim)) :
    bornWeightOn (cosetState dim N m a) B
      = ((B.filter (· ∈ cosetWindow dim N m a)).card : ℝ) / 2 ^ m := by
  rw [bornWeightOn, Finset.sum_congr rfl (fun i _ => cosetState_normSq dim N m a i),
      Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- **THE BOUNDARY COUNT (upper side).**  The window at `r+q·N` minus the window at
    `r` has `≤ q` elements — the `q` representatives with index `≥ 2^m`.  Injection of
    the `Fin`-values into `(Finset.Ico (2^m) (q+2^m)).image (·↦ r+·N)` (card `q`). -/
theorem windowDiff_card_le (dim N m r q : Nat) (hN : 0 < N) :
    ((Finset.univ.filter (· ∈ cosetWindow dim N m (r + q * N)))
     \ (Finset.univ.filter (· ∈ cosetWindow dim N m r))).card ≤ q := by
  classical
  set S : Finset Nat := (Finset.Ico (2 ^ m) (q + 2 ^ m)).image (fun k => r + k * N) with hS
  have hScard : S.card ≤ q := by
    calc S.card ≤ (Finset.Ico (2 ^ m) (q + 2 ^ m)).card := Finset.card_image_le
      _ = q := by rw [Nat.card_Ico]; omega
  refine le_trans (Finset.card_le_card_of_injOn (fun i => (i : Nat)) ?_ ?_) hScard
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hi
    obtain ⟨⟨_, hin⟩, hout⟩ := hi
    rw [mem_cosetWindow dim N m (r + q * N) hN] at hin
    obtain ⟨j, hj, hval⟩ := hin
    have hval' : (i : Nat) = r + (q + j) * N := by rw [hval]; ring
    have hge : 2 ^ m ≤ q + j := by
      by_contra hlt
      rw [not_le] at hlt
      exact hout ⟨Finset.mem_univ i, (mem_cosetWindow dim N m r hN i).mpr ⟨q + j, hlt, hval'⟩⟩
    rw [Finset.mem_coe, hS, Finset.mem_image]
    exact ⟨q + j, by rw [Finset.mem_Ico]; exact ⟨hge, by omega⟩, hval'.symm⟩
  · intro a _ b _ hab
    exact Fin.ext hab

/-- **THE BOUNDARY COUNT (lower side).**  The window at `r` minus the window at
    `r+q·N` has `≤ q` elements — the `q` representatives with index `< q`.  Injection
    into `(Finset.range q).image (·↦ r+·N)`. -/
theorem windowDiff_card_le' (dim N m r q : Nat) (hN : 0 < N) :
    ((Finset.univ.filter (· ∈ cosetWindow dim N m r))
     \ (Finset.univ.filter (· ∈ cosetWindow dim N m (r + q * N)))).card ≤ q := by
  classical
  set S : Finset Nat := (Finset.range q).image (fun k => r + k * N) with hS
  have hScard : S.card ≤ q :=
    le_trans Finset.card_image_le (le_of_eq (Finset.card_range q))
  refine le_trans (Finset.card_le_card_of_injOn (fun i => (i : Nat)) ?_ ?_) hScard
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hi
    obtain ⟨⟨_, hin⟩, hout⟩ := hi
    rw [mem_cosetWindow dim N m r hN] at hin
    obtain ⟨j, hj, hval⟩ := hin
    have hlt : j < q := by
      by_contra hge
      rw [not_lt] at hge
      apply hout
      refine ⟨Finset.mem_univ i, (mem_cosetWindow dim N m (r + q * N) hN i).mpr ⟨j - q, by omega, ?_⟩⟩
      have hqj : q * N ≤ j * N := by gcongr
      have hsub : (j - q) * N = j * N - q * N := Nat.sub_mul j q N
      rw [hval]; omega
    rw [Finset.mem_coe, hS, Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hlt, hval.symm⟩
  · intro a _ b _ hab
    exact Fin.ext hab

/-- **THE FOLD-LEVEL COSET-EMBEDDING AGREEMENT (off bad, TIGHT mass).**  The unreduced
    coset state `cosetState (r + q·N)` agrees with `E_data` of the canonical residue
    `cosetState r` off the symmetric difference `B` of their windows, and EACH side
    carries Born mass `≤ q/2^m` on `B` (the `q` non-shared boundary reps).  Off `B`,
    every position is in both windows or neither, so the amplitudes agree exactly. -/
theorem cosetState_multiWrap_agree_off (dim N m r q : Nat) (hN : 0 < N) :
    ∃ B : Finset (Fin dim),
      (∀ i, i ∉ B → cosetState dim N m (r + q * N) i 0 = cosetState dim N m r i 0)
      ∧ bornWeightOn (cosetState dim N m (r + q * N)) B ≤ (q : ℝ) / 2 ^ m
      ∧ bornWeightOn (cosetState dim N m r) B ≤ (q : ℝ) / 2 ^ m := by
  classical
  set W1 : Finset (Fin dim) := Finset.univ.filter (· ∈ cosetWindow dim N m (r + q * N)) with hW1
  set W2 : Finset (Fin dim) := Finset.univ.filter (· ∈ cosetWindow dim N m r) with hW2
  refine ⟨(W1 \ W2) ∪ (W2 \ W1), ?_, ?_, ?_⟩
  · -- agreement off the symmetric difference
    intro i hi
    simp only [Finset.mem_union, Finset.mem_sdiff, hW1, hW2, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or, not_and, not_not] at hi
    rw [cosetState, cosetState]
    by_cases h1 : i ∈ cosetWindow dim N m (r + q * N)
    · rw [if_pos h1, if_pos (hi.1 h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hi.2 h2))]
  · -- actual-side Born mass ≤ q/2^m (the W1-side of the symmetric difference)
    rw [cosetState_bornWeightOn_eq]
    have hsub : (((W1 \ W2) ∪ (W2 \ W1)).filter (· ∈ cosetWindow dim N m (r + q * N)))
        ⊆ W1 \ W2 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiB, hip⟩ := hi
      have hiW1 : i ∈ W1 := by rw [hW1, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hip⟩
      rw [Finset.mem_union] at hiB
      rcases hiB with h | h
      · exact h
      · exact absurd hiW1 (Finset.mem_sdiff.mp h).2
    have hc := le_trans (Finset.card_le_card hsub) (windowDiff_card_le dim N m r q hN)
    gcongr
  · -- ideal-side Born mass ≤ q/2^m (the W2-side of the symmetric difference)
    rw [cosetState_bornWeightOn_eq]
    have hsub : (((W1 \ W2) ∪ (W2 \ W1)).filter (· ∈ cosetWindow dim N m r))
        ⊆ W2 \ W1 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiB, hip⟩ := hi
      have hiW2 : i ∈ W2 := by rw [hW2, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hip⟩
      rw [Finset.mem_union] at hiB
      rcases hiB with h | h
      · exact absurd hiW2 (Finset.mem_sdiff.mp h).2
      · exact h
    have hc := le_trans (Finset.card_le_card hsub) (windowDiff_card_le' dim N m r q hN)
    gcongr

end FormalRV.Shor.GidneyInPlace.CosetFold
