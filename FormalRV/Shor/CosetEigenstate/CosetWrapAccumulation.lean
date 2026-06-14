/-
  FormalRV.Shor.CosetEigenstate.CosetWrapAccumulation — obligation (3): the total wrap
  Born-mass accumulation for the Route-2 capstone.
  ════════════════════════════════════════════════════════════════════════════

  The Route-2 capstone (`CosetShorEmbedCapstone.coset_shor_succeeds_embed`) consumes a
  per-outcome wrap bad set `badY` with two total Born-mass bounds (`h_coset_wrap`,
  `h_embed_wrap`), each `≤ ε`.  This file builds the ACCUMULATION ALGEBRA that produces
  those bounds: the total bad set is the UNION over all steps (the `numIter` controlled
  multiplications × the `numWin` window additions), and its total Born mass is bounded by
  the SUM of the per-step masses (`dataBornMass_union_le`, iterated), hence by
  `numStep · β` when each step carries mass `≤ β`.

    * `totalBadSet` — the per-outcome union `⋃_{k<numStep} B k x` of the per-step bad sets.
    * `dataBornMass_biUnion_le` — (single outcome) the Born mass on the union is `≤` the
      sum of the per-step masses (iterated `dataBornMass_union_le`).
    * `totalWrapMass_le` — (summed over outcomes) the TOTAL wrap mass is `≤ numStep · β`,
      given each step's outcome-summed mass is `≤ β`.  GENERIC in the state `s`, so it
      yields BOTH capstone bounds: apply to `Shor_final_state f_coset` for `h_coset_wrap`
      and to `embedIdeal` for `h_embed_wrap`.
    * `totalWrapMass_le_numWin` — the coarse instantiation `≤ numStep · (numWin / 2^m)`
      (with `numStep = numIter` the per-multiply granularity, this is the
      `numIter · numWin / 2^m` bound; the per-addition granularity `numStep = numIter·numWin`
      with `β = 1/2^m` gives the same).

  WHERE `β` COMES FROM (the honest link).  The per-step outcome-summed bound `β =
  numWin / 2^m` is the per-multiply wrap fraction `CosetFoldWindowed.cosetState_windowedMul_embed_off`
  proves for the coset eigenstate (`bornWeightOn (cosetState …) B ≤ numWin/2^m`), times the
  unit total state norm.  Transferring it to `Shor_final_state f_coset` / `embedIdeal` per
  step is the ORBIT/EIGENSTATE lift (capstone obligations 1–2): `β` is the hypothesis
  `hstep` here, dischargeable once the orbit places each per-step coset eigenstate.
  Controlled-INACTIVE branches contribute the identity (no wrap), so they are bounded by
  the SAME per-step estimate (their per-step bad set is empty / mass 0 ≤ β).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.PhaseMarginalOracle

namespace FormalRV.Shor.CosetEigenstate.CosetWrapAccumulation

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.PhaseMarginalOracle (dataBornMass_union_le)

/-- The total wrap bad set at outcome `x`: the union of the per-step bad sets `B k x`
    over all `numStep` steps (controlled multiplications × window additions). -/
def totalBadSet {m_dim full_dim : Nat}
    (B : Nat → Fin m_dim → Finset (Fin (full_dim / m_dim))) (numStep : Nat)
    (x : Fin m_dim) : Finset (Fin (full_dim / m_dim)) :=
  (Finset.range numStep).biUnion (fun k => B k x)

/-- **Iterated union subadditivity (single outcome).**  The data Born mass on the total
    bad set is at most the sum of the per-step masses — `dataBornMass_union_le` iterated
    over the `numStep` steps. -/
theorem dataBornMass_biUnion_le {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s : QState full_dim) (x : Fin m_dim)
    (B : Nat → Fin m_dim → Finset (Fin (full_dim / m_dim))) (numStep : Nat) :
    (∑ y ∈ totalBadSet B numStep x, Complex.normSq (s (jointIdx h x y) 0))
      ≤ ∑ k ∈ Finset.range numStep,
          ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0) := by
  induction numStep with
  | zero => simp [totalBadSet]
  | succ K ih =>
      have hb : totalBadSet B (K + 1) x = B K x ∪ totalBadSet B K x := by
        ext z
        simp only [totalBadSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
        constructor
        · rintro ⟨k, hk, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | h'
          · exact Or.inr ⟨k, h', hz⟩
          · exact Or.inl (h' ▸ hz)
        · rintro (hz | ⟨k, hk, hz⟩)
          · exact ⟨K, Nat.lt_succ_self K, hz⟩
          · exact ⟨k, Nat.lt_succ_of_lt hk, hz⟩
      rw [hb, Finset.sum_range_succ]
      calc (∑ y ∈ B K x ∪ totalBadSet B K x, Complex.normSq (s (jointIdx h x y) 0))
          ≤ (∑ y ∈ B K x, Complex.normSq (s (jointIdx h x y) 0))
              + (∑ y ∈ totalBadSet B K x, Complex.normSq (s (jointIdx h x y) 0)) :=
            dataBornMass_union_le h s x (B K x) (totalBadSet B K x)
        _ ≤ (∑ y ∈ B K x, Complex.normSq (s (jointIdx h x y) 0))
              + (∑ k ∈ Finset.range K, ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0)) := by
            linarith [ih]
        _ = (∑ k ∈ Finset.range K, ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0))
              + (∑ y ∈ B K x, Complex.normSq (s (jointIdx h x y) 0)) := by ring

/-- **TOTAL WRAP MASS ACCUMULATION.**  If every step's outcome-summed Born mass is `≤ β`,
    the TOTAL wrap mass (summed over outcomes, on the union bad set) is `≤ numStep · β`.
    GENERIC in `s`: instantiate with `Shor_final_state f_coset` for `h_coset_wrap` and with
    `embedIdeal` for `h_embed_wrap`. -/
theorem totalWrapMass_le {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s : QState full_dim)
    (B : Nat → Fin m_dim → Finset (Fin (full_dim / m_dim))) (numStep : Nat) (β : ℝ)
    (hstep : ∀ k, k < numStep →
        (∑ x : Fin m_dim, ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0)) ≤ β) :
    (∑ x : Fin m_dim, ∑ y ∈ totalBadSet B numStep x,
        Complex.normSq (s (jointIdx h x y) 0)) ≤ numStep * β := by
  calc (∑ x : Fin m_dim, ∑ y ∈ totalBadSet B numStep x,
            Complex.normSq (s (jointIdx h x y) 0))
      ≤ ∑ x : Fin m_dim, ∑ k ∈ Finset.range numStep,
            ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0) :=
        Finset.sum_le_sum (fun x _ => dataBornMass_biUnion_le h s x B numStep)
    _ = ∑ k ∈ Finset.range numStep, ∑ x : Fin m_dim,
            ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0) := Finset.sum_comm
    _ ≤ ∑ _k ∈ Finset.range numStep, β :=
        Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
    _ = numStep * β := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The coarse `numStep · (numWin / 2^m)` bound.**  Specializing `β = numWin / 2^m`
    (the per-multiply wrap fraction `CosetFoldWindowed` bounds the coset eigenstate by):
    the total wrap mass is `≤ numStep · numWin / 2^m`.  With `numStep = numIter` this is
    the `numIter · numWin / 2^m` per-side bound the capstone's `ε = totalDeviationR` carries. -/
theorem totalWrapMass_le_numWin {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s : QState full_dim)
    (B : Nat → Fin m_dim → Finset (Fin (full_dim / m_dim)))
    (numStep numWin m : Nat)
    (hstep : ∀ k, k < numStep →
        (∑ x : Fin m_dim, ∑ y ∈ B k x, Complex.normSq (s (jointIdx h x y) 0))
          ≤ (numWin : ℝ) / 2 ^ m) :
    (∑ x : Fin m_dim, ∑ y ∈ totalBadSet B numStep x,
        Complex.normSq (s (jointIdx h x y) 0))
      ≤ (numStep : ℝ) * numWin / 2 ^ m := by
  have h1 := totalWrapMass_le h s B numStep ((numWin : ℝ) / 2 ^ m) hstep
  rw [mul_div_assoc]; exact h1

end FormalRV.Shor.CosetEigenstate.CosetWrapAccumulation
