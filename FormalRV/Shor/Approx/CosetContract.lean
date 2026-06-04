/-
  FormalRV.Shor.Approx.CosetContract — Phase C contract + named (cited) obligations.

  Assembles the proved graceful-degradation engine (`SuccessStable`) into a
  pluggable contract for the Gidney–Ekerå *coset / approximate* modular-arithmetic
  oracle, mirroring the exact `VerifiedModMulFamily` path but tolerating a bounded
  ℓ²-deviation.

  The ONLY research-level facts are quarantined as two named obligations, cited
  verbatim to Gidney 2019 (arXiv:1905.08488):

    * `CosetAdderDeviationBound` — Thm 3.3 (`modular-coset-deviation`): one
      non-modular addition on `|Coset_m(r)⟩ = 2^{-m/2} Σ_{j<2^m} |r+jN⟩` has
      combinatorial deviation `Dev ≤ 2^{-m}`.
    * `TraceDistanceFromDeviation` — Thm 2.6 (`quantum-deviation`): an approximate
      encoded permutation with `Dev ≤ ε` has output within trace/state distance
      `2√ε` of the ideal.

  Everything else (the per-outcome Lipschitz bridge, the success-probability
  degradation, the assembly below) is PROVED, kernel-clean.
-/
import FormalRV.Shor.Approx.SuccessStable

namespace FormalRV.Shor.Approx

open scoped BigOperators
open FormalRV.SQIRPort

/-- **Named obligation — Gidney 2019, Thm 3.3 (`modular-coset-deviation`).**
    The per-addition combinatorial deviation of the coset representation with
    padding `pad`: one non-modular add deviates with `Dev ≤ 2^{-pad}`.  (Proof in
    the paper: the only deviated coset value is `c = 2^{pad} − 1`.)  Stated as a
    predicate so callers discharge it from the paper / a future Lean proof. -/
def CosetAdderDeviationBound (pad : Nat) (dev : ℝ) : Prop :=
  dev ≤ (2 : ℝ) ^ (-(pad : ℤ))

/-- **Named obligation — Gidney 2019, Thm 2.6 (`quantum-deviation`).**  An
    approximate encoded permutation whose combinatorial deviation is `≤ totalDev`
    produces a final state within ℓ²-distance `2√(totalDev)` of the ideal final
    state.  (Paper proof: fidelity `≥ 1 − 2ε`, then `T = √(1−d²) ≤ 2√ε`.) -/
def TraceDistanceFromDeviation (m n anc : Nat)
    (f g : Nat → BaseUCom (n + anc)) (totalDev : ℝ) : Prop :=
  pmDist (Shor_final_state m n anc f) (Shor_final_state m n anc g)
    ≤ 2 * Real.sqrt totalDev

/-- **The Phase-C approximate-oracle contract.**  Bundles an approximate family
    `fApprox`, an ideal family `gIdeal` achieving a success bound `idealBound`, an
    accumulated combinatorial deviation `totalDev`, and the two named obligations
    that turn `totalDev` into an ℓ²-distance between the final states.  Mirrors the
    exact `VerifiedModMulFamily`, but the correctness guarantee is *degraded* by an
    explicit, bounded toll. -/
structure ApproxCosetShor (a r N m n anc : Nat) where
  fApprox : Nat → BaseUCom (n + anc)
  gIdeal : Nat → BaseUCom (n + anc)
  /-- accumulated combinatorial deviation `Σ` per-op `Dev` (Gidney `Dev`). -/
  totalDev : ℝ
  totalDev_nonneg : 0 ≤ totalDev
  /-- the ideal success bound, e.g. `κ / (log₂ N)^4`. -/
  idealBound : ℝ
  /-- normalization of the two final states. -/
  normf : pmNorm (Shor_final_state m n anc fApprox) ≤ 1
  normg : pmNorm (Shor_final_state m n anc gIdeal) ≤ 1
  /-- the ideal family meets the headline success bound (exact-oracle path). -/
  ideal_ge : idealBound ≤ probability_of_success a r N m n anc gIdeal
  /-- **named obligation** (Gidney Thm 2.6): `Dev ≤ totalDev ⟹ distance ≤ 2√totalDev`. -/
  trace_obl : TraceDistanceFromDeviation m n anc fApprox gIdeal totalDev

/-- **Phase-C correctness (proved).**  The approximate coset oracle succeeds with
    probability at least `idealBound − 2^m · 4√(totalDev)` — the ideal bound minus
    an explicit toll that vanishes as the padding grows (`totalDev → 0`). -/
theorem ApproxCosetShor.shorCorrect {a r N m n anc : Nat}
    (W : ApproxCosetShor a r N m n anc) :
    W.idealBound - (2 ^ m : ℝ) * (2 * (2 * Real.sqrt W.totalDev))
      ≤ probability_of_success a r N m n anc W.fApprox :=
  shor_success_approx a r N m n anc W.fApprox W.gIdeal W.idealBound
    (2 * Real.sqrt W.totalDev) W.normf W.normg W.ideal_ge W.trace_obl

/-- **Exact-oracle path is the `totalDev = 0` special case** (no degradation):
    when the deviation budget is zero the approximate family meets the ideal bound
    exactly.  This confirms the approximate contract strictly generalizes the
    exact one. -/
theorem ApproxCosetShor.shorCorrect_exact {a r N m n anc : Nat}
    (W : ApproxCosetShor a r N m n anc) (h0 : W.totalDev = 0) :
    W.idealBound ≤ probability_of_success a r N m n anc W.fApprox := by
  have := W.shorCorrect
  rw [h0, Real.sqrt_zero] at this
  simpa using this

end FormalRV.Shor.Approx
