/-
  FormalRV.Shor.GidneyInPlace.CosetState — the coset state + per-add deviation.
  ════════════════════════════════════════════════════════════════════════════

  Assembles the two infrastructure pieces into the Zalka/Gidney coset state

      cosetState dim N m r  =  uniformSuperposition over (cosetWindow dim N m r)
                            =  (1/√2^m) · ∑_{j<2^m} |r + j·N⟩,

  and proves — directly on the real state — the paper's PER-ADD DEVIATION (Gidney
  arXiv:1905.08488, Thm 3.2): the Born weight the coset state places on the single
  wrapping representative (the top, `j = 2^m−1`) is EXACTLY `1/2^m`.

  This is the concrete, never-assumed form of the per-addition deviation `Dev =
  1/2^m`, and the building block of the wrap Born-weight bounds that the repo's
  `CosetAgreesOffWrap` / `coset_ideal_normSqDist_le` consume (then subadditive over
  all adds → `totalDeviation`, then `ApproxTransfer` → the success bound).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Primitives.Def.UniformState
import FormalRV.Shor.GidneyInPlace.Primitives.Def.CosetClass

namespace FormalRV.Shor.GidneyInPlace.CosetState

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.UniformState (uniformSuperposition uniformSuperposition_bornWeightOn)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow cosetWindow_card)

/-- The Zalka/Gidney coset state `|Coset_m(r)⟩` as a uniform superposition over the
    fixed `2^m`-representative window. -/
noncomputable def cosetState (dim N m r : Nat) : QState dim :=
  uniformSuperposition dim (cosetWindow dim N m r)

/-- The single wrapping representative — the TOP of the window (`j = 2^m−1`). -/
def topRep (dim N m r : Nat) (hfit : r + (2 ^ m - 1) * N < dim) : Fin dim :=
  ⟨r + (2 ^ m - 1) * N, hfit⟩

/-- The top representative is in the window. -/
theorem topRep_mem (dim N m r : Nat) (hN : 0 < N) (hfit : r + (2 ^ m - 1) * N < dim) :
    topRep dim N m r hfit ∈ cosetWindow dim N m r := by
  rw [mem_cosetWindow dim N m r hN]
  exact ⟨2 ^ m - 1, by have := Nat.two_pow_pos m; omega, rfl⟩

/-- **THE PER-ADD DEVIATION (Gidney Thm 3.2), on the real coset state.**  The Born
    weight the coset state places on the single wrapping (top) representative is
    EXACTLY `1/2^m` — every representative carries equal mass `1/2^m`, and exactly
    one wraps per non-modular addition.  This is the concrete `Dev = 1/2^m`. -/
theorem cosetState_topWrap_bornWeight (dim N m r : Nat) (hN : 0 < N)
    (hfit : r + (2 ^ m - 1) * N < dim) :
    bornWeightOn (cosetState dim N m r) {topRep dim N m r hfit} = 1 / (2 ^ m : ℝ) := by
  unfold cosetState
  rw [uniformSuperposition_bornWeightOn,
      Finset.singleton_inter_of_mem (topRep_mem dim N m r hN hfit),
      Finset.card_singleton, cosetWindow_card dim N m r hN hfit]
  push_cast
  ring

/-- **The wrap Born-weight bound — the form `CosetAgreesOffWrap` consumes.**  If a
    wrap set `B` contains at most `t` representatives, the coset state's Born weight
    on `B` is at most `t/2^m`.  (Each rep carries mass `1/2^m`; `B` hits at most `t`
    of the window's `2^m`.)  With `t` = (the number of additions, by subadditivity)
    this is the per-window contribution to `totalDeviation`. -/
theorem cosetState_wrap_bornWeight_le (dim N m r t : Nat) (B : Finset (Fin dim))
    (hN : 0 < N) (hfit : r + (2 ^ m - 1) * N < dim) (hB : B.card ≤ t) :
    bornWeightOn (cosetState dim N m r) B ≤ (t : ℝ) / 2 ^ m := by
  unfold cosetState
  rw [uniformSuperposition_bornWeightOn, cosetWindow_card dim N m r hN hfit]
  push_cast
  gcongr
  exact_mod_cast le_trans (Finset.card_le_card Finset.inter_subset_left) hB

end FormalRV.Shor.GidneyInPlace.CosetState
