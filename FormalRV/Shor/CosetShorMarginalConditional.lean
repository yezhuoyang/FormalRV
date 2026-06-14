/-
  FormalRV.Shor.CosetShorMarginalConditional — the SOUND conditional coset-Shor
  success bound, wired to the phase-marginal route (NOT the discredited full-state
  `CosetAgreesOffWrap`/`CosetIdealL1Bound` object).
  ════════════════════════════════════════════════════════════════════════════

  ⚠ CORRECTNESS NOTE (verified against the in-repo no-cheating audit,
  `CosetMarginalShorBound.lean:6-24`, 2026-06-13).  The earlier
  `ApproxCosetShorBound.ge2021_coset_shor_succeeds` rides `CosetIdealL1Bound`
  (full-state `normSqDist`-to-canonical), an obligation that is **unsatisfiable**:
  the coset gadget keeps the data register UNREDUCED (`a·x ≥ N`), so the coset and
  canonical final states sit on DIFFERENT data supports and their full-state
  `normSqDist` is `Ω(1)`, never `≤ 2·totalDeviationR`.  We therefore do NOT wire to
  `CosetAgreesOffWrap`; we wire to the SOUND phase-marginal route
  (`CosetMarginalShorBound.coset_shor_succeeds_marginal`), whose frontier
  `CosetMarginalRelabel` is satisfiable in principle (off wrap the coset IS a
  data-register permutation of the ideal, with identical phase marginals).

  THE CONDITIONAL FINAL THEOREM.  `ge2021_coset_shor_succeeds_marginal` carries
  exactly ONE hypothesis about the two final states — the sound `CosetMarginalRelabel`
  witness `R` (the QPE-lifted exact off-wrap data permutation + the wrap Born-weight
  bounds).  The ideal success bound `P_ideal = κ/(log₂ N)⁴` is DISCHARGED, not
  assumed (`windowedModNMul_shor_correct`, which rides the Mertens-FREE totient lower
  bound `phi_n_over_n_lowerbound_proved` — no Mertens, no axioms).  So the only
  remaining frontier is `R` — and `R` is the multiply→full-QPE lift, whose
  per-iterate arithmetic content is supplied (off wrap) by the coset multiplier's
  exact decoded-value contract (`CosetEigenstate.CosetLayout.CosetMulFwdContract`),
  with the bottom-up `uc_eval`/`branchOf` composition through all `m` controlled
  iterates + the inverse QFT being the genuine remaining mathematical work.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.ApproxCosetShorBound
import FormalRV.Shor.CosetMarginalShorBound

namespace FormalRV.Shor.ApproxCosetShorBound

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.BQAlgo.WindowedModNShor
open VerifiedShor (ShorSetting)
open FormalRV.Shor.CosetMarginalShorBound (CosetMarginalRelabel coset_shor_succeeds_marginal)

/-- **THE SOUND CONDITIONAL COSET-SHOR BOUND (phase-marginal route).**  For the
    GE2021 windowed parameters, the coset modexp family `f_coset` succeeds with
    probability `≥ κ/(log₂ N)⁴ − 2·totalDeviationR`, conditional on ONE sound
    frontier: a `CosetMarginalRelabel` witness `R` (off-wrap the coset final state is
    the ideal final state with the data register relabeled by a permutation, both
    placing Born weight `≤ totalDeviationR` on the wrap set).  The ideal bound
    `P_ideal = κ/(log₂ N)⁴` is PROVEN (`windowedModNMul_shor_correct`, Mertens-free),
    not a hypothesis.

    This is the SOUND replacement for `ge2021_coset_shor_succeeds` (which rides the
    unsatisfiable `CosetIdealL1Bound`): the only carried obligation `R` is
    satisfiable in principle, and everything downstream of it is proven. -/
theorem ge2021_coset_shor_succeeds_marginal
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits)
    (f_coset : Nat → BaseUCom (bits + (2 * w + 2 * bits + 3)))
    (R : CosetMarginalRelabel a r N m bits (2 * w + 2 * bits + 3) f_coset
          (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
            hw hbits hb1 hN1 hN2 h_inv0).family
          totalDeviationR) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3) f_coset
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 - 2 * totalDeviationR :=
  coset_shor_succeeds_marginal a r N m bits (2 * w + 2 * bits + 3)
    f_coset
    (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
      hw hbits hb1 hN1 hN2 h_inv0).family
    totalDeviationR (κ / (Nat.log2 N : ℝ) ^ 4)
    (windowedModNMul_shor_correct w bits numWin N a ainv0 r m
      hw hbits hb1 hN1 hN2 h_inv0 h_setting)
    R

end FormalRV.Shor.ApproxCosetShorBound
