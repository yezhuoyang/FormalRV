/-
  FormalRV.Shor.GidneyWindowedShorEndToEnd — the END-TO-END Shor FACTORING theorem for the
  windowed (Gidney/Babbush lookup) modular multiplier, with the cheap MEASURED circuit certified
  equal to the success-driving unitary.
  ════════════════════════════════════════════════════════════════════════════════════════════

  This composes the two verified halves into one circuit→factoring statement:

    • `windowedModNMul_shor_correct` (the windowed multiplier's QPE family attains the Shor
      success bound `≥ κ/(log₂N)⁴`), wired through
    • `ShorFactoring.shor_factoring_succeeds_good_base` (order-finding success ⇒ a nontrivial
      FACTOR of N for a good base — gap ④, vanilla order-finding, axiom-clean),

  giving `gidney_windowed_shor_factoring`: for a good base, the windowed Shor algorithm outputs a
  NONTRIVIAL FACTOR of N with probability `≥ κ/(log₂N)⁴`.

  And it records the MEASURED certification: `MeasuredCoherentCircuit.physMeasWindowedModNMulInPlace_channel`
  proves the CHEAP measured modular multiplier (Gidney's measurement-based uncomputation) realizes —
  as a quantum channel on the encoded subspace, coherences and all — EXACTLY the reversible unitary
  `windowedModNMulInPlace` that the family above is built from.  So the measured circuit drives the
  SAME QPE evolution as the success-bearing unitary, at the cheap measured Toffoli count.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.NumberTheory.ShorFactoringEndToEnd
import FormalRV.Shor.WindowedModNShor
import FormalRV.Shor.MeasuredCoherentCircuit

namespace FormalRV.Shor.GidneyWindowedShorEndToEnd

open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.NumberTheory.ShorFactoring

/-- **★★ END-TO-END WINDOWED SHOR FACTORING ★★** — for a good base `a` (even order `r` mod `N`,
    `a^(r/2) ≢ −1`), running Shor's algorithm with the windowed (lookup) modular-multiplier family
    on a precision register of size `m` (with `N² < 2^m ≤ 2N²`):

    1. outputs a NONTRIVIAL FACTOR of `N` with probability `≥ κ/(log₂N)⁴`
       (`factoringSuccessProb`), and
    2. that factor concretely exists.

    This is the first statement in the development tying the windowed-multiplier CIRCUIT all the way
    to FACTORING: the multiplier's verified Shor-success bound (`windowedModNMul_shor_correct`,
    i.e. `VerifiedModMulFamily.shorCorrect`) welded through the gap-④ order→factor reduction
    (`shor_factoring_succeeds_good_base`).  Vanilla order-finding — no Ekerå–Håstad, no Assumption 1. -/
theorem gidney_windowed_shor_factoring
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : BasicSettingRelaxed a r N m bits)
    (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    factoringSuccessProb a N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  set F := windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
    hw hbits hb1 hN1 hN2 h_inv0 with hF
  exact shor_factoring_succeeds_good_base h_setting F.mmi (fun i _ => F.wellTyped i) hN1 hr_even hgood

end FormalRV.Shor.GidneyWindowedShorEndToEnd
