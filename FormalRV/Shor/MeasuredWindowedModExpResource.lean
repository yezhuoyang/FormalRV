/-
  FormalRV.Shor.MeasuredWindowedModExpResource — Concern-2 closure for the MEASURED windowed modexp:
  the WHOLE m-iterate modular-exponentiation resource, walked over the SAME measured gates that drive
  Shor to success.

  ## What this closes (resource on the SAME verified circuit as the value)

  `MeasuredWindowedShorCapstone.measWindowed_shor_resource_capstone` already gives, on ONE per-iterate
  object: (i) the verified measured family attains Shor success `≥ κ/(log₂N)⁴`, and (ii) each
  per-iterate measured gate `measWindowedModNEncodeGate` has the measurement-optimized Toffoli count
  `2·numWin·(4·w·2^w + 8·bits)`.

  This file lifts (ii) from per-iterate to the WHOLE modexp: the total Toffoli count of the `m`
  per-iterate measured gates (one per QPE control bit `i < m`, constant in `i`) is
  `m · 2·numWin·(4·w·2^w + 8·bits)` — obtained by SUMMING `EGate.toffoli` over the actual measured
  gate terms, not a formula.  So the published modexp resource is now reported from the IDENTICAL
  measured circuit whose value drives Shor — the measurement-uncompute (`EGate.mz`) contained in the
  syntactic object the resource proof walks.  Axiom-clean.
-/
import FormalRV.Shor.MeasuredWindowedShorCapstone

namespace FormalRV.Shor.MeasuredWindowedShorCapstone

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredWindowedModN
open VerifiedShor
open scoped BigOperators

/-- **★ MEASURED WINDOWED MODEXP — Shor success ∧ WHOLE-modexp measured resource on ONE circuit ★.**
    Simultaneously, on the SAME measured gates:

      (I)  the family the faithful MEASURED windowed multiplier acts as attains the canonical Shor
           success bound `≥ κ/(log₂N)⁴` (`measWindowed_shor_succeeds`);

      (II) the WHOLE `m`-iterate modexp's Toffoli count — the SUM of `EGate.toffoli` over the actual
           per-iterate measured gates `measWindowedModNEncodeGate … ((a^(2^i))%N) …`, one per QPE
           control bit `i < m` — is exactly `m · 2·numWin·(4·w·2^w + 8·bits)`.

    Both faces ride the IDENTICAL measured circuit (measurement-uncompute included): the resource the
    audit reports is walked over the very gates whose value drives Shor — Concern-2 satisfied for the
    measured windowed-modexp route, end to end, with the measurement-optimized count. -/
theorem measWindowed_modexp_resource_capstone (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ (∑ i ∈ Finset.range m,
        EGate.toffoli (measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i)))))
        = m * (2 * (numWin * (4 * w * 2 ^ w + 8 * bits))) := by
  refine ⟨measWindowed_shor_succeeds w bits numWin N a ainv0 r m hw hbits hb1 hN1 hN2 h_inv0 h_setting,
    ?_⟩
  rw [Finset.sum_congr rfl (fun i _ =>
        toffoli_measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i)))),
      Finset.sum_const, Finset.card_range, smul_eq_mul]

end FormalRV.Shor.MeasuredWindowedShorCapstone
