/-
  FormalRV.Shor.MeasuredBabbushWindowedModExpResource — the WHOLE m-iterate modexp resource of the
  BABBUSH-MEASURED in-place windowed mod-N multiplier, walked over the SAME verified gates that drive
  Shor to success, with the paper-exact `4L − 4` per-lookup T-count.

  ## What this closes (Concern-2 at the paper's OPTIMIZED lookup cost)

  `MeasuredBabbushWindowedShorCapstone.babbushMeasWindowed_shor_resource_capstone` gives, on ONE
  per-iterate object: (i) Shor success `≥ κ/(log₂N)⁴`, (ii) per-iterate Babbush Toffoli count
  `2·numWin·(2·(2^w − 1) + 8·bits)`, and (iii) the per-iterate Gidney temporary-AND T-count `4·` that
  — the lookups contributing the paper's exact `4L − 4` per QROM read (`GidneyTCount.gidneyTCount_unaryQROMAt`,
  arXiv:1805.03662 §III.A/§III.C).

  This file lifts (ii),(iii) from per-iterate to the WHOLE modexp: the total Toffoli / Gidney-T cost
  of the `m` per-iterate Babbush-measured gates (one per QPE control bit `i < m`, constant in `i`) is
  `m ×` the per-iterate cost — obtained by SUMMING `EGate.toffoli` / `gidneyTCount` over the actual
  gate terms, not a formula.  So the published modexp resource — with the paper's OPTIMIZED Babbush
  `2^w − 1` lookup and Gidney's `4L − 4` T per read — is reported from the IDENTICAL verified circuit
  whose value drives Shor.  Axiom-clean.

  HONEST SCOPE (inherited from the per-iterate capstone): the `4L − 4` per QROM read is EXACT and
  paper-matching; the `8·bits/step` adder/mod-N-reduction term is charged at the uniform Gidney
  4-T-per-AND model (not every Cuccaro carry Toffoli is a clean-target temporary AND), so the
  whole-modexp total is the OPTIMIZED-lookup, uniform-adder estimate — not the scattered `modExpAt`
  headline `2.578×10⁹` (a different circuit structure: in-place mod-N reduction vs coset rep).
-/
import FormalRV.Shor.MeasuredBabbushWindowedShorCapstone

namespace FormalRV.Shor.MeasuredBabbushWindowedShorCapstone

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredBabbushWindowedModN
open VerifiedShor
open scoped BigOperators

/-- **★ BABBUSH-MEASURED WINDOWED MODEXP — Shor success ∧ WHOLE-modexp resource on ONE circuit, at
    the paper's optimized lookup cost ★.**  Simultaneously, on the SAME Babbush-measured gates:

      (I)   the family the Babbush-measured windowed multiplier acts as attains Shor success
            `≥ κ/(log₂N)⁴`;

      (II)  the WHOLE `m`-iterate modexp Toffoli count — the SUM of `EGate.toffoli` over the actual
            per-iterate Babbush-measured gates `babbushMeasWindowedModNEncodeGate … ((a^(2^i))%N) …`,
            one per QPE control bit `i < m` — is exactly `m · 2·numWin·(2·(2^w − 1) + 8·bits)` (the
            Babbush `2^w − 1` lookup); and

      (III) the WHOLE-modexp Gidney temporary-AND T-count is `4·` that — the lookups contributing the
            paper's `4L − 4` per QROM read.

    The optimized Babbush lookup and Gidney's `4L − 4` T are contained in the IDENTICAL verified
    circuit whose value drives Shor — Concern-2 satisfied at the paper's optimized lookup cost. -/
theorem babbushMeasWindowed_modexp_resource_capstone (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ (∑ i ∈ Finset.range m,
        EGate.toffoli (babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i)))))
        = m * (2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits)))
    ∧ (∑ i ∈ Finset.range m,
        FormalRV.Shor.GidneyTCount.gidneyTCount
          (babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i)))))
        = m * (4 * (2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits)))) := by
  obtain ⟨hsucc, htoff, hgid⟩ :=
    babbushMeasWindowed_shor_resource_capstone w bits numWin N a ainv0 r m
      hw hbits hb1 hN1 hN2 h_inv0 h_setting
  refine ⟨hsucc, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun i _ => htoff i), Finset.sum_const, Finset.card_range, smul_eq_mul]
  · rw [Finset.sum_congr rfl (fun i _ => hgid i), Finset.sum_const, Finset.card_range, smul_eq_mul]

end FormalRV.Shor.MeasuredBabbushWindowedShorCapstone
