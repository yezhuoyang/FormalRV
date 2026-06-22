/-
  FormalRV.Shor.MeasuredBabbushWindowedShorCapstone — STEP 4 for the BABBUSH-MEASURED
  in-place windowed mod-N multiplier: the family-level Shor-success lift, with the
  Babbush `2^w − 1` lookup and Gidney's `4L − 4`-T temporary AND, on ONE syntactic object.

  Identical in shape to `MeasuredWindowedShorCapstone`, but the per-iterate gate is the
  Babbush-measured `MeasuredBabbushWindowedModN.babbushMeasWindowedModNEncodeGate` (the
  count-optimal Babbush+Gidney circuit) instead of the flat-measured one.  Its value on
  every encoded basis state equals the verified reversible family
  (`windowedModNMultiplier_verifiedModMulFamily`), so it inherits the canonical Shor
  success bound `≥ κ/(log₂N)⁴`, and carries the Babbush Toffoli count
  `2·numWin·(2·(2^w − 1) + 8·bits)`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredBabbushWindowedModN
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

namespace FormalRV.Shor.MeasuredBabbushWindowedShorCapstone

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredBabbushWindowedModN
open FormalRV.Shor.EGateToUnitaryBridge
open Audit.GidneyEkera2021.ShorComposed
open VerifiedShor

/-- **The Babbush-measured = reversible witness on the encoded subspace.**  `rev` is the verified
    windowed mod-N multiplier family; `eg i` is the BABBUSH-MEASURED encode gate for the per-iterate
    constant; they agree on every encoded basis state because both compute `((a^(2^i))%N · x) mod N`
    there (`babbushMeasWindowedModNEncodeGate_apply` vs `windowedModNEncodeGate_apply`, lifted by
    `uc_eval_toUCom_acts_on_basis`). -/
noncomputable def babbushMeasWindowedShorWitness (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N bits (2 * w + 2 * bits + 3)
      (fun i => babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))))
      (fun _ x => encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  rev := windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0
  eg_wellTyped := fun i =>
    babbushMeasWindowedModNEncodeGate_wellTypedAt w bits N numWin ((a ^ (2 ^ i)) % N)
      (modInv N (a ^ (2 ^ i))) hw hbits
  egate_matches_rev := by
    intro i x hx
    have hN_pos : 0 < N := by omega
    obtain ⟨h_lt, h_inv⟩ := modInv_spec N (a ^ (2 ^ i)) hN_pos
      ⟨ainv0 ^ (2 ^ i), by rw [Nat.mul_mod]; exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩
    have h_inv' : ((a ^ (2 ^ i)) % N) * modInv N (a ^ (2 ^ i)) % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_inv
    rw [windowedFamily_iterate_gate w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0 i,
        uc_eval_toUCom_acts_on_basis (bits + (2 * w + 2 * bits + 3))
          (windowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))))
          (windowedModNEncodeGate_wellTyped w bits N numWin ((a ^ (2 ^ i)) % N)
            (modInv N (a ^ (2 ^ i))) hw hbits)
          (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x),
        windowedModNEncodeGate_apply w bits numWin N ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) x
          hw hbits hb1 hN_pos hN2 hx h_lt h_inv',
        babbushMeasWindowedModNEncodeGate_apply w bits numWin N ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))) x hw hbits hb1 hN_pos hN2 hx h_lt h_inv']

/-- **★ STEP 4 — THE BABBUSH-MEASURED WINDOWED SHOR SUCCESS BOUND ★.**  The family the
    Babbush-measured windowed mod-N multiplier acts as (on the encoded subspace) attains the
    canonical Shor success-probability bound `≥ κ/(log₂N)⁴`. -/
theorem babbushMeasWindowed_shor_succeeds (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  countOptimal_shor_succeeds_constrained (w := w) (numWin := numWin) (q_start := 1 + 2 * w)
    (Tfam := fun _ _ _ => 0) hw (by omega)
    (babbushMeasWindowedShorWitness w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0) r m h_setting

/-- **★ THE BABBUSH-MEASURED-UNCOMPUTE SHOR CAPSTONE — success ∧ Babbush count ∧ paper `4L − 4`. ★**
    Simultaneously: (i) the family the Babbush-measured windowed multiplier acts as attains Shor
    success `≥ κ/(log₂N)⁴`; (ii) each per-iterate gate (the Babbush+Gidney measurement-uncompute
    circuit) has the Toffoli count `2·numWin·(2·(2^w − 1) + 8·bits)` — the Babbush `2^w − 1`
    lookup; and (iii) its Gidney temporary-AND T-count is `4·` that, the lookups contributing the
    paper's `4L − 4` per QROM read (arXiv:1805.03662 §III.A/§III.C).  The Babbush lookup and
    Gidney's 4-T AND are contained in the very syntactic object driving Shor, and that object is
    proven correct. -/
theorem babbushMeasWindowed_shor_resource_capstone (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ (∀ i, EGate.toffoli (babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i)))) = 2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits)))
    ∧ (∀ i, FormalRV.Shor.GidneyTCount.gidneyTCount
        (babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
          (modInv N (a ^ (2 ^ i))))
        = 4 * (2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits)))) :=
  ⟨babbushMeasWindowed_shor_succeeds w bits numWin N a ainv0 r m hw hbits hb1 hN1 hN2 h_inv0 h_setting,
   fun i => toffoli_babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
     (modInv N (a ^ (2 ^ i))),
   fun i => gidneyTCount_babbushMeasWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
     (modInv N (a ^ (2 ^ i)))⟩

end FormalRV.Shor.MeasuredBabbushWindowedShorCapstone
