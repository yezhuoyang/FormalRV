/-
  FormalRV.Shor.MeasuredWindowedShorCapstone — STEP 4: the family-level Shor-success lift for the
  FAITHFUL MEASURED windowed mod-N multiplier.

  The measured in-place multiplier (`MeasuredWindowedModN.measWindowedModNMulInPlace`, the
  count-optimal measurement-uncompute circuit) is proven correct (3a–3d) and counted on one
  measured `EGate`.  Here we lift it to the canonical `encodeDataZeroAnc` Shor layout
  (`measWindowedModNEncodeGate`) and feed it through the EGate→reversible bridge:

    * `egate_matches_rev` is PER-encoded-basis-state (∀ x < N), so it is discharged directly from
      the basis value (`measWindowedModNEncodeGate_apply`) via `uc_eval_toUCom_acts_on_basis` —
      NO superposition perfection needed; `countOptimal_shor_succeeds_constrained` handles the
      superposition internally.
    * The reversible family is the verified `windowedModNMultiplier_verifiedModMulFamily`, whose
      per-iterate gate IS `Gate.toUCom` of `windowedModNEncodeGate` (`windowedFamily_iterate_gate`).

  Result: the family the measured gate acts as attains the canonical Shor success bound
  `≥ κ/(log₂N)⁴`, and the measured per-iterate gate carries the measurement-optimized Toffoli
  count `2·numWin·(4·w·2^w + 8·bits)` — Shor success ∧ measured count, the measured-uncompute
  contained in the syntactic object the resource proof is about.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredWindowedModN
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal

namespace FormalRV.Shor.MeasuredWindowedShorCapstone

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredWindowedModN
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Audit.GidneyEkera2021.ShorComposed
open VerifiedShor

/-- The measured encode gate's adapters are T-free, so its Toffoli count equals the measured
    in-place multiplier's: `2·numWin·(4·w·2^w + 8·bits)`. -/
theorem toffoli_measWindowedModNEncodeGate (w bits N numWin c cinv : Nat) :
    EGate.toffoli (measWindowedModNEncodeGate w bits N numWin c cinv)
      = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)) := by
  have htc : EGate.tcount (measWindowedModNEncodeGate w bits N numWin c cinv)
      = 2 * (numWin * (28 * w * 2 ^ w + 56 * bits)) := by
    unfold measWindowedModNEncodeGate
    have hin : Gate.tcount (windowedEncodeIn w bits) = 0 := by
      simp [windowedEncodeIn, Gate.tcount, tcount_swapCascade]
    have hout : Gate.tcount (windowedEncodeOut w bits) = 0 := by
      simp [windowedEncodeOut, Gate.tcount, tcount_swapCascade]
    simp only [EGate.tcount, hin, hout, tcount_measWindowedModNMulInPlace, Nat.add_zero, Nat.zero_add]
  unfold EGate.toffoli
  rw [htc, show 2 * (numWin * (28 * w * 2 ^ w + 56 * bits))
          = (2 * (numWin * (4 * w * 2 ^ w + 8 * bits))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **The measured = reversible witness on the encoded subspace.**  `rev` is the verified windowed
    mod-N multiplier family; `eg i` is the MEASURED encode gate for the per-iterate constant; they
    agree on every encoded basis state because both compute `((a^(2^i))%N · x) mod N` there
    (`measWindowedModNEncodeGate_apply` vs `windowedModNEncodeGate_apply`, lifted by
    `uc_eval_toUCom_acts_on_basis`). -/
noncomputable def measWindowedShorWitness (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N bits (2 * w + 2 * bits + 3)
      (fun i => measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i))))
      (fun _ x => encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  rev := windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0
  eg_wellTyped := fun i =>
    measWindowedModNEncodeGate_wellTypedAt w bits N numWin ((a ^ (2 ^ i)) % N)
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
        measWindowedModNEncodeGate_apply w bits numWin N ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) x
          hw hbits hb1 hN_pos hN2 hx h_lt h_inv']

/-- **★ STEP 4 — THE MEASURED WINDOWED SHOR SUCCESS BOUND ★.**  The family the faithful MEASURED
    windowed mod-N multiplier acts as (on the encoded subspace) attains the canonical Shor
    success-probability bound `≥ κ/(log₂N)⁴` — the measurement-uncompute circuit drives Shor. -/
theorem measWindowed_shor_succeeds (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  countOptimal_shor_succeeds_constrained (w := w) (numWin := numWin) (q_start := 1 + 2 * w)
    (Tfam := fun _ _ _ => 0) hw (by omega)
    (measWindowedShorWitness w bits numWin N a ainv0 hw hbits hb1 hN1 hN2 h_inv0) r m h_setting

/-- **★ THE MEASURED-UNCOMPUTE SHOR CAPSTONE — success ∧ measured count ★.**  Simultaneously:
    (i) the family the faithful measured windowed multiplier acts as attains Shor success
    `≥ κ/(log₂N)⁴`; and (ii) each per-iterate MEASURED gate (the measurement-uncompute circuit,
    `mz`-clears density-justified) has the optimized Toffoli count `2·numWin·(4·w·2^w + 8·bits)`.
    The measured-uncompute is contained in the syntactic object driving Shor, and counted. -/
theorem measWindowed_shor_resource_capstone (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i, EGate.toffoli (measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
        (modInv N (a ^ (2 ^ i)))) = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)) :=
  ⟨measWindowed_shor_succeeds w bits numWin N a ainv0 r m hw hbits hb1 hN1 hN2 h_inv0 h_setting,
   fun i => toffoli_measWindowedModNEncodeGate w bits N numWin ((a ^ (2 ^ i)) % N)
     (modInv N (a ^ (2 ^ i)))⟩

end FormalRV.Shor.MeasuredWindowedShorCapstone
