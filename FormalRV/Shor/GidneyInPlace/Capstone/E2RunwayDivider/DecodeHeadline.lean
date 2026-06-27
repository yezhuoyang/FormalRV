/- E2RunwayDivider — Â§5h support-form decode HEADLINE.  Part of the `E2RunwayDivider` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.DecodeInduction

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (compareConstXor_state_general condSub_state_general)


/-! ### §5h. HEADLINE: the support-form decode (the deliverable). -/

/-- The clean input `encDiv bits v` is a `DivState bits cm N v` whenever `v < N·2^cm`,
    `N·2^cm ≤ 2^bits`, `cm ≤ bits`, `0 < N`. -/
theorem encDiv_DivState (bits cm N v : Nat)
    (hr : v < N * 2 ^ cm) (hbud : N * 2 ^ cm ≤ 2 ^ bits) (hcm : cm ≤ bits) (hN : 0 < N) :
    DivState bits cm N v (encDiv bits v) :=
  { hr := hr, hbudget := hbud, hcm := hcm, hN := hN
    h_cin := encDiv_cin bits v
    h_flag := encDiv_flag bits v
    h_tgt := fun i hi => encDiv_data bits v i hi
    h_read := fun i hi => encDiv_read bits v i hi
    h_quot := fun k _ => encDiv_qbit bits v k }

/-- **HEADLINE — the reversible DIVMOD-by-N decode (Stage A), fully verified.**
    On the support `v = z + j·N` (`z < N`, `j < 2^cm`, budget `2^cm·N ≤ 2^bits`),
    running `divModN bits cm N` on the clean input `encDiv bits v`:
      • the DATA band (Cuccaro target reg, `q_start = 0`) decodes to `z = v % N`,
      • the QUOTIENT band wire `qBase bits + k` holds bit `k` of `j = v / N`,
      • the TRANSIENT workspace (carry / read band / flag) returns clean,
      • the gate is WellTyped at `dimDiv bits cm`.
    (`Gate.reverse (divModN bits cm N)` then composes for Stage C.) -/
theorem divModN_decode
    (bits cm N z j : Nat)
    (hbits : 1 ≤ bits) (hN : 0 < N) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (hz : z < N) (hj : j < 2 ^ cm) :
    -- DATA band → remainder z = v % N
    cuccaro_target_val bits 0
        (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N))) = z
    -- QUOTIENT band → bit k of j = v / N
    ∧ (∀ k, k < cm →
        Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (qBase bits + k)
          = j.testBit k)
    -- TRANSIENT clean: flag, read band, carry
    ∧ Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (flagW bits) = false
    ∧ (∀ i, i < bits →
        Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (0 + 2 * i + 2) = false)
    ∧ Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) 0 = false
    -- WELL-TYPED
    ∧ Gate.WellTyped (dimDiv bits cm) (divModN bits cm N) := by
  set v := z + j * N with hv
  -- budget in the convenient orientation, and v < N*2^cm.
  have hbud' : N * 2 ^ cm ≤ 2 ^ bits := by rw [Nat.mul_comm]; exact hbudget
  have hv_lt : v < N * 2 ^ cm := by
    rw [hv]
    calc z + j * N < N + j * N := by omega
      _ = (j + 1) * N := by ring
      _ ≤ 2 ^ cm * N := Nat.mul_le_mul_right _ (by omega)
      _ = N * 2 ^ cm := by ring
  have hv_bits : v < 2 ^ bits := lt_of_lt_of_le hv_lt hbud'
  -- the general decode on the DivState of encDiv.
  obtain ⟨hd_tgt, hd_quot, hd_cin, hd_flag, hd_read⟩ :=
    divModN_decode_gen cm bits N v (encDiv bits v)
      (encDiv_DivState bits cm N v hv_lt hbud' hcm hN)
  -- arithmetic: v % N = z, v / N = j.
  obtain ⟨hjdiv, hzmod⟩ := divModN_arith N z j hN hz
  rw [← hv] at hjdiv hzmod
  refine ⟨?_, ?_, hd_flag, hd_read, hd_cin, ?_⟩
  · -- DATA band decode = v % N = z.
    have hz_bits : z < 2 ^ bits := by
      have hNle : N ≤ 2 ^ bits := le_trans (Nat.le_mul_of_pos_right N (by positivity : 0 < 2 ^ cm)) hbud'
      omega
    rw [cuccaro_target_val_eq_sum_when_bits_match bits 0 (v % N) _
          (fun i hi => by rw [hd_tgt i hi])]
    rw [hzmod]
    exact Nat.mod_eq_of_lt hz_bits
  · -- QUOTIENT band → bit k of v/N = j.
    intro k hk; rw [hd_quot k hk, hjdiv]
  · exact divModN_wellTyped bits cm N hbits hcm


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
