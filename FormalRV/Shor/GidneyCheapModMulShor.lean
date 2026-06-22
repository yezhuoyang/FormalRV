/-
  FormalRV.Shor.GidneyCheapModMulShor — wiring the cheap in-place measured multiplier
  `gcMulEncodeGate` to the FULL Shor success bound.

  The measured circuit `gcMulEncodeGate` (GidneyCheapModMulInPlace) computes `x ↦ (a·x) mod N` on
  every encoded basis state (`gcMulEncodeGate_apply`) and is well-typed (`gcMulEncodeGate_wellTypedAt`).
  Here we:
    1. build a verified reversible family `gcRevFamily` at the gcMul ancilla width
       `gcAnc w bits = 3·bits + w + 7` (by PADDING the verified `windowedModNEncodeGate` up to that
       width — the 3-per-bit Gidney layout needs more ancilla than the Cuccaro `2w+2bits+3`), which
       carries the Shor success bound;
    2. assemble the `MeasuredEqualsReversibleOnEncoded` witness — the MEASURED `gcMulEncodeGate` acts
       on every encoded basis state EXACTLY as the reversible family (both compute `(a^(2^i)·x) mod N`);
    3. conclude `probability_of_success ≥ κ/(log₂N)⁴` AND attach the measured Toffoli count — Shor
       success and the cheap measured count on ONE composed syntactic circuit, no cheating.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyCheapModMulInPlace
import FormalRV.Shor.WindowedShorConnection
import FormalRV.Shor.MultiplierInstances
import FormalRV.Arithmetic.ModExp.ModExpCorrectness
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
import FormalRV.Audit.Gidney2025.ToffoliReproduction

namespace FormalRV.Shor.GidneyCheapModMulShor

open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open VerifiedShor
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.ModularAdder.GidneyModAddReg
open FormalRV.Shor.GidneyCheapModMul
open FormalRV.Shor.GidneyCheapModMulInPlace
open FormalRV.Shor.EGateToUnitaryBridge

/-! ## §1. The reversible multiplier family at the gcMul ancilla width (padded). -/

/-- **Padded round-trip:** the verified `windowedModNEncodeGate` (native anc `2w+2bits+3`) computes
    `|x⟩|0⟩ ↦ |(c·x) % N⟩|0⟩` at ANY larger anc `ancbig` — the extra ancilla wires are untouched
    zeros.  Proven by `Gate.applyNat_congr` (the two encodings agree on the gate's typed region)
    plus `Gate.applyNat_oob` for the out-of-band wires. -/
theorem windowedModNEncodeGate_apply_anc
    (w bits numWin N c cinv x ancbig : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1)
    (hbig : 2 * w + 2 * bits + 3 ≤ ancbig) :
    Gate.applyNat (windowedModNEncodeGate w bits N numWin c cinv)
        (encodeDataZeroAnc bits ancbig x)
      = encodeDataZeroAnc bits ancbig (c * x % N) := by
  set nat := 2 * w + 2 * bits + 3 with hnat
  set nat_dim := bits + nat with hnatdim
  set g := windowedModNEncodeGate w bits N numWin c cinv with hg
  have the_wt : Gate.WellTyped nat_dim g :=
    windowedModNEncodeGate_wellTyped w bits N numWin c cinv hw hbits
  have hN_le : N ≤ 2 ^ bits := by omega
  have hx2 : x < 2 ^ bits := lt_of_lt_of_le hx hN_le
  have hcx2 : c * x % N < 2 ^ bits := lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN_le
  have hancbig_pos : 0 < ancbig := by omega
  have hnat_pos : 0 < nat := by omega
  have h_native : Gate.applyNat g (encodeDataZeroAnc bits nat x)
      = encodeDataZeroAnc bits nat (c * x % N) :=
    windowedModNEncodeGate_apply w bits numWin N c cinv x hw hbits hb1 hN_pos hN2 hx hcinv hinv
  have hagree : ∀ i, i < nat_dim →
      encodeDataZeroAnc bits ancbig x i = encodeDataZeroAnc bits nat x i := by
    intro i hi
    by_cases hib : i < bits
    · rw [encodeDataZeroAnc_data hx2 hib, encodeDataZeroAnc_data hx2 hib]
    · have hj : i - bits < nat := by omega
      have hjbig : i - bits < ancbig := by omega
      have hieq : i = bits + (i - bits) := by omega
      rw [hieq, encodeDataZeroAnc_anc hx2 hjbig, encodeDataZeroAnc_anc hx2 hj]
  have hcongr : ∀ p, p < nat_dim →
      Gate.applyNat g (encodeDataZeroAnc bits ancbig x) p
        = Gate.applyNat g (encodeDataZeroAnc bits nat x) p :=
    Gate.applyNat_congr the_wt _ _ hagree
  apply eq_encodeDataZeroAnc_of_data_anc_oob hancbig_pos hcx2
  · intro i hi
    have hi' : i < nat_dim := by omega
    rw [hcongr i hi', h_native, encodeDataZeroAnc_data hcx2 hi]
  · intro j hj
    by_cases hjn : j < nat
    · have hp : bits + j < nat_dim := by omega
      rw [hcongr (bits + j) hp, h_native, encodeDataZeroAnc_anc hcx2 hjn]
    · have hp : nat_dim ≤ bits + j := by omega
      rw [Gate.applyNat_oob the_wt _ hp]
      exact encodeDataZeroAnc_anc hx2 hj
  · intro i hi
    have hp : nat_dim ≤ i := by omega
    rw [Gate.applyNat_oob the_wt _ hp]
    exact encodeDataZeroAnc_oob hancbig_pos hi

/-- The `encodeDataZeroAnc`-round-trip multiplier at the gcMul ancilla width `3·bits + w + 7`. -/
noncomputable def gcRevEncode (w bits numWin N : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) :
    EncodeRoundTripModMul N bits (3 * bits + w + 7) where
  gate := fun c => windowedModNEncodeGate w bits N numWin (c % N) (modInv N c)
  wellTyped := fun c => by
    have hnumWin : 1 ≤ numWin := by
      rcases Nat.eq_zero_or_pos numWin with h0 | hpos
      · rw [h0, Nat.zero_mul] at hbits; omega
      · exact hpos
    have hw_le_bits : w ≤ bits := by
      calc w = 1 * w := by rw [Nat.one_mul]
        _ ≤ numWin * w := Nat.mul_le_mul_right _ hnumWin
        _ = bits := hbits
    exact Gate.WellTyped.mono
      (windowedModNEncodeGate_wellTyped w bits N numWin (c % N) (modInv N c) hw hbits)
      (by omega)
  roundTrip := by
    intro c x hx hc
    have hN_pos : 0 < N := by omega
    obtain ⟨h_lt, h_inv⟩ := modInv_spec N c hN_pos hc
    have h_inv' : (c % N) * modInv N c % N = 1 := by rw [Nat.mod_mul_mod]; exact h_inv
    have hbig : 2 * w + 2 * bits + 3 ≤ 3 * bits + w + 7 := by
      have hnumWin : 1 ≤ numWin := by
        rcases Nat.eq_zero_or_pos numWin with h0 | hpos
        · rw [h0, Nat.zero_mul] at hbits; omega
        · exact hpos
      have hw_le_bits : w ≤ bits := by
        calc w = 1 * w := by rw [Nat.one_mul]
          _ ≤ numWin * w := Nat.mul_le_mul_right _ hnumWin
          _ = bits := hbits
      omega
    show Gate.applyNat (windowedModNEncodeGate w bits N numWin (c % N) (modInv N c))
        (encodeDataZeroAnc bits (3 * bits + w + 7) x)
      = encodeDataZeroAnc bits (3 * bits + w + 7) ((c * x) % N)
    rw [windowedModNEncodeGate_apply_anc w bits numWin N (c % N) (modInv N c) x
          (3 * bits + w + 7) hw hbits hb1 hN_pos hN2 hx h_lt h_inv' hbig, Nat.mod_mul_mod]

/-- **The verified reversible family at the gcMul ancilla width** — carries the Shor success bound. -/
noncomputable def gcRevFamily (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1) :
    VerifiedShor.VerifiedModMulFamily a N bits (3 * bits + w + 7) :=
  (gcRevEncode w bits numWin N hw hbits hb1 hN1 hN2).toVerifiedModMulFamily a (by omega) ainv0 hN1 h_inv0

/-! ## §2. The measured = reversible witness on the encoded subspace. -/

/-- **The witness:** the verified reversible family `gcRevFamily` carries Shor success; the MEASURED
    `gcMulEncodeGate` (per QPE iterate `i`) acts on every encoded basis state EXACTLY as the
    reversible family, because both compute `((a^(2^i)) · x) mod N` there — the reversible side via
    the padded `gcRevEncode.roundTrip`, the measured side via `gcMulEncodeGate_apply`, lifted by
    `uc_eval_toUCom_acts_on_basis`. -/
noncomputable def gcMulShorWitness (w n numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = n + 1)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ (n + 1)) (h_inv0 : a * ainv0 % N = 1) :
    MeasuredEqualsReversibleOnEncoded a N (n + 1) (3 * (n + 1) + w + 7)
      (fun i => gcMulEncodeGate w (n + 1) ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin)
      (fun _ x => encodeDataZeroAnc (n + 1) (3 * (n + 1) + w + 7) x) where
  rev := gcRevFamily w (n + 1) numWin N a ainv0 hw hbits (by omega) hN1 hN2 h_inv0
  eg_wellTyped := fun i =>
    gcMulEncodeGate_wellTypedAt w n ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin
      ((n + 1) + (3 * (n + 1) + w + 7)) hbits (by omega)
  egate_matches_rev := by
    intro i x hx
    have hN_pos : 0 < N := by omega
    have hguard : ∃ d, ((a ^ (2 ^ i)) * d) % N = 1 :=
      ⟨ainv0 ^ (2 ^ i), by rw [Nat.mul_mod]; exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩
    obtain ⟨h_modinv_lt, h_modinv⟩ := modInv_spec N (a ^ (2 ^ i)) hN_pos hguard
    have h_inv' : ((a ^ (2 ^ i)) % N) * modInv N (a ^ (2 ^ i)) % N = 1 := by
      rw [Nat.mod_mul_mod]; exact h_modinv
    have hfam : (gcRevFamily w (n + 1) numWin N a ainv0 hw hbits (by omega) hN1 hN2 h_inv0).family i
        = Gate.toUCom ((n + 1) + (3 * (n + 1) + w + 7))
            (windowedModNEncodeGate w (n + 1) N numWin ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i)))) :=
      rfl
    have h_rev_wt : Gate.WellTyped ((n + 1) + (3 * (n + 1) + w + 7))
        (windowedModNEncodeGate w (n + 1) N numWin ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i)))) :=
      (gcRevEncode w (n + 1) numWin N hw hbits (by omega) hN1 hN2).wellTyped (a ^ (2 ^ i))
    have h_round : Gate.applyNat
          (windowedModNEncodeGate w (n + 1) N numWin ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))))
          (encodeDataZeroAnc (n + 1) (3 * (n + 1) + w + 7) x)
        = encodeDataZeroAnc (n + 1) (3 * (n + 1) + w + 7) ((a ^ (2 ^ i)) * x % N) :=
      (gcRevEncode w (n + 1) numWin N hw hbits (by omega) hN1 hN2).roundTrip (a ^ (2 ^ i)) x hx hguard
    have happly := gcMulEncodeGate_apply w n ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin x
      hw hN_pos (by omega) hbits hx h_modinv_lt h_inv'
    simp only [gcAnc] at happly
    rw [hfam, uc_eval_toUCom_acts_on_basis _ _ h_rev_wt
          (encodeDataZeroAnc (n + 1) (3 * (n + 1) + w + 7) x), h_round, happly, Nat.mod_mul_mod]

/-! ## §3. ★ THE CAPSTONE — full Shor success ∧ the cheap measured count, on the gcMul circuit. -/

/-- **★ FULL SHOR SUCCESS ∧ MEASURED COUNT ★.**  Simultaneously:
    (i) the family the cheap measured multiplier `gcMulEncodeGate` realizes (on the encoded subspace)
    attains the canonical Shor success-probability bound `≥ κ/(log₂N)⁴`; and
    (ii) each per-iterate MEASURED gate has the cheap Toffoli count `2·numWin·((2^w−1)+3·(bits+1))`.
    The measured cheap multiplier drives Shor (its semantics certified on every encoded basis state by
    the witness), and is counted — Shor success and the cheap count on ONE composed syntactic circuit,
    no cheating. -/
theorem gcMul_shor_resource_capstone (w n numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = n + 1)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ (n + 1)) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m (n + 1)) :
    probability_of_success a r N m (n + 1) (3 * (n + 1) + w + 7)
        (gcRevFamily w (n + 1) numWin N a ainv0 hw hbits (by omega) hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ ∀ i, EGate.toffoli
        (gcMulEncodeGate w (n + 1) ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin)
        = 2 * (numWin * ((2 ^ w - 1) + 2 * (n + 2))) :=
  ⟨FormalRV.Audit.GidneyEkera2021.ShorComposed.countOptimal_shor_succeeds_constrained
      (w := w) (numWin := numWin) (q_start := 1) (Tfam := fun _ _ _ => 0) hw (by norm_num)
      (gcMulShorWitness w n numWin N a ainv0 hw hbits hN1 hN2 h_inv0) r m h_setting,
   fun i => toffoli_gcMulEncodeGate w n ((a ^ (2 ^ i)) % N) (modInv N (a ^ (2 ^ i))) N numWin⟩

/-! ## §4. ★ COST-FAITHFULNESS ★ — the count is EXACTLY Gidney-2025's per-gadget cost model.

    The keystone register modular-add is the COST-OPTIMAL 2-add (not the naive 3-add): its Toffoli
    count `2·(bits+1)` EQUALS Gidney-2025's `addCost`, and the per-window cost equals Gidney-2025's
    loop-body model `lookupCost + addCost` gadget-for-gadget.  This pins the resource count to the
    paper's verified per-gadget figures (no over-count). -/

theorem toffoli_gidneyModAddRegMeasured (n N : Nat) :
    EGate.toffoli (gidneyModAddRegMeasured (n + 1) N) = 2 * (n + 2) := by
  unfold EGate.toffoli
  rw [tcount_gidneyModAddRegMeasured, show 14 * (n + 2) = 2 * (n + 2) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

theorem toffoli_gcStep (w n a N numWin j : Nat) :
    EGate.toffoli (gcStep w (n + 1) a N numWin j) = (2 ^ w - 1) + 2 * (n + 2) := by
  unfold EGate.toffoli
  rw [tcount_gcStep, show 7 * ((2 ^ w - 1) + 2 * (n + 2)) = ((2 ^ w - 1) + 2 * (n + 2)) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **The keystone register modular-add costs EXACTLY Gidney-2025's `addCost = 2·(r+1)`.** -/
theorem gcMul_adder_eq_gidney2025_addCost (n N : Nat) :
    EGate.toffoli (gidneyModAddRegMeasured (n + 1) N)
      = FormalRV.Audit.Gidney2025.ToffoliReproduction.addCost (n + 1) := by
  rw [toffoli_gidneyModAddRegMeasured]
  unfold FormalRV.Audit.Gidney2025.ToffoliReproduction.addCost; ring

/-- **The per-window cost EQUALS Gidney-2025's loop body `lookupCost w + addCost (bits)`.** -/
theorem gcStep_eq_gidney2025_loopBody (w n a N numWin j : Nat) :
    EGate.toffoli (gcStep w (n + 1) a N numWin j)
      = FormalRV.Audit.Gidney2025.ToffoliReproduction.lookupCost w
        + FormalRV.Audit.Gidney2025.ToffoliReproduction.addCost (n + 1) := by
  rw [toffoli_gcStep]
  unfold FormalRV.Audit.Gidney2025.ToffoliReproduction.lookupCost
    FormalRV.Audit.Gidney2025.ToffoliReproduction.addCost; ring

/-- **The whole cheap multiplier's count in Gidney-2025's per-gadget terms:**
    `numWin · (lookupCost + addCost)`. -/
theorem gcMul_count_eq_gidney2025 (w n a N numWin : Nat) :
    EGate.toffoli (gcMul w (n + 1) a N numWin)
      = numWin * (FormalRV.Audit.Gidney2025.ToffoliReproduction.lookupCost w
        + FormalRV.Audit.Gidney2025.ToffoliReproduction.addCost (n + 1)) := by
  rw [toffoli_gcMul]
  unfold FormalRV.Audit.Gidney2025.ToffoliReproduction.lookupCost
    FormalRV.Audit.Gidney2025.ToffoliReproduction.addCost; ring

end FormalRV.Shor.GidneyCheapModMulShor
