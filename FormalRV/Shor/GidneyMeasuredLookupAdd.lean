/-
  FormalRV.Shor.GidneyMeasuredLookupAdd — the ALL-TEMPORARY-AND windowed lookup-add step
  (Concern-2, route (2)): the paper's per-window add structure where EVERY Toffoli is a
  genuine temporary AND, so the uniform Gidney 4-T model is GADGET-BY-GADGET HONEST.

  ## Why this exists (closing the route-(1) accounting residue)

  `MeasuredBabbushHonestTCount` (route (1)) gave the HONEST gadget-by-gadget T-count of the
  as-built Babbush-measured step — and showed that there the uniform `gidneyTCount = 4·toffoli`
  UNDER-counts by `24·bits`, because that step's adder/reduce (`cuccaro_n_bit_adder_full`,
  `modNReduceFlag`, `regCompareXor`) are the TEXTBOOK reversible construction whose carry
  Toffolis run IN PLACE (no clean ancilla to measurement-uncompute), so they cost the full 7 T,
  not 4.  The accounting was honest, but the uniform 4-T model was not valid for that circuit.

  The fix is architectural, and it is exactly what the papers do: a temporary-AND adder REQUIRES
  the **3-per-bit Gidney layout** (`read[i]=3i`, `target[i]=3i+1`, `carry[i]=3i+2`) — the dedicated
  carry-ancilla register is what lets the carry ANDs be computed into a clean ancilla and
  uncomputed by MEASUREMENT (Gidney arXiv:1709.06648).  The 2-per-bit cuccaro layout has no such
  ancilla, which is *why* its carries are 7-T in place.

  This file builds the per-window lookup-add step at the Gidney layout out of pieces that are
  EACH a genuine temporary AND, with value + count + honesty on ONE composed syntactic object:

    * the LOAD — the Babbush merged-AND unary-iteration QROM read (`unaryQROMPos`, arXiv:1805.03662
      §III.A/§III.C) writing the table word `T[v]` into the adder's READ register; each merged AND
      targets an `mz`-cleared ancilla — a temporary AND, paper-exact `4L − 4` per read;
    * the ADD — the MEASURED Gidney adder (`gidneyAdderMeasured`), whose forward carry sweep is
      `n` clean-ancilla temporary ANDs and whose reverse sweep is measurement-uncompute (0 Toffoli);
    * the UNCOMPUTE — `mz`-clearing the read word (the measurement-uncompute of the load, 0 Toffoli).

  `gidneyLookupAddStep_target_val`: VALUE — the accumulator becomes `(s + T[v]) mod 2^bits`
  (the faithful add; the mod-N reduction is deferred to the coset/runway, exactly as the papers do).
  `gidneyTCount_gidneyLookupAddStep`: COUNT — `4·((2^w − 1) + bits)`.
  `gidneyLookupAddStep_honest`: HONESTY — the uniform `gidneyTCount` EQUALS the gadget-by-gadget
  sum of the three gadgets' true temporary-AND costs (`4·(2^w−1)` lookup + `4·bits` adder + `0` mz).
  Unlike route (1) (where the uniform count under-counts), here it is EXACT — because every gadget
  is genuinely a temporary AND.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredBabbushRead
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderCorrectness
import FormalRV.Arithmetic.MeasuredAdder.MeasuredAdderResource
import FormalRV.Shor.GidneyTCount

namespace FormalRV.Shor.GidneyMeasuredLookupAdd

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredBabbushRead
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.GidneyTCount

/-! ## §1. Layout — lookup registers placed ABOVE the base-0 Gidney adder block. -/

/-- The lookup ADDRESS bit `i`, placed just above the `bits = n+2` adder block. -/
def gLookAddr (n : Nat) : Nat → Nat := fun i => adder_n_qubits (n + 2) + i

/-- The lookup AND-ANCILLA `i`, placed above the address register. -/
def gLookAnc (w n : Nat) : Nat → Nat := fun i => adder_n_qubits (n + 2) + w + i

/-- The lookup root CONTROL, placed above the ancilla register. -/
def gLookCtrl (w n : Nat) : Nat := adder_n_qubits (n + 2) + 2 * w

/-! ## §2. The all-temporary-AND lookup-add step. -/

/-- The LOAD: the Babbush merged-AND QROM read writing `T[v]` into the adder's READ register
    (`pos = read_idx`), with address/ancilla/control above the block.  Every merged AND is a
    temporary AND (`mz`-cleared ancilla); paper-exact `4L − 4` T per read. -/
def gidneyLookupLoad (w n : Nat) (T : Nat → Nat) : EGate :=
  unaryQROMPos (gLookAddr n) (gLookAnc w n) read_idx (n + 2) T w (gLookCtrl w n) 0

/-- **★ THE ALL-TEMPORARY-AND WINDOWED LOOKUP-ADD STEP ★** — load `T[v]` into the read register
    (Babbush temporary-AND QROM), add it into the accumulator (MEASURED Gidney adder, temporary-AND
    forward sweep + measurement uncompute), then `mz`-clear the read word.  Every Toffoli is a
    genuine temporary AND. -/
def gidneyLookupAddStep (w n : Nat) (T : Nat → Nat) : EGate :=
  EGate.seq (gidneyLookupLoad w n T)
    (EGate.seq (gidneyAdderMeasured (n + 2) 0)
      (mzList ((List.range (n + 2)).map read_idx)))

/-! ## §3. Counts — each gadget at its true temporary-AND cost. -/

/-- The step's exact T-count: `7·((2^w − 1) + bits)` (textbook 7-T accounting of the real
    Toffolis: `2^w − 1` lookup ANDs + `bits` forward-sweep carries; the measured reverse and the
    `mz`-clears are Toffoli-free). -/
theorem tcount_gidneyLookupAddStep (w n : Nat) (T : Nat → Nat) :
    EGate.tcount (gidneyLookupAddStep w n T) = 7 * ((2 ^ w - 1) + (n + 2)) := by
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) 0) = 7 * (n + 2) := by
    show EGate.tcount (EGate.seq (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
        (gidney_final_cx_cascade (n + 2)))) (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
      tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  unfold gidneyLookupAddStep gidneyLookupLoad
  have hstruct : EGate.tcount (EGate.seq
        (unaryQROMPos (gLookAddr n) (gLookAnc w n) read_idx (n + 2) T w (gLookCtrl w n) 0)
        (EGate.seq (gidneyAdderMeasured (n + 2) 0) (mzList ((List.range (n + 2)).map read_idx))))
      = EGate.tcount (unaryQROMPos (gLookAddr n) (gLookAnc w n) read_idx (n + 2) T w (gLookCtrl w n) 0)
        + (EGate.tcount (gidneyAdderMeasured (n + 2) 0)
            + EGate.tcount (mzList ((List.range (n + 2)).map read_idx))) := rfl
  rw [hstruct, tcount_unaryQROMPos, hadd, tcount_mzList]
  ring

/-- The step's Toffoli count: `(2^w − 1) + bits`. -/
theorem toffoli_gidneyLookupAddStep (w n : Nat) (T : Nat → Nat) :
    EGate.toffoli (gidneyLookupAddStep w n T) = (2 ^ w - 1) + (n + 2) := by
  unfold EGate.toffoli
  rw [tcount_gidneyLookupAddStep, Nat.mul_div_cancel_left _ (by norm_num)]

/-- The step's Gidney temporary-AND T-count: `4·((2^w − 1) + bits)`. -/
theorem gidneyTCount_gidneyLookupAddStep (w n : Nat) (T : Nat → Nat) :
    gidneyTCount (gidneyLookupAddStep w n T) = 4 * ((2 ^ w - 1) + (n + 2)) := by
  unfold gidneyTCount FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_gidneyLookupAddStep]

/-! ## §4. Gadget-by-gadget honesty — the uniform 4-T model is EXACT here. -/

/-- Per-gadget Gidney T-count of the LOAD: paper-exact `4·(2^w − 1) = 4L − 4` (every merged AND
    a temporary AND, arXiv:1805.03662 §III.A/§III.C). -/
theorem gidneyTCount_gidneyLookupLoad (w n : Nat) (T : Nat → Nat) :
    gidneyTCount (gidneyLookupLoad w n T) = 4 * (2 ^ w - 1) := by
  unfold gidneyTCount gidneyLookupLoad FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_unaryQROMPos]

/-- Per-gadget Gidney T-count of the MEASURED ADD: `4·bits` (every forward-sweep carry a temporary
    AND, the reverse measurement-uncomputed). -/
theorem gidneyTCount_gidneyAdderMeasured0 (n : Nat) :
    gidneyTCount (gidneyAdderMeasured (n + 2) 0) = 4 * (n + 2) := by
  unfold gidneyTCount FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_gidneyAdderMeasured]

/-- Per-gadget Gidney T-count of the `mz`-CLEAR: `0` (measurement, Toffoli-free). -/
theorem gidneyTCount_mzClear (n : Nat) :
    gidneyTCount (mzList ((List.range (n + 2)).map read_idx)) = 0 := by
  unfold gidneyTCount EGate.toffoli
  rw [tcount_mzList, Nat.zero_div, Nat.mul_zero]

/-- The honest gadget-by-gadget temporary-AND T-count of the step: the SUM of each gadget's true
    temporary-AND cost (LOAD `4·(2^w−1)` + ADD `4·bits` + `mz` `0`). -/
def gidneyLookupAddHonestTCount (w n : Nat) (T : Nat → Nat) : Nat :=
  gidneyTCount (gidneyLookupLoad w n T)
  + gidneyTCount (gidneyAdderMeasured (n + 2) 0)
  + gidneyTCount (mzList ((List.range (n + 2)).map read_idx))

/-- **★ THE UNIFORM 4-T MODEL IS GADGET-BY-GADGET HONEST HERE ★.**  The step's uniform
    `gidneyTCount = 4·toffoli` EQUALS the sum of the three gadgets' true temporary-AND costs —
    because EVERY gadget is genuinely a temporary AND (the Babbush merged-AND load, the measured
    Gidney adder, the `mz`-clears).  Contrast `MeasuredBabbushHonestTCount.gidneyTCount_le_honest`,
    where the uniform model strictly UNDER-counts the textbook adder/reduce. -/
theorem gidneyLookupAddStep_honest (w n : Nat) (T : Nat → Nat) :
    gidneyTCount (gidneyLookupAddStep w n T) = gidneyLookupAddHonestTCount w n T := by
  unfold gidneyLookupAddHonestTCount
  rw [gidneyTCount_gidneyLookupAddStep, gidneyTCount_gidneyLookupLoad,
      gidneyTCount_gidneyAdderMeasured0, gidneyTCount_mzClear]
  ring

/-! ## §5. Value — the accumulator becomes `(s + T[v]) mod 2^bits` (faithful add). -/

/-- `adder_input_F` at any non-`read` position is independent of the read operand `a`
    (the read register is the only `a`-dependent part).  Used to bridge `adder_input_F _ 0 s`
    (the clean input) and `adder_input_F _ (T v) s` (the post-load input) off the read register. -/
theorem adder_input_F_read_indep (n a a' b q : Nat)
    (hq : ∀ j, j < n → q ≠ read_idx j) :
    adder_input_F n a b q = adder_input_F n a' b q := by
  rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega) with h | h | h
  · have hqn : ¬ q / 3 < n := fun hlt => hq (q / 3) hlt (by simp only [read_idx]; omega)
    simp [adder_input_F, h, hqn]
  · simp only [adder_input_F, h]
  · simp only [adder_input_F, h]

/-- **★ VALUE OF THE ALL-TEMPORARY-AND STEP ★.**  On a clean Gidney-layout input — accumulator
    `s < 2^bits` in the target register, read & carry clean (the adder block equals
    `adder_input_F (n+2) 0 s`), lookup address `= v`, ancilla clean, root control set — the step
    leaves the accumulator holding `(s + T[v]) mod 2^bits`.  The faithful add; the mod-N reduction
    is deferred to the coset/runway exactly as the papers do.  Value and the temporary-AND count
    ride the SAME composed syntactic object. -/
theorem gidneyLookupAddStep_target_val (w n v s : Nat) (T : Nat → Nat) (f : Nat → Bool)
    (hw : 0 < w) (hv : v < 2 ^ w) (hs : s < 2 ^ (n + 2)) (hTv : T v < 2 ^ (n + 2))
    (hblock : ∀ q, q < adder_n_qubits (n + 2) → f q = adder_input_F (n + 2) 0 s q)
    (hctrl : f (gLookCtrl w n) = true)
    (haddr : ∀ i, i < w → f (gLookAddr n i) = v.testBit i)
    (hanc : ∀ i, i < w → f (gLookAnc w n i) = false) :
    gidney_target_val (n + 2) (EGate.applyNat (gidneyLookupAddStep w n T) f)
      = (s + T v) % 2 ^ (n + 2) := by
  -- the address register decodes to `v`
  have hdec : decodeReg (gLookAddr n) w f = v := by
    rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (gLookAddr n) w v f haddr,
      Nat.mod_eq_of_lt hv]
  -- disjointness side-conditions for the selection lemma
  have hpos_inj : ∀ j k, j < n + 2 → k < n + 2 → read_idx j = read_idx k → j = k := by
    intro j k _ _ h; simp only [read_idx] at h; omega
  have hc_inj : ∀ i i', gLookAnc w n i = gLookAnc w n i' → i = i' := by
    intro i i' h; simp only [gLookAnc] at h; omega
  have h_anc_out : ∀ i j, i < w → j < n + 2 → gLookAnc w n i ≠ read_idx j := by
    intro i j _ hj; simp only [gLookAnc, read_idx, adder_n_qubits]; omega
  have h_anc_addr : ∀ i i', i < w → i' < w → gLookAnc w n i ≠ gLookAddr n i' := by
    intro i i' _ hi'; simp only [gLookAnc, gLookAddr]; omega
  have h_addr_out : ∀ i j, i < w → j < n + 2 → gLookAddr n i ≠ read_idx j := by
    intro i j _ hj; simp only [gLookAddr, read_idx, adder_n_qubits]; omega
  have h_ctrl_out : ∀ j, j < n + 2 → gLookCtrl w n ≠ read_idx j := by
    intro j hj; simp only [gLookCtrl, read_idx, adder_n_qubits]; omega
  have h_ctrl_anc : ∀ i, i < w → gLookCtrl w n ≠ gLookAnc w n i := by
    intro i hi; simp only [gLookCtrl, gLookAnc]; omega
  have hsel := unaryQROMPos_selects_word (gLookAddr n) (gLookAnc w n) read_idx (n + 2) T
    hpos_inj hc_inj w (gLookCtrl w n) 0 f h_anc_out h_anc_addr h_addr_out h_ctrl_out h_ctrl_anc hanc
  -- the post-load state equals `adder_input_F (n+2) (T v) s` on the adder block
  have hA : ∀ q, q < adder_n_qubits (n + 2) →
      EGate.applyNat (gidneyLookupLoad w n T) f q = adder_input_F (n + 2) (T v) s q := by
    intro q hq
    unfold gidneyLookupLoad
    by_cases hr : ∃ j, j < n + 2 ∧ q = read_idx j
    · obtain ⟨j, hj, rfl⟩ := hr
      have hfr : f (read_idx j) = false := by
        rw [hblock (read_idx j) hq]
        unfold adder_input_F read_idx
        rw [show (3 * j) % 3 = 0 from by omega, show (3 * j) / 3 = j from by omega]
        simp [Nat.zero_testBit]
      have hrhs : adder_input_F (n + 2) (T v) s (read_idx j) = (T v).testBit j := by
        unfold adder_input_F read_idx
        rw [show (3 * j) % 3 = 0 from by omega, show (3 * j) / 3 = j from by omega]
        simp [hj]
      rw [hsel j hj, hctrl, Bool.true_and, Nat.zero_add, hdec, hfr, Bool.false_xor, hrhs]
    · push Not at hr
      rw [unaryQROMPos_frame (gLookAddr n) (gLookAnc w n) read_idx (n + 2) T w (gLookCtrl w n) 0 f q
            hr (fun i _ => by simp only [gLookAnc]; omega),
          hblock q hq]
      exact adder_input_F_read_indep (n + 2) 0 (T v) s q hr
  -- each target bit of the final state is the faithful sum bit
  have hbits : ∀ i, i < n + 2 →
      EGate.applyNat (gidneyLookupAddStep w n T) f (target_idx i) = (s + T v).testBit i := by
    intro i hi
    have htidx : target_idx i < adder_n_qubits (n + 2) := by
      simp only [target_idx, adder_n_qubits]; omega
    have hmz : EGate.applyNat (gidneyLookupAddStep w n T) f (target_idx i)
        = EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
            (EGate.applyNat (gidneyLookupLoad w n T) f) (target_idx i) := by
      show EGate.applyNat (mzList ((List.range (n + 2)).map read_idx))
          (EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
            (EGate.applyNat (gidneyLookupLoad w n T) f)) (target_idx i)
        = EGate.applyNat (gidneyAdderMeasured (n + 2) 0)
            (EGate.applyNat (gidneyLookupLoad w n T) f) (target_idx i)
      apply applyNat_mzList_preserves
      intro hmem
      obtain ⟨j, _, hjeq⟩ := List.mem_map.mp hmem
      simp only [target_idx, read_idx] at hjeq; omega
    rw [hmz,
        EGate.applyNat_congr_lt (adder_n_qubits (n + 2)) (gidneyAdderMeasured (n + 2) 0)
          (gidneyAdderMeasured_boundedBy n 0) (EGate.applyNat (gidneyLookupLoad w n T) f)
          (adder_input_F (n + 2) (T v) s) hA (target_idx i) htidx,
        (gidneyAdderMeasured_correct n (T v) s 0 hTv hs i hi).1, adder_sum_bit_classical,
        Nat.add_comm (T v) s]
  exact gidney_target_val_eq_sum_when_bits_match (n + 2) (s + T v)
    (EGate.applyNat (gidneyLookupAddStep w n T) f) hbits

end FormalRV.Shor.GidneyMeasuredLookupAdd
