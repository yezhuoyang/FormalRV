/-
  FormalRV.Shor.MeasuredBabbushWindowedModN — the BABBUSH-MEASURED faithful mod-N
  windowed multiplier: the missing combination of (i) Babbush's `2^w − 1` unary-iteration
  QROM read (arXiv:1805.03662 §III.A/§III.C) with (ii) Gidney's measurement-based
  uncompute and (iii) the in-place mod-N multiplier structure — value AND count on ONE
  syntactic object, at the paper's `4L − 4` T-count per lookup.

  ## The combination that did not exist before

  The repo had the three ingredients separately: the flat unary `lookupReadAt`
  (`2·w·2^w`, reversible) used by all in-place multipliers; the Babbush merged-AND read
  (`2^w − 1`, measured) only in the scattered `modExpAt` skeleton; and the measured
  in-place multiplier (`MeasuredWindowedModN.measWindowedModNMulInPlace`) still using the
  expensive flat read.  This file combines them: the in-place measured step with the flat
  LOAD reads replaced by the layout-correct Babbush read `MeasuredBabbushRead.babbushReadInPlace`.

  ## Value by transport (no re-derivation)

  `babbushReadInPlace_selects` has EXACTLY the conclusion of `lookupReadAt_selects`, so on
  any clean-ancilla state the two reads are extensionally equal (`babbushRead_eq_lookupRead`).
  The Babbush-measured step therefore equals the flat-measured step on clean inputs (the
  two LOAD reads are bridged; the two `mz`-uncomputes are identical), and so inherits
  `MeasuredWindowedModN.measModNLookupAddStep_applyNat_eq` — i.e. equals the unitary
  `modNLookupAddStep`.  The whole multiplier and the Shor capstone then follow exactly the
  flat-measured development, only cheaper.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasuredBabbushRead
import FormalRV.Shor.MeasuredWindowedModN
import FormalRV.Shor.GidneyTCount

namespace FormalRV.Shor.MeasuredBabbushWindowedModN

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.MeasuredBabbushRead
open FormalRV.Shor.MeasuredWindowedModN

/-! ## §1. Read-equivalence: the Babbush read = the flat read on clean states. -/

/-- **The Babbush read and the flat read agree on clean-ancilla states.**  Both
    `babbushReadInPlace_selects` and `WindowedLookupSelect.lookupReadAt_selects` have the
    SAME conclusion (XOR `T v` onto the word, preserve the rest), so on any state whose
    lookup registers are clean with address `= v`, the two reads compute the same map. -/
theorem babbushRead_eq_lookupRead (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat)
    (f : Nat → Bool) (v : Nat)
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    EGate.applyNat (babbushReadInPlace w pos W T) f
      = Gate.applyNat (lookupReadAt w pos W T) f := by
  obtain ⟨hbv, hbf⟩ :=
    babbushReadInPlace_selects w W T pos f v hw hv hctrl haddr hand hpos_high hpos_inj
  obtain ⟨hlv, hlf⟩ :=
    lookupReadAt_selects w W T pos f v hw hv hctrl haddr hand hpos_high hpos_inj
  funext p
  by_cases hp : ∃ j, j < W ∧ p = pos j
  · obtain ⟨j, hj, rfl⟩ := hp
    rw [hbv j hj, hlv j hj]
  · simp only [not_exists, not_and] at hp
    rw [hbf p hp, hlf p hp]

/-! ## §2. The Babbush-measured mod-N lookup-add step and its counts. -/

/-- **The Babbush-MEASURED mod-N lookup-add step.**  `MeasuredWindowedModN.measModNLookupAddStep`
    with each flat LOAD read (`lookupReadAt`, `2·w·2^w` Toffolis) replaced by the
    layout-correct Babbush merged-AND read (`babbushReadInPlace`, `2^w − 1` Toffolis).  The
    two `mz`-uncomputes are unchanged. -/
def babbushMeasModNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) : EGate :=
  EGate.seq (babbushReadInPlace w (addendIdx q_start) bits T)
    (EGate.seq (EGate.base (cuccaro_n_bit_adder_full bits q_start))
      (EGate.seq (mzList ((List.range bits).map (addendIdx q_start)))
        (EGate.seq (EGate.base (modNReduceFlag bits q_start N flagPos))
          (EGate.seq (babbushReadInPlace w (addendIdx q_start) bits T)
            (EGate.seq (EGate.base (regCompareXor bits q_start flagPos))
              (mzList ((List.range bits).map (addendIdx q_start))))))))

/-- **The Babbush-measured step's exact T-count: `14·(2^w − 1) + 56·bits`** — two Babbush
    LOAD reads (`2·7·(2^w − 1)`) + adder (`14·bits`) + mod-N reduce (`28·bits`) +
    register-compare (`14·bits`); the two uncompute reads are `mz`-clears (Toffoli-free). -/
theorem tcount_babbushMeasModNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    EGate.tcount (babbushMeasModNLookupAddStep w bits N T q_start flagPos)
      = 14 * (2 ^ w - 1) + 56 * bits := by
  unfold babbushMeasModNLookupAddStep
  simp only [EGate.tcount, tcount_mzList, tcount_babbushReadInPlace,
      tcount_cuccaro_n_bit_adder_full, tcount_modNReduceFlag, tcount_regCompareXor]
  omega

/-- **The Babbush-measured step's Toffoli count: `2·(2^w − 1) + 8·bits`** — vs the flat
    measured step's `4·w·2^w + 8·bits`: the Babbush merged-AND read replaces the flat
    `2·w·2^w` per read with `2^w − 1`. -/
theorem toffoli_babbushMeasModNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    EGate.toffoli (babbushMeasModNLookupAddStep w bits N T q_start flagPos)
      = 2 * (2 ^ w - 1) + 8 * bits := by
  unfold EGate.toffoli
  rw [tcount_babbushMeasModNLookupAddStep,
      show 14 * (2 ^ w - 1) + 56 * bits = (2 * (2 ^ w - 1) + 8 * bits) * 7 by omega,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **The Gidney temporary-AND T-count of the Babbush-measured step.**  Under Gidney's
    4-T logical AND (`GidneyTCount.gidneyTCount`), the step costs
    `4·(2·(2^w − 1) + 8·bits) = 8·(2^w − 1) + 32·bits` T — the two lookups contributing
    `2·(4L − 4)`, the paper's `4L − 4` per read. -/
theorem gidneyTCount_babbushMeasModNLookupAddStep (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos : Nat) :
    FormalRV.Shor.GidneyTCount.gidneyTCount (babbushMeasModNLookupAddStep w bits N T q_start flagPos)
      = 4 * (2 * (2 ^ w - 1) + 8 * bits) := by
  unfold FormalRV.Shor.GidneyTCount.gidneyTCount
  rw [toffoli_babbushMeasModNLookupAddStep]
  rfl

/-! ## §3. VALUE BY TRANSPORT — the Babbush-measured step = the unitary step.

`babbushMeasModNLookupAddStep` and `MeasuredWindowedModN.measModNLookupAddStep` differ ONLY
at the two LOAD reads (Babbush vs flat); the two `mz`-uncomputes are identical.  On a clean
entry the two LOAD reads agree (`babbushRead_eq_lookupRead`, since both `_selects` lemmas have
the same conclusion).  The second bridge needs the post-reduce state's lookup registers clean,
which we derive exactly as the flat-measured proof does.  Equality with the flat-measured step
then inherits `measModNLookupAddStep_applyNat_eq` — i.e. the unitary `modNLookupAddStep`. -/
theorem babbushMeasModNLookupAddStep_applyNat_eq
    (w bits N : Nat) (T : Nat → Nat) (q_start flagPos v s : Nat) (f : Nat → Bool)
    (hw : 0 < w) (hv : v < 2 ^ w) (hq : 2 * w < q_start)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hs : s < N) (hTv : T v < N)
    (hflag_hi : q_start + 2 * bits + 1 ≤ flagPos)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (h_clean : ∀ j, j < bits → f (addendIdx q_start j) = false)
    (h_acc : ∀ i, i < bits → f (q_start + 2 * i + 1) = s.testBit i)
    (h_cin : f q_start = false)
    (h_flag : f flagPos = false) :
    EGate.applyNat (babbushMeasModNLookupAddStep w bits N T q_start flagPos) f
      = Gate.applyNat (modNLookupAddStep w bits N T q_start flagPos) f := by
  have hph : ∀ k, k < bits → 2 * w < addendIdx q_start k := fun k _ => by unfold addendIdx; omega
  have hpi : ∀ k l, k < bits → l < bits → addendIdx q_start k = addendIdx q_start l → k = l :=
    fun k l _ _ h => by unfold addendIdx at h; omega
  have notin : ∀ p : Nat, (∀ k, k < bits → p ≠ addendIdx q_start k) →
      p ∉ (List.range bits).map (addendIdx q_start) := by
    intro p hp hmem
    obtain ⟨k, hkr, hpk⟩ := List.mem_map.mp hmem
    exact hp k (List.mem_range.mp hkr) hpk.symm
  -- LOAD1 bridge
  have hRE1 : EGate.applyNat (babbushReadInPlace w (addendIdx q_start) bits T) f
      = Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) f :=
    babbushRead_eq_lookupRead w bits T (addendIdx q_start) f v hw hv hctrl haddr hand hph hpi
  -- g1 = flat read1 f
  set g1 := Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) f with hg1
  obtain ⟨hs1v, hs1f⟩ :=
    lookupReadAt_selects w bits T (addendIdx q_start) f v hw hv hctrl haddr hand hph hpi
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1, hs1f _ (fun k _ => by unfold ulookup_ctrl_idx addendIdx; omega)]; exact hctrl
  have hg1_addr : ∀ i, i < w → g1 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg1, hs1f _ (fun k _ => by unfold ulookup_address_idx addendIdx; omega)]; exact haddr i hi
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg1, hs1f _ (fun k _ => by unfold ulookup_and_idx addendIdx; omega)]; exact hand i hi
  have hg1_addend : ∀ j, j < bits → g1 (addendIdx q_start j) = (T v).testBit j := fun j hj => by
    rw [hg1, hs1v j hj, h_clean j hj, Bool.false_xor]
  have hg1_acc : ∀ i, i < bits → g1 (q_start + 2 * i + 1) = s.testBit i := fun i hi => by
    rw [hg1, hs1f _ (fun k _ => by unfold addendIdx; omega)]; exact h_acc i hi
  have hg1_cin : g1 q_start = false := by
    rw [hg1, hs1f _ (fun k _ => by unfold addendIdx; omega)]; exact h_cin
  have hg1_flag : g1 flagPos = false := by
    rw [hg1, hs1f _ (fun k _ => by unfold addendIdx; omega)]; exact h_flag
  -- g2 = add g1
  set g2 := Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g1 with hg2
  have hg2_ctrl : g2 ulookup_ctrl_idx = true := by
    rw [hg2, cuccaro_n_bit_adder_full_frame_below bits q_start g1 _ (by unfold ulookup_ctrl_idx; omega)]
    exact hg1_ctrl
  have hg2_addr : ∀ i, i < w → g2 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg2, cuccaro_n_bit_adder_full_frame_below bits q_start g1 _ (by unfold ulookup_address_idx; omega)]
    exact hg1_addr i hi
  have hg2_and : ∀ i, i < w → g2 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg2, cuccaro_n_bit_adder_full_frame_below bits q_start g1 _ (by unfold ulookup_and_idx; omega)]
    exact hg1_and i hi
  have hg2_addend : ∀ j, j < bits → g2 (addendIdx q_start j) = (T v).testBit j := fun j hj => by
    rw [hg2]
    show Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g1 (q_start + 2 * j + 2) = _
    rw [(cuccaro_n_bit_adder_full_correct bits q_start g1).2.2 j hj]; exact hg1_addend j hj
  have hg2_acc : ∀ i, i < bits → g2 (q_start + 2 * i + 1) = (s + T v).testBit i := fun i hi => by
    rw [hg2]; exact cuccaro_adder_sum_bits_general bits q_start s (T v) g1 hg1_cin hg1_acc hg1_addend i hi
  have hg2_cin : g2 q_start = false := by
    rw [hg2, (cuccaro_n_bit_adder_full_correct bits q_start g1).1]; exact hg1_cin
  have hg2_flag : g2 flagPos = false := by
    rw [hg2, cuccaro_n_bit_adder_full_frame_above bits q_start g1 _ hflag_hi]; exact hg1_flag
  -- g2m = mzList g2 (the first measured uncompute)
  set g2m := EGate.applyNat (mzList ((List.range bits).map (addendIdx q_start))) g2 with hg2m
  have hg2m_ctrl : g2m ulookup_ctrl_idx = true := by
    rw [hg2m, applyNat_mzList_preserves _ g2 (notin _ (fun k _ => by unfold ulookup_ctrl_idx addendIdx; omega))]
    exact hg2_ctrl
  have hg2m_addr : ∀ i, i < w → g2m (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg2m, applyNat_mzList_preserves _ g2 (notin _ (fun k _ => by unfold ulookup_address_idx addendIdx; omega))]
    exact hg2_addr i hi
  have hg2m_and : ∀ i, i < w → g2m (ulookup_and_idx i) = false := fun i hi => by
    rw [hg2m, applyNat_mzList_preserves _ g2 (notin _ (fun k _ => by unfold ulookup_and_idx addendIdx; omega))]
    exact hg2_and i hi
  have hg2m_addend : ∀ j, j < bits → g2m (addendIdx q_start j) = false := fun j hj => by
    rw [hg2m, applyNat_mzList_clears _ g2 (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)]
  have hg2m_acc : ∀ i, i < bits → g2m (q_start + 2 * i + 1) = (s + T v).testBit i := fun i hi => by
    rw [hg2m, applyNat_mzList_preserves _ g2 (notin _ (fun k _ => by unfold addendIdx; omega))]
    exact hg2_acc i hi
  have hg2m_cin : g2m q_start = false := by
    rw [hg2m, applyNat_mzList_preserves _ g2 (notin _ (fun k _ => by unfold addendIdx; omega))]
    exact hg2_cin
  have hg2m_flag : g2m flagPos = false := by
    rw [hg2m, applyNat_mzList_preserves _ g2 (notin _ (fun k _ => by unfold addendIdx; omega))]
    exact hg2_flag
  -- g4 = reduce g2m
  set g4 := Gate.applyNat (modNReduceFlag bits q_start N flagPos) g2m with hg4
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos := Or.inr hflag_hi
  obtain ⟨_, _, _, _, hred_frame⟩ :=
    modNReduceFlag_state_general bits q_start N flagPos (s + T v) g2m hN_pos hN2
      (by omega) hflag_out hg2m_cin hg2m_flag hg2m_acc hg2m_addend
  have hg4_ctrl : g4 ulookup_ctrl_idx = true := by
    rw [hg4, hred_frame ulookup_ctrl_idx (by unfold ulookup_ctrl_idx; omega)
      (Or.inl (by unfold ulookup_ctrl_idx; omega))]
    exact hg2m_ctrl
  have hg4_addr : ∀ i, i < w → g4 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg4, hred_frame (ulookup_address_idx i) (by unfold ulookup_address_idx; omega)
      (Or.inl (by unfold ulookup_address_idx; omega))]
    exact hg2m_addr i hi
  have hg4_and : ∀ i, i < w → g4 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg4, hred_frame (ulookup_and_idx i) (by unfold ulookup_and_idx; omega)
      (Or.inl (by unfold ulookup_and_idx; omega))]
    exact hg2m_and i hi
  -- LOAD2 bridge (on the post-reduce state g4)
  have hRE2 : EGate.applyNat (babbushReadInPlace w (addendIdx q_start) bits T) g4
      = Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) g4 :=
    babbushRead_eq_lookupRead w bits T (addendIdx q_start) g4 v hw hv hg4_ctrl hg4_addr hg4_and hph hpi
  -- the two measured steps agree, then chain to the unitary step
  have key : EGate.applyNat (babbushMeasModNLookupAddStep w bits N T q_start flagPos) f
      = EGate.applyNat (measModNLookupAddStep w bits N T q_start flagPos) f := by
    unfold babbushMeasModNLookupAddStep measModNLookupAddStep
    simp only [EGate.applyNat]
    rw [hRE1, ← hg1, ← hg2, ← hg2m, ← hg4, hRE2]
  rw [key]
  exact measModNLookupAddStep_applyNat_eq w bits N T q_start flagPos v s f hw hv hq hN_pos hN2
    hs hTv hflag_hi hctrl haddr hand h_clean h_acc h_cin h_flag

/-! ## §4. Compose into the Babbush-measured in-place multiplier (value + count). -/

/-- T-count of a left-fold of constant-T-count steps (local copy of the private helper). -/
private theorem tcount_foldl_egate_step (step : Nat → EGate) (c : Nat)
    (hc : ∀ j, EGate.tcount (step j) = c) :
    ∀ n, EGate.tcount
        ((List.range n).foldl (fun g j => EGate.seq g (step j)) (EGate.base Gate.I)) = n * c := by
  intro n
  induction n with
  | zero => simp [EGate.tcount, Gate.tcount]
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hsplit : EGate.tcount
          (EGate.seq ((List.range k).foldl (fun g j => EGate.seq g (step j)) (EGate.base Gate.I))
            (step k))
          = EGate.tcount ((List.range k).foldl (fun g j => EGate.seq g (step j)) (EGate.base Gate.I))
            + EGate.tcount (step k) := rfl
      rw [hsplit, ih, hc k]; ring

/-- The Babbush-measured window step (copy in · Babbush-measured lookup-add · copy out). -/
def babbushMeasWindowedModNStep (w bits a N q_start yBase flagPos j : Nat) : EGate :=
  EGate.seq (EGate.base (copyWindow w yBase j))
    (EGate.seq (babbushMeasModNLookupAddStep w bits N (WindowedArith.tableValue a N w j) q_start flagPos)
      (EGate.base (copyWindow w yBase j)))

theorem tcount_babbushMeasWindowedModNStep (w bits a N q_start yBase flagPos j : Nat) :
    EGate.tcount (babbushMeasWindowedModNStep w bits a N q_start yBase flagPos j)
      = 14 * (2 ^ w - 1) + 56 * bits := by
  unfold babbushMeasWindowedModNStep
  simp only [EGate.tcount, tcount_copyWindow, tcount_babbushMeasModNLookupAddStep]
  omega

/-- The Babbush-measured per-window mod-N multiplier (a fold of Babbush-measured steps). -/
def babbushMeasWindowedModNMul (w bits a N q_start yBase flagPos numWin : Nat) : EGate :=
  (List.range numWin).foldl
    (fun g j => EGate.seq g (babbushMeasWindowedModNStep w bits a N q_start yBase flagPos j))
    (EGate.base Gate.I)

/-- The full Babbush-measured per-window mod-N multiplier circuit (standard layout). -/
def babbushMeasWindowedModNMulCircuit (w bits a N numWin : Nat) : EGate :=
  babbushMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
    (1 + 2 * w + (2 * bits + 1) + numWin * w) numWin

theorem tcount_babbushMeasWindowedModNMulCircuit (w bits a N numWin : Nat) :
    EGate.tcount (babbushMeasWindowedModNMulCircuit w bits a N numWin)
      = numWin * (14 * (2 ^ w - 1) + 56 * bits) := by
  unfold babbushMeasWindowedModNMulCircuit babbushMeasWindowedModNMul
  exact tcount_foldl_egate_step
    (fun j => babbushMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
      (1 + 2 * w + (2 * bits + 1) + numWin * w) j)
    (14 * (2 ^ w - 1) + 56 * bits)
    (fun j => tcount_babbushMeasWindowedModNStep w bits a N _ _ _ j) numWin

/-- **★ THE BABBUSH-MEASURED IN-PLACE WINDOWED MULTIPLIER ★** — `y ← (a·y) mod N` with both
    passes' lookups done by the Babbush merged-AND read (`2^w − 1` Toffolis) and measurement
    uncompute.  The count-optimal object the Babbush+Gidney lookup is contained in. -/
def babbushMeasWindowedModNMulInPlace (w bits a ainv N numWin : Nat) : EGate :=
  EGate.seq (EGate.seq (babbushMeasWindowedModNMulCircuit w bits a N numWin)
      (EGate.base (accYSwap cuccaroAdder w bits)))
    (babbushMeasWindowedModNMulCircuit w bits (N - ainv) N numWin)

theorem tcount_babbushMeasWindowedModNMulInPlace (w bits a ainv N numWin : Nat) :
    EGate.tcount (babbushMeasWindowedModNMulInPlace w bits a ainv N numWin)
      = 2 * (numWin * (14 * (2 ^ w - 1) + 56 * bits)) := by
  unfold babbushMeasWindowedModNMulInPlace
  simp only [EGate.tcount]
  rw [tcount_babbushMeasWindowedModNMulCircuit, tcount_babbushMeasWindowedModNMulCircuit,
      tcount_accYSwap]
  ring

/-- **Toffoli count of the Babbush-measured in-place multiplier: `2·numWin·(2·(2^w − 1) + 8·bits)`** —
    vs the flat measured `2·numWin·(4·w·2^w + 8·bits)`: the Babbush read replaces `2·w·2^w` per
    read with `2^w − 1`. -/
theorem toffoli_babbushMeasWindowedModNMulInPlace (w bits a ainv N numWin : Nat) :
    EGate.toffoli (babbushMeasWindowedModNMulInPlace w bits a ainv N numWin)
      = 2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits)) := by
  unfold EGate.toffoli
  rw [tcount_babbushMeasWindowedModNMulInPlace,
      show 2 * (numWin * (14 * (2 ^ w - 1) + 56 * bits))
          = (2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-! ### Value transport through the fold and the two passes. -/

theorem babbushMeasWindowedModNStep_eq (w bits a N numWin y j s : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hj : j < numWin) (hs : s < N) (g : Nat → Bool)
    (hg : ModNStepInv w bits numWin y s g) :
    EGate.applyNat (babbushMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) g
      = Gate.applyNat (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) g := by
  obtain ⟨hF, hD, hC, hG, hV⟩ := hg
  have hjw_le : j * w + w ≤ numWin * w := by
    have h1 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * w = j * w + w := by ring
    omega
  have hg_ctrl : g ulookup_ctrl_idx = true := by
    rw [hF ulookup_ctrl_idx (by unfold inBlock ulookup_ctrl_idx; omega)
          (by unfold ulookup_ctrl_idx; omega)]
    exact mulInputOf_ctrl cuccaroAdder w bits numWin y
  have hg_addr : ∀ i, i < w → g (ulookup_address_idx i) = false := fun i hi => by
    rw [hF _ (by unfold inBlock ulookup_address_idx; omega) (by unfold ulookup_address_idx; omega)]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_address_idx; omega) (by unfold ulookup_address_idx; omega)
  have hg_and : ∀ i, i < w → g (ulookup_and_idx i) = false := fun i hi => by
    rw [hF _ (by unfold inBlock ulookup_and_idx; omega) (by unfold ulookup_and_idx; omega)]
    exact mulInputOf_low cuccaroAdder w bits numWin y _
      (by unfold ulookup_ctrl_idx ulookup_and_idx; omega) (by unfold ulookup_and_idx; omega)
  have hg_y : ∀ i, i < w →
      g ((1 + 2 * w + (2 * bits + 1)) + j * w + i)
        = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
            ((1 + 2 * w + (2 * bits + 1)) + j * w + i) := fun i hi => by
    rw [hF _ (by unfold inBlock; omega) (by omega)]
    exact mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y _ (by unfold ulookup_ctrl_idx; omega)
  have hctrl_addr : ∀ i k, i < w → k < w →
      (1 + 2 * w + (2 * bits + 1)) + j * w + i ≠ ulookup_address_idx k :=
    ctrl_ne_addr_of_le_yBase w (1 + 2 * w + (2 * bits + 1)) j (by omega)
  set cw := Gate.applyNat (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) g with hcw
  have hcw_frame : ∀ p, (∀ i, i < w → p ≠ ulookup_address_idx i) → cw p = g p :=
    fun p hp => copyWindow_frame w (1 + 2 * w + (2 * bits + 1)) j g p hp
  have hcw_addr : ∀ i, i < w → cw (ulookup_address_idx i) = (WindowedArith.window w y j).testBit i :=
    fun i hi => copyWindow_loads_window w (1 + 2 * w + (2 * bits + 1)) numWin y j g
      hctrl_addr hg_addr hg_y hj i hi
  have hcw_ctrl : cw ulookup_ctrl_idx = true := by
    rw [hcw_frame _ (fun i hi => by unfold ulookup_ctrl_idx ulookup_address_idx; omega)]; exact hg_ctrl
  have hcw_and : ∀ i, i < w → cw (ulookup_and_idx i) = false := fun i hi => by
    rw [hcw_frame _ (fun k hk => by unfold ulookup_and_idx ulookup_address_idx; omega)]; exact hg_and i hi
  have hcw_addend : ∀ k, k < bits → cw (addendIdx (1 + 2 * w) k) = false := fun k hk => by
    rw [hcw_frame _ (fun i hi => by unfold addendIdx ulookup_address_idx; omega)]; exact hD k hk
  have hcw_acc : ∀ i, i < bits → cw (1 + 2 * w + 2 * i + 1) = s.testBit i := fun i hi => by
    rw [hcw_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hV i hi
  have hcw_cin : cw (1 + 2 * w) = false := by
    rw [hcw_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hC
  have hcw_flag : cw (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hcw_frame _ (fun k hk => by unfold ulookup_address_idx; omega)]; exact hG
  have hinner := babbushMeasModNLookupAddStep_applyNat_eq w bits N (WindowedArith.tableValue a N w j)
    (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w) (WindowedArith.window w y j) s cw
    hw (WindowedArith.window_lt w y j) (by omega) hN_pos hN2 hs
    (by unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN_pos) (by omega)
    hcw_ctrl hcw_addr hcw_and hcw_addend hcw_acc hcw_cin hcw_flag
  unfold babbushMeasWindowedModNStep windowedModNStep
  simp only [EGate.applyNat, Gate.applyNat_seq]
  rw [← hcw, hinner]

theorem babbushMeasWindowedModNMul_eq_gen (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (s0 : Nat) (g0 : Nat → Bool) (hs0 : s0 < N) (hg0 : ModNStepInv w bits numWin y s0 g0) :
    ∀ n, n ≤ numWin →
      EGate.applyNat (babbushMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) g0
        = Gate.applyNat (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) g0 := by
  intro n
  induction n with
  | zero => intro _; simp [babbushMeasWindowedModNMul, windowedModNMul, EGate.applyNat, Gate.applyNat_I]
  | succ n ih =>
    intro hn
    have hsplit_m : babbushMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = EGate.seq (babbushMeasWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (babbushMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold babbushMeasWindowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hsplit_u : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit_m, hsplit_u]
    simp only [EGate.applyNat, Gate.applyNat_seq]
    rw [ih (by omega)]
    obtain ⟨s, hs, hinv⟩ := unitFold_inv_gen w bits a N numWin y hw hN_pos hN2 s0 g0 hs0 hg0 n (by omega)
    exact babbushMeasWindowedModNStep_eq w bits a N numWin y n s hw hN_pos hN2 (by omega) hs _ hinv

theorem babbushMeasWindowedModNMulCircuit_eq_gen (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (s0 : Nat) (g0 : Nat → Bool) (hs0 : s0 < N) (hg0 : ModNStepInv w bits numWin y s0 g0) :
    EGate.applyNat (babbushMeasWindowedModNMulCircuit w bits a N numWin) g0
      = Gate.applyNat (windowedModNMulCircuit w bits a N numWin) g0 := by
  unfold babbushMeasWindowedModNMulCircuit windowedModNMulCircuit
  exact babbushMeasWindowedModNMul_eq_gen w bits a N numWin y hw hN_pos hN2 s0 g0 hs0 hg0 numWin
    (le_refl numWin)

theorem babbushMeasWindowedModNMulInPlace_eq (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    EGate.applyNat (babbushMeasWindowedModNMulInPlace w bits a ainv N numWin) f
      = Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) f := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have hpow : (2 : Nat) ^ (w * numWin) = 2 ^ bits := by rw [Nat.mul_comm w numWin, hbits]
  have hy1 : y < 2 ^ (w * numWin) := by rw [hpow]; exact Nat.lt_of_lt_of_le hy hN_le
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  have hy_bit : ∀ (v i : Nat), i < numWin * w →
      mulInputOf cuccaroAdder w bits numWin v (1 + 2 * w + (2 * bits + 1) + i) = v.testBit i := by
    intro v i hi
    rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v _ (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_at _ _ _ i hi
  unfold babbushMeasWindowedModNMulInPlace windowedModNMulInPlace
  simp only [EGate.applyNat, Gate.applyNat_seq]
  rw [babbushMeasWindowedModNMulCircuit_eq_gen w bits a N numWin y hw hN_pos hN2 0 f hN_pos hf.toStepInv]
  set s1 : Nat → Bool := Gate.applyNat (windowedModNMulCircuit w bits a N numWin) f with hs1def
  set s2 : Nat → Bool := Gate.applyNat (accYSwap cuccaroAdder w bits) s1 with hs2def
  have h1 := modNStepInv_full_pass w bits a N numWin y 0 hw hN_pos hN2 hN_pos hy1 f hf.toStepInv
  rw [Nat.zero_add] at h1
  obtain ⟨h1F, h1D, h1C, h1G, h1V⟩ := h1
  rw [← hs1def] at h1F h1D h1C h1G h1V
  have h1y : ∀ i, i < bits → s1 (1 + 2 * w + (2 * bits + 1) + i) = y.testBit i := by
    intro i hi
    rw [h1F _ (by unfold inBlock; omega) (by omega)]
    exact hy_bit y i (by omega)
  obtain ⟨hsw_acc, hsw_y, hsw_fr⟩ := accYSwap_apply cuccaroAdder w bits s1
    (fun i j _ _ h => cuccaroAdder_augendIdx_inj (1 + 2 * w) i j h)
  rw [← hs2def] at hsw_acc hsw_y hsw_fr
  have hsw_acc' : ∀ i, i < bits →
      s2 (1 + 2 * w + 2 * i + 1) = s1 (1 + 2 * w + (2 * bits + 1) + i) := fun i hi => hsw_acc i hi
  have hsw_y' : ∀ i, i < bits →
      s2 (1 + 2 * w + (2 * bits + 1) + i) = s1 (1 + 2 * w + 2 * i + 1) := fun i hi => hsw_y i hi
  have hsw_fr' : ∀ p, (∀ i, i < bits →
      p ≠ 1 + 2 * w + 2 * i + 1 ∧ p ≠ 1 + 2 * w + (2 * bits + 1) + i) → s2 p = s1 p :=
    fun p hp => hsw_fr p (fun i hi => hp i hi)
  have h2F : ∀ p, ¬ inBlock (1 + 2 * w) (2 * bits + 1) p →
      p ≠ 1 + 2 * w + (2 * bits + 1) + numWin * w →
      s2 p = mulInputOf cuccaroAdder w bits numWin (a * y % N) p := by
    intro p hpb hpf
    by_cases hpy : ∃ i, i < bits ∧ p = 1 + 2 * w + (2 * bits + 1) + i
    · obtain ⟨i, hi, rfl⟩ := hpy
      rw [hsw_y' i hi, h1V i hi, hy_bit (a * y % N) i (by omega)]
    · push Not at hpy
      have hp_out : p < 1 + 2 * w ∨ 1 + 2 * w + 2 * bits + 1 ≤ p := by unfold inBlock at hpb; omega
      rw [hsw_fr' p (fun i hi => ⟨by omega, hpy i hi⟩), h1F p hpb hpf]
      by_cases hpc : p = ulookup_ctrl_idx
      · rw [hpc, mulInputOf_ctrl, mulInputOf_ctrl]
      · rcases hp_out with hlow | hhigh
        · rw [mulInputOf_low cuccaroAdder w bits numWin y p hpc (by omega),
              mulInputOf_low cuccaroAdder w bits numWin _ p hpc (by omega)]
        · have hphigh : 1 + 2 * w + (2 * bits + 1) + bits ≤ p := by
            by_contra hcon
            exact hpy (p - (1 + 2 * w + (2 * bits + 1))) (by omega) (by omega)
          rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y p hpc,
              mulInputOf_eq_encodeReg cuccaroAdder w bits numWin (a * y % N) p hpc,
              encodeReg_high (1 + 2 * w + cuccaroAdder.span bits) (numWin * w) y p (by omega),
              encodeReg_high (1 + 2 * w + cuccaroAdder.span bits) (numWin * w) (a * y % N) p (by omega)]
  have h2D : ∀ i, i < bits → s2 (1 + 2 * w + 2 * i + 2) = false := by
    intro i hi; rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]; exact h1D i hi
  have h2C : s2 (1 + 2 * w) = false := by
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]; exact h1C
  have h2G : s2 (1 + 2 * w + (2 * bits + 1) + numWin * w) = false := by
    rw [hsw_fr' _ (fun k hk => ⟨by omega, by omega⟩)]; exact h1G
  have h2V : ∀ i, i < bits → s2 (1 + 2 * w + 2 * i + 1) = y.testBit i := by
    intro i hi; rw [hsw_acc' i hi]; exact h1y i hi
  rw [babbushMeasWindowedModNMulCircuit_eq_gen w bits (N - ainv) N numWin (a * y % N) hw hN_pos hN2
    y s2 hy ⟨h2F, h2D, h2C, h2G, h2V⟩]

theorem babbushMeasWindowedModNMulInPlace_correct (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (a * y % N)
      (EGate.applyNat (babbushMeasWindowedModNMulInPlace w bits a ainv N numWin) f) := by
  rw [babbushMeasWindowedModNMulInPlace_eq w bits a ainv N numWin y hw hbits hN_pos hN2 hy hainv hinv f hf]
  exact windowedModNMulInPlace_correct w bits a ainv N numWin y hw hbits hN_pos hN2 hy hainv hinv f hf

/-! ### Well-typedness of the Babbush-measured circuits. -/

theorem babbushReadInPlace_wellTypedAt_addend (w bits N : Nat) (T : Nat → Nat)
    (q_start dim : Nat) (hw : 0 < w) (hq : 2 * w + 1 ≤ q_start)
    (h_ws : q_start + 2 * bits + 1 ≤ dim) :
    EGate.WellTypedAt dim (babbushReadInPlace w (addendIdx q_start) bits T) := by
  apply babbushReadInPlace_wellTypedAt w bits T (addendIdx q_start) dim hw (by omega)
  intro j hj; unfold addendIdx; exact ⟨by omega, by omega⟩

theorem babbushMeasModNLookupAddStep_wellTypedAt (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos dim : Nat) (hw : 0 < w)
    (hq : 2 * w + 1 ≤ q_start) (h_ws : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim) (h_ne : flagPos ≠ q_start + 2 * bits)
    (h_add : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    EGate.WellTypedAt dim (babbushMeasModNLookupAddStep w bits N T q_start flagPos) := by
  have h_read := babbushReadInPlace_wellTypedAt_addend w bits N T q_start dim hw hq h_ws
  have h_mz : EGate.WellTypedAt dim (mzList ((List.range bits).map (addendIdx q_start))) := by
    apply mzList_wellTypedAt dim (by omega)
    intro q hq2
    simp only [List.mem_map, List.mem_range] at hq2
    obtain ⟨j, hj, rfl⟩ := hq2
    unfold addendIdx; omega
  exact ⟨h_read, cuccaro_n_bit_adder_full_wellTyped bits q_start dim h_ws, h_mz,
    modNReduceFlag_wellTyped bits q_start N flagPos dim h_ws h_flag h_ne h_add,
    h_read, regCompareXor_wellTyped bits q_start flagPos dim h_ws h_flag h_ne, h_mz⟩

theorem babbushMeasWindowedModNStep_wellTypedAt (w bits a N numWin j dim : Nat)
    (hw : 0 < w) (hj : j < numWin)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    EGate.WellTypedAt dim (babbushMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
      (1 + 2 * w + (2 * bits + 1) + numWin * w) j) := by
  have hjw' : j * w + w ≤ numWin * w := by
    calc j * w + w = (j + 1) * w := by ring
    _ ≤ numWin * w := Nat.mul_le_mul_right w hj
  have hcw : Gate.WellTyped dim (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) := by
    apply copyWindow_wellTyped w _ j dim (by omega)
    · intro i hi; omega
    · intro i hi; omega
  refine ⟨hcw, ?_, hcw⟩
  apply babbushMeasModNLookupAddStep_wellTypedAt w bits N _ (1 + 2 * w)
    (1 + 2 * w + (2 * bits + 1) + numWin * w) dim hw (by omega) (by omega) (by omega) (by omega)
  intro i hi; omega

theorem babbushMeasWindowedModNMulCircuit_wellTypedAt (w bits a N numWin dim : Nat) (hw : 0 < w)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    EGate.WellTypedAt dim (babbushMeasWindowedModNMulCircuit w bits a N numWin) := by
  unfold babbushMeasWindowedModNMulCircuit babbushMeasWindowedModNMul
  exact wellTypedAt_foldl_egate dim (by omega)
    (fun j => babbushMeasWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
      (1 + 2 * w + (2 * bits + 1) + numWin * w) j) numWin
    (fun j hj => babbushMeasWindowedModNStep_wellTypedAt w bits a N numWin j dim hw hj hdim)

theorem babbushMeasWindowedModNMulInPlace_wellTypedAt (w bits a ainv N numWin dim : Nat) (hw : 0 < w)
    (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    EGate.WellTypedAt dim (babbushMeasWindowedModNMulInPlace w bits a ainv N numWin) :=
  ⟨⟨babbushMeasWindowedModNMulCircuit_wellTypedAt w bits a N numWin dim hw hdim,
    accYSwap_cuccaro_wellTyped w bits dim (by omega)⟩,
   babbushMeasWindowedModNMulCircuit_wellTypedAt w bits (N - ainv) N numWin dim hw hdim⟩

/-! ### The Babbush-measured encode gate. -/

/-- The Babbush-measured encode-layout in-place mod-N multiplier (T-free adapters wrapping the
    Babbush-measured core). -/
def babbushMeasWindowedModNEncodeGate (w bits N numWin c cinv : Nat) : EGate :=
  EGate.seq (EGate.base (windowedEncodeIn w bits))
    (EGate.seq (babbushMeasWindowedModNMulInPlace w bits c cinv N numWin)
      (EGate.base (windowedEncodeOut w bits)))

theorem babbushMeasWindowedModNEncodeGate_apply (w bits numWin N c cinv x : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    EGate.applyNat (babbushMeasWindowedModNEncodeGate w bits N numWin c cinv)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) (c * x % N) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  unfold babbushMeasWindowedModNEncodeGate
  simp only [EGate.applyNat]
  rw [windowedEncodeIn_apply w bits numWin x hbits hb1 (Nat.lt_of_lt_of_le hx hN_le)]
  have hmid := babbushMeasWindowedModNMulInPlace_correct w bits c cinv N numWin x hw hbits hN_pos hN2
    hx hcinv hinv _ (modNMulReady_mulInputOf w bits numWin x)
  rw [modNMulReady_eq w bits numWin _ _ hmid]
  exact windowedEncodeOut_apply w bits numWin (c * x % N) hbits hb1
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN_le)

theorem babbushMeasWindowedModNEncodeGate_wellTypedAt (w bits N numWin c cinv : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    EGate.WellTypedAt (bits + (2 * w + 2 * bits + 3))
      (babbushMeasWindowedModNEncodeGate w bits N numWin c cinv) := by
  have hswap : Gate.WellTyped (bits + (2 * w + 2 * bits + 3))
      (swapCascade (fun i => bits - 1 - i) (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits) := by
    apply swapCascade_wellTyped _ _ bits _ (by omega)
    intro i hi; refine ⟨by omega, by omega, by omega⟩
  have hX : Gate.WellTyped (bits + (2 * w + 2 * bits + 3)) (Gate.X ulookup_ctrl_idx) := by
    show ulookup_ctrl_idx < bits + (2 * w + 2 * bits + 3); unfold ulookup_ctrl_idx; omega
  refine ⟨⟨hswap, hX⟩,
    ⟨babbushMeasWindowedModNMulInPlace_wellTypedAt w bits c cinv N numWin
      (bits + (2 * w + 2 * bits + 3)) hw hbits (by omega), ?_⟩⟩
  exact ⟨hX, hswap⟩

/-- Toffoli count of the Babbush-measured encode gate: adapters are T-free, so it equals the
    in-place multiplier's `2·numWin·(2·(2^w − 1) + 8·bits)`. -/
theorem toffoli_babbushMeasWindowedModNEncodeGate (w bits N numWin c cinv : Nat) :
    EGate.toffoli (babbushMeasWindowedModNEncodeGate w bits N numWin c cinv)
      = 2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits)) := by
  have htc : EGate.tcount (babbushMeasWindowedModNEncodeGate w bits N numWin c cinv)
      = 2 * (numWin * (14 * (2 ^ w - 1) + 56 * bits)) := by
    unfold babbushMeasWindowedModNEncodeGate
    have hin : Gate.tcount (windowedEncodeIn w bits) = 0 := by
      simp [windowedEncodeIn, Gate.tcount, tcount_swapCascade]
    have hout : Gate.tcount (windowedEncodeOut w bits) = 0 := by
      simp [windowedEncodeOut, Gate.tcount, tcount_swapCascade]
    simp only [EGate.tcount, hin, hout, tcount_babbushMeasWindowedModNMulInPlace,
      Nat.add_zero, Nat.zero_add]
  unfold EGate.toffoli
  rw [htc, show 2 * (numWin * (14 * (2 ^ w - 1) + 56 * bits))
          = (2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ The Babbush+Gidney lookup hits the paper's `4L − 4` per read, on the verified object. ★**
    The Gidney temporary-AND T-count of the Babbush-measured encode gate is
    `4·(2·numWin·(2·(2^w − 1) + 8·bits))`; the lookup contribution is `2·numWin·2·(4·(2^w − 1))`
    — `4 reads × numWin × (4L − 4)`, exactly arXiv:1805.03662 §III.A/§III.C per QROM read. -/
theorem gidneyTCount_babbushMeasWindowedModNEncodeGate (w bits N numWin c cinv : Nat) :
    FormalRV.Shor.GidneyTCount.gidneyTCount (babbushMeasWindowedModNEncodeGate w bits N numWin c cinv)
      = 4 * (2 * (numWin * (2 * (2 ^ w - 1) + 8 * bits))) := by
  unfold FormalRV.Shor.GidneyTCount.gidneyTCount
  rw [toffoli_babbushMeasWindowedModNEncodeGate]
  rfl

end FormalRV.Shor.MeasuredBabbushWindowedModN
