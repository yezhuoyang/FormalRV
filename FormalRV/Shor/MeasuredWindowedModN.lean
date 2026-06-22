/-
  FormalRV.Shor.MeasuredWindowedModN — the MEASURED faithful mod-N windowed multiplier.

  ## Goal (John 2026-06-22): contain the measured-uncompute IN the final syntactic object
  that the resource proof is about — not a unitary stand-in (too expensive) nor the
  count-skeleton `modExpAt` (does not thread).

  The faithful UNITARY in-place multiplier `WindowedCircuit.windowedModNMulInPlace` clears each
  QROM lookup by a SECOND read (`lookupReadAt` is its own inverse: re-reading XOR-clears the
  addend word).  Gidney's measurement-based uncomputation instead MEASURES the word register
  (cost 0 Toffoli) — the `EGate.mz` of `Shor.MeasUncompute`, whose density model is the genuine
  measure-and-reset channel (`EGateToUnitaryBridge.measReset`) and whose superposition-level
  perfection on the computed subspace is proven (`MeasuredLookupUncompute.measWordUncompute_perfect`).

  This file builds the MEASURED step `measModNLookupAddStep` (the unitary
  `WindowedCircuit.modNLookupAddStep` with its two uncompute reads replaced by `mz`-clears of the
  addend word) and proves its EXACT count: `28·w·2^w + 56·bits` T (Toffoli `4·w·2^w + 8·bits`),
  versus the unitary step's `56·w·2^w + 56·bits` (`8·w·2^w + 8·bits` Toffoli) — the measured
  uncompute removes exactly the two uncompute reads (`2·(14·w·2^w)` = `2·(2·w·2^w)` Toffoli).

  NEXT (roadmap, this is step 1 of the build approved "through the measured Shor capstone"):
    2. compose `measModNLookupAddStep` through the window fold + two passes + `accYSwap` into
       `measWindowedModNMulInPlace` (an `EGate`), count it (= measured count);
    3. VALUE BY TRANSPORT — `EGate.applyNat (measured) f = Gate.applyNat (unitary) f` on the
       computed subspace (both clear the word to 0), inheriting `windowedModNMulInPlace_correct`;
    4. discharge `MeasuredEqualsReversibleOnEncoded` via `measWordUncompute_perfect` and land the
       one-object Shor-success ∧ measured-count capstone.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.MeasUncompute
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace
import FormalRV.Shor.WindowedModNShor
import FormalRV.Shor.EGateToUnitaryBridge

namespace FormalRV.Shor.MeasuredWindowedModN

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.WindowedCircuit

/-- **The MEASURED mod-N lookup-add step.**  The unitary `modNLookupAddStep` is
    `read · add · read⁻¹ · reduce · read · regCompare · read⁻¹` (the 2nd and 4th reads are
    the uncompute that XOR-clears the addend word).  Here those two uncompute reads become
    measurement-clears `mzList` of the addend word `{addendIdx q_start j : j < bits}` — cost-0,
    the measurement-uncompute saving.  The two LOAD reads and the mod-N reduction stay. -/
def measModNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) : EGate :=
  EGate.seq (EGate.base (lookupReadAt w (addendIdx q_start) bits T))
    (EGate.seq (EGate.base (cuccaro_n_bit_adder_full bits q_start))
      (EGate.seq (mzList ((List.range bits).map (addendIdx q_start)))
        (EGate.seq (EGate.base (modNReduceFlag bits q_start N flagPos))
          (EGate.seq (EGate.base (lookupReadAt w (addendIdx q_start) bits T))
            (EGate.seq (EGate.base (regCompareXor bits q_start flagPos))
              (mzList ((List.range bits).map (addendIdx q_start))))))))

/-- **The measured step's exact T-count: `28·w·2^w + 56·bits`** — two LOAD reads
    (`2·14·w·2^w`) + adder (`14·bits`) + mod-N reduce (`28·bits`) + register-compare (`14·bits`);
    the two uncompute reads are now `mz`-clears (Toffoli-free). -/
theorem tcount_measModNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    EGate.tcount (measModNLookupAddStep w bits N T q_start flagPos)
      = 28 * w * 2 ^ w + 56 * bits := by
  unfold measModNLookupAddStep
  simp only [EGate.tcount, tcount_mzList, tcount_lookupReadAt, tcount_cuccaro_n_bit_adder_full,
      tcount_modNReduceFlag, tcount_regCompareXor]
  ring

/-- Toffoli count of the measured step: `4·w·2^w + 8·bits`. -/
theorem toffoli_measModNLookupAddStep (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    EGate.toffoli (measModNLookupAddStep w bits N T q_start flagPos)
      = 4 * w * 2 ^ w + 8 * bits := by
  unfold EGate.toffoli
  rw [tcount_measModNLookupAddStep,
      show 28 * w * 2 ^ w + 56 * bits = (4 * w * 2 ^ w + 8 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **The measurement-uncompute saves exactly two table reads.**  The measured step's Toffoli
    count plus `4·w·2^w` (= two reads, `2·(2·w·2^w)`) equals the unitary `modNLookupAddStep`'s
    Toffoli count `8·w·2^w + 8·bits` — the saving is precisely the two uncompute reads, the
    mod-N reduction (compare + conditional subtract + register-compare) being untouched. -/
theorem measModNStep_saves_two_reads (w bits N : Nat) (T : Nat → Nat) (q_start flagPos : Nat) :
    EGate.toffoli (measModNLookupAddStep w bits N T q_start flagPos) + 4 * w * 2 ^ w
      = tcount (modNLookupAddStep w bits N T q_start flagPos) / 7 := by
  rw [toffoli_measModNLookupAddStep, tcount_modNLookupAddStep,
      show 56 * w * 2 ^ w + 56 * bits = (8 * w * 2 ^ w + 8 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  ring

/-! ## §2. Compose the measured step into the faithful measured in-place multiplier. -/

/-- T-count of a left-fold of measured window steps, each of constant T-count `c`: `n·c`. -/
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

/-- **The measured window step**: copy window `j` in, MEASURED mod-N lookup-add, copy window `j`
    out — `WindowedCircuit.windowedModNStep` with its mod-N lookup-add replaced by the measured
    `measModNLookupAddStep` (the two `copyWindow`s are T-free). -/
def measWindowedModNStep (w bits a N q_start yBase flagPos j : Nat) : EGate :=
  EGate.seq (EGate.base (copyWindow w yBase j))
    (EGate.seq (measModNLookupAddStep w bits N (WindowedArith.tableValue a N w j) q_start flagPos)
      (EGate.base (copyWindow w yBase j)))

theorem tcount_measWindowedModNStep (w bits a N q_start yBase flagPos j : Nat) :
    EGate.tcount (measWindowedModNStep w bits a N q_start yBase flagPos j)
      = 28 * w * 2 ^ w + 56 * bits := by
  unfold measWindowedModNStep measModNLookupAddStep
  simp only [EGate.tcount, tcount_mzList, tcount_copyWindow, tcount_lookupReadAt,
    tcount_cuccaro_n_bit_adder_full, tcount_modNReduceFlag, tcount_regCompareXor]
  ring

/-- **The measured per-window mod-N multiplier**: a fold of `numWin` measured window steps. -/
def measWindowedModNMul (w bits a N q_start yBase flagPos numWin : Nat) : EGate :=
  (List.range numWin).foldl
    (fun g j => EGate.seq g (measWindowedModNStep w bits a N q_start yBase flagPos j))
    (EGate.base Gate.I)

theorem tcount_measWindowedModNMul (w bits a N q_start yBase flagPos numWin : Nat) :
    EGate.tcount (measWindowedModNMul w bits a N q_start yBase flagPos numWin)
      = numWin * (28 * w * 2 ^ w + 56 * bits) := by
  unfold measWindowedModNMul
  exact tcount_foldl_egate_step
    (fun j => measWindowedModNStep w bits a N q_start yBase flagPos j)
    (28 * w * 2 ^ w + 56 * bits)
    (fun j => tcount_measWindowedModNStep w bits a N q_start yBase flagPos j) numWin

/-- **The full measured per-window mod-N multiplier circuit** at the standard layout
    (the measured analogue of `WindowedCircuit.windowedModNMulCircuit`). -/
def measWindowedModNMulCircuit (w bits a N numWin : Nat) : EGate :=
  measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
    (1 + 2 * w + (2 * bits + 1) + numWin * w) numWin

theorem tcount_measWindowedModNMulCircuit (w bits a N numWin : Nat) :
    EGate.tcount (measWindowedModNMulCircuit w bits a N numWin)
      = numWin * (28 * w * 2 ^ w + 56 * bits) := by
  unfold measWindowedModNMulCircuit
  exact tcount_measWindowedModNMul w bits a N _ _ _ numWin

/-- **★ THE FAITHFUL MEASURED IN-PLACE WINDOWED MULTIPLIER ★** — `y ← (a·y) mod N`, built as
    `WindowedCircuit.windowedModNMulInPlace` with both mod-N passes' lookup-uncomputes done by
    MEASUREMENT (`measModNLookupAddStep`): two measured passes around the T-free `accYSwap`.
    This is the count-bearing object the measured-uncompute is CONTAINED in. -/
def measWindowedModNMulInPlace (w bits a ainv N numWin : Nat) : EGate :=
  EGate.seq (EGate.seq (measWindowedModNMulCircuit w bits a N numWin)
      (EGate.base (accYSwap cuccaroAdder w bits)))
    (measWindowedModNMulCircuit w bits (N - ainv) N numWin)

/-- **The measured in-place multiplier's exact T-count**: `2·numWin·(28·w·2^w + 56·bits)`. -/
theorem tcount_measWindowedModNMulInPlace (w bits a ainv N numWin : Nat) :
    EGate.tcount (measWindowedModNMulInPlace w bits a ainv N numWin)
      = 2 * (numWin * (28 * w * 2 ^ w + 56 * bits)) := by
  unfold measWindowedModNMulInPlace
  simp only [EGate.tcount]
  rw [tcount_measWindowedModNMulCircuit, tcount_measWindowedModNMulCircuit, tcount_accYSwap]
  ring

/-- Toffoli count of the faithful measured in-place multiplier: `2·numWin·(4·w·2^w + 8·bits)`. -/
theorem toffoli_measWindowedModNMulInPlace (w bits a ainv N numWin : Nat) :
    EGate.toffoli (measWindowedModNMulInPlace w bits a ainv N numWin)
      = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)) := by
  unfold EGate.toffoli
  rw [tcount_measWindowedModNMulInPlace,
      show 2 * (numWin * (28 * w * 2 ^ w + 56 * bits))
          = (2 * (numWin * (4 * w * 2 ^ w + 8 * bits))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **The faithful measured multiplier saves half the lookup reads vs the unitary one.**  Its
    Toffoli count plus `2·numWin·(4·w·2^w)` (the two passes' uncompute reads, now measured)
    equals the unitary `WindowedCircuit.windowedModNMulInPlace`'s Toffoli count
    `2·numWin·(8·w·2^w + 8·bits)` — the mod-N reduction is untouched. -/
theorem measInPlace_saves_half_the_reads (w bits a ainv N numWin : Nat) :
    EGate.toffoli (measWindowedModNMulInPlace w bits a ainv N numWin)
      + 2 * (numWin * (4 * w * 2 ^ w))
      = tcount (windowedModNMulInPlace w bits a ainv N numWin) / 7 := by
  rw [toffoli_measWindowedModNMulInPlace, tcount_windowedModNMulInPlace,
      show 2 * (numWin * (56 * w * 2 ^ w + 56 * bits))
          = (2 * (numWin * (8 * w * 2 ^ w + 8 * bits))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  ring

/-! ## §3. VALUE BY TRANSPORT — `mz`-clear ≡ re-read-clear (the crux).

The measured circuit differs from the unitary one ONLY by replacing each lookup uncompute (a
second `lookupReadAt`, which XOR-clears the addend word) with a measurement-clear `mzList`.  On
any state whose addend word holds the loaded table value `T[v]` (and whose lookup registers are
clean — ctrl set, address `= v`, AND-ancillas `0`), the two agree: the re-read XORs `T[v]`
against the loaded `T[v]` → `0`, exactly what `mz` does; off the addend both preserve.  This is
the value-layer heart of the whole transport (the `T[v]` cancels — no need to know its value). -/

/-- **★ `mz`-clear ≡ re-read-clear on a loaded-addend state ★.**  If the lookup ctrl/address/
    AND-ancilla registers are clean (address `= v`) and the addend word holds `T[v]`, then
    measurement-clearing the addend word equals re-reading the table (the unitary uncompute):
    both send the state to "addend word zeroed, everything else untouched". -/
theorem mzClear_eq_lookupRead_on_loaded
    (w bits : Nat) (T : Nat → Nat) (q_start v : Nat) (s : Nat → Bool)
    (hw : 0 < w) (hv : v < 2 ^ w) (hq : 2 * w < q_start)
    (hctrl : s ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → s (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → s (ulookup_and_idx i) = false)
    (hloaded : ∀ j, j < bits → s (addendIdx q_start j) = (T v).testBit j) :
    EGate.applyNat (mzList ((List.range bits).map (addendIdx q_start))) s
      = Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) s := by
  have hhigh : ∀ j, j < bits → 2 * w < addendIdx q_start j := by
    intro j _; unfold addendIdx; omega
  have hinj : ∀ j k, j < bits → k < bits → addendIdx q_start j = addendIdx q_start k → j = k := by
    intro j k _ _ h; unfold addendIdx at h; omega
  obtain ⟨hval, hframe⟩ :=
    lookupReadAt_selects w bits T (addendIdx q_start) s v hw hv hctrl haddr hand hhigh hinj
  funext p
  by_cases hp : p ∈ (List.range bits).map (addendIdx q_start)
  · obtain ⟨j, hjr, hpj⟩ := List.mem_map.mp hp
    have hj : j < bits := List.mem_range.mp hjr
    subst hpj
    rw [applyNat_mzList_clears _ s hp, hval j hj, hloaded j hj, Bool.xor_self]
  · rw [applyNat_mzList_preserves _ s hp]
    refine (hframe p ?_).symm
    intro j hj hcontra
    exact hp (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, hcontra.symm⟩)

/-! ## §3b. STEP TRANSPORT — `measModNLookupAddStep` ≡ `modNLookupAddStep` on clean inputs.

Threading the crux through the step: from a clean entry (ctrl set, address `= v`, AND-ancillas `0`,
addend `0`, accumulator `= s < N`, carry/flag clean), the measured step and the unitary step have
the SAME `Gate.applyNat`.  The only accumulator content needed is for the mod-N reduction
(`modNReduceFlag_state_general`'s `h_tgt`): after the add the accumulator holds `(s + T v)`
(`cuccaro_adder_sum_bits_general`), and `s + T v < 2N` since `s, T v < N`.  Both `mz`-clears are
discharged by the crux `mzClear_eq_lookupRead_on_loaded` at the two divergence points. -/
theorem measModNLookupAddStep_applyNat_eq
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
    EGate.applyNat (measModNLookupAddStep w bits N T q_start flagPos) f
      = Gate.applyNat (modNLookupAddStep w bits N T q_start flagPos) f := by
  -- position facts
  have hph : ∀ k, k < bits → 2 * w < addendIdx q_start k := fun k _ => by unfold addendIdx; omega
  have hpi : ∀ k l, k < bits → l < bits → addendIdx q_start k = addendIdx q_start l → k = l :=
    fun k l _ _ h => by unfold addendIdx at h; omega
  have hctrl_ne : ∀ k, k < bits → ulookup_ctrl_idx ≠ addendIdx q_start k :=
    fun k _ => by unfold ulookup_ctrl_idx addendIdx; omega
  have haddr_ne : ∀ i, i < w → ∀ k, k < bits → ulookup_address_idx i ≠ addendIdx q_start k :=
    fun i hi k _ => by unfold ulookup_address_idx addendIdx; omega
  have hand_ne : ∀ i, i < w → ∀ k, k < bits → ulookup_and_idx i ≠ addendIdx q_start k :=
    fun i hi k _ => by unfold ulookup_and_idx addendIdx; omega
  have hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos := Or.inr hflag_hi
  -- set the two common prefix states g1 = read1 f, g2 = add g1
  set g1 := Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) f with hg1
  set g2 := Gate.applyNat (cuccaro_n_bit_adder_full bits q_start) g1 with hg2
  obtain ⟨hs1v, hs1f⟩ :=
    lookupReadAt_selects w bits T (addendIdx q_start) f v hw hv hctrl haddr hand hph hpi
  -- g1 register facts
  have hg1_ctrl : g1 ulookup_ctrl_idx = true := by
    rw [hg1, hs1f _ (fun k hk => hctrl_ne k hk)]; exact hctrl
  have hg1_addr : ∀ i, i < w → g1 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg1, hs1f _ (fun k hk => haddr_ne i hi k hk)]; exact haddr i hi
  have hg1_and : ∀ i, i < w → g1 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg1, hs1f _ (fun k hk => hand_ne i hi k hk)]; exact hand i hi
  have hg1_addend : ∀ j, j < bits → g1 (addendIdx q_start j) = (T v).testBit j := fun j hj => by
    rw [hg1, hs1v j hj, h_clean j hj, Bool.false_xor]
  have hg1_acc : ∀ i, i < bits → g1 (q_start + 2 * i + 1) = s.testBit i := fun i hi => by
    rw [hg1, hs1f _ (fun k hk => by unfold addendIdx; omega)]; exact h_acc i hi
  have hg1_cin : g1 q_start = false := by
    rw [hg1, hs1f _ (fun k hk => by unfold addendIdx; omega)]; exact h_cin
  have hg1_flag : g1 flagPos = false := by
    rw [hg1, hs1f _ (fun k hk => by unfold addendIdx; omega)]; exact h_flag
  -- g2 register facts (cuccaro frames the lookup regs, preserves the addend, sums the accumulator)
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
    rw [(cuccaro_n_bit_adder_full_correct bits q_start g1).2.2 j hj]
    exact hg1_addend j hj
  have hg2_acc : ∀ i, i < bits → g2 (q_start + 2 * i + 1) = (s + T v).testBit i := fun i hi => by
    rw [hg2]; exact cuccaro_adder_sum_bits_general bits q_start s (T v) g1 hg1_cin hg1_acc hg1_addend i hi
  have hg2_cin : g2 q_start = false := by
    rw [hg2, (cuccaro_n_bit_adder_full_correct bits q_start g1).1]; exact hg1_cin
  have hg2_flag : g2 flagPos = false := by
    rw [hg2, cuccaro_n_bit_adder_full_frame_above bits q_start g1 _ hflag_hi]; exact hg1_flag
  -- CRUX at point 1
  have hcrux1 := mzClear_eq_lookupRead_on_loaded w bits T q_start v g2 hw hv hq
    hg2_ctrl hg2_addr hg2_and hg2_addend
  -- unfold both circuits, rewrite the first divergence, then set the middle chain
  unfold measModNLookupAddStep modNLookupAddStep
  simp only [Gate.applyNat_seq, EGate.applyNat]
  rw [← hg1, ← hg2, hcrux1]
  set g3 := Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) g2 with hg3
  set g4 := Gate.applyNat (modNReduceFlag bits q_start N flagPos) g3 with hg4
  set g5 := Gate.applyNat (lookupReadAt w (addendIdx q_start) bits T) g4 with hg5
  set g6 := Gate.applyNat (regCompareXor bits q_start flagPos) g5 with hg6
  -- g3 = read2 g2: addend cleared, lookup regs / accumulator / carry / flag preserved
  obtain ⟨hs2v, hs2f⟩ :=
    lookupReadAt_selects w bits T (addendIdx q_start) g2 v hw hv hg2_ctrl hg2_addr hg2_and hph hpi
  have hg3_ctrl : g3 ulookup_ctrl_idx = true := by
    rw [hg3, hs2f _ (fun k hk => hctrl_ne k hk)]; exact hg2_ctrl
  have hg3_addr : ∀ i, i < w → g3 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg3, hs2f _ (fun k hk => haddr_ne i hi k hk)]; exact hg2_addr i hi
  have hg3_and : ∀ i, i < w → g3 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg3, hs2f _ (fun k hk => hand_ne i hi k hk)]; exact hg2_and i hi
  have hg3_addend : ∀ j, j < bits → g3 (addendIdx q_start j) = false := fun j hj => by
    rw [hg3, hs2v j hj, hg2_addend j hj, Bool.xor_self]
  have hg3_acc : ∀ i, i < bits → g3 (q_start + 2 * i + 1) = (s + T v).testBit i := fun i hi => by
    rw [hg3, hs2f _ (fun k hk => by unfold addendIdx; omega)]; exact hg2_acc i hi
  have hg3_cin : g3 q_start = false := by
    rw [hg3, hs2f _ (fun k hk => by unfold addendIdx; omega)]; exact hg2_cin
  have hg3_flag : g3 flagPos = false := by
    rw [hg3, hs2f _ (fun k hk => by unfold addendIdx; omega)]; exact hg2_flag
  -- g4 = reduce g3: addend stays clean, lookup regs preserved (frame, below q_start)
  obtain ⟨_, hred_read, _, _, hred_frame⟩ :=
    modNReduceFlag_state_general bits q_start N flagPos (s + T v) g3 hN_pos hN2
      (by omega) hflag_out hg3_cin hg3_flag hg3_acc hg3_addend
  have hg4_ctrl : g4 ulookup_ctrl_idx = true := by
    rw [hg4, hred_frame ulookup_ctrl_idx (by unfold ulookup_ctrl_idx; omega)
      (Or.inl (by unfold ulookup_ctrl_idx; omega))]
    exact hg3_ctrl
  have hg4_addr : ∀ i, i < w → g4 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg4, hred_frame (ulookup_address_idx i) (by unfold ulookup_address_idx; omega)
      (Or.inl (by unfold ulookup_address_idx; omega))]
    exact hg3_addr i hi
  have hg4_and : ∀ i, i < w → g4 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg4, hred_frame (ulookup_and_idx i) (by unfold ulookup_and_idx; omega)
      (Or.inl (by unfold ulookup_and_idx; omega))]
    exact hg3_and i hi
  have hg4_addend : ∀ j, j < bits → g4 (addendIdx q_start j) = false := fun j hj => by
    rw [hg4]; show Gate.applyNat (modNReduceFlag bits q_start N flagPos) g3 (q_start + 2 * j + 2) = _
    exact hred_read j hj
  -- g5 = read3 g4: addend reloaded to T v, lookup regs preserved
  obtain ⟨hs3v, hs3f⟩ :=
    lookupReadAt_selects w bits T (addendIdx q_start) g4 v hw hv hg4_ctrl hg4_addr hg4_and hph hpi
  have hg5_ctrl : g5 ulookup_ctrl_idx = true := by
    rw [hg5, hs3f _ (fun k hk => hctrl_ne k hk)]; exact hg4_ctrl
  have hg5_addr : ∀ i, i < w → g5 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg5, hs3f _ (fun k hk => haddr_ne i hi k hk)]; exact hg4_addr i hi
  have hg5_and : ∀ i, i < w → g5 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg5, hs3f _ (fun k hk => hand_ne i hi k hk)]; exact hg4_and i hi
  have hg5_addend : ∀ j, j < bits → g5 (addendIdx q_start j) = (T v).testBit j := fun j hj => by
    rw [hg5, hs3v j hj, hg4_addend j hj, Bool.false_xor]
  -- g6 = regCompare g5: addend preserved (workspace), lookup regs preserved (frame)
  have hg6_ctrl : g6 ulookup_ctrl_idx = true := by
    rw [hg6, regCompareXor_frame_outside bits q_start flagPos g5 ulookup_ctrl_idx
      (by unfold ulookup_ctrl_idx; omega) (Or.inl (by unfold ulookup_ctrl_idx; omega))]
    exact hg5_ctrl
  have hg6_addr : ∀ i, i < w → g6 (ulookup_address_idx i) = v.testBit i := fun i hi => by
    rw [hg6, regCompareXor_frame_outside bits q_start flagPos g5 (ulookup_address_idx i)
      (by unfold ulookup_address_idx; omega) (Or.inl (by unfold ulookup_address_idx; omega))]
    exact hg5_addr i hi
  have hg6_and : ∀ i, i < w → g6 (ulookup_and_idx i) = false := fun i hi => by
    rw [hg6, regCompareXor_frame_outside bits q_start flagPos g5 (ulookup_and_idx i)
      (by unfold ulookup_and_idx; omega) (Or.inl (by unfold ulookup_and_idx; omega))]
    exact hg5_and i hi
  have hg6_addend : ∀ j, j < bits → g6 (addendIdx q_start j) = (T v).testBit j := fun j hj => by
    rw [hg6]; show Gate.applyNat (regCompareXor bits q_start flagPos) g5 (q_start + 2 * j + 2) = _
    rw [regCompareXor_workspace_restored_at bits q_start flagPos g5 hflag_out (q_start + 2 * j + 2)
      (by omega) (by omega)]
    exact hg5_addend j hj
  -- CRUX at point 2
  have hcrux2 := mzClear_eq_lookupRead_on_loaded w bits T q_start v g6 hw hv hq
    hg6_ctrl hg6_addr hg6_and hg6_addend
  rw [hcrux2]

/-! ## §3c. Lift through `copyWindow`, fold over windows, single-pass correctness.

`measWindowedModNStep` and `windowedModNStep` share the (T-free) `copyWindow` wrappers; after
`copyWindow` the state meets §3b's preconditions (`ModNStepInv` supplies them), so the two steps
agree.  Folding over the windows (the invariant maintained by the unitary `modNStepInv_fold`)
gives the per-window multiplier circuits equal, hence the measured circuit inherits the unitary
`windowedModNMulCircuit_correct` value `(a·y) mod N`. -/

/-- **Step-level transport with `copyWindow`.**  On any `ModNStepInv` state (accumulator `s < N`),
    the measured window step equals the unitary window step. -/
theorem measWindowedModNStep_eq (w bits a N numWin y j s : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hj : j < numWin) (hs : s < N) (g : Nat → Bool)
    (hg : ModNStepInv w bits numWin y s g) :
    EGate.applyNat (measWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) g
      = Gate.applyNat (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) g := by
  obtain ⟨hF, hD, hC, hG, hV⟩ := hg
  have hjw_le : j * w + w ≤ numWin * w := by
    have h1 : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
    have h2 : (j + 1) * w = j * w + w := by ring
    omega
  -- pre-copyWindow facts (from the invariant frame + the clean input)
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
  -- copyWindow g = the inner step's clean input (`cw`)
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
  -- §3b on `cw` (window value `v = window w y j`, table `tableValue a N w j`)
  have hinner := measModNLookupAddStep_applyNat_eq w bits N (WindowedArith.tableValue a N w j)
    (1 + 2 * w) (1 + 2 * w + (2 * bits + 1) + numWin * w) (WindowedArith.window w y j) s cw
    hw (WindowedArith.window_lt w y j) (by omega) hN_pos hN2 hs
    (by unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN_pos) (by omega)
    hcw_ctrl hcw_addr hcw_and hcw_addend hcw_acc hcw_cin hcw_flag
  unfold measWindowedModNStep windowedModNStep
  simp only [EGate.applyNat, Gate.applyNat_seq]
  rw [← hcw, hinner]

/-- **Fold transport.**  The measured per-window multiplier equals the unitary one (on the clean
    input), for every prefix of `n ≤ numWin` windows — the invariant is maintained by the unitary
    `modNStepInv_fold`, and each step agrees by `measWindowedModNStep_eq`. -/
theorem measWindowedModNMul_eq (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) :
    ∀ n, n ≤ numWin →
      EGate.applyNat (measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) (mulInputOf cuccaroAdder w bits numWin y)
        = Gate.applyNat (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) (mulInputOf cuccaroAdder w bits numWin y) := by
  intro n
  induction n with
  | zero => intro _; simp [measWindowedModNMul, windowedModNMul, EGate.applyNat, Gate.applyNat_I]
  | succ n ih =>
    intro hn
    have hn' : n ≤ numWin := by omega
    have hsplit_m : measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = EGate.seq (measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (measWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold measWindowedModNMul; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hsplit_u : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit_m, hsplit_u]
    simp only [EGate.applyNat, Gate.applyNat_seq]
    rw [ih hn']
    have hinv := modNStepInv_fold w bits a N numWin y hw hN_pos hN2 n hn'
    have hlt : WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) n 0 < N := by
      cases n with
      | zero => exact hN_pos
      | succ m => exact Nat.mod_lt _ hN_pos
    exact measWindowedModNStep_eq w bits a N numWin y n _ hw hN_pos hN2 (by omega) hlt _ hinv

/-- Toffoli count of the measured per-window multiplier circuit: `numWin·(4·w·2^w + 8·bits)`. -/
theorem toffoli_measWindowedModNMulCircuit (w bits a N numWin : Nat) :
    EGate.toffoli (measWindowedModNMulCircuit w bits a N numWin)
      = numWin * (4 * w * 2 ^ w + 8 * bits) := by
  unfold EGate.toffoli
  rw [tcount_measWindowedModNMulCircuit,
      show numWin * (28 * w * 2 ^ w + 56 * bits) = (numWin * (4 * w * 2 ^ w + 8 * bits)) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ Single-pass measured multiplier — VALUE and COUNT on ONE measured `EGate`. ★**  On the
    clean encoded input, the measured per-window mod-N multiplier circuit leaves `(a·y) mod N` in
    the accumulator (value-correct, via the §3a–§3c transport, inheriting
    `windowedModNMulCircuit_correct`), AND has the measurement-optimized Toffoli count
    `numWin·(4·w·2^w + 8·bits)` — half the unitary lookup cost.  The measured-uncompute is
    contained in the very object the resource proof is about, and that object is proven correct. -/
theorem measWindowedModNMulCircuit_verified (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hy : y < 2 ^ (w * numWin)) :
    decodeAccOf cuccaroAdder
        (EGate.applyNat (measWindowedModNMulCircuit w bits a N numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits = (a * y) % N
    ∧ EGate.toffoli (measWindowedModNMulCircuit w bits a N numWin)
        = numWin * (4 * w * 2 ^ w + 8 * bits) := by
  refine ⟨?_, toffoli_measWindowedModNMulCircuit w bits a N numWin⟩
  have heq : EGate.applyNat (measWindowedModNMulCircuit w bits a N numWin)
        (mulInputOf cuccaroAdder w bits numWin y)
      = Gate.applyNat (windowedModNMulCircuit w bits a N numWin)
        (mulInputOf cuccaroAdder w bits numWin y) := by
    unfold measWindowedModNMulCircuit windowedModNMulCircuit
    exact measWindowedModNMul_eq w bits a N numWin y hw hN_pos hN2 numWin (le_refl numWin)
  rw [heq]
  exact windowedModNMulCircuit_correct w bits a N numWin y hw hN_pos hN2 hy

/-! ## §3d. The in-place transport — generalized fold + two passes + inherit correctness. -/

/-- **The unitary fold keeps the invariant from ANY `ModNStepInv` start** (general initial `s0`):
    after `n ≤ numWin` windows the state is still `ModNStepInv` for some `s < N`.  Mirrors
    `modNStepInv_fold` but starts from an arbitrary invariant state (needed for the in-place
    second pass, whose accumulator is not clean). -/
theorem unitFold_inv_gen (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (s0 : Nat) (g0 : Nat → Bool) (hs0 : s0 < N) (hg0 : ModNStepInv w bits numWin y s0 g0) :
    ∀ n, n ≤ numWin → ∃ s, s < N ∧ ModNStepInv w bits numWin y s
      (Gate.applyNat (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) n) g0) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨s0, hs0, by simpa [windowedModNMul, Gate.applyNat_I] using hg0⟩
  | succ n ih =>
    intro hn
    obtain ⟨s, hs, hinv⟩ := ih (by omega)
    have hsplit : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit, Gate.applyNat_seq]
    exact ⟨_, Nat.mod_lt _ hN_pos,
      modNStepInv_step w bits a N numWin y hw hN_pos hN2 n (by omega) s hs _ hinv⟩

/-- **Generalized fold transport** (any `ModNStepInv` start): the measured per-window multiplier
    equals the unitary one for every prefix. -/
theorem measWindowedModNMul_eq_gen (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (s0 : Nat) (g0 : Nat → Bool) (hs0 : s0 < N) (hg0 : ModNStepInv w bits numWin y s0 g0) :
    ∀ n, n ≤ numWin →
      EGate.applyNat (measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) g0
        = Gate.applyNat (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) n) g0 := by
  intro n
  induction n with
  | zero => intro _; simp [measWindowedModNMul, windowedModNMul, EGate.applyNat, Gate.applyNat_I]
  | succ n ih =>
    intro hn
    have hsplit_m : measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = EGate.seq (measWindowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (measWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold measWindowedModNMul; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hsplit_u : windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
          (1 + 2 * w + (2 * bits + 1) + numWin * w) (n + 1)
        = Gate.seq (windowedModNMul w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
            (1 + 2 * w + (2 * bits + 1) + numWin * w) n)
            (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
              (1 + 2 * w + (2 * bits + 1) + numWin * w) n) := by
      unfold windowedModNMul; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit_m, hsplit_u]
    simp only [EGate.applyNat, Gate.applyNat_seq]
    rw [ih (by omega)]
    obtain ⟨s, hs, hinv⟩ := unitFold_inv_gen w bits a N numWin y hw hN_pos hN2 s0 g0 hs0 hg0 n (by omega)
    exact measWindowedModNStep_eq w bits a N numWin y n s hw hN_pos hN2 (by omega) hs _ hinv

/-- The circuit-level generalized transport. -/
theorem measWindowedModNMulCircuit_eq_gen (w bits a N numWin y : Nat)
    (hw : 0 < w) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (s0 : Nat) (g0 : Nat → Bool) (hs0 : s0 < N) (hg0 : ModNStepInv w bits numWin y s0 g0) :
    EGate.applyNat (measWindowedModNMulCircuit w bits a N numWin) g0
      = Gate.applyNat (windowedModNMulCircuit w bits a N numWin) g0 := by
  unfold measWindowedModNMulCircuit windowedModNMulCircuit
  exact measWindowedModNMul_eq_gen w bits a N numWin y hw hN_pos hN2 s0 g0 hs0 hg0 numWin (le_refl numWin)

/-- **★ THE IN-PLACE TRANSPORT ★** — on any `ModNMulReady` input, the measured in-place mod-N
    multiplier has the SAME `applyNat` as the unitary one.  Pass 1 transports on the clean input;
    the post-swap state (pass 2's input) is the `ModNStepInv` state characterized exactly as in
    `windowedModNMulInPlace_correct` (multiplicand `(a·y) mod N`, accumulator value `y`), so the
    generalized fold transport applies to pass 2 too. -/
theorem measWindowedModNMulInPlace_eq (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    EGate.applyNat (measWindowedModNMulInPlace w bits a ainv N numWin) f
      = Gate.applyNat (windowedModNMulInPlace w bits a ainv N numWin) f := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have hpow : (2 : Nat) ^ (w * numWin) = 2 ^ bits := by rw [Nat.mul_comm w numWin, hbits]
  have hy1 : y < 2 ^ (w * numWin) := by rw [hpow]; exact Nat.lt_of_lt_of_le hy hN_le
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  -- public replacements for the private `mulInputOf_cuccaro_y_bit` / `_encodeReg`
  have hy_bit : ∀ (v i : Nat), i < numWin * w →
      mulInputOf cuccaroAdder w bits numWin v (1 + 2 * w + (2 * bits + 1) + i) = v.testBit i := by
    intro v i hi
    rw [mulInputOf_eq_encodeReg cuccaroAdder w bits numWin v _ (by unfold ulookup_ctrl_idx; omega)]
    exact encodeReg_at _ _ _ i hi
  unfold measWindowedModNMulInPlace windowedModNMulInPlace
  simp only [EGate.applyNat, Gate.applyNat_seq]
  rw [measWindowedModNMulCircuit_eq_gen w bits a N numWin y hw hN_pos hN2 0 f hN_pos hf.toStepInv]
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
  rw [measWindowedModNMulCircuit_eq_gen w bits (N - ainv) N numWin (a * y % N) hw hN_pos hN2
    y s2 hy ⟨h2F, h2D, h2C, h2G, h2V⟩]

/-- **The faithful measured in-place multiplier is CORRECT** — on a `ModNMulReady` input it maps
    `y ↦ (a·y) mod N` (inherited from `windowedModNMulInPlace_correct` via the transport). -/
theorem measWindowedModNMulInPlace_correct (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (a * y % N)
      (EGate.applyNat (measWindowedModNMulInPlace w bits a ainv N numWin) f) := by
  rw [measWindowedModNMulInPlace_eq w bits a ainv N numWin y hw hbits hN_pos hN2 hy hainv hinv f hf]
  exact windowedModNMulInPlace_correct w bits a ainv N numWin y hw hbits hN_pos hN2 hy hainv hinv f hf

/-- **★ THE MEASURED-UNCOMPUTE CAPSTONE — value AND measured count on ONE in-place `EGate`. ★**
    The faithful measured in-place windowed mod-N multiplier (the count-optimal measurement-uncompute
    circuit) simultaneously: (1) maps `y ↦ (a·y) mod N` in place (semantics on the actual measured
    syntactic object), and (2) has the measurement-optimized Toffoli count
    `2·numWin·(4·w·2^w + 8·bits)` (half the unitary lookup cost).  The measured-uncompute is fully
    modeled (`EGate.mz`, density-justified) and CONTAINED in the very object the resource proof
    is about — and that object is proven correct. -/
theorem measWindowedModNMulInPlace_verified (w bits a ainv N numWin y : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hy : y < N) (hainv : ainv < N) (hinv : a * ainv % N = 1)
    (f : Nat → Bool) (hf : ModNMulReady w bits numWin y f) :
    ModNMulReady w bits numWin (a * y % N)
        (EGate.applyNat (measWindowedModNMulInPlace w bits a ainv N numWin) f)
    ∧ EGate.toffoli (measWindowedModNMulInPlace w bits a ainv N numWin)
        = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)) :=
  ⟨measWindowedModNMulInPlace_correct w bits a ainv N numWin y hw hbits hN_pos hN2 hy hainv hinv f hf,
   toffoli_measWindowedModNMulInPlace w bits a ainv N numWin⟩

/-! ## §4a. Well-typedness of the measured circuits + the measured ENCODE gate.

For the Shor-family lift (step 4) the measured gate must be `EGate.WellTypedAt`.  These mirror the
unitary `windowedModN*_wellTyped` lemmas, with `mz`-clears in place of the two uncompute reads. -/

/-- `mzList` is well-typed iff every measured qubit is `< dim`. -/
theorem mzList_wellTypedAt (dim : Nat) (h0 : 0 < dim) (L : List Nat) (h : ∀ q ∈ L, q < dim) :
    EGate.WellTypedAt dim (mzList L) := by
  induction L with
  | nil => exact h0
  | cons q qs ih =>
      exact ⟨ih (fun p hp => h p (List.mem_cons.mpr (Or.inr hp))),
             h q (List.mem_cons.mpr (Or.inl rfl))⟩

/-- Well-typedness of the measured mod-N lookup-add step. -/
theorem measModNLookupAddStep_wellTypedAt (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos dim : Nat) (hw : 0 < w)
    (hq : 2 * w + 1 ≤ q_start) (h_ws : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim) (h_ne : flagPos ≠ q_start + 2 * bits)
    (h_add : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    EGate.WellTypedAt dim (measModNLookupAddStep w bits N T q_start flagPos) := by
  have h_look : Gate.WellTyped dim (lookupReadAt w (addendIdx q_start) bits T) := by
    apply lookupReadAt_wellTyped w bits (addendIdx q_start) T dim hw (by omega)
    intro j hj; unfold addendIdx ulookup_and_idx; constructor <;> omega
  have h_mz : EGate.WellTypedAt dim (mzList ((List.range bits).map (addendIdx q_start))) := by
    apply mzList_wellTypedAt dim (by omega)
    intro q hq2
    simp only [List.mem_map, List.mem_range] at hq2
    obtain ⟨j, hj, rfl⟩ := hq2
    unfold addendIdx; omega
  exact ⟨h_look, cuccaro_n_bit_adder_full_wellTyped bits q_start dim h_ws, h_mz,
    modNReduceFlag_wellTyped bits q_start N flagPos dim h_ws h_flag h_ne h_add,
    h_look, regCompareXor_wellTyped bits q_start flagPos dim h_ws h_flag h_ne, h_mz⟩

/-- Well-typedness of the measured window step. -/
theorem measWindowedModNStep_wellTypedAt (w bits a N numWin j dim : Nat)
    (hw : 0 < w) (hj : j < numWin)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    EGate.WellTypedAt dim (measWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
      (1 + 2 * w + (2 * bits + 1) + numWin * w) j) := by
  have hjw' : j * w + w ≤ numWin * w := by
    calc j * w + w = (j + 1) * w := by ring
    _ ≤ numWin * w := Nat.mul_le_mul_right w hj
  have hcw : Gate.WellTyped dim (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) := by
    apply copyWindow_wellTyped w _ j dim (by omega)
    · intro i hi; omega
    · intro i hi; omega
  refine ⟨hcw, ?_, hcw⟩
  apply measModNLookupAddStep_wellTypedAt w bits N _ (1 + 2 * w)
    (1 + 2 * w + (2 * bits + 1) + numWin * w) dim hw (by omega) (by omega) (by omega) (by omega)
  intro i hi; omega

/-- A left-fold of well-typed measured steps is well-typed. -/
theorem wellTypedAt_foldl_egate (dim : Nat) (h0 : 0 < dim) (step : Nat → EGate) :
    ∀ n, (∀ j, j < n → EGate.WellTypedAt dim (step j)) →
      EGate.WellTypedAt dim
        ((List.range n).foldl (fun g j => EGate.seq g (step j)) (EGate.base Gate.I)) := by
  intro n
  induction n with
  | zero => intro _; simp only [List.range_zero, List.foldl_nil]; exact h0
  | succ k ih =>
      intro h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ⟨ih (fun j hj => h j (by omega)), h k (by omega)⟩

/-- Well-typedness of the measured per-window multiplier circuit. -/
theorem measWindowedModNMulCircuit_wellTypedAt (w bits a N numWin dim : Nat) (hw : 0 < w)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    EGate.WellTypedAt dim (measWindowedModNMulCircuit w bits a N numWin) := by
  unfold measWindowedModNMulCircuit measWindowedModNMul
  exact wellTypedAt_foldl_egate dim (by omega)
    (fun j => measWindowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
      (1 + 2 * w + (2 * bits + 1) + numWin * w) j) numWin
    (fun j hj => measWindowedModNStep_wellTypedAt w bits a N numWin j dim hw hj hdim)

/-- Well-typedness of the measured in-place multiplier. -/
theorem measWindowedModNMulInPlace_wellTypedAt (w bits a ainv N numWin dim : Nat) (hw : 0 < w)
    (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    EGate.WellTypedAt dim (measWindowedModNMulInPlace w bits a ainv N numWin) :=
  ⟨⟨measWindowedModNMulCircuit_wellTypedAt w bits a N numWin dim hw hdim,
    accYSwap_cuccaro_wellTyped w bits dim (by omega)⟩,
   measWindowedModNMulCircuit_wellTypedAt w bits (N - ainv) N numWin dim hw hdim⟩

/-- **The measured encode-layout in-place mod-N multiplier** — the canonical-`encodeDataZeroAnc`
    adapter (T-free, unitary) wrapping the measured core `measWindowedModNMulInPlace`. -/
def measWindowedModNEncodeGate (w bits N numWin c cinv : Nat) : EGate :=
  EGate.seq (EGate.base (windowedEncodeIn w bits))
    (EGate.seq (measWindowedModNMulInPlace w bits c cinv N numWin)
      (EGate.base (windowedEncodeOut w bits)))

/-- **Round trip** for the measured encode gate: `|x⟩|0⟩ ↦ |(c·x) mod N⟩|0⟩` — inherited from the
    measured core's correctness (`measWindowedModNMulInPlace_correct`) through the T-free adapters,
    exactly as the unitary `windowedModNEncodeGate_apply`. -/
theorem measWindowedModNEncodeGate_apply (w bits numWin N c cinv x : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    EGate.applyNat (measWindowedModNEncodeGate w bits N numWin c cinv)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) (c * x % N) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  unfold measWindowedModNEncodeGate
  simp only [EGate.applyNat]
  rw [windowedEncodeIn_apply w bits numWin x hbits hb1 (Nat.lt_of_lt_of_le hx hN_le)]
  have hmid := measWindowedModNMulInPlace_correct w bits c cinv N numWin x hw hbits hN_pos hN2
    hx hcinv hinv _ (modNMulReady_mulInputOf w bits numWin x)
  rw [modNMulReady_eq w bits numWin _ _ hmid]
  exact windowedEncodeOut_apply w bits numWin (c * x % N) hbits hb1
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN_le)

/-- Well-typedness of the measured encode gate at the canonical Shor dimension. -/
theorem measWindowedModNEncodeGate_wellTypedAt (w bits N numWin c cinv : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    EGate.WellTypedAt (bits + (2 * w + 2 * bits + 3)) (measWindowedModNEncodeGate w bits N numWin c cinv) := by
  have hswap : Gate.WellTyped (bits + (2 * w + 2 * bits + 3))
      (swapCascade (fun i => bits - 1 - i) (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits) := by
    apply swapCascade_wellTyped _ _ bits _ (by omega)
    intro i hi; refine ⟨by omega, by omega, by omega⟩
  have hX : Gate.WellTyped (bits + (2 * w + 2 * bits + 3)) (Gate.X ulookup_ctrl_idx) := by
    show ulookup_ctrl_idx < bits + (2 * w + 2 * bits + 3); unfold ulookup_ctrl_idx; omega
  refine ⟨⟨hswap, hX⟩,
    ⟨measWindowedModNMulInPlace_wellTypedAt w bits c cinv N numWin (bits + (2 * w + 2 * bits + 3))
      hw hbits (by omega), ?_⟩⟩
  exact ⟨hX, hswap⟩

end FormalRV.Shor.MeasuredWindowedModN
