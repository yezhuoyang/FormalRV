/-
  FormalRV.Shor.GidneyRunwayMul — folding the all-temporary-AND Gidney lookup-add step into a
  WHOLE windowed mod-N multiplier, via the SINGLE-WIDE-RUNWAY coset bridge.

  ## What this closes

  `GidneyMeasuredLookupAdd.gidneyLookupAddStep` is the per-window LOAD·ADD·`mz` step at the Gidney
  3-per-bit layout, all-temporary-AND, value `acc ← (s + T[v]) mod 2^bits` (a FAITHFUL add, NO
  per-step mod-N reduction).  This file folds it over the `numWin` windows of `y` into a whole
  multiplier and supplies the missing `mod N` exactly as the papers do — via the RUNWAY (coset)
  representation, not per-step reduction:

    * each window `j` reads its digit `windowⱼ(y)` DIRECTLY from the y-register (the Babbush read's
      address map `aIdx` is a parameter — no `copyWindow` needed) and adds the table word
      `tableValue a N w j (windowⱼ y) = (a·(2^w)^j·windowⱼ y) mod N` to the accumulator;
    * the accumulator is a SINGLE wide register (the "runway"): if `numWin·N ≤ 2^bits` it never
      overflows, so the fold lands the EXACT integer sum `S = Σⱼ tableValueⱼ` with no wraparound;
    * the residue is the coset value-bridge: `S mod N = (a·y) mod N`
      (`WindowedArith.windowed_modProductAdd`).  The accumulator holds an un-reduced coset rep of
      `(a·y) mod N` — exactly the Gidney/Babbush coset multiplier's invariant.

  Every gadget in every window is a genuine temporary AND (Babbush merged-AND load + measured Gidney
  adder + `mz`-clears), so the whole multiplier's `gidneyTCount = 4·toffoli` is gadget-by-gadget
  honest — `numWin·(4·((2^w − 1) + bits))`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyMeasuredLookupAdd
import FormalRV.Arithmetic.Windowed.WindowedArith
import FormalRV.Arithmetic.Windowed.WindowedCoset

namespace FormalRV.Shor.GidneyRunwayMul

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredBabbushRead
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.GidneyTCount
open FormalRV.Shor.GidneyMeasuredLookupAdd

/-! ## §1. A bounded `EGate`/`Gate` leaves HIGH indices untouched.

The mirror of `MeasuredAdder.EGate.applyNat_congr_lt`: a circuit all of whose gate indices are `< B`
fixes every index `≥ B`.  This lets the base-0 measured adder frame the high-placed y-register,
lookup ancilla, and control across each fold step. -/

theorem Gate_applyNat_ge_of_boundedBy (B : Nat) :
    ∀ (g : Gate), Gate.boundedBy B g → ∀ (f : Nat → Bool) (q : Nat), B ≤ q →
      Gate.applyNat g f q = f q := by
  intro g
  induction g with
  | I => intro _ f q _; rfl
  | X p =>
      intro hb f q hq
      have hp : p < B := hb
      simp only [Gate.applyNat_X]
      exact update_neq _ _ _ _ (by omega)
  | CX c t =>
      intro hb f q hq
      obtain ⟨_, ht⟩ := hb
      simp only [Gate.applyNat_CX]
      exact update_neq _ _ _ _ (by omega)
  | CCX a b c =>
      intro hb f q hq
      obtain ⟨_, _, hc⟩ := hb
      simp only [Gate.applyNat_CCX]
      exact update_neq _ _ _ _ (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
      intro hb f q hq
      obtain ⟨hb₁, hb₂⟩ := hb
      show Gate.applyNat g₂ (Gate.applyNat g₁ f) q = f q
      rw [ih₂ hb₂ _ q hq, ih₁ hb₁ f q hq]

theorem EGate_applyNat_ge_of_boundedBy (B : Nat) :
    ∀ (eg : EGate), EGate.boundedBy B eg → ∀ (f : Nat → Bool) (q : Nat), B ≤ q →
      EGate.applyNat eg f q = f q := by
  intro eg
  induction eg with
  | base g => intro hb f q hq; exact Gate_applyNat_ge_of_boundedBy B g hb f q hq
  | mz p =>
      intro hb f q hq
      have hp : p < B := hb
      show Function.update f p false q = f q
      exact Function.update_of_ne (by omega) _ _
  | seq a b iha ihb =>
      intro hb f q hq
      obtain ⟨hba, hbb⟩ := hb
      show EGate.applyNat b (EGate.applyNat a f) q = f q
      rw [ihb hbb _ q hq, iha hba f q hq]

/-! ## §2. The address-generalized lookup-add step.

`GidneyMeasuredLookupAdd.gidneyLookupAddStep` hard-wires the address register at `gLookAddr`.  For
the fold each window reads a different slice of `y`, so we parameterize the Babbush read's address
map `aIdx`, ancilla map `cIdx`, and root control `ctrl` — all placed ABOVE the base-0 adder block. -/

/-- The address-generalized LOAD: Babbush merged-AND read with address `aIdx`, ancilla `cIdx`,
    control `ctrl`, writing `T[v]` into the read register. -/
def gidneyLoadGen (w : Nat) (aIdx cIdx : Nat → Nat) (ctrl n : Nat) (T : Nat → Nat) : EGate :=
  unaryQROMPos aIdx cIdx read_idx (n + 2) T w ctrl 0

/-- The address-generalized all-temporary-AND lookup-add step. -/
def gidneyStepGen (w : Nat) (aIdx cIdx : Nat → Nat) (ctrl n : Nat) (T : Nat → Nat) : EGate :=
  EGate.seq (gidneyLoadGen w aIdx cIdx ctrl n T)
    (EGate.seq (gidneyAdderMeasured (n + 2) 0)
      (mzList ((List.range (n + 2)).map read_idx)))

/-- T-count of the generalized step: `7·((2^w − 1) + bits)`. -/
theorem tcount_gidneyStepGen (w : Nat) (aIdx cIdx : Nat → Nat) (ctrl n : Nat) (T : Nat → Nat) :
    EGate.tcount (gidneyStepGen w aIdx cIdx ctrl n T) = 7 * ((2 ^ w - 1) + (n + 2)) := by
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) 0) = 7 * (n + 2) := by
    show EGate.tcount (EGate.seq (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
        (gidney_final_cx_cascade (n + 2)))) (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
      tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  unfold gidneyStepGen gidneyLoadGen
  have hstruct : EGate.tcount (EGate.seq
        (unaryQROMPos aIdx cIdx read_idx (n + 2) T w ctrl 0)
        (EGate.seq (gidneyAdderMeasured (n + 2) 0) (mzList ((List.range (n + 2)).map read_idx))))
      = EGate.tcount (unaryQROMPos aIdx cIdx read_idx (n + 2) T w ctrl 0)
        + (EGate.tcount (gidneyAdderMeasured (n + 2) 0)
            + EGate.tcount (mzList ((List.range (n + 2)).map read_idx))) := rfl
  rw [hstruct, tcount_unaryQROMPos, hadd, tcount_mzList]; ring

/-- Toffoli count of the generalized step: `(2^w − 1) + bits` (same as the fixed-address step). -/
theorem toffoli_gidneyStepGen (w : Nat) (aIdx cIdx : Nat → Nat) (ctrl n : Nat) (T : Nat → Nat) :
    EGate.toffoli (gidneyStepGen w aIdx cIdx ctrl n T) = (2 ^ w - 1) + (n + 2) := by
  unfold EGate.toffoli
  rw [tcount_gidneyStepGen, Nat.mul_div_cancel_left _ (by norm_num)]

/-- Gidney temporary-AND T-count of the generalized step: `4·((2^w − 1) + bits)`, gadget-by-gadget
    honest (every gadget a temporary AND). -/
theorem gidneyTCount_gidneyStepGen (w : Nat) (aIdx cIdx : Nat → Nat) (ctrl n : Nat) (T : Nat → Nat) :
    gidneyTCount (gidneyStepGen w aIdx cIdx ctrl n T) = 4 * ((2 ^ w - 1) + (n + 2)) := by
  unfold gidneyTCount FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_gidneyStepGen]

/-! ## §3. `adder_input_F` evaluation at the three register classes. -/

theorem adder_input_F_at_read (m a b i : Nat) :
    adder_input_F m a b (read_idx i) = (decide (i < m) && a.testBit i) := by
  simp only [adder_input_F, read_idx, show (3 * i) % 3 = 0 from by omega,
    show (3 * i) / 3 = i from by omega]

theorem adder_input_F_at_target (m a b i : Nat) :
    adder_input_F m a b (target_idx i) = (decide (i < m) && b.testBit i) := by
  simp only [adder_input_F, target_idx, show (3 * i + 1) % 3 = 1 from by omega,
    show (3 * i + 1) / 3 = i from by omega]

theorem adder_input_F_at_carry (m a b i : Nat) :
    adder_input_F m a b (carry_idx i) = false := by
  simp only [adder_input_F, carry_idx, show (3 * i + 2) % 3 = 2 from by omega]

/-! ## §4. The whole-multiplier layout and the per-window step.

`bits = n+2`.  The adder block occupies `[0, 3(n+2))` (the measured adder touches nothing above,
`gidneyAdderMeasured_boundedBy_tight`); the accumulator IS the target register.  Above the block:
the y-register, then the lookup ancilla, then the root control.  Window `j` reads its digit
`windowⱼ(y)` DIRECTLY from the y-register via the address map `aIdxAt` — no copy. -/

/-- y-register base (just above the adder block's `adder_n_qubits` total). -/
def gYBase (n : Nat) : Nat := adder_n_qubits (n + 2)

/-- Lookup AND-ancilla base (above the full y-register `numWin*w`). -/
def gCBase (w n numWin : Nat) : Nat := gYBase n + numWin * w

/-- Lookup AND-ancilla map. -/
def gCAnc (w n numWin : Nat) : Nat → Nat := fun i => gCBase w n numWin + i

/-- Lookup root control (above the ancilla register). -/
def gCtrl (w n numWin : Nat) : Nat := gCBase w n numWin + w

/-- Address map for window `j`: points directly at the `j`-th width-`w` slice of the y-register. -/
def aIdxAt (w n j : Nat) : Nat → Nat := fun i => gYBase n + j * w + i

/-- The per-window step: the address-generalized all-temporary-AND lookup-add, reading window `j`
    of `y` and adding the table word `tableValue a N w j (·)` to the accumulator. -/
def gidneyRunwayStep (w n a N numWin j : Nat) : EGate :=
  gidneyStepGen w (aIdxAt w n j) (gCAnc w n numWin) (gCtrl w n numWin) n
    (fun v => WindowedArith.tableValue a N w j v)

/-- The first `m` windows of the runway multiplier (the fold prefix). -/
def gidneyRunwayMulN (w n a N numWin m : Nat) : EGate :=
  (List.range m).foldl
    (fun g j => EGate.seq g (gidneyRunwayStep w n a N numWin j)) (EGate.base Gate.I)

/-- **The whole windowed runway multiplier**: fold the per-window step over `numWin` windows. -/
def gidneyRunwayMul (w n a N numWin : Nat) : EGate :=
  gidneyRunwayMulN w n a N numWin numWin

/-! ## §5. The fold invariant and its single-step preservation. -/

/-- **The clean Gidney-runway state invariant** for running accumulator value `s`: the adder block
    holds `adder_input_F (n+2) 0 s` (read & carry clean, target = `s`); the y-register holds `y`;
    the lookup ancilla is clean; the root control is set. -/
def GInv (w n numWin y s : Nat) (g : Nat → Bool) : Prop :=
  (∀ q, q < 3 * (n + 2) → g q = adder_input_F (n + 2) 0 s q)
  ∧ (∀ k, k < numWin * w → g (gYBase n + k) = y.testBit k)
  ∧ (∀ i, i < w → g (gCAnc w n numWin i) = false)
  ∧ g (gCtrl w n numWin) = true

/-- **★ SINGLE-STEP PRESERVATION ★** — the per-window step takes the invariant for running sum `s`
    to the invariant for `s + tableValueⱼ(windowⱼ(y))`, with NO per-step reduction (the runway
    absorbs the growth).  Threads load (Babbush select + frame + ancilla-clear) → measured adder
    (tight congruence for target/carry, tight frame-above for the y-register/ancilla/control) →
    `mz`-clear (read register). -/
theorem gInv_step (w n a N numWin y s j : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2)) (hj : j < numWin)
    (hs : s < 2 ^ (n + 2))
    (g : Nat → Bool) (hg : GInv w n numWin y s g) :
    GInv w n numWin y (s + WindowedArith.tableValue a N w j (WindowedArith.window w y j))
      (EGate.applyNat (gidneyRunwayStep w n a N numWin j) g) := by
  obtain ⟨hblock, hy, hanc, hctrl⟩ := hg
  set v := WindowedArith.window w y j with hv_def
  set Tv := WindowedArith.tableValue a N w j v with hTv_def
  have hv_lt : v < 2 ^ w := WindowedArith.window_lt w y j
  have hTv_ltN : Tv < N := by rw [hTv_def]; unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN
  have hTv_lt : Tv < 2 ^ (n + 2) := lt_of_lt_of_le hTv_ltN hN2
  have hjwin : j * w + w ≤ numWin * w := by
    calc j * w + w = (j + 1) * w := by ring
    _ ≤ numWin * w := Nat.mul_le_mul_right w hj
  -- address decode: the lookup reads window j of y
  have haddr : ∀ i, i < w → g (aIdxAt w n j i) = v.testBit i := by
    intro i hi
    have hk : j * w + i < numWin * w := by omega
    have he : aIdxAt w n j i = gYBase n + (j * w + i) := by unfold aIdxAt; ring
    rw [he, hy (j * w + i) hk, hv_def, FormalRV.Shor.WindowedCircuit.window_testBit w y j i hi]
  have hdec : decodeReg (aIdxAt w n j) w g = v := by
    rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (aIdxAt w n j) w v g haddr,
        Nat.mod_eq_of_lt hv_lt]
  -- disjointness side-conditions (all lookup registers ≥ gYBase = 3(n+2)+2 > read_idx)
  have hgY : gYBase n = 3 * (n + 2) + 2 := by unfold gYBase adder_n_qubits; ring
  have hpos_inj : ∀ a' b', a' < n + 2 → b' < n + 2 → read_idx a' = read_idx b' → a' = b' := by
    intro a' b' _ _ h; simp only [read_idx] at h; omega
  have hc_inj : ∀ i i', gCAnc w n numWin i = gCAnc w n numWin i' → i = i' := by
    intro i i' h; simp only [gCAnc, gCBase] at h; omega
  have h_anc_out : ∀ i j', i < w → j' < n + 2 → gCAnc w n numWin i ≠ read_idx j' := by
    intro i j' _ hj'; simp only [gCAnc, gCBase, read_idx, hgY]; omega
  have h_anc_addr : ∀ i i', i < w → i' < w → gCAnc w n numWin i ≠ aIdxAt w n j i' := by
    intro i i' _ hi'; simp only [gCAnc, gCBase, aIdxAt]; omega
  have h_addr_out : ∀ i j', i < w → j' < n + 2 → aIdxAt w n j i ≠ read_idx j' := by
    intro i j' _ hj'; simp only [aIdxAt, read_idx, hgY]; omega
  have h_ctrl_out : ∀ j', j' < n + 2 → gCtrl w n numWin ≠ read_idx j' := by
    intro j' hj'; simp only [gCtrl, gCBase, read_idx, hgY]; omega
  have h_ctrl_anc : ∀ i, i < w → gCtrl w n numWin ≠ gCAnc w n numWin i := by
    intro i hi; simp only [gCtrl, gCAnc, gCBase]; omega
  -- the load's selection + frame + ancilla-clear
  have hsel := unaryQROMPos_selects_word (aIdxAt w n j) (gCAnc w n numWin) read_idx (n + 2)
    (fun v => WindowedArith.tableValue a N w j v) hpos_inj hc_inj w (gCtrl w n numWin) 0 g
    h_anc_out h_anc_addr h_addr_out h_ctrl_out h_ctrl_anc hanc
  -- abbreviate the loaded state
  set gl := EGate.applyNat (gidneyLoadGen w (aIdxAt w n j) (gCAnc w n numWin) (gCtrl w n numWin) n
    (fun v => WindowedArith.tableValue a N w j v)) g with hgl_def
  have hgl_read : ∀ i, i < n + 2 → gl (read_idx i) = Tv.testBit i := by
    intro i hi
    have := hsel i hi
    rw [hctrl, Bool.true_and, Nat.zero_add, hdec] at this
    have hg0 : g (read_idx i) = false := by
      rw [hblock (read_idx i) (by simp only [read_idx]; omega), adder_input_F_at_read]; simp
    show gl (read_idx i) = Tv.testBit i
    rw [hgl_def]; show EGate.applyNat (unaryQROMPos _ _ _ _ _ _ _ _) g (read_idx i) = _
    rw [this, hg0, Bool.false_xor]
  have hgl_frame : ∀ q, (∀ j', j' < n + 2 → q ≠ read_idx j') →
      (∀ i, i < w → q ≠ gCAnc w n numWin i) → gl q = g q := by
    intro q hqr hqc
    show gl q = g q
    rw [hgl_def]; show EGate.applyNat (unaryQROMPos _ _ _ _ _ _ _ _) g q = _
    exact unaryQROMPos_frame (aIdxAt w n j) (gCAnc w n numWin) read_idx (n + 2)
      (fun v => WindowedArith.tableValue a N w j v) w (gCtrl w n numWin) 0 g q
      (fun j' hj' => hqr j' hj') (fun i hi => hqc i hi)
  have hgl_anc : ∀ i, i < w → gl (gCAnc w n numWin i) = false := by
    intro i hi
    show gl (gCAnc w n numWin i) = false
    rw [hgl_def]; show EGate.applyNat (unaryQROMPos _ _ _ _ _ _ _ _) g (gCAnc w n numWin i) = _
    rw [unaryQROMPos_anc_cleared (aIdxAt w n j) (gCAnc w n numWin) read_idx (n + 2)
      (fun v => WindowedArith.tableValue a N w j v) hc_inj w (gCtrl w n numWin) 0 g i hi]
  -- the loaded state agrees with `adder_input_F (n+2) Tv s` on the meaningful block `< 3(n+2)`
  have hgl_block : ∀ q, q < 3 * (n + 2) → gl q = adder_input_F (n + 2) Tv s q := by
    intro q hq
    -- q is read/target/carry of some i < n+2
    have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have hi : q / 3 < n + 2 := by omega
      have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
      rw [hqr, hgl_read _ hi, adder_input_F_at_read]; simp [hi]
    · have hi : q / 3 < n + 2 := by omega
      have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
      rw [hqt, hgl_frame _ (fun j' _ => by simp only [target_idx, read_idx]; omega)
            (fun i _ => by simp only [target_idx, gCAnc, gCBase, hgY]; omega),
          hblock (target_idx (q / 3)) (by rw [← hqt]; exact hq), adder_input_F_at_target,
          adder_input_F_at_target]
    · have hi : q / 3 < n + 2 := by omega
      have hqc : q = carry_idx (q / 3) := by simp only [carry_idx]; omega
      rw [hqc, hgl_frame _ (fun j' _ => by simp only [carry_idx, read_idx]; omega)
            (fun i _ => by simp only [carry_idx, gCAnc, gCBase, hgY]; omega),
          hblock (carry_idx (q / 3)) (by rw [← hqc]; exact hq), adder_input_F_at_carry,
          adder_input_F_at_carry]
  -- run the adder on the loaded state
  set ga := EGate.applyNat (gidneyAdderMeasured (n + 2) 0) gl with hga_def
  have hcongr : ∀ q, q < 3 * (n + 2) →
      ga q = EGate.applyNat (gidneyAdderMeasured (n + 2) 0) (adder_input_F (n + 2) Tv s) q := by
    intro q hq
    exact EGate.applyNat_congr_lt (3 * (n + 2)) (gidneyAdderMeasured (n + 2) 0)
      (gidneyAdderMeasured_boundedBy_tight n 0) gl (adder_input_F (n + 2) Tv s) hgl_block q hq
  have hga_high : ∀ q, 3 * (n + 2) ≤ q → ga q = gl q := by
    intro q hq
    exact EGate_applyNat_ge_of_boundedBy (3 * (n + 2)) (gidneyAdderMeasured (n + 2) 0)
      (gidneyAdderMeasured_boundedBy_tight n 0) gl q hq
  have ha_target : ∀ i, i < n + 2 → ga (target_idx i) = (s + Tv).testBit i := by
    intro i hi
    rw [hcongr (target_idx i) (by simp only [target_idx]; omega),
        (gidneyAdderMeasured_correct n Tv s 0 hTv_lt hs i hi).1, adder_sum_bit_classical,
        Nat.add_comm Tv s]
  have ha_carry : ∀ i, i < n + 2 → ga (carry_idx i) = false := by
    intro i hi
    rw [hcongr (carry_idx i) (by simp only [carry_idx]; omega),
        (gidneyAdderMeasured_correct n Tv s 0 hTv_lt hs i hi).2]
  -- the final mz-clear of the read register
  have notin_read : ∀ p : Nat, (∀ i, i < n + 2 → p ≠ read_idx i) →
      p ∉ (List.range (n + 2)).map read_idx := by
    intro p hp hmem
    obtain ⟨i, hir, hpi⟩ := List.mem_map.mp hmem
    exact hp i (List.mem_range.mp hir) hpi.symm
  -- assemble the post-step state
  have hstep : EGate.applyNat (gidneyRunwayStep w n a N numWin j) g
      = EGate.applyNat (mzList ((List.range (n + 2)).map read_idx)) ga := by
    show EGate.applyNat (mzList ((List.range (n + 2)).map read_idx)) ga = _
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- block: read=0, target=(s+Tv), carry=0
    intro q hq
    rw [hstep]
    have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have hi : q / 3 < n + 2 := by omega
      have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
      rw [hqr, applyNat_mzList_clears _ ga (List.mem_map.mpr ⟨q / 3, List.mem_range.mpr hi, rfl⟩),
          adder_input_F_at_read]; simp
    · have hi : q / 3 < n + 2 := by omega
      have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
      rw [hqt, applyNat_mzList_preserves _ ga (notin_read _ (fun i _ => by
            simp only [target_idx, read_idx]; omega)),
          ha_target _ hi, adder_input_F_at_target]; simp [hi]
    · have hi : q / 3 < n + 2 := by omega
      have hqc : q = carry_idx (q / 3) := by simp only [carry_idx]; omega
      rw [hqc, applyNat_mzList_preserves _ ga (notin_read _ (fun i _ => by
            simp only [carry_idx, read_idx]; omega)),
          ha_carry _ hi, adder_input_F_at_carry]
  · -- y-register preserved
    intro k hk
    rw [hstep, applyNat_mzList_preserves _ ga (notin_read _ (fun i _ => by
          simp only [gYBase, adder_n_qubits, read_idx]; omega)),
        hga_high _ (by simp only [gYBase, adder_n_qubits]; omega),
        hgl_frame _ (fun j' _ => by simp only [gYBase, adder_n_qubits, read_idx]; omega)
          (fun i _ => by simp only [gYBase, adder_n_qubits, gCAnc, gCBase]; omega)]
    exact hy k hk
  · -- ancilla cleared
    intro i hi
    rw [hstep, applyNat_mzList_preserves _ ga (notin_read _ (fun i' _ => by
          simp only [gCAnc, gCBase, gYBase, adder_n_qubits, read_idx]; omega)),
        hga_high _ (by simp only [gCAnc, gCBase, gYBase, adder_n_qubits]; omega)]
    exact hgl_anc i hi
  · -- control preserved
    rw [hstep, applyNat_mzList_preserves _ ga (notin_read _ (fun i _ => by
          simp only [gCtrl, gCBase, gYBase, adder_n_qubits, read_idx]; omega)),
        hga_high _ (by simp only [gCtrl, gCBase, gYBase, adder_n_qubits]; omega),
        hgl_frame _ (fun j' _ => by simp only [gCtrl, gCBase, gYBase, adder_n_qubits, read_idx]; omega)
          (fun i hi => (h_ctrl_anc i hi))]
    exact hctrl

/-! ## §6. The clean input and the fold induction. -/

theorem adder_input_F_zero (m q : Nat) : adder_input_F m 0 0 q = false := by
  rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega) with h | h | h <;>
    simp [adder_input_F, h, Nat.zero_testBit]

/-- The clean Gidney-runway input: accumulator/runway `= 0` (block all clear), the y-register holds
    `y`, the lookup ancilla clear, the root control set. -/
def gMulInput (w n numWin y : Nat) : Nat → Bool := fun q =>
  if q = gCtrl w n numWin then true
  else if gYBase n ≤ q ∧ q < gYBase n + numWin * w then y.testBit (q - gYBase n)
  else false

theorem gInv_init (w n numWin y : Nat) : GInv w n numWin y 0 (gMulInput w n numWin y) := by
  have hgY : gYBase n = 3 * (n + 2) + 2 := by unfold gYBase adder_n_qubits; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [adder_input_F_zero]
    unfold gMulInput
    rw [if_neg (by simp only [gCtrl, gCBase, hgY]; omega), if_neg (by simp only [hgY]; omega)]
  · intro k hk
    unfold gMulInput
    rw [if_neg (by simp only [gCtrl, gCBase]; omega), if_pos ⟨by omega, by omega⟩]
    congr 1; omega
  · intro i hi
    unfold gMulInput
    rw [if_neg (by simp only [gCtrl, gCAnc, gCBase]; omega),
        if_neg (by simp only [gCAnc, gCBase]; omega)]
  · unfold gMulInput; rw [if_pos rfl]

/-- **The fold invariant holds after every prefix of windows.**  After folding the first `m ≤ numWin`
    windows from the clean input, the state is `GInv` for the running unreduced sum
    `Σ_{j<m} tableValueⱼ(windowⱼ(y))` — the runway accumulating the coset-word sum. -/
theorem gInv_fold (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2)) (hrun : numWin * N ≤ 2 ^ (n + 2)) :
    ∀ m, m ≤ numWin →
      GInv w n numWin y
          (∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w y j))
          (EGate.applyNat (gidneyRunwayMulN w n a N numWin m) (gMulInput w n numWin y)) := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [Finset.sum_range_zero]
      have he : EGate.applyNat (gidneyRunwayMulN w n a N numWin 0) (gMulInput w n numWin y)
          = gMulInput w n numWin y := by
        simp [gidneyRunwayMulN, EGate.applyNat, Gate.applyNat_I]
      rw [he]; exact gInv_init w n numWin y
  | succ m ih =>
      intro hm
      have hsplit : gidneyRunwayMulN w n a N numWin (m + 1)
          = EGate.seq (gidneyRunwayMulN w n a N numWin m) (gidneyRunwayStep w n a N numWin m) := by
        unfold gidneyRunwayMulN
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      show GInv w n numWin y
          (∑ j ∈ Finset.range (m + 1), WindowedArith.tableValue a N w j (WindowedArith.window w y j))
          (EGate.applyNat (gidneyRunwayStep w n a N numWin m)
            (EGate.applyNat (gidneyRunwayMulN w n a N numWin m) (gMulInput w n numWin y)))
      rw [Finset.sum_range_succ]
      have hs : (∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w y j))
          < 2 ^ (n + 2) := by
        have hle : (∑ j ∈ Finset.range m,
            WindowedArith.tableValue a N w j (WindowedArith.window w y j)) ≤ m * N := by
          calc (∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w y j))
              ≤ ∑ _j ∈ Finset.range m, N :=
                Finset.sum_le_sum (fun j _ => le_of_lt (by
                  unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN))
            _ = m * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        have h1 : (m + 1) * N ≤ numWin * N := Nat.mul_le_mul_right N hm
        have h2 : (m + 1) * N = m * N + N := by ring
        omega
      exact gInv_step w n a N numWin y
        (∑ j ∈ Finset.range m, WindowedArith.tableValue a N w j (WindowedArith.window w y j)) m
        hw hN hN2 (by omega) hs _ (ih (by omega))

/-! ## §7. The whole-multiplier value, the coset residue bridge, and the counts. -/

/-- The runway accumulator never overflows: the unreduced coset-word sum stays `< 2^bits`. -/
theorem runwaySum_lt (w n a N numWin y : Nat) (hN : 0 < N) (hrun : numWin * N ≤ 2 ^ (n + 2)) :
    (∑ j ∈ Finset.range numWin, WindowedArith.tableValue a N w j (WindowedArith.window w y j))
      < 2 ^ (n + 2) := by
  rcases Nat.eq_zero_or_pos numWin with h0 | hpos
  · subst h0; rw [Finset.sum_range_zero]; positivity
  · have hstrict : (∑ j ∈ Finset.range numWin,
        WindowedArith.tableValue a N w j (WindowedArith.window w y j)) < numWin * N := by
      calc (∑ j ∈ Finset.range numWin,
            WindowedArith.tableValue a N w j (WindowedArith.window w y j))
          < ∑ _j ∈ Finset.range numWin, N :=
            Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
              (fun j _ => by unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN)
        _ = numWin * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

/-- **★ THE WHOLE-MULTIPLIER VALUE ★** — the accumulator/runway holds the EXACT unreduced coset-word
    sum `Σⱼ tableValueⱼ(windowⱼ(y))` (no per-step reduction; the runway `numWin·N ≤ 2^bits` absorbs
    the growth so the integer sum lands without wraparound). -/
theorem gidneyRunwayMul_value (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2)) (hrun : numWin * N ≤ 2 ^ (n + 2)) :
    gidney_target_val (n + 2)
        (EGate.applyNat (gidneyRunwayMul w n a N numWin) (gMulInput w n numWin y))
      = ∑ j ∈ Finset.range numWin, WindowedArith.tableValue a N w j (WindowedArith.window w y j) := by
  unfold gidneyRunwayMul
  have hSlt := runwaySum_lt w n a N numWin y hN hrun
  obtain ⟨hblock, _, _, _⟩ := gInv_fold w n a N numWin y hw hN hN2 hrun numWin (le_refl _)
  rw [gidney_target_val_eq_sum_when_bits_match (n + 2)
        (∑ j ∈ Finset.range numWin, WindowedArith.tableValue a N w j (WindowedArith.window w y j))
        _ (fun i hi => by
          rw [hblock (target_idx i) (by simp only [target_idx]; omega), adder_input_F_at_target];
          simp [hi])]
  exact Nat.mod_eq_of_lt hSlt

/-- **★ THE COSET VALUE-BRIDGE ★** — the whole runway multiplier computes `y ↦ (a·y) mod N`: the
    accumulator's residue mod `N` is exactly `(a·y) mod N`.  The runway holds an UNREDUCED coset
    representative; reducing once (the coset readout) recovers the modular product — exactly the
    Gidney/Babbush coset multiplier, now on an ALL-temporary-AND verified circuit.  Reuses the
    layout-free arithmetic identity `WindowedArith.windowed_modProductAdd`. -/
theorem gidneyRunwayMul_residue (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2)) (hrun : numWin * N ≤ 2 ^ (n + 2))
    (hy : y < (2 ^ w) ^ numWin) :
    (gidney_target_val (n + 2)
        (EGate.applyNat (gidneyRunwayMul w n a N numWin) (gMulInput w n numWin y))) % N
      = (a * y) % N := by
  rw [gidneyRunwayMul_value w n a N numWin y hw hN hN2 hrun]
  exact WindowedArith.windowed_modProductAdd w numWin a N y hy

/-- **★ THE ACCUMULATOR IS A COSET REPRESENTATIVE OF `a·y` ★** — in the canonical coset interface:
    the runway register value reduces to `(a·y) mod N` and fits the padded `n+2`-bit register.  This
    is precisely the invariant the Gidney coset-eigenstate Shor wrapper consumes. -/
theorem gidneyRunwayMul_isCosetRep (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2)) (hrun : numWin * N ≤ 2 ^ (n + 2))
    (hy : y < (2 ^ w) ^ numWin) :
    FormalRV.Shor.WindowedCoset.IsCosetRep (n + 2) N
      (gidney_target_val (n + 2)
        (EGate.applyNat (gidneyRunwayMul w n a N numWin) (gMulInput w n numWin y)))
      (a * y) :=
  ⟨by rw [gidneyRunwayMul_residue w n a N numWin y hw hN hN2 hrun hy],
   by rw [gidneyRunwayMul_value w n a N numWin y hw hN hN2 hrun]
      exact runwaySum_lt w n a N numWin y hN hrun⟩

/-- **The coset readout recovers `(a·y) mod N`.** -/
theorem gidneyRunwayMul_cosetValue (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 2)) (hrun : numWin * N ≤ 2 ^ (n + 2))
    (hy : y < (2 ^ w) ^ numWin) :
    FormalRV.Shor.WindowedCoset.cosetValue N
      (gidney_target_val (n + 2)
        (EGate.applyNat (gidneyRunwayMul w n a N numWin) (gMulInput w n numWin y)))
      = (a * y) % N :=
  FormalRV.Shor.WindowedCoset.cosetValue_of_isCosetRep
    (gidneyRunwayMul_isCosetRep w n a N numWin y hw hN hN2 hrun hy)

/-! ### Counts — `numWin ×` the per-window step, all temporary AND. -/

private theorem tcount_foldl_step (step : Nat → EGate) (c : Nat) (hc : ∀ j, EGate.tcount (step j) = c) :
    ∀ m, EGate.tcount
        ((List.range m).foldl (fun g j => EGate.seq g (step j)) (EGate.base Gate.I)) = m * c := by
  intro m
  induction m with
  | zero => simp [List.range_zero, EGate.tcount, Gate.tcount]
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      show EGate.tcount ((List.range k).foldl (fun g j => EGate.seq g (step j)) (EGate.base Gate.I))
          + EGate.tcount (step k) = (k + 1) * c
      rw [ih, hc k]; ring

theorem tcount_gidneyRunwayStep (w n a N numWin j : Nat) :
    EGate.tcount (gidneyRunwayStep w n a N numWin j) = 7 * ((2 ^ w - 1) + (n + 2)) := by
  unfold gidneyRunwayStep
  exact tcount_gidneyStepGen w (aIdxAt w n j) (gCAnc w n numWin) (gCtrl w n numWin) n _

theorem tcount_gidneyRunwayMul (w n a N numWin : Nat) :
    EGate.tcount (gidneyRunwayMul w n a N numWin) = numWin * (7 * ((2 ^ w - 1) + (n + 2))) := by
  unfold gidneyRunwayMul gidneyRunwayMulN
  exact tcount_foldl_step (gidneyRunwayStep w n a N numWin) _
    (fun j => tcount_gidneyRunwayStep w n a N numWin j) numWin

/-- **Whole-multiplier Toffoli count: `numWin·((2^w − 1) + bits)`** (the Babbush `2^w − 1` lookup +
    the `bits`-Toffoli measured adder, per window). -/
theorem toffoli_gidneyRunwayMul (w n a N numWin : Nat) :
    EGate.toffoli (gidneyRunwayMul w n a N numWin) = numWin * ((2 ^ w - 1) + (n + 2)) := by
  unfold EGate.toffoli
  rw [tcount_gidneyRunwayMul,
      show numWin * (7 * ((2 ^ w - 1) + (n + 2))) = (numWin * ((2 ^ w - 1) + (n + 2))) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **★ WHOLE-MULTIPLIER GADGET-BY-GADGET-HONEST T-COUNT ★** — every gadget in every window is a
    genuine temporary AND (Babbush merged-AND load + measured Gidney adder + `mz`-clears), so the
    uniform Gidney 4-T model is exact: `gidneyTCount = numWin·(4·((2^w − 1) + bits))`. -/
theorem gidneyTCount_gidneyRunwayMul (w n a N numWin : Nat) :
    gidneyTCount (gidneyRunwayMul w n a N numWin) = numWin * (4 * ((2 ^ w - 1) + (n + 2))) := by
  unfold gidneyTCount FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_gidneyRunwayMul]; ring

end FormalRV.Shor.GidneyRunwayMul
