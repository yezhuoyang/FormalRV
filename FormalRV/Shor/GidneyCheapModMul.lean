/-
  FormalRV.Shor.GidneyCheapModMul — the CHEAP, value-composed windowed mod-N multiplier:
  `y ↦ (a·y) mod N`, EXACTLY (reduced, accumulator stays `< N`), at the all-temporary-AND Gidney
  layout, using the keystone register-register measured modular adder.

  ## Why this exists (the no-cheating, paper-structure multiplier)

  `GidneyRunwayMul` is the COSET multiplier (lookup + add, NO per-step reduce → runway).  Its
  count is paper-faithful but its output is a coset rep, not the exact residue.  The papers' cheap
  count actually comes from a per-step *measured modular* add (`~3·bits`, the keystone), keeping the
  accumulator reduced.  This file is that multiplier: per window, the Babbush merged-AND lookup
  (`2^w − 1`) writes `T_j[windowⱼ y]` into the read register, and the keystone
  `gidneyModAddRegMeasured` adds it into the accumulator mod `N`.  The accumulator stays `< N`, so
  the value is the EXACT reduced product `(a·y) mod N` (`WindowedArith.windowedLookupFold_eq_modmul`)
  — a clean permutation oracle, on the SAME circuit whose count is the paper structure.

  `gcMul_value`: `gidney_target_val bits (the whole circuit on the clean input) = (a·y) mod N`.
  Every gadget is a temporary AND (Babbush merged-AND + the measured modular adder).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.ModularAdder.GidneyModAddReg
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Resource
import FormalRV.Arithmetic.Windowed.WindowedArith

namespace FormalRV.Shor.GidneyCheapModMul

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasuredBabbushRead
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Arithmetic.ModularAdder.GidneyModAddReg
open FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
open FormalRV.Shor.GidneyTCount
open FormalRV.Shor.GidneyRunwayMul

/-! ## §1. Layout: the accumulator/adder block at base 0, the y-register/lookup above the flag. -/

/-- The keystone's fixup-flag ancilla index. -/
def gcFlag (bits : Nat) : Nat := adder_n_qubits (bits + 1)

/-- The y-register base (just above the flag). -/
def gcYBase (bits : Nat) : Nat := adder_n_qubits (bits + 1) + 1

/-- The lookup AND-ancilla map. -/
def gcCAnc (w bits numWin : Nat) : Nat → Nat := fun i => gcYBase bits + numWin * w + i

/-- The lookup root control. -/
def gcCtrl (w bits numWin : Nat) : Nat := gcYBase bits + numWin * w + w

/-- Window-`j` address map (points at the `j`-th width-`w` slice of the y-register). -/
def gcAIdxAt (w bits j : Nat) : Nat → Nat := fun i => gcYBase bits + j * w + i

/-! ## §2. The per-window step and the fold. -/

/-- Biased lookup table: stores `2^(bits+1) − (N − T[v])` so the keystone's single measured add lands
    the reduced value directly (the `−N` of the modular reduction folded into the table — free). -/
def biasedTableValue (a N bits w j : Nat) : Nat → Nat :=
  fun v => 2 ^ (bits + 1) - (N - WindowedArith.tableValue a N w j v)

/-- The per-window step: Babbush merged-AND lookup of the BIASED `2^(bits+1) − (N − T_j[windowⱼ y])`
    into the read register, then the keystone register-register measured modular add into the
    accumulator mod `N`. -/
def gcStep (w bits a N numWin j : Nat) : EGate :=
  EGate.seq
    (unaryQROMPos (gcAIdxAt w bits j) (gcCAnc w bits numWin) read_idx (bits + 1)
      (biasedTableValue a N bits w j) w (gcCtrl w bits numWin) 0)
    (gidneyModAddRegMeasured bits N)

/-- The first `m` windows. -/
def gcMulN (w bits a N numWin m : Nat) : EGate :=
  (List.range m).foldl (fun g j => EGate.seq g (gcStep w bits a N numWin j)) (EGate.base Gate.I)

/-- The whole cheap value-composed windowed mod-N multiplier. -/
def gcMul (w bits a N numWin : Nat) : EGate := gcMulN w bits a N numWin numWin

/-- The clean-state invariant for accumulator value `acc < N`. -/
def GCInv (w bits numWin y acc : Nat) (g : Nat → Bool) : Prop :=
  (∀ q, q < adder_n_qubits (bits + 1) → g q = adder_input_F (bits + 1) 0 acc q)
  ∧ g (gcFlag bits) = false
  ∧ (∀ k, k < numWin * w → g (gcYBase bits + k) = y.testBit k)
  ∧ (∀ i, i < w → g (gcCAnc w bits numWin i) = false)
  ∧ g (gcCtrl w bits numWin) = true

/-! ## §3. Single-step preservation (the crux). -/

theorem gcInv_step (w n a N numWin y acc j : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1))
    (hbw : numWin * w = n + 1) (hj : j < numWin) (hacc : acc < N)
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin y acc g) :
    GCInv w (n + 1) numWin y
        ((acc + WindowedArith.tableValue a N w j (WindowedArith.window w y j)) % N)
        (EGate.applyNat (gcStep w (n + 1) a N numWin j) g) := by
  obtain ⟨hblock, hflag, hy, hanc, hctrl⟩ := hg
  set bits := n + 1 with hbitsdef
  set v := WindowedArith.window w y j with hv_def
  set Tv := WindowedArith.tableValue a N w j v with hTv_def
  set biasedTv := 2 ^ (bits + 1) - (N - Tv) with hbTv_def
  have hv_lt : v < 2 ^ w := WindowedArith.window_lt w y j
  have hTv_ltN : Tv < N := by rw [hTv_def]; unfold WindowedArith.tableValue; exact Nat.mod_lt _ hN
  have hTv_lt : Tv < 2 ^ bits := lt_of_lt_of_le hTv_ltN hN2
  have hacc_lt : acc < 2 ^ bits := lt_of_lt_of_le hacc hN2
  have hjwin : j * w + w ≤ numWin * w := by
    calc j * w + w = (j + 1) * w := by ring
    _ ≤ numWin * w := Nat.mul_le_mul_right w hj
  have hgY : gcYBase bits = adder_n_qubits (bits + 1) + 1 := rfl
  have hYadd : adder_n_qubits (bits + 1) = 3 * (bits + 1) + 2 := by unfold adder_n_qubits; ring
  -- ===== address decode =====
  have haddr : ∀ i, i < w → g (gcAIdxAt w bits j i) = v.testBit i := by
    intro i hi
    have hk : j * w + i < numWin * w := by omega
    have he : gcAIdxAt w bits j i = gcYBase bits + (j * w + i) := by unfold gcAIdxAt; ring
    rw [he, hy (j * w + i) hk, hv_def, FormalRV.Shor.WindowedCircuit.window_testBit w y j i hi]
  have hdec : decodeReg (gcAIdxAt w bits j) w g = v := by
    rw [FormalRV.Shor.WindowedCircuit.decodeReg_eq_mod_of_testBit (gcAIdxAt w bits j) w v g haddr,
        Nat.mod_eq_of_lt hv_lt]
  -- ===== lookup disjointness =====
  have hpos_inj : ∀ a' b', a' < bits + 1 → b' < bits + 1 → read_idx a' = read_idx b' → a' = b' := by
    intro a' b' _ _ h; simp only [read_idx] at h; omega
  have hc_inj : ∀ i i', gcCAnc w bits numWin i = gcCAnc w bits numWin i' → i = i' := by
    intro i i' h; simp only [gcCAnc] at h; omega
  have h_anc_out : ∀ i jj, i < w → jj < bits + 1 → gcCAnc w bits numWin i ≠ read_idx jj := by
    intro i jj _ hjj; simp only [gcCAnc, gcYBase, read_idx, hYadd]; omega
  have h_anc_addr : ∀ i i', i < w → i' < w → gcCAnc w bits numWin i ≠ gcAIdxAt w bits j i' := by
    intro i i' _ hi'; simp only [gcCAnc, gcAIdxAt]; omega
  have h_addr_out : ∀ i jj, i < w → jj < bits + 1 → gcAIdxAt w bits j i ≠ read_idx jj := by
    intro i jj _ hjj; simp only [gcAIdxAt, gcYBase, read_idx, hYadd]; omega
  have h_ctrl_out : ∀ jj, jj < bits + 1 → gcCtrl w bits numWin ≠ read_idx jj := by
    intro jj hjj; simp only [gcCtrl, gcYBase, read_idx, hYadd]; omega
  have h_ctrl_anc : ∀ i, i < w → gcCtrl w bits numWin ≠ gcCAnc w bits numWin i := by
    intro i hi; simp only [gcCtrl, gcCAnc]; omega
  have hsel := unaryQROMPos_selects_word (gcAIdxAt w bits j) (gcCAnc w bits numWin) read_idx (bits + 1)
    (biasedTableValue a N bits w j) hpos_inj hc_inj w (gcCtrl w bits numWin) 0 g
    h_anc_out h_anc_addr h_addr_out h_ctrl_out h_ctrl_anc hanc
  set gl := EGate.applyNat (unaryQROMPos (gcAIdxAt w bits j) (gcCAnc w bits numWin) read_idx (bits + 1)
    (biasedTableValue a N bits w j) w (gcCtrl w bits numWin) 0) g with hgl
  -- gl reads: read register = biasedTv on [0,bits+1)
  have hgl_read : ∀ i, i < bits + 1 → gl (read_idx i) = biasedTv.testBit i := by
    intro i hi
    have := hsel i hi
    rw [hctrl, Bool.true_and, Nat.zero_add, hdec] at this
    simp only [biasedTableValue] at this
    rw [← hTv_def, ← hbTv_def] at this
    have hg0 : g (read_idx i) = false := by
      rw [hblock (read_idx i) (by simp only [read_idx, hYadd]; omega), adder_input_F_at_read]; simp
    rw [this, hg0, Bool.false_xor]
  -- gl frame: off the read word and the ancilla, gl = g
  have hgl_frame : ∀ q, (∀ jj, jj < bits + 1 → q ≠ read_idx jj) →
      (∀ i, i < w → q ≠ gcCAnc w bits numWin i) → gl q = g q := by
    intro q hqr hqc
    rw [hgl]
    show EGate.applyNat (unaryQROMPos _ _ _ _ _ _ _ _) g q = _
    exact unaryQROMPos_frame (gcAIdxAt w bits j) (gcCAnc w bits numWin) read_idx (bits + 1)
      (biasedTableValue a N bits w j) w (gcCtrl w bits numWin) 0 g q hqr hqc
  have hgl_anc : ∀ i, i < w → gl (gcCAnc w bits numWin i) = false := by
    intro i hi
    rw [hgl]
    show EGate.applyNat (unaryQROMPos _ _ _ _ _ _ _ _) g (gcCAnc w bits numWin i) = _
    rw [unaryQROMPos_anc_cleared (gcAIdxAt w bits j) (gcCAnc w bits numWin) read_idx (bits + 1)
      (biasedTableValue a N bits w j) hc_inj w (gcCtrl w bits numWin) 0 g i hi]
  -- gl = adder_input_F (bits+1) biasedTv acc on q < adder_n_qubits(bits+1)+1 (block + slack + flag)
  have hgl_block : ∀ q, q < adder_n_qubits (bits + 1) + 1 → gl q = adder_input_F (bits + 1) biasedTv acc q := by
    intro q hq
    -- the lookup ancilla sits at/above gcYBase = B, so it never collides with q < B
    have hq_anc : ∀ i, i < w → q ≠ gcCAnc w bits numWin i := by
      intro i hi; simp only [gcCAnc, gcYBase]; omega
    by_cases hread_written : q % 3 = 0 ∧ q / 3 < bits + 1
    · -- a lookup-written read index: reads biasedTv directly
      obtain ⟨hmod, hjlt⟩ := hread_written
      have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
      rw [hqr, hgl_read _ hjlt, adder_input_F_at_read,
          decide_eq_true (show q / 3 < bits + 1 by omega), Bool.true_and]
    · -- NOT a written read index: the lookup frames it, gl = g
      have hframe_jj : ∀ jj, jj < bits + 1 → q ≠ read_idx jj := by
        intro jj hjj heq
        exact hread_written ⟨by rw [heq]; simp only [read_idx]; omega,
                             by rw [heq]; simp only [read_idx]; omega⟩
      rw [hgl_frame q hframe_jj hq_anc]
      by_cases hqflag : q = adder_n_qubits (bits + 1)
      · -- the fixup-flag ancilla: g = false (hflag), literal carry = false
        have hlhs : g q = false := by rw [hqflag]; exact hflag
        have hcarry_eq : adder_n_qubits (bits + 1) = carry_idx (bits + 1) := by
          simp only [adder_n_qubits, carry_idx]
        have hrhs : adder_input_F (bits + 1) biasedTv acc q = false := by
          rw [hqflag, hcarry_eq, adder_input_F_at_carry]
        rw [hlhs, hrhs]
      · -- strictly below the flag: hblock gives g = adder_input_F 0 acc
        have hqlt : q < adder_n_qubits (bits + 1) := by omega
        rw [hblock q hqlt]
        rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h | h
        · -- read index strictly above the written word (q/3 = bits+1): both decode false
          have hjge : bits + 1 ≤ q / 3 := by
            by_contra hlt; push_neg at hlt; exact hread_written ⟨h, hlt⟩
          have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
          rw [hqr, adder_input_F_at_read, adder_input_F_at_read,
              decide_eq_false (show ¬ (q / 3 < bits + 1) by omega)]
          simp
        · have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
          rw [hqt, adder_input_F_at_target, adder_input_F_at_target]
        · have hqc : q = carry_idx (q / 3) := by simp only [carry_idx]; omega
          rw [hqc, adder_input_F_at_carry, adder_input_F_at_carry]
  -- ===== run the keystone modular adder =====
  set gf := EGate.applyNat (gidneyModAddRegMeasured bits N) gl with hgf
  set B := adder_n_qubits (bits + 1) + 1 with hBdef
  have hbnd : EGate.boundedBy B (gidneyModAddRegMeasured bits N) :=
    gidneyModAddRegMeasured_boundedBy n N
  have hcongr : ∀ q, q < B →
      gf q = EGate.applyNat (gidneyModAddRegMeasured bits N) (adder_input_F (bits + 1) biasedTv acc) q :=
    fun q hq => EGate.applyNat_congr_lt B (gidneyModAddRegMeasured bits N) hbnd gl
      (adder_input_F (bits + 1) biasedTv acc) hgl_block q hq
  have hgf_high : ∀ q, B ≤ q → gf q = gl q :=
    fun q hq => EGate_applyNat_ge_of_boundedBy B (gidneyModAddRegMeasured bits N) hbnd gl q hq
  -- the keystone's per-bit post-state on the literal biased input `adder_input_F (bits+1) biasedTv acc`
  obtain ⟨_, hk_Q, hk_flag, hk_tgt, hk_read, hk_carry⟩ :=
    gidneyModAddRegMeasured_correct bits N Tv acc (by omega) hN hN2 hacc hTv_ltN
  -- fold the keystone's literal addend `2^(bits+1) − (N − Tv)` into `biasedTv`
  rw [← hbTv_def] at hk_Q hk_flag hk_tgt hk_read hk_carry
  set acc' := (acc + Tv) % N with hacc'def
  have hacc'_lt : acc' < 2 ^ bits := by
    rw [hacc'def]; exact lt_of_lt_of_le (Nat.mod_lt _ hN) hN2
  -- gf is FALSE on the two slack slots {read_idx(bits+1), target_idx(bits+1)} — slack preservation
  -- carries them through the keystone, and the literal addend is 0 there.
  have hgf_slack : ∀ q, 3 * (bits + 1) ≤ q → q < adder_n_qubits (bits + 1) → gf q = false := by
    intro q hlo hhi
    have hslackpres : EGate.applyNat (gidneyModAddRegMeasured bits N)
          (adder_input_F (bits + 1) biasedTv acc) q = adder_input_F (bits + 1) biasedTv acc q :=
      gidneyModAddRegMeasured_preserves_slack n N q hlo hhi (adder_input_F (bits + 1) biasedTv acc)
    have hqB : q < B := by rw [hBdef]; omega
    rw [hcongr q hqB, hslackpres]
    rw [hYadd] at hhi
    rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h | h
    · rw [show q = read_idx (bits + 1) by simp only [read_idx]; omega, adder_input_F_at_read]; simp
    · rw [show q = target_idx (bits + 1) by simp only [target_idx]; omega, adder_input_F_at_target]; simp
    · omega
  -- ===== assemble the post-step invariant =====
  rw [show (EGate.applyNat (gcStep w bits a N numWin j) g) = gf from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- block of gf = adder_input_F (bits+1) 0 acc'
    intro q hq
    by_cases hslack : 3 * (bits + 1) ≤ q
    · -- the two slack slots {read_idx(bits+1), target_idx(bits+1)}: gf = 0 = literal addend 0
      rw [hgf_slack q hslack hq]
      rw [hYadd] at hq
      rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h | h
      · rw [show q = read_idx (bits + 1) by simp only [read_idx]; omega, adder_input_F_at_read]; simp
      · rw [show q = target_idx (bits + 1) by simp only [target_idx]; omega, adder_input_F_at_target]; simp
      · omega
    · push_neg at hslack
      have hqB : q < B := by rw [hBdef, hYadd]; omega
      rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h | h
      · have hjW : q / 3 < bits + 1 := by omega
        have hqr : q = read_idx (q / 3) := by simp only [read_idx]; omega
        rw [hqr, hcongr _ (by rw [← hqr]; exact hqB), hk_read _ hjW, adder_input_F_at_read]; simp
      · have hjW : q / 3 < bits + 1 := by omega
        have hqt : q = target_idx (q / 3) := by simp only [target_idx]; omega
        rw [hqt, hcongr _ (by rw [← hqt]; exact hqB)]
        by_cases hjbits : q / 3 < bits
        · rw [hk_tgt _ hjbits, adder_input_F_at_target,
              decide_eq_true (show q / 3 < bits + 1 by omega), Bool.true_and, hacc'def]
        · -- q/3 = bits : Q = 0 ; adder_input_F 0 acc' at target_idx bits = acc'.testBit bits = 0
          have hqeq : q / 3 = bits := by omega
          rw [hqeq, hk_Q, adder_input_F_at_target, Nat.testBit_lt_two_pow hacc'_lt]; simp
      · have hjW : q / 3 < bits + 1 := by omega
        have hqc : q = carry_idx (q / 3) := by simp only [carry_idx]; omega
        rw [hqc, hcongr _ (by rw [← hqc]; exact hqB), hk_carry _ hjW, adder_input_F_at_carry]
  · -- flag = 0
    show gf (gcFlag bits) = false
    rw [hcongr (gcFlag bits) (by simp only [gcFlag, hBdef]; omega)]
    exact hk_flag
  · -- y-register preserved
    intro k hk
    rw [hgf_high _ (by simp only [gcYBase, hBdef] at *; omega),
        hgl_frame _ (fun jj _ => by simp only [gcYBase, read_idx, hYadd]; omega)
          (fun i _ => by simp only [gcYBase, gcCAnc]; omega)]
    exact hy k hk
  · -- ancilla cleared
    intro i hi
    rw [hgf_high _ (by simp only [gcCAnc, gcYBase, hBdef]; omega)]
    exact hgl_anc i hi
  · -- control preserved
    rw [hgf_high _ (by simp only [gcCtrl, gcYBase, hBdef]; omega),
        hgl_frame _ (fun jj _ => by simp only [gcCtrl, gcYBase, read_idx, hYadd]; omega)
          (fun i hi => h_ctrl_anc i hi)]
    exact hctrl

/-! ## §4. The fold over all windows, and the whole-multiplier value `(a·y) mod N`. -/

/-- **The reduced fold holds after every prefix of windows.**  Starting from any clean `GCInv … 0`
    input, after the first `m ≤ numWin` windows the accumulator is the per-step-reduced lookup-fold
    `windowedLookupFold a N w (windowⱼ y) m 0` (the running `(… ) mod N`, always `< N` — no runway). -/
theorem gcInv_fold (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin y 0 g) :
    ∀ m, m ≤ numWin →
      GCInv w (n + 1) numWin y
          (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m 0)
          (EGate.applyNat (gcMulN w (n + 1) a N numWin m) g) := by
  have hfoldlt : ∀ m, WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m 0 < N := by
    intro m; cases m with
    | zero => exact hN
    | succ k => exact Nat.mod_lt _ hN
  intro m
  induction m with
  | zero =>
      intro _
      have he : EGate.applyNat (gcMulN w (n + 1) a N numWin 0) g = g := by
        simp [gcMulN, EGate.applyNat, Gate.applyNat_I]
      rw [show WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) 0 0 = 0 from rfl, he]
      exact hg
  | succ m ih =>
      intro hm
      have hkn : m < numWin := by omega
      have hsplit : gcMulN w (n + 1) a N numWin (m + 1)
          = EGate.seq (gcMulN w (n + 1) a N numWin m) (gcStep w (n + 1) a N numWin m) := by
        unfold gcMulN
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      show GCInv w (n + 1) numWin y
          (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) (m + 1) 0)
          (EGate.applyNat (gcStep w (n + 1) a N numWin m)
            (EGate.applyNat (gcMulN w (n + 1) a N numWin m) g))
      rw [show WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) (m + 1) 0
            = (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m 0
                + WindowedArith.tableValue a N w m (WindowedArith.window w y m)) % N from rfl]
      exact gcInv_step w n a N numWin y
        (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) m 0) m
        hw hN hN2 hbw hkn (hfoldlt m) _ (ih (by omega))

/-- **★ THE WHOLE CHEAP MULTIPLIER VALUE ★** — `y ↦ (a·y) mod N`, EXACTLY (no coset readout): from
    any clean `GCInv … 0` input, the accumulator's low `n+1` value bits decode to `(a·y) mod N`.  The
    per-step reduction keeps the accumulator `< N ≤ 2^(n+1)`, so the integer value IS the residue;
    closes via the layout-free identity `WindowedArith.windowedLookupFold_eq_modmul`. -/
theorem gcMul_value (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (hy : y < (2 ^ w) ^ numWin)
    (g : Nat → Bool) (hg : GCInv w (n + 1) numWin y 0 g) :
    gidney_target_val (n + 1) (EGate.applyNat (gcMul w (n + 1) a N numWin) g) = (a * y) % N := by
  rw [show gcMul w (n + 1) a N numWin = gcMulN w (n + 1) a N numWin numWin from rfl]
  obtain ⟨hblock, _, _, _, _⟩ :=
    gcInv_fold w n a N numWin y hw hN hN2 hbw g hg numWin (le_refl _)
  have hval : WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0 = (a * y) % N :=
    WindowedArith.windowedLookupFold_eq_modmul a N w numWin y hN hy
  have hdecode : gidney_target_val (n + 1) (EGate.applyNat (gcMulN w (n + 1) a N numWin numWin) g)
      = WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0 % 2 ^ (n + 1) := by
    apply FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.gidney_target_val_low (n + 1)
      (WindowedArith.windowedLookupFold a N w (WindowedArith.window w y) numWin 0)
    intro i hi
    rw [hblock (target_idx i) (by simp only [target_idx, adder_n_qubits]; omega),
        adder_input_F_at_target, decide_eq_true (show i < (n + 1) + 1 by omega), Bool.true_and]
  rw [hdecode, hval, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hN) hN2)]

/-! ## §5. The clean input state and the concrete value corollary. -/

/-- The clean cheap-multiplier input: accumulator/target block all clear (`acc = 0`), the y-register
    holds `y`, the lookup ancilla clear, the root control set. -/
def gcInit (w bits numWin y : Nat) : Nat → Bool := fun q =>
  if q = gcCtrl w bits numWin then true
  else if gcYBase bits ≤ q ∧ q < gcYBase bits + numWin * w then y.testBit (q - gcYBase bits)
  else false

theorem gcInv_init (w bits numWin y : Nat) : GCInv w bits numWin y 0 (gcInit w bits numWin y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [adder_input_F_zero]
    unfold gcInit
    rw [if_neg (by simp only [gcCtrl, gcYBase]; omega), if_neg (by simp only [gcYBase]; omega)]
  · unfold gcInit
    rw [if_neg (by simp only [gcFlag, gcCtrl, gcYBase]; omega),
        if_neg (by simp only [gcFlag, gcYBase]; omega)]
  · intro k hk
    unfold gcInit
    rw [if_neg (by simp only [gcCtrl, gcYBase]; omega), if_pos ⟨by omega, by omega⟩]
    congr 1; omega
  · intro i hi
    unfold gcInit
    rw [if_neg (by simp only [gcCtrl, gcCAnc, gcYBase]; omega),
        if_neg (by simp only [gcCAnc, gcYBase]; omega)]
  · unfold gcInit; rw [if_pos rfl]

/-- **★ CONCRETE WHOLE-MULTIPLIER VALUE ★** — on the canonical clean input `gcInit`, the cheap
    windowed multiplier computes `y ↦ (a·y) mod N` exactly. -/
theorem gcMul_value_init (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (hy : y < (2 ^ w) ^ numWin) :
    gidney_target_val (n + 1)
        (EGate.applyNat (gcMul w (n + 1) a N numWin) (gcInit w (n + 1) numWin y)) = (a * y) % N :=
  gcMul_value w n a N numWin y hw hN hN2 hbw hy _ (gcInv_init w (n + 1) numWin y)

/-! ## §6. The Toffoli count — on the SAME object whose value is `(a·y) mod N`.

Every gadget is a measured temporary AND.  Per window: the Babbush merged-AND lookup
(`unaryQROMPos`, `2^w − 1` Toffoli) + the COST-OPTIMAL biased keystone modular adder (TWO measured
`n`-Toffoli adds = `2·(bits+1)` Toffoli — the `−p` reduction folded into the biased lookup table).
No carry-ancilla reuse cheat, no flat-lookup blow-up: this is the cheapest honest per-window cost,
and it rides the value-correct `gcMul`. -/

/-- The keystone modular adder costs `14·(bits+1) = 2·7·(bits+1)` T — TWO measured Gidney adds
    (biased front register-add + conditional `+p`); the `mz`/CX/prepare gadgets are T-free.  The
    naive third add (`subtract-p`) is eliminated by folding `−p` into the BIASED lookup table. -/
theorem tcount_gidneyModAddRegMeasured (n N : Nat) :
    EGate.tcount (gidneyModAddRegMeasured (n + 1) N) = 14 * (n + 2) := by
  have hadd : EGate.tcount (gidneyAdderMeasured (n + 2) 0) = 7 * (n + 2) := by
    show EGate.tcount (EGate.seq (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
        (gidney_final_cx_cascade (n + 2)))) (gidneyMeasFullReverse (n + 2))) = 7 * (n + 2)
    simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
      tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]
  have hstruct : EGate.tcount (gidneyModAddRegMeasured (n + 1) N)
      = EGate.tcount (gidneyAdderMeasured (n + 2) 0)
        + EGate.tcount (mzList ((List.range (n + 2)).map read_idx))
        + EGate.tcount (EGate.base (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2))))
        + (EGate.tcount (conditionalAddP (n + 2) (adder_n_qubits (n + 2)) N)
          + EGate.tcount (EGate.mz (adder_n_qubits (n + 2)))) := rfl
  rw [hstruct, hadd, tcount_mzList,
      FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.tcount_conditionalAddP]
  simp only [EGate.tcount, Gate.tcount]
  ring

/-- T-count of one cheap window step: `7·((2^w − 1) + 2·(bits+1))` (biased lookup + 2-add keystone). -/
theorem tcount_gcStep (w n a N numWin j : Nat) :
    EGate.tcount (gcStep w (n + 1) a N numWin j) = 7 * ((2 ^ w - 1) + 2 * (n + 2)) := by
  have hstruct : EGate.tcount (gcStep w (n + 1) a N numWin j)
      = EGate.tcount (unaryQROMPos (gcAIdxAt w (n + 1) j) (gcCAnc w (n + 1) numWin) read_idx (n + 2)
          (biasedTableValue a N (n + 1) w j) w (gcCtrl w (n + 1) numWin) 0)
        + EGate.tcount (gidneyModAddRegMeasured (n + 1) N) := rfl
  rw [hstruct, tcount_unaryQROMPos, tcount_gidneyModAddRegMeasured]; ring

/-- T-count of the whole `m`-window cheap multiplier: `m · 7·((2^w − 1) + 2·(bits+1))`. -/
theorem tcount_gcMulN (w n a N numWin m : Nat) :
    EGate.tcount (gcMulN w (n + 1) a N numWin m) = m * (7 * ((2 ^ w - 1) + 2 * (n + 2))) := by
  induction m with
  | zero => simp [gcMulN, EGate.tcount, Gate.tcount]
  | succ k ih =>
      have hsplit : gcMulN w (n + 1) a N numWin (k + 1)
          = EGate.seq (gcMulN w (n + 1) a N numWin k) (gcStep w (n + 1) a N numWin k) := by
        unfold gcMulN; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit]
      show EGate.tcount (gcMulN w (n + 1) a N numWin k)
          + EGate.tcount (gcStep w (n + 1) a N numWin k) = (k + 1) * (7 * ((2 ^ w - 1) + 2 * (n + 2)))
      rw [ih, tcount_gcStep]; ring

/-- **★ THE CHEAP MULTIPLIER TOFFOLI COUNT ★** — `numWin · ((2^w − 1) + 2·(bits+1))`, on the SAME
    `gcMul` object whose value is `(a·y) mod N`.  Babbush merged-AND lookup (`2^w − 1`) + the
    biased 2-add keystone (`2·(bits+1)`) per window — the cheapest honest per-step-reduced count,
    every gadget a measured temporary AND.  (`bits + 1 = n + 2`.) -/
theorem toffoli_gcMul (w n a N numWin : Nat) :
    EGate.toffoli (gcMul w (n + 1) a N numWin) = numWin * ((2 ^ w - 1) + 2 * (n + 2)) := by
  unfold gcMul EGate.toffoli
  rw [tcount_gcMulN, show numWin * (7 * ((2 ^ w - 1) + 2 * (n + 2)))
        = (numWin * ((2 ^ w - 1) + 2 * (n + 2))) * 7 by ring, Nat.mul_div_cancel _ (by norm_num)]

/-- The Gidney temporary-AND T-count (`4·` Toffoli, the 2018 logical-AND model):
    `4 · numWin · ((2^w − 1) + 2·(bits+1))`, gadget-by-gadget honest. -/
theorem gidneyTCount_gcMul (w n a N numWin : Nat) :
    gidneyTCount (gcMul w (n + 1) a N numWin) = 4 * (numWin * ((2 ^ w - 1) + 2 * (n + 2))) := by
  unfold gidneyTCount FormalRV.PaperClaims.gidney_2018_logical_AND_compute_tcount
  rw [toffoli_gcMul]

/-- **★ VALUE ∧ COUNT ON ONE OBJECT (no cheating) ★** — the cheap windowed multiplier `gcMul`
    SIMULTANEOUSLY (i) computes `y ↦ (a·y) mod N` exactly on the clean input, and (ii) has measured
    Toffoli count `numWin · ((2^w − 1) + 2·(bits+1))`.  The count rides the EXACT-value circuit —
    the resource theorem is about the SAME syntactic `EGate` whose semantics is verified, every
    gadget a measured temporary AND, no coset readout, no flat-lookup blow-up, no carry-reuse cheat. -/
theorem gcMul_value_and_count (w n a N numWin y : Nat)
    (hw : 0 < w) (hN : 0 < N) (hN2 : N ≤ 2 ^ (n + 1)) (hbw : numWin * w = n + 1)
    (hy : y < (2 ^ w) ^ numWin) :
    gidney_target_val (n + 1)
        (EGate.applyNat (gcMul w (n + 1) a N numWin) (gcInit w (n + 1) numWin y)) = (a * y) % N
    ∧ EGate.toffoli (gcMul w (n + 1) a N numWin) = numWin * ((2 ^ w - 1) + 2 * (n + 2)) :=
  ⟨gcMul_value_init w n a N numWin y hw hN hN2 hbw hy, toffoli_gcMul w n a N numWin⟩

end FormalRV.Shor.GidneyCheapModMul
