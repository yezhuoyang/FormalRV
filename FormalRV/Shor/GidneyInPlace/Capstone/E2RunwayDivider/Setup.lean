/- E2RunwayDivider — Â§0-3 layout + divstep gadget + decode lemma + wellTyped.  Part of the `E2RunwayDivider` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayResidueMul
import FormalRV.Arithmetic.Windowed.WindowedModN
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (compareConstXor_state_general condSub_state_general)


/-! ## §0. Layout constants. -/

/-- Total register dimension: data+read interleaved (`2·bits+1`), flag (`+1`),
    quotient band (`+cm`). -/
def dimDiv (bits cm : Nat) : Nat := 2 * bits + 2 + cm

/-- Quotient band base wire. -/
def qBase (bits : Nat) : Nat := 2 * bits + 2

/-! ## §1. The single divstep gadget. -/

/-- One long-division step on the width-`bits` window at `q_start`, comparing
    against constant `N`, with comparison flag at `flagPos` and quotient bit
    written to `qbit`.  See file header for the four-gate decomposition. -/
def divStep (bits q_start N flagPos qbit : Nat) : Gate :=
  Gate.seq (sqir_style_compareConst_candidate bits q_start N flagPos)
    (Gate.seq (sqir_conditionalSubConstGate bits q_start N flagPos)
      (Gate.seq (Gate.CX flagPos qbit)
        (Gate.CX qbit flagPos)))

/-! ## §2. The single-divstep DECODE lemma. -/

/-- Reduction arithmetic (inlined `modNReduce_arith`): for `r < 2N ≤ 2^bits`,
    `(r + [N ≤ r]·(2^bits − N)) mod 2^bits = r mod N`. -/
theorem divStep_arith (bits N r : Nat)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hr : r < 2 * N) :
    (r + if decide (N ≤ r) = true then 2 ^ bits - N else 0) % 2 ^ bits = r % N := by
  by_cases h : N ≤ r
  · rw [if_pos (by simp [h])]
    have h_eq : r + (2 ^ bits - N) = (r - N) + 2 ^ bits := by omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r - N < 2 ^ bits)]
    have h_rN : r % N = r - N := by
      conv_lhs => rw [show r = N + (r - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : r - N < N)]
    rw [h_rN]
  · rw [if_neg (by simp [Nat.not_le.mpr (Nat.lt_of_not_le h)] : ¬ decide (N ≤ r) = true)]
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega : r < 2 ^ bits),
        Nat.mod_eq_of_lt (Nat.lt_of_not_le h)]

/-- **DIVSTEP DECODE (single step), fully verified.**  On a state `f` with clear
    carry-in / read register / flag / quotient bit, target register holding
    `r < 2N`, and `flagPos`, `qbit` both outside the Cuccaro workspace
    `[q_start, q_start+2·bits+1)` with `qbit ≠ flagPos`:

    after `divStep` the target register holds `r % N`, the quotient bit holds
    `decide (N ≤ r) = r / N`, the flag is restored to `false`, the read register
    and carry stay clear, and everything outside workspace ∪ {flag, qbit} is fixed. -/
theorem divStep_decode
    (bits q_start N flagPos qbit r : Nat)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hr : r < 2 * N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hqbit_out : qbit < q_start ∨ q_start + 2 * bits + 1 ≤ qbit)
    (hqf : qbit ≠ flagPos)
    (f : Nat → Bool)
    (h_cin : f q_start = false)
    (h_flag : f flagPos = false)
    (h_qbit : f qbit = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = r.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    (∀ i, i < bits →
        Gate.applyNat (divStep bits q_start N flagPos qbit) f (q_start + 2 * i + 1)
          = (r % N).testBit i)
    ∧ Gate.applyNat (divStep bits q_start N flagPos qbit) f qbit = decide (N ≤ r)
    ∧ Gate.applyNat (divStep bits q_start N flagPos qbit) f flagPos = false
    ∧ Gate.applyNat (divStep bits q_start N flagPos qbit) f q_start = false
    ∧ (∀ i, i < bits →
        Gate.applyNat (divStep bits q_start N flagPos qbit) f (q_start + 2 * i + 2) = false)
    ∧ (∀ p, p ≠ flagPos → p ≠ qbit →
        p < q_start ∨ q_start + 2 * bits + 1 ≤ p →
        Gate.applyNat (divStep bits q_start N flagPos qbit) f p = f p) := by
  have hr' : r < 2 ^ bits := by omega
  have hN : N ≤ 2 ^ bits := by omega
  -- distinctness facts
  have h_flag_ne_tgt : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 1 := by
    intro i hi; rcases hflag_out with h | h <;> omega
  have h_flag_ne_read : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intro i hi; rcases hflag_out with h | h <;> omega
  have h_flag_ne_cin : flagPos ≠ q_start := by rcases hflag_out with h | h <;> omega
  have h_qbit_ne_tgt : ∀ i, i < bits → qbit ≠ q_start + 2 * i + 1 := by
    intro i hi; rcases hqbit_out with h | h <;> omega
  have h_qbit_ne_read : ∀ i, i < bits → qbit ≠ q_start + 2 * i + 2 := by
    intro i hi; rcases hqbit_out with h | h <;> omega
  have h_qbit_ne_cin : qbit ≠ q_start := by rcases hqbit_out with h | h <;> omega
  -- ===== Stage 1: compareConst sets flag := [N ≤ r]. =====
  have hcmp := compareConstXor_state_general bits q_start N flagPos r f
      hN_pos hN hr' hflag_out h_cin h_tgt h_read
  -- g1 := state after compareConst = update f flagPos [N ≤ r]
  set g1 := update f flagPos (xor (f flagPos) (decide (N ≤ r))) with hg1
  rw [h_flag, Bool.false_xor] at hg1
  -- Reading g1 at the relevant positions.
  have hg1_cin : g1 q_start = false := by
    rw [hg1]; rw [update_neq _ _ _ _ (fun h => h_flag_ne_cin h.symm)]; exact h_cin
  have hg1_flag : g1 flagPos = decide (N ≤ r) := by rw [hg1]; exact update_eq _ _ _
  have hg1_tgt : ∀ i, i < bits → g1 (q_start + 2 * i + 1) = r.testBit i := by
    intro i hi; rw [hg1, update_neq _ _ _ _ (fun h => h_flag_ne_tgt i hi h.symm)]; exact h_tgt i hi
  have hg1_read : ∀ i, i < bits → g1 (q_start + 2 * i + 2) = false := by
    intro i hi; rw [hg1, update_neq _ _ _ _ (fun h => h_flag_ne_read i hi h.symm)]; exact h_read i hi
  have hg1_qbit : g1 qbit = false := by
    rw [hg1, update_neq _ _ _ _ (fun h => (hqf h).elim)]; exact h_qbit
  -- ===== Stage 2: condSub subtracts [N ≤ r]·N from the target. =====
  have hsub := condSub_state_general bits q_start N flagPos r g1 hr'
      hflag_out hg1_cin hg1_tgt hg1_read
  -- g2 := state after condSub.
  set g2 := Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) g1 with hg2
  -- Target bits of g2: r % N.
  have hg2_tgt : ∀ i, i < bits → g2 (q_start + 2 * i + 1) = (r % N).testBit i := by
    intro i hi
    have := hsub.1 i hi
    rw [hg1_flag] at this
    rw [this, divStep_arith bits N r hN_pos hN2 hr]
  have hg2_read : ∀ i, i < bits → g2 (q_start + 2 * i + 2) = false := fun i hi => hsub.2.1 i hi
  have hg2_cin : g2 q_start = false := hsub.2.2.1
  -- frame of condSub at flagPos and qbit (both outside workspace).
  have hg2_flag : g2 flagPos = decide (N ≤ r) := by
    rw [hsub.2.2.2 flagPos hflag_out]; exact hg1_flag
  have hg2_qbit : g2 qbit = false := by
    rw [hsub.2.2.2 qbit hqbit_out]; exact hg1_qbit
  -- ===== Stage 3 + 4: the two CX gates copy the flag to qbit and clean the flag. =====
  -- divStep f = Gate.CX qbit flagPos (Gate.CX flagPos qbit g2).
  have hunfold : Gate.applyNat (divStep bits q_start N flagPos qbit) f
      = Gate.applyNat (Gate.CX qbit flagPos) (Gate.applyNat (Gate.CX flagPos qbit) g2) := by
    show Gate.applyNat (Gate.seq _ (Gate.seq _ (Gate.seq _ _))) f = _
    simp only [Gate.applyNat_seq]
    rw [hcmp]
  -- g3 := after CX flagPos qbit : qbit ^= flag.
  set g3 := Gate.applyNat (Gate.CX flagPos qbit) g2 with hg3
  -- g4 := after CX qbit flagPos : flag ^= qbit.
  set g4 := Gate.applyNat (Gate.CX qbit flagPos) g3 with hg4
  rw [hunfold]
  -- Read g3 (= update g2 qbit (g2 qbit ^ g2 flagPos)).
  have hg3_eq : g3 = update g2 qbit (xor (g2 qbit) (g2 flagPos)) := by rw [hg3, Gate.applyNat_CX]
  -- Read g4 (= update g3 flagPos (g3 flagPos ^ g3 qbit)).
  have hg4_eq : g4 = update g3 flagPos (xor (g3 flagPos) (g3 qbit)) := by rw [hg4, Gate.applyNat_CX]
  -- g3 qbit = false ^ [N≤r] = [N≤r].
  have hg3_qbit : g3 qbit = decide (N ≤ r) := by
    rw [hg3_eq, update_eq, hg2_qbit, hg2_flag, Bool.false_xor]
  -- g3 flagPos = g2 flagPos (qbit ≠ flagPos).
  have hg3_flag : g3 flagPos = decide (N ≤ r) := by
    rw [hg3_eq, update_neq _ _ _ _ hqf.symm]; exact hg2_flag
  -- Now compute each conclusion on g4.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- target band unchanged by the two CX (qbit, flagPos both ≠ target positions).
    intro i hi
    rw [hg4_eq, update_neq _ _ _ _ (fun h => (h_flag_ne_tgt i hi) h.symm), hg3_eq,
        update_neq _ _ _ _ (fun h => (h_qbit_ne_tgt i hi) h.symm)]
    exact hg2_tgt i hi
  · -- qbit value = [N ≤ r].
    rw [hg4_eq, update_neq _ _ _ _ hqf, hg3_qbit]
  · -- flag cleaned to false.
    rw [hg4_eq, update_eq, hg3_flag, hg3_qbit, Bool.xor_self]
  · -- carry clear.
    rw [hg4_eq, update_neq _ _ _ _ (fun h => h_flag_ne_cin h.symm), hg3_eq,
        update_neq _ _ _ _ (fun h => h_qbit_ne_cin h.symm)]
    exact hg2_cin
  · -- read band clear.
    intro i hi
    rw [hg4_eq, update_neq _ _ _ _ (fun h => (h_flag_ne_read i hi) h.symm), hg3_eq,
        update_neq _ _ _ _ (fun h => (h_qbit_ne_read i hi) h.symm)]
    exact hg2_read i hi
  · -- frame outside workspace ∪ {flag, qbit}.
    intro p hpf hpq hp_out
    rw [hg4_eq, update_neq _ _ _ _ hpf, hg3_eq, update_neq _ _ _ _ hpq]
    rw [hsub.2.2.2 p hp_out, hg1]
    exact update_neq _ _ _ _ hpf

/-! ## §3. WellTyped for the divstep. -/

/-- `divStep` is well-typed in any `dim` containing the workspace, the flag, and
    the quotient bit, with `flagPos`, `qbit` distinct from the read register and
    from `q_start + 2·bits` (the comparator's top carry CX target), and from each
    other. -/
theorem divStep_wellTyped (bits q_start N flagPos qbit dim : Nat)
    (h_ws : q_start + 2 * bits + 1 ≤ dim) (h_flag : flagPos < dim) (h_qbit : qbit < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_top : flagPos ≠ q_start + 2 * bits)
    (hqf : qbit ≠ flagPos) :
    Gate.WellTyped dim (divStep bits q_start N flagPos qbit) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_ws h_flag h_flag_top
  · exact sqir_conditionalSubConstGate_wellTyped bits q_start N flagPos dim
      h_ws h_flag h_flag_distinct
  · exact ⟨h_flag, h_qbit, fun h => hqf h.symm⟩
  · exact ⟨h_qbit, h_flag, hqf⟩


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
