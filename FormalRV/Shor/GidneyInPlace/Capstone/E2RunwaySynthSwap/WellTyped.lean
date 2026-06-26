/- E2RunwaySynthSwap — Â§6 well-typedness.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Compose

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §6. Well-typedness. -/

/-- `xfold` is well-typed when every used register wire is `< dim`. -/
theorem xfold_wellTyped (reg : List Nat) (cond : Nat → Bool) (L : List Nat) (dim : Nat)
    (hdim : 0 < dim) (hb : ∀ i ∈ L, regIdx reg i < dim) :
    Gate.WellTyped dim (xfold reg cond L) := by
  induction L with
  | nil => exact hdim
  | cons a L ih =>
    rw [xfold_cons]
    by_cases hc : cond a
    · rw [if_pos hc]
      exact ⟨hb a (by simp), ih (fun i hi => hb i (by simp [hi]))⟩
    · rw [if_neg hc]
      exact ih (fun i hi => hb i (by simp [hi]))

/-- `cxfold` is well-typed when the control and every used target wire is `< dim`
    and the control is never a target (`ctrl ≠ regIdx reg i` for active `i`). -/
theorem cxfold_wellTyped (reg : List Nat) (ctrl : Nat) (cond : Nat → Bool) (L : List Nat)
    (dim : Nat) (hdim : 0 < dim) (hctrl : ctrl < dim) (hb : ∀ i ∈ L, regIdx reg i < dim)
    (hne : ∀ i ∈ L, cond i = true → ctrl ≠ regIdx reg i) :
    Gate.WellTyped dim (cxfold reg ctrl cond L) := by
  induction L with
  | nil => exact hdim
  | cons a L ih =>
    rw [cxfold_cons]
    by_cases hc : cond a
    · rw [if_pos hc]
      exact ⟨⟨hctrl, hb a (by simp), hne a (by simp) hc⟩,
        ih (fun i hi => hb i (by simp [hi])) (fun i hi => hne i (by simp [hi]))⟩
    · rw [if_neg hc]
      exact ih (fun i hi => hb i (by simp [hi])) (fun i hi => hne i (by simp [hi]))

/-- `antiCtrlXGate` is well-typed: the `Xall` legs are well-typed and the central
    `mcxClean` is well-typed via `mcxClean_wellTyped` (its wires are register/anc
    wires, distinct via the `Nodup`/disjointness). -/
theorem antiCtrlXGate_wellTyped (reg : List Nat) (p : Nat) (anc : List Nat) (dim : Nat)
    (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg) (hdim : 0 < dim)
    (hp : p < reg.length) (hridx : ∀ i, i < reg.length → regIdx reg i < dim)
    (hancb : ∀ a ∈ anc, a < dim) (hlen : (ctrlIdxs reg.length p).length ≤ anc.length + 1) :
    Gate.WellTyped dim (antiCtrlXGate reg p anc) := by
  unfold antiCtrlXGate
  have hXall : Gate.WellTyped dim (xallExceptGate reg p) := by
    unfold xallExceptGate
    exact xfold_wellTyped reg _ _ dim hdim (fun i hi => hridx i (List.mem_range.mp hi))
  refine ⟨hXall, ?_, hXall⟩
  -- the mcxClean
  apply mcxClean_wellTyped _ _ _ dim (mcx_nodup reg p anc hnd hp hanc hdisj)
  · rwa [List.length_map]
  · intro c hc
    obtain ⟨i, hilt, _, rfl⟩ := mem_ctrl_wires reg p c hc
    exact hridx i hilt
  · exact hridx p hp
  · exact hancb

/-- **`swapGate_wellTyped`.**  When every register wire and ancilla wire is `< dim`
    (with the register `Nodup`, ancilla `Nodup` and disjoint, enough ancillae, and
    `x, y` in range so the construction is meaningful), `swapGate reg x y anc` is a
    well-typed `dim`-qubit circuit. -/
theorem swapGate_wellTyped (reg : List Nat) (x y : Nat) (anc : List Nat) (dim : Nat)
    (hx : x < 2 ^ reg.length) (hy : y < 2 ^ reg.length)
    (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hdim : 0 < dim) (hregb : ∀ q ∈ reg, q < dim) (hancb : ∀ a ∈ anc, a < dim)
    (hlen : reg.length ≤ anc.length + 1) :
    Gate.WellTyped dim (swapGate reg x y anc) := by
  have hridx : ∀ i, i < reg.length → regIdx reg i < dim :=
    fun i hi => hregb _ (regIdx_mem reg i hi)
  unfold swapGate
  by_cases hxy : x = y
  · rw [if_pos hxy]; exact hdim
  · rw [if_neg hxy]
    set z := x ^^^ y with hzdef
    set p := lowestBit z with hpdef
    have hz : z ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp (hzdef ▸ h))
    have hzlt : z < 2 ^ reg.length := hzdef ▸ Nat.xor_lt_two_pow hx hy
    have hp : p < reg.length := hpdef ▸ lowestBit_lt z reg.length hz hzlt
    have hlen' : (ctrlIdxs reg.length p).length ≤ anc.length + 1 :=
      Nat.le_trans (ctrlIdxs_length_le reg.length p) hlen
    -- stage well-typedness
    have hX : Gate.WellTyped dim (xmaskGate reg x) := by
      unfold xmaskGate
      exact xfold_wellTyped reg _ _ dim hdim (fun i hi => hridx i (List.mem_range.mp hi))
    have hRed : Gate.WellTyped dim (reduceCNOTGate reg z p) := by
      unfold reduceCNOTGate
      refine cxfold_wellTyped reg (regIdx reg p) _ _ dim hdim (hridx p hp)
        (fun i hi => hridx i (List.mem_range.mp hi)) ?_
      intro i hi hci heq
      have hik : i < reg.length := List.mem_range.mp hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hci
      exact hci.1 (regIdx_inj reg hnd p i hp hik heq).symm
    have hAnti : Gate.WellTyped dim (antiCtrlXGate reg p anc) :=
      antiCtrlXGate_wellTyped reg p anc dim hnd hanc hdisj hdim hp hridx hancb hlen'
    exact ⟨hX, hRed, hAnti, hRed, hX⟩


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
