/- E2RunwaySynthSwap — Â§5 composed swapGate action.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Values

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §5. The composed `swapGate` action. -/

/-- **`swapGate` acts as `swapNet`** (the value-level transposition of `x` and
    `y`) on a `Nodup` register with a disjoint, big-enough clean ancilla. -/
theorem swapGate_RegAct (reg : List Nat) (x y : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hx : x < 2 ^ reg.length) (hy : y < 2 ^ reg.length)
    (hlen : reg.length ≤ anc.length + 1) :
    RegAct (swapGate reg x y anc) reg anc
      (if x = y then id else swapNet reg.length x y) := by
  unfold swapGate
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]; exact RegAct_id reg anc hnd
  · rw [if_neg hxy, if_neg hxy]
    have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
    set z := x ^^^ y with hzdef
    set p := lowestBit z with hpdef
    have hzlt : z < 2 ^ reg.length := hzdef ▸ Nat.xor_lt_two_pow hx hy
    have hp : p < reg.length := hpdef ▸ lowestBit_lt z reg.length hz hzlt
    have hlen' : (ctrlIdxs reg.length p).length ≤ anc.length + 1 :=
      Nat.le_trans (ctrlIdxs_length_le reg.length p) hlen
    -- stage RegActs
    have hA := xmaskGate_RegAct reg x anc hnd hx
    have hB := reduceCNOTGate_RegAct reg z p anc hnd hp hzlt
    have hC := antiCtrlXGate_RegAct reg p anc hnd hp hanc hdisj hlen'
    have hD := reduceCNOTGate_RegAct reg z p anc hnd hp hzlt
    have hE := xmaskGate_RegAct reg x anc hnd hx
    -- compose innermost first: seq D E
    have hDE := RegAct_seq _ _ reg anc _ _ hnd hdisj hD hE
    have hCDE := RegAct_seq _ _ reg anc _ _ hnd hdisj hC hDE
    have hBCDE := RegAct_seq _ _ reg anc _ _ hnd hdisj hB hCDE
    have hABCDE := RegAct_seq _ _ reg anc _ _ hnd hdisj hA hBCDE
    -- the composed permutation IS swapNet (definitionally, up to the if-folds).
    exact hABCDE

/-- Writing the register with its own current decode is a no-op. -/
theorem setReg_regVal_self (reg : List Nat) (f : Nat → Bool) (hnd : reg.Nodup) :
    setReg reg (regVal reg f) f = f := by
  funext p
  by_cases hp : p ∈ reg
  · obtain ⟨j, hj, rfl⟩ := (mem_reg_iff_regIdx reg p).mp hp
    rw [setReg_at reg _ f hnd j hj, regVal_testBit reg f j hj]
  · rw [setReg_frame reg _ f p hp]

/-- **`swapGate_apply` (clean-ancilla action + frame).**  On a `Nodup` register
    with a disjoint, big-enough clean ancilla, `swapGate reg x y anc` swaps the
    two basis states decoding to `x` and `y` and fixes every other state — with
    the ancilla restored and all off-register wires framed (both folded into the
    single `setReg`/`if` right-hand side, exactly as in SYNTH-1). -/
theorem swapGate_apply (reg : List Nat) (x y : Nat) (anc : List Nat) (f : Nat → Bool)
    (hx : x < 2 ^ reg.length) (hy : y < 2 ^ reg.length)
    (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hlen : reg.length ≤ anc.length + 1)
    (hclean : ∀ a ∈ anc, f a = false) :
    Gate.applyNat (swapGate reg x y anc) f =
      (if regVal reg f = x then setReg reg y f
       else if regVal reg f = y then setReg reg x f
       else f) := by
  obtain ⟨_, hact⟩ := swapGate_RegAct reg x y anc hnd hanc hdisj hx hy hlen
  rw [hact f hclean]
  by_cases hxy : x = y
  · -- x = y: every branch is `f`.
    subst hxy
    rw [if_pos rfl]  -- π picks `id`
    simp only [id_eq]
    -- LHS: setReg reg (regVal f) f = f
    rw [setReg_regVal_self reg f hnd]
    by_cases hvx : regVal reg f = x
    · rw [if_pos hvx, ← hvx, setReg_regVal_self reg f hnd]
    · rw [if_neg hvx, if_neg hvx]
  · rw [if_neg hxy]
    set v := regVal reg f with hv
    have hvlt : v < 2 ^ reg.length := hv ▸ regVal_lt reg f
    have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
    have hzlt : x ^^^ y < 2 ^ reg.length := Nat.xor_lt_two_pow hx hy
    have hplt : lowestBit (x ^^^ y) < reg.length := lowestBit_lt _ reg.length hz hzlt
    by_cases hvx : v = x
    · rw [if_pos hvx, hvx, swapNet_x reg.length x y hxy hplt]
    · rw [if_neg hvx]
      by_cases hvy : v = y
      · rw [if_pos hvy, hvy, swapNet_y reg.length x y hxy hplt]
      · rw [if_neg hvy, swapNet_other reg.length x y hxy hplt hx hy v hvlt hvx hvy,
            setReg_regVal_self reg f hnd]


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
