/- E2RunwaySynthSwap — Â§0 register index/decode/write helpers.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
import FormalRV.Arithmetic.Windowed.WindowedInPlace

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §0. Register index, decode, and write helpers. -/

/-- Index function for a register list: bit `i` lives at wire `reg.getD i 0`. -/
def regIdx (reg : List Nat) : Nat → Nat := fun i => reg.getD i 0

/-- Register decode: the natural number whose bit `i` is `f reg[i]`. -/
def regVal (reg : List Nat) (f : Nat → Bool) : Nat :=
  decodeReg (regIdx reg) reg.length f

/-- Encode `v` into the register positions (bit `i` of `v` at wire `reg[i]`). -/
def setReg (reg : List Nat) (v : Nat) (f : Nat → Bool) : Nat → Bool :=
  writeReg (regIdx reg) reg.length v f

/-- `regIdx reg i ∈ reg` for `i < reg.length`. -/
theorem regIdx_mem (reg : List Nat) (i : Nat) (hi : i < reg.length) :
    regIdx reg i ∈ reg := by
  unfold regIdx
  rw [List.getD_eq_getElem reg 0 hi]
  exact List.getElem_mem hi

/-- On a `Nodup` register, `regIdx` is injective for in-range indices. -/
theorem regIdx_inj (reg : List Nat) (hnd : reg.Nodup) :
    ∀ i j, i < reg.length → j < reg.length → regIdx reg i = regIdx reg j → i = j := by
  intro i j hi hj h
  unfold regIdx at h
  rw [List.getD_eq_getElem reg 0 hi, List.getD_eq_getElem reg 0 hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).mp h

/-- Bit `i` of `regVal reg f` is the state at wire `regIdx reg i` (for `i < k`). -/
theorem regVal_testBit (reg : List Nat) (f : Nat → Bool) (i : Nat)
    (hi : i < reg.length) :
    (regVal reg f).testBit i = f (regIdx reg i) :=
  decodeReg_testBit (regIdx reg) reg.length f i hi

/-- `regVal reg f < 2 ^ reg.length`. -/
theorem regVal_lt (reg : List Nat) (f : Nat → Bool) :
    regVal reg f < 2 ^ reg.length :=
  decodeReg_lt_two_pow (regIdx reg) reg.length f

/-- `regVal` depends only on the state at register wires. -/
theorem regVal_congr (reg : List Nat) (f g : Nat → Bool)
    (h : ∀ i, i < reg.length → f (regIdx reg i) = g (regIdx reg i)) :
    regVal reg f = regVal reg g := by
  unfold regVal
  exact FormalRV.BQAlgo.decodeReg_ext (regIdx reg) reg.length f g h

/-- `setReg` frame: off-register wires are untouched. -/
theorem setReg_frame (reg : List Nat) (v : Nat) (f : Nat → Bool) (p : Nat)
    (hp : p ∉ reg) : setReg reg v f p = f p := by
  unfold setReg
  exact writeReg_frame (regIdx reg) reg.length v f p
    (fun i hi heq => hp (heq ▸ regIdx_mem reg i hi))

/-- `setReg` writes: on a `Nodup` register, wire `regIdx reg i` ends as bit `i`. -/
theorem setReg_at (reg : List Nat) (v : Nat) (f : Nat → Bool) (hnd : reg.Nodup)
    (i : Nat) (hi : i < reg.length) :
    setReg reg v f (regIdx reg i) = v.testBit i := by
  unfold setReg
  exact writeReg_at (regIdx reg) reg.length v f (regIdx_inj reg hnd) i hi

/-- Every register member is `regIdx reg i` for some in-range `i`. -/
theorem mem_reg_iff_regIdx (reg : List Nat) (p : Nat) :
    p ∈ reg ↔ ∃ i, i < reg.length ∧ regIdx reg i = p := by
  constructor
  · intro hp
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hp
    exact ⟨i, hi, by unfold regIdx; rw [List.getD_eq_getElem reg 0 hi]; exact heq⟩
  · rintro ⟨i, hi, rfl⟩; exact regIdx_mem reg i hi

/-- Two register-writes collapse: the later value wins. -/
theorem setReg_setReg (reg : List Nat) (v w : Nat) (f : Nat → Bool)
    (hnd : reg.Nodup) :
    setReg reg w (setReg reg v f) = setReg reg w f := by
  funext p
  by_cases hp : p ∈ reg
  · obtain ⟨i, hi, rfl⟩ := (mem_reg_iff_regIdx reg p).mp hp
    rw [setReg_at reg w _ hnd i hi, setReg_at reg w f hnd i hi]
  · rw [setReg_frame reg w _ p hp, setReg_frame reg v f p hp, setReg_frame reg w f p hp]

/-- `setReg` with a clean ancilla disjoint from `reg` keeps it clean. -/
theorem setReg_clean (reg : List Nat) (anc : List Nat) (v : Nat) (f : Nat → Bool)
    (hdisj : ∀ a ∈ anc, a ∉ reg) (hclean : ∀ a ∈ anc, f a = false) :
    ∀ a ∈ anc, setReg reg v f a = false := by
  intro a ha
  rw [setReg_frame reg v f a (hdisj a ha)]
  exact hclean a ha

/-- Decoding a freshly-written register recovers the value (mod `2^k`). -/
theorem regVal_setReg (reg : List Nat) (v : Nat) (f : Nat → Bool) (hnd : reg.Nodup)
    (hv : v < 2 ^ reg.length) :
    regVal reg (setReg reg v f) = v := by
  have hbit : ∀ i, i < reg.length →
      (regVal reg (setReg reg v f)).testBit i = v.testBit i := by
    intro i hi
    rw [regVal_testBit reg _ i hi, setReg_at reg v f hnd i hi]
  -- both are < 2^k and agree on all bits < k ⇒ equal.
  have hl1 : regVal reg (setReg reg v f) < 2 ^ reg.length := regVal_lt reg _
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < reg.length
  · exact hbit i hi
  · have hi' : reg.length ≤ i := Nat.le_of_not_lt hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hl1 (Nat.pow_le_pow_right (by norm_num) hi')),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hi'))]


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
