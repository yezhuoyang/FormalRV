/- E2RunwaySynthSwap — Â§2-3b stage defs + RegAct lemmas + ctrlIdxs facts.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.RegAct

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §2. Stage definitions. -/

/-- `Xmask reg x`: `X reg[i]` for each `i < k` with `x.testBit i = true`.
    Acts on a reg-value `v` as `v ↦ v XOR x`. -/
def xmaskGate (reg : List Nat) (x : Nat) : Gate :=
  xfold reg (fun i => x.testBit i) (List.range reg.length)

/-- `reduceCNOT reg z p`: `CX reg[p] reg[i]` for each `i ≠ p` (`i < k`) with
    `z.testBit i = true`.  Acts on `v` as: flip bits `{i ≠ p : z.testBit i}` iff
    bit `p` of `v` is set. -/
def reduceCNOTGate (reg : List Nat) (z p : Nat) : Gate :=
  cxfold reg (regIdx reg p) (fun i => decide (i ≠ p) && z.testBit i) (List.range reg.length)

/-- `Xall reg p`: `X reg[i]` for each `i ≠ p`, `i < k`. -/
def xallExceptGate (reg : List Nat) (p : Nat) : Gate :=
  xfold reg (fun i => decide (i ≠ p)) (List.range reg.length)

/-- The index list of all register positions except `p`. -/
def ctrlIdxs (k p : Nat) : List Nat := (List.range k).filter (fun i => decide (i ≠ p))

/-- The AND of all register bits except bit `p`. -/
def andExceptP (v p k : Nat) : Bool := (ctrlIdxs k p).all (fun i => v.testBit i)

/-- The anti-controlled flip of `reg[p]`: flip `reg[p]` iff every OTHER reg wire
    is `0`, i.e. iff the reg-value is in `{0, 2^p}`.  Conjugate the multi-controlled
    flip by `X` on all wires except `p`. -/
def antiCtrlXGate (reg : List Nat) (p : Nat) (anc : List Nat) : Gate :=
  Gate.seq (xallExceptGate reg p)
    (Gate.seq (mcxClean ((ctrlIdxs reg.length p).map (regIdx reg)) (regIdx reg p) anc)
      (xallExceptGate reg p))

/-- The transposition gate on register values `x`, `y` using clean ancilla `anc`.
    For `x = y` it is the identity.  Otherwise, with `z := x XOR y` and
    `p := lowestBit z`, it is the conjugation
    `Xmask ; reduceCNOT ; antiCtrlX ; reduceCNOT ; Xmask`. -/
noncomputable def swapGate (reg : List Nat) (x y : Nat) (anc : List Nat) : Gate :=
  if x = y then Gate.I
  else
    Gate.seq (xmaskGate reg x)
      (Gate.seq (reduceCNOTGate reg (x ^^^ y) (lowestBit (x ^^^ y)))
        (Gate.seq (antiCtrlXGate reg (lowestBit (x ^^^ y)) anc)
          (Gate.seq (reduceCNOTGate reg (x ^^^ y) (lowestBit (x ^^^ y)))
            (xmaskGate reg x))))

/-! ## §3. Stage RegAct lemmas. -/

/-- **Xmask stage.**  `xmaskGate reg x` acts on the register as `v ↦ v XOR x`. -/
theorem xmaskGate_RegAct (reg : List Nat) (x : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hx : x < 2 ^ reg.length) :
    RegAct (xmaskGate reg x) reg anc (fun v => v ^^^ x) := by
  unfold xmaskGate
  exact xfold_RegAct reg (fun i => x.testBit i) anc x hnd hx (fun i _ => rfl)

/-- The "clear bit `p`" mask of `z`: `z` with bit `p` set to `0`. -/
def clearBit (z p : Nat) : Nat := z ^^^ (z &&& 2 ^ p)

/-- `clearBit z p` has bit `p` cleared and all other bits as in `z`. -/
theorem clearBit_testBit (z p i : Nat) :
    (clearBit z p).testBit i = (decide (i ≠ p) && z.testBit i) := by
  unfold clearBit
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hip : i = p
  · subst hip; simp
  · have hpi : ¬ p = i := fun h => hip h.symm
    simp [hip, hpi]

/-- `clearBit z p < 2^k` when `z < 2^k`. -/
theorem clearBit_lt (z p k : Nat) (hz : z < 2 ^ k) : clearBit z p < 2 ^ k :=
  Nat.xor_lt_two_pow hz (Nat.lt_of_le_of_lt Nat.and_le_left hz)

/-- **reduceCNOT stage.**  `reduceCNOTGate reg z p` acts on the register as
    `v ↦ if v.testBit p then v XOR (clearBit z p) else v` — i.e. when bit `p` is
    set it clears every OTHER set bit of `z`.  In particular `0 ↦ 0` and, when `p`
    is a set bit of `z`, `z ↦ z XOR clearBit z p = 2^p`. -/
theorem reduceCNOTGate_RegAct (reg : List Nat) (z p : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hp : p < reg.length) (hz : z < 2 ^ reg.length) :
    RegAct (reduceCNOTGate reg z p) reg anc
      (fun v => if v.testBit p then v ^^^ clearBit z p else v) := by
  unfold reduceCNOTGate
  have hcp : (fun i => decide (i ≠ p) && z.testBit i) p = false := by simp
  exact cxfold_RegAct reg anc p (clearBit z p) hnd hp (clearBit_lt z p reg.length hz)
    (fun i => decide (i ≠ p) && z.testBit i) hcp
    (fun i _ => clearBit_testBit z p i)

/-! ## §3b. `ctrlIdxs` facts. -/

/-- Membership in `ctrlIdxs k p`. -/
theorem mem_ctrlIdxs (k p i : Nat) : i ∈ ctrlIdxs k p ↔ i < k ∧ i ≠ p := by
  unfold ctrlIdxs
  rw [List.mem_filter, List.mem_range]
  simp

/-- `ctrlIdxs k p` is `Nodup`. -/
theorem ctrlIdxs_nodup (k p : Nat) : (ctrlIdxs k p).Nodup :=
  (List.nodup_range).filter _

/-- All members of `ctrlIdxs k p` are `< k`. -/
theorem ctrlIdxs_lt (k p i : Nat) (hi : i ∈ ctrlIdxs k p) : i < k :=
  ((mem_ctrlIdxs k p i).mp hi).1

/-- `p ∉ ctrlIdxs k p`. -/
theorem p_not_mem_ctrlIdxs (k p : Nat) : p ∉ ctrlIdxs k p := by
  intro h; exact ((mem_ctrlIdxs k p p).mp h).2 rfl

/-- `ctrlIdxs k p` has length `≤ k`. -/
theorem ctrlIdxs_length_le (k p : Nat) : (ctrlIdxs k p).length ≤ k := by
  unfold ctrlIdxs
  calc ((List.range k).filter (fun i => decide (i ≠ p))).length
      ≤ (List.range k).length := List.length_filter_le _ _
    _ = k := List.length_range

/-- A control wire `c ∈ map (regIdx reg) (ctrlIdxs k p)` is `regIdx reg i` for some
    `i < k`, `i ≠ p`. -/
theorem mem_ctrl_wires (reg : List Nat) (p c : Nat)
    (hc : c ∈ (ctrlIdxs reg.length p).map (regIdx reg)) :
    ∃ i, i < reg.length ∧ i ≠ p ∧ regIdx reg i = c := by
  rw [List.mem_map] at hc
  obtain ⟨i, hi, heq⟩ := hc
  obtain ⟨hilt, hip⟩ := (mem_ctrlIdxs reg.length p i).mp hi
  exact ⟨i, hilt, hip, heq⟩

/-- The mcxClean distinctness package: `controls ++ target :: anc` is `Nodup`. -/
theorem mcx_nodup (reg : List Nat) (p : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hp : p < reg.length) (hanc : anc.Nodup)
    (hdisj : ∀ a ∈ anc, a ∉ reg) :
    (((ctrlIdxs reg.length p).map (regIdx reg)) ++ (regIdx reg p) :: anc).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · -- controls Nodup
    apply List.Nodup.map_on ?_ (ctrlIdxs_nodup reg.length p)
    intro a ha b hb hab
    exact regIdx_inj reg hnd a b (ctrlIdxs_lt _ _ a ha) (ctrlIdxs_lt _ _ b hb) hab
  · -- target :: anc Nodup
    rw [List.nodup_cons]
    refine ⟨?_, hanc⟩
    intro hmem
    exact hdisj (regIdx reg p) hmem (regIdx_mem reg p hp)
  · -- disjoint
    intro c hc b hb
    obtain ⟨i, hilt, hip, rfl⟩ := mem_ctrl_wires reg p c hc
    rw [List.mem_cons] at hb
    rcases hb with rfl | hmem
    · intro heq; exact hip (regIdx_inj reg hnd i p hilt hp heq)
    · intro heq; exact hdisj b hmem (heq ▸ regIdx_mem reg i hilt)

/-- The mcxClean AND of the control wires equals the AND of register bits except
    bit `p`: `controls.all (f ·) = andExceptP (regVal f) p k`. -/
theorem mcx_all_eq_andExceptP (reg : List Nat) (p : Nat) (f : Nat → Bool) :
    (((ctrlIdxs reg.length p).map (regIdx reg)).all (fun c => f c))
      = andExceptP (regVal reg f) p reg.length := by
  unfold andExceptP
  rw [List.all_map]
  apply all_congr_mem
  intro i hi
  exact (regVal_testBit reg f i (ctrlIdxs_lt _ _ i hi)).symm

/-- The mask with every low-`k` bit set EXCEPT bit `p`. -/
def maskAllExceptP (k p : Nat) : Nat := (2 ^ k - 1) ^^^ 2 ^ p

/-- `maskAllExceptP k p` has bit `i` (for `i < k`) equal to `decide (i ≠ p)`. -/
theorem maskAllExceptP_testBit (k p i : Nat) (hi : i < k) :
    (maskAllExceptP k p).testBit i = decide (i ≠ p) := by
  unfold maskAllExceptP
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  rw [decide_eq_true hi]
  by_cases hip : i = p
  · subst hip; simp
  · have : ¬ p = i := fun h => hip h.symm
    simp [hip, this]

/-- `maskAllExceptP k p < 2^k` when `p < k`. -/
theorem maskAllExceptP_lt (k p : Nat) (hp : p < k) : maskAllExceptP k p < 2 ^ k :=
  Nat.xor_lt_two_pow (by have := Nat.one_le_two_pow (n := k); omega)
    (Nat.pow_lt_pow_right (by norm_num) hp)

/-- **Xall-except-`p` stage.**  `xallExceptGate reg p` acts on the register as
    `v ↦ v XOR maskAllExceptP k p` (flips every bit except bit `p`). -/
theorem xallExceptGate_RegAct (reg : List Nat) (p : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hp : p < reg.length) :
    RegAct (xallExceptGate reg p) reg anc (fun v => v ^^^ maskAllExceptP reg.length p) := by
  unfold xallExceptGate
  exact xfold_RegAct reg (fun i => decide (i ≠ p)) anc (maskAllExceptP reg.length p) hnd
    (maskAllExceptP_lt reg.length p hp)
    (fun i hi => maskAllExceptP_testBit reg.length p i hi)

/-- **The multi-controlled flip stage as a `RegAct`.**  `mcxClean (controls = reg
    wires `i ≠ p`) (target = reg[p]) anc` flips bit `p` of the register value iff
    every OTHER register bit is set, restoring `anc`. -/
theorem mcxClean_RegAct (reg : List Nat) (p : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hp : p < reg.length) (hanc : anc.Nodup)
    (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hlen : (ctrlIdxs reg.length p).length ≤ anc.length + 1) :
    RegAct (mcxClean ((ctrlIdxs reg.length p).map (regIdx reg)) (regIdx reg p) anc) reg anc
      (fun v => if andExceptP v p reg.length then v ^^^ 2 ^ p else v) := by
  have hnd_pkg := mcx_nodup reg p anc hnd hp hanc hdisj
  have hlen' : ((ctrlIdxs reg.length p).map (regIdx reg)).length ≤ anc.length + 1 := by
    rwa [List.length_map]
  refine ⟨?_, ?_⟩
  · -- range preservation
    intro v hv
    simp only
    by_cases hb : andExceptP v p reg.length
    · rw [if_pos hb]
      exact Nat.xor_lt_two_pow hv (Nat.pow_lt_pow_right (by norm_num) hp)
    · rw [if_neg hb]; exact hv
  · intro f hclean
    rw [mcxClean_apply ((ctrlIdxs reg.length p).map (regIdx reg)) (regIdx reg p) anc f
          hnd_pkg hlen' hclean]
    rw [mcx_all_eq_andExceptP reg p f]
    funext q
    by_cases hq : q ∈ reg
    · obtain ⟨j, hj, rfl⟩ := (mem_reg_iff_regIdx reg q).mp hq
      rw [setReg_at reg _ f hnd j hj]
      simp only
      by_cases hjp : j = p
      · -- the flipped bit
        subst hjp
        rw [update_eq, ← regVal_testBit reg f j hj]
        by_cases hb : andExceptP (regVal reg f) j reg.length
        · rw [if_pos hb, Nat.testBit_xor, Nat.testBit_two_pow_self, hb]
        · rw [if_neg hb]
          have : andExceptP (regVal reg f) j reg.length = false := Bool.not_eq_true _ ▸ hb
          rw [this, Bool.xor_false]
      · -- an unflipped bit (j ≠ p)
        have hne : regIdx reg j ≠ regIdx reg p := by
          intro heq; exact hjp (regIdx_inj reg hnd j p hj hp heq)
        rw [update_neq _ _ _ _ hne, ← regVal_testBit reg f j hj]
        by_cases hb : andExceptP (regVal reg f) p reg.length
        · rw [if_pos hb, Nat.testBit_xor, Nat.testBit_two_pow]
          have : ¬ p = j := fun h => hjp h.symm
          simp [this]
        · rw [if_neg hb]
    · -- off-register frame
      rw [setReg_frame reg _ f q hq]
      have hqp : q ≠ regIdx reg p := fun h => hq (h ▸ regIdx_mem reg p hp)
      rw [update_neq _ _ _ _ hqp]

/-- **antiCtrlX stage.**  Conjugating the multi-controlled flip by `Xall` yields
    the ANTI-controlled flip: flip bit `p` iff every OTHER register bit is `0`.
    The exposed permutation, before simplification, is
    `v ↦ if andExceptP (v XOR M) p k then v XOR 2^p else v` with `M = maskAllExceptP k p`. -/
theorem antiCtrlXGate_RegAct (reg : List Nat) (p : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hp : p < reg.length) (hanc : anc.Nodup)
    (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hlen : (ctrlIdxs reg.length p).length ≤ anc.length + 1) :
    RegAct (antiCtrlXGate reg p anc) reg anc
      (fun v => if andExceptP (v ^^^ maskAllExceptP reg.length p) p reg.length
                then v ^^^ 2 ^ p else v) := by
  unfold antiCtrlXGate
  set M := maskAllExceptP reg.length p with hM
  have hXall := xallExceptGate_RegAct reg p anc hnd hp
  have hmcx := mcxClean_RegAct reg p anc hnd hp hanc hdisj hlen
  -- inner: seq mcx xall acts as fun w => (πmcx w) ^^^ M
  have hinner := RegAct_seq _ _ reg anc
    (fun v => if andExceptP v p reg.length then v ^^^ 2 ^ p else v)
    (fun v => v ^^^ M) hnd hdisj hmcx hXall
  -- outer: seq xall (inner)
  have hcomp := RegAct_seq _ _ reg anc
    (fun v => v ^^^ M)
    (fun w => (if andExceptP w p reg.length then w ^^^ 2 ^ p else w) ^^^ M)
    hnd hdisj hXall hinner
  -- the composed permutation simplifies to the stated one.
  have hpi : (fun v => (if andExceptP (v ^^^ M) p reg.length then (v ^^^ M) ^^^ 2 ^ p else v ^^^ M) ^^^ M)
      = (fun v => if andExceptP (v ^^^ M) p reg.length then v ^^^ 2 ^ p else v) := by
    funext v
    by_cases hb : andExceptP (v ^^^ M) p reg.length
    · rw [if_pos hb, if_pos hb]
      simp [Nat.xor_comm, Nat.xor_left_comm]
    · rw [if_neg hb, if_neg hb, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hpi] at hcomp
  exact hcomp


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
