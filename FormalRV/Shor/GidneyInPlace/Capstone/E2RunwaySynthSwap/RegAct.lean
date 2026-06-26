/- E2RunwaySynthSwap — Â§1-1d RegAct abstraction + lowest-bit + conditional-X/CX folds.  Part of the `E2RunwaySynthSwap` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap.Indices

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
open FormalRV.Shor.WindowedCircuit (writeReg writeReg_at writeReg_frame
  decodeReg_testBit decodeReg_lt_two_pow decodeReg_succ_eq)


/-! ## §1. The register-action abstraction `RegAct`.

A gate `g` "acts as the register permutation `π` with clean ancilla `anc`" when,
on any state whose `anc` is clean, `g` rewrites the register to encode
`π (regVal reg f)` and leaves EVERYTHING ELSE (off-register, including `anc`)
exactly as it was.  `setReg` captures this single form: it overwrites only the
register positions and frames the rest, so it subsumes both "anc restored clean"
and "frame off-register". -/

/-- `g` acts on register `reg` (clean ancilla `anc`) as the value permutation `π`,
    where `π` is required to preserve the value range `[0, 2^k)`. -/
def RegAct (g : Gate) (reg anc : List Nat) (π : Nat → Nat) : Prop :=
  (∀ v, v < 2 ^ reg.length → π v < 2 ^ reg.length) ∧
  ∀ f, (∀ a ∈ anc, f a = false) →
    Gate.applyNat g f = setReg reg (π (regVal reg f)) f

/-- The identity gate acts as the identity permutation. -/
theorem RegAct_id (reg anc : List Nat) (hnd : reg.Nodup) :
    RegAct Gate.I reg anc id := by
  refine ⟨fun v hv => hv, ?_⟩
  intro f _
  rw [Gate.applyNat_I]
  -- setReg reg (regVal reg f) f = f
  funext p
  by_cases hp : p ∈ reg
  · obtain ⟨i, hi, rfl⟩ := (mem_reg_iff_regIdx reg p).mp hp
    rw [setReg_at reg _ f hnd i hi, id, regVal_testBit reg f i hi]
  · rw [setReg_frame reg _ f p hp]

/-- **Composition.**  If `g₁` acts as `π₁` and `g₂` acts as `π₂` (same register,
    same ancilla, ancilla disjoint from the register), then `seq g₁ g₂` acts as
    `π₂ ∘ π₁`. -/
theorem RegAct_seq (g₁ g₂ : Gate) (reg anc : List Nat) (π₁ π₂ : Nat → Nat)
    (hnd : reg.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (h₁ : RegAct g₁ reg anc π₁) (h₂ : RegAct g₂ reg anc π₂) :
    RegAct (Gate.seq g₁ g₂) reg anc (fun v => π₂ (π₁ v)) := by
  obtain ⟨hb₁, ha₁⟩ := h₁
  obtain ⟨hb₂, ha₂⟩ := h₂
  refine ⟨fun v hv => hb₂ _ (hb₁ v hv), ?_⟩
  intro f hclean
  rw [Gate.applyNat_seq, ha₁ f hclean]
  -- intermediate state: g := setReg reg (π₁ (regVal reg f)) f
  set v := regVal reg f with hv
  have hvlt : v < 2 ^ reg.length := hv ▸ regVal_lt reg f
  -- anc stays clean in the intermediate state.
  have hclean2 : ∀ a ∈ anc, setReg reg (π₁ v) f a = false :=
    setReg_clean reg anc (π₁ v) f hdisj hclean
  rw [ha₂ (setReg reg (π₁ v) f) hclean2]
  -- regVal of the intermediate state is π₁ v (it was freshly written).
  rw [regVal_setReg reg (π₁ v) f hnd (hb₁ v hvlt)]
  -- two writes collapse.
  rw [setReg_setReg reg (π₁ v) (π₂ (π₁ v)) f hnd]

/-! ## §1b. Lowest set bit. -/

open Classical in
/-- The position of the lowest set bit of a nonzero `z` (the least `i` with
    `z.testBit i = true`).  Defined for all `z`; only meaningful when `z ≠ 0`. -/
noncomputable def lowestBit (z : Nat) : Nat :=
  if h : ∃ i, z.testBit i = true then Nat.find h else 0

/-- For `z ≠ 0`, `lowestBit z` IS a set bit of `z`. -/
theorem testBit_lowestBit (z : Nat) (hz : z ≠ 0) :
    z.testBit (lowestBit z) = true := by
  have h : ∃ i, z.testBit i = true := Nat.exists_testBit_of_ne_zero hz
  unfold lowestBit
  rw [dif_pos h]
  exact Nat.find_spec h

/-- `lowestBit z` is the LEAST set bit: every lower bit of `z` is `0`. -/
theorem lowestBit_min (z : Nat) (hz : z ≠ 0) (i : Nat) (hi : i < lowestBit z) :
    z.testBit i = false := by
  have h : ∃ i, z.testBit i = true := Nat.exists_testBit_of_ne_zero hz
  unfold lowestBit at hi
  rw [dif_pos h] at hi
  have := Nat.find_min h hi
  simpa using this

/-- For `z < 2^k`, `z ≠ 0`, the lowest set bit is `< k`. -/
theorem lowestBit_lt (z k : Nat) (hz : z ≠ 0) (hzk : z < 2 ^ k) :
    lowestBit z < k := by
  by_contra hcon
  have hcon : k ≤ lowestBit z := Nat.le_of_not_lt hcon
  have hset : z.testBit (lowestBit z) = true := testBit_lowestBit z hz
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hzk (Nat.pow_le_pow_right (by norm_num) hcon))]
    at hset
  exact Bool.noConfusion hset

/-! ## §1c. Generic conditional-X fold. -/

/-- A fold of conditional `X` gates over a list of register indices. -/
def xfold (reg : List Nat) (cond : Nat → Bool) (L : List Nat) : Gate :=
  L.foldr (fun i g => if cond i then Gate.seq (Gate.X (regIdx reg i)) g else g) Gate.I

/-- Head-peeling equation for `xfold`, keeping the tail folded. -/
theorem xfold_cons (reg : List Nat) (cond : Nat → Bool) (a : Nat) (L : List Nat) :
    xfold reg cond (a :: L)
      = if cond a then Gate.seq (Gate.X (regIdx reg a)) (xfold reg cond L) else xfold reg cond L := by
  unfold xfold; rw [List.foldr_cons]

/-- Per-wire action of `xfold` at an OFF-register-list wire (not among the
    targets `regIdx reg i` for `i ∈ L`): unchanged. -/
theorem xfold_frame (reg : List Nat) (cond : Nat → Bool) (L : List Nat)
    (p : Nat) (hp : ∀ i ∈ L, p ≠ regIdx reg i) :
    ∀ f, Gate.applyNat (xfold reg cond L) f p = f p := by
  induction L with
  | nil => intro f; rfl
  | cons a L ih =>
    intro f
    rw [xfold_cons]
    by_cases hc : cond a
    · rw [if_pos hc, Gate.applyNat_seq, Gate.applyNat_X]
      -- X a applied first, then the inner fold acts on the updated state.
      have hpa : p ≠ regIdx reg a := hp a (by simp)
      have := ih (fun i hi => hp i (by simp [hi])) (update f (regIdx reg a) (!f (regIdx reg a)))
      rw [this, update_neq _ _ _ _ hpa]
    · rw [if_neg hc]
      exact ih (fun i hi => hp i (by simp [hi])) f

/-- Per-wire action of `xfold` at a register wire `regIdx reg j`, where `j ∈ L`
    occurs at most once (the indices in `L` map injectively to distinct wires):
    the bit is flipped iff `cond j`. -/
theorem xfold_at (reg : List Nat) (cond : Nat → Bool) (L : List Nat)
    (hnd : reg.Nodup) (hL : ∀ i ∈ L, i < reg.length) (hLnd : L.Nodup)
    (j : Nat) (hj : j ∈ L) :
    ∀ f, Gate.applyNat (xfold reg cond L) f (regIdx reg j)
      = xor (f (regIdx reg j)) (cond j) := by
  induction L with
  | nil => simp at hj
  | cons a L ih =>
    intro f
    rw [xfold_cons]
    rw [List.nodup_cons] at hLnd
    obtain ⟨ha_notin, hLnd'⟩ := hLnd
    rcases List.mem_cons.mp hj with hja | hjL
    · -- j = a (head): X applied first sets regIdx reg j, inner fold leaves it.
      subst hja
      have hinner : ∀ g, Gate.applyNat (xfold reg cond L) g (regIdx reg j) = g (regIdx reg j) := by
        intro g
        apply xfold_frame
        intro i hi heq
        have hij : j = i := regIdx_inj reg hnd j i (hL j (by simp))
          (hL i (by simp [hi])) heq
        exact ha_notin (hij ▸ hi)
      by_cases hc : cond j
      · rw [if_pos hc, Gate.applyNat_seq, Gate.applyNat_X]
        rw [hinner (update f (regIdx reg j) (!f (regIdx reg j))), update_eq, hc, Bool.xor_true]
      · rw [if_neg hc]
        rw [hinner f]
        cases hcv : cond j
        · rw [Bool.xor_false]
        · exact absurd hcv (by simp [hc])
    · -- j ∈ L (tail)
      have hja : j ≠ a := fun h => ha_notin (h ▸ hjL)
      by_cases hc : cond a
      · rw [if_pos hc, Gate.applyNat_seq, Gate.applyNat_X]
        have hne : regIdx reg j ≠ regIdx reg a := by
          intro heq
          exact hja (regIdx_inj reg hnd j a (hL j (by simp [hjL])) (hL a (by simp)) heq)
        have := ih (fun i hi => hL i (by simp [hi])) hLnd' hjL
          (update f (regIdx reg a) (!f (regIdx reg a)))
        rw [this, update_neq _ _ _ _ hne]
      · rw [if_neg hc]
        exact ih (fun i hi => hL i (by simp [hi])) hLnd' hjL f

/-- **`xfold` acts as XOR by a mask.**  If `m < 2^k` realizes `cond` on its low
    `k` bits (`m.testBit i = cond i` for `i < k`), then `xfold reg cond (range k)`
    acts on the register as `v ↦ v XOR m`. -/
theorem xfold_RegAct (reg : List Nat) (cond : Nat → Bool) (anc : List Nat) (m : Nat)
    (hnd : reg.Nodup) (hm : m < 2 ^ reg.length)
    (hmc : ∀ i, i < reg.length → m.testBit i = cond i) :
    RegAct (xfold reg cond (List.range reg.length)) reg anc (fun v => v ^^^ m) := by
  refine ⟨?_, ?_⟩
  · -- range preservation: v, m < 2^k ⇒ v XOR m < 2^k.
    intro v hv
    exact Nat.xor_lt_two_pow hv hm
  · intro f hclean
    funext p
    by_cases hp : p ∈ reg
    · obtain ⟨j, hj, rfl⟩ := (mem_reg_iff_regIdx reg p).mp hp
      rw [setReg_at reg _ f hnd j hj]
      rw [xfold_at reg cond (List.range reg.length) hnd
            (fun i hi => List.mem_range.mp hi) (List.nodup_range)
            j (List.mem_range.mpr hj) f]
      rw [Nat.testBit_xor, regVal_testBit reg f j hj, hmc j hj]
    · rw [setReg_frame reg _ f p hp]
      exact xfold_frame reg cond (List.range reg.length) p
        (fun i hi heq => hp (heq ▸ regIdx_mem reg i (List.mem_range.mp hi))) f

/-! ## §1d. Generic CX-fold from a fixed control. -/

/-- A fold of conditional `CX ctrl (regIdx reg i)` gates over a list of indices.
    All gates share the SAME control `ctrl`. -/
def cxfold (reg : List Nat) (ctrl : Nat) (cond : Nat → Bool) (L : List Nat) : Gate :=
  L.foldr (fun i g => if cond i then Gate.seq (Gate.CX ctrl (regIdx reg i)) g else g) Gate.I

/-- Head-peeling equation for `cxfold`. -/
theorem cxfold_cons (reg : List Nat) (ctrl : Nat) (cond : Nat → Bool) (a : Nat) (L : List Nat) :
    cxfold reg ctrl cond (a :: L)
      = if cond a then Gate.seq (Gate.CX ctrl (regIdx reg a)) (cxfold reg ctrl cond L)
        else cxfold reg ctrl cond L := by
  unfold cxfold; rw [List.foldr_cons]

/-- `cxfold` frame: a wire that is none of the targets `regIdx reg i` (`i ∈ L`)
    is unchanged.  (In particular, the shared control `ctrl`, when it is not a
    target, is preserved — so the cascade reads a STABLE control value.) -/
theorem cxfold_frame (reg : List Nat) (ctrl : Nat) (cond : Nat → Bool) (L : List Nat)
    (p : Nat) (hp : ∀ i ∈ L, p ≠ regIdx reg i) :
    ∀ f, Gate.applyNat (cxfold reg ctrl cond L) f p = f p := by
  induction L with
  | nil => intro f; rfl
  | cons a L ih =>
    intro f
    rw [cxfold_cons]
    by_cases hc : cond a
    · rw [if_pos hc, Gate.applyNat_seq, Gate.applyNat_CX]
      have hpa : p ≠ regIdx reg a := hp a (by simp)
      have := ih (fun i hi => hp i (by simp [hi]))
        (update f (regIdx reg a) (xor (f (regIdx reg a)) (f ctrl)))
      rw [this, update_neq _ _ _ _ hpa]
    · rw [if_neg hc]
      exact ih (fun i hi => hp i (by simp [hi])) f

/-- `cxfold` at a target wire `regIdx reg j` (`j ∈ L`, distinct indices, and the
    shared control `ctrl` is NOT any target — so it is read unchanged throughout):
    the bit is XORed with the control value iff `cond j`. -/
theorem cxfold_at (reg : List Nat) (ctrl : Nat) (cond : Nat → Bool) (L : List Nat)
    (hnd : reg.Nodup) (hL : ∀ i ∈ L, i < reg.length) (hLnd : L.Nodup)
    (hctrl : ∀ i ∈ L, cond i = true → ctrl ≠ regIdx reg i)
    (j : Nat) (hj : j ∈ L) :
    ∀ f, Gate.applyNat (cxfold reg ctrl cond L) f (regIdx reg j)
      = xor (f (regIdx reg j)) (if cond j then f ctrl else false) := by
  induction L with
  | nil => simp at hj
  | cons a L ih =>
    intro f
    rw [cxfold_cons]
    rw [List.nodup_cons] at hLnd
    obtain ⟨ha_notin, hLnd'⟩ := hLnd
    rcases List.mem_cons.mp hj with hja | hjL
    · -- j = a (head): CX a applied first, inner cascade leaves regIdx reg j.
      subst hja
      have hinner : ∀ g, Gate.applyNat (cxfold reg ctrl cond L) g (regIdx reg j) = g (regIdx reg j) := by
        intro g
        apply cxfold_frame
        intro i hi heq
        have hij : j = i := regIdx_inj reg hnd j i (hL j (by simp)) (hL i (by simp [hi])) heq
        exact ha_notin (hij ▸ hi)
      by_cases hc : cond j
      · rw [if_pos hc, Gate.applyNat_seq, Gate.applyNat_CX]
        rw [hinner (update f (regIdx reg j) (xor (f (regIdx reg j)) (f ctrl)))]
        -- control ctrl was read off the inner-modified state; but cxfold writes
        -- only at targets ≠ ctrl, so f ctrl is the original.
        rw [update_eq, if_pos hc]
      · rw [if_neg hc, hinner f, if_neg hc, Bool.xor_false]
    · -- j ∈ L (tail)
      have hja : j ≠ a := fun h => ha_notin (h ▸ hjL)
      by_cases hc : cond a
      · rw [if_pos hc, Gate.applyNat_seq, Gate.applyNat_CX]
        have hne : regIdx reg j ≠ regIdx reg a := by
          intro heq
          exact hja (regIdx_inj reg hnd j a (hL j (by simp [hjL])) (hL a (by simp)) heq)
        have hctrl_ne : ctrl ≠ regIdx reg a := hctrl a (by simp) hc
        have := ih (fun i hi => hL i (by simp [hi])) hLnd'
          (fun i hi => hctrl i (by simp [hi])) hjL
          (update f (regIdx reg a) (xor (f (regIdx reg a)) (f ctrl)))
        rw [this, update_neq _ _ _ _ hne, update_neq _ _ _ _ hctrl_ne]
      · rw [if_neg hc]
        exact ih (fun i hi => hL i (by simp [hi])) hLnd'
          (fun i hi => hctrl i (by simp [hi])) hjL f

/-- **`cxfold` (control = reg wire `p`) acts as a controlled XOR.**  With control
    `regIdx reg p` and a mask `m < 2^k` realizing `cond` on the low `k` bits and
    `cond p = false` (the control is never a target), `cxfold` acts on the
    register as `v ↦ if v.testBit p then v XOR m else v`. -/
theorem cxfold_RegAct (reg : List Nat) (anc : List Nat) (p m : Nat)
    (hnd : reg.Nodup) (hp : p < reg.length) (hm : m < 2 ^ reg.length)
    (cond : Nat → Bool) (hcp : cond p = false)
    (hmc : ∀ i, i < reg.length → m.testBit i = cond i) :
    RegAct (cxfold reg (regIdx reg p) cond (List.range reg.length)) reg anc
      (fun v => if v.testBit p then v ^^^ m else v) := by
  -- The control index `p` is not a target of any conditional CX (cond p = false),
  -- so `regIdx reg p ≠ regIdx reg i` whenever `cond i = true`.
  have hctrl : ∀ i ∈ List.range reg.length, regIdx reg p ≠ regIdx reg i ∨ cond i = false := by
    intro i hi
    by_cases hip : i = p
    · right; rw [hip]; exact hcp
    · left; intro heq
      exact hip (regIdx_inj reg hnd p i hp (List.mem_range.mp hi) heq).symm
  refine ⟨?_, ?_⟩
  · -- range preservation
    intro v hv
    simp only
    by_cases hb : v.testBit p
    · rw [if_pos hb]; exact Nat.xor_lt_two_pow hv hm
    · rw [if_neg hb]; exact hv
  · intro f hclean
    funext q
    by_cases hq : q ∈ reg
    · obtain ⟨j, hj, rfl⟩ := (mem_reg_iff_regIdx reg q).mp hq
      rw [setReg_at reg _ f hnd j hj]
      -- per-target action: control p is not an active target.
      have hctrl_at : ∀ i ∈ List.range reg.length, cond i = true → regIdx reg p ≠ regIdx reg i := by
        intro i hi hci heq
        have hip : p = i := regIdx_inj reg hnd p i hp (List.mem_range.mp hi) heq
        rw [← hip, hcp] at hci; exact Bool.noConfusion hci
      rw [cxfold_at reg (regIdx reg p) cond (List.range reg.length) hnd
            (fun i hi => List.mem_range.mp hi) (List.nodup_range) hctrl_at
            j (List.mem_range.mpr hj) f]
      -- read the control bit `f (regIdx reg p) = (regVal f).testBit p`.
      rw [← regVal_testBit reg f p hp]
      simp only
      by_cases hb : (regVal reg f).testBit p
      · rw [if_pos hb, Nat.testBit_xor, regVal_testBit reg f j hj, hmc j hj, hb]
        cases hcj : cond j <;> simp
      · have hbf : (regVal reg f).testBit p = false := Bool.not_eq_true _ ▸ hb
        rw [if_neg hb, regVal_testBit reg f j hj, hbf]
        cases hcj : cond j <;> simp
    · rw [setReg_frame reg _ f q hq]
      exact cxfold_frame reg (regIdx reg p) cond (List.range reg.length) q
        (fun i hi heq => hq (heq ▸ regIdx_mem reg i (List.mem_range.mp hi))) f


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
