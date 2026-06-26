/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap —
  SYNTH-2 (attempt A): a TRANSPOSITION gate on a register, with proven
  CLEAN-ancilla action.
  ════════════════════════════════════════════════════════════════════════════

  Goal: `swapGate reg x y anc : Gate` realizing the transposition of the two
  register-VALUES `x` and `y` (x, y < 2^k, k = reg.length): it swaps the basis
  state whose reg-decode is `x` with the one whose reg-decode is `y`, leaving
  every other state fixed, using `anc` as CLEAN scratch (restored).

  regVal = `decodeReg (reg.getD · 0) reg.length` from the repo (Adder.lean).

  CONSTRUCTION (conjugation; reuse `mcxClean` from E2RunwaySynthMCX):
    swapGate reg x y anc := Xmask ; reduceCNOT ; antiCtrlX ; reduceCNOT ; Xmask
  with z := x XOR y, p := lowest set bit of z:
   • Xmask   : X reg[i] for each i with x.testBit i — maps reg-value v ↦ v XOR x.
   • reduceCNOT : CX reg[p] reg[i] for each i≠p with z.testBit i — maps 0↦0, z↦2^p.
   • antiCtrlX : (X reg[i] for i≠p) ; mcxClean (reg i≠p) reg[p] anc ; (X reg[i] for i≠p)
       — flips reg[p] iff all other reg wires are 0 ⇔ reg-value ∈ {0, 2^p}.
  For x = y (z = 0) the construction reduces to identity on reg-values.

  Kernel-clean target: no `sorry`, no `native_decide`.
-/
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

/-! ## §4. Value-level reasoning for the conjugation. -/

/-- When bit `p` of `z` is set, `clearBit z p = z XOR 2^p`. -/
theorem clearBit_eq_xor (z p : Nat) (hzp : z.testBit p = true) :
    clearBit z p = z ^^^ 2 ^ p := by
  unfold clearBit
  congr 1
  -- z &&& 2^p = 2^p
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hip : i = p
  · subst hip; rw [hzp]; simp
  · have : ¬ p = i := fun h => hip h.symm
    simp [this]

/-- `andExceptP M p k = true` for `M = maskAllExceptP k p` (every bit `i ≠ p`,
    `i < k`, of `M` is set). -/
theorem andExceptP_maskAllExceptP (k p : Nat) :
    andExceptP (maskAllExceptP k p) p k = true := by
  unfold andExceptP
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨hilt, hip⟩ := (mem_ctrlIdxs k p i).mp hi
  rw [maskAllExceptP_testBit k p i hilt]
  simp [hip]

/-- `andExceptP (2^p XOR M) p k = true` (each bit `i ≠ p`, `i < k`, is
    `false XOR true = true`). -/
theorem andExceptP_two_pow_xor_mask (k p : Nat) (_hp : p < k) :
    andExceptP (2 ^ p ^^^ maskAllExceptP k p) p k = true := by
  unfold andExceptP
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨hilt, hip⟩ := (mem_ctrlIdxs k p i).mp hi
  rw [Nat.testBit_xor, maskAllExceptP_testBit k p i hilt, Nat.testBit_two_pow]
  have : ¬ p = i := fun h => hip h.symm
  simp [hip, this]

/-! ## §4b. The stage permutations as named functions. -/

/-- `πreduce z p`: the reduceCNOT value permutation. -/
def piReduce (z p : Nat) (v : Nat) : Nat := if v.testBit p then v ^^^ clearBit z p else v

/-- `πanti k p`: the antiCtrlX value permutation (swaps `0 ↔ 2^p`, fixes others). -/
def piAnti (k p : Nat) (v : Nat) : Nat :=
  if andExceptP (v ^^^ maskAllExceptP k p) p k then v ^^^ 2 ^ p else v

/-- `clearBit z p` has bit `p` clear. -/
theorem clearBit_testBit_self (z p : Nat) : (clearBit z p).testBit p = false := by
  rw [clearBit_testBit]; simp

/-- `piReduce` preserves bit `p`. -/
theorem piReduce_testBit_p (z p v : Nat) : (piReduce z p v).testBit p = v.testBit p := by
  unfold piReduce
  by_cases hb : v.testBit p
  · rw [if_pos hb, Nat.testBit_xor, clearBit_testBit_self, Bool.xor_false]
  · rw [if_neg hb]

/-- `piReduce` is an involution. -/
theorem piReduce_involutive (z p v : Nat) : piReduce z p (piReduce z p v) = v := by
  unfold piReduce
  by_cases hb : v.testBit p
  · have hb' : (v ^^^ clearBit z p).testBit p = true := by
      rw [Nat.testBit_xor, clearBit_testBit_self, Bool.xor_false]; exact hb
    rw [if_pos hb, if_pos hb', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rw [if_neg hb, if_neg hb]

/-- `piAnti` fixes every value not in `{0, 2^p}` (when `p < k`).  More precisely:
    if some bit `i ≠ p` (`i < k`) of `w` is set, `piAnti` fixes `w`. -/
theorem piAnti_fix (k p w : Nat) (_hp : p < k)
    (hne : ¬ andExceptP (w ^^^ maskAllExceptP k p) p k) : piAnti k p w = w := by
  unfold piAnti; rw [if_neg hne]

/-- The net value permutation of the conjugation (`x ≠ y` case). -/
noncomputable def swapNet (k x y : Nat) (v : Nat) : Nat :=
  (piReduce (x ^^^ y) (lowestBit (x ^^^ y))
    (piAnti k (lowestBit (x ^^^ y))
      (piReduce (x ^^^ y) (lowestBit (x ^^^ y)) (v ^^^ x)))) ^^^ x

/-! ### The two moved values. -/

/-- `swapNet` sends `x` to `y`. -/
theorem swapNet_x (k x y : Nat) (hxy : x ≠ y) (_hp : lowestBit (x ^^^ y) < k) :
    swapNet k x y x = y := by
  have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
  set z := x ^^^ y with hzdef
  set p := lowestBit z with hpdef
  have hzp : z.testBit p = true := by rw [hpdef]; exact testBit_lowestBit z hz
  unfold swapNet
  rw [← hzdef, ← hpdef]
  -- v ^^^ x = x ^^^ x = 0
  rw [Nat.xor_self]
  -- piReduce z p 0 = 0 (bit p of 0 is false)
  have h0 : piReduce z p 0 = 0 := by unfold piReduce; simp
  rw [h0]
  -- piAnti k p 0 = 0 ^^^ 2^p (condition true)
  have hanti : piAnti k p 0 = 2 ^ p := by
    unfold piAnti
    rw [Nat.zero_xor, if_pos (andExceptP_maskAllExceptP k p), Nat.zero_xor]
  rw [hanti]
  -- piReduce z p (2^p) = 2^p ^^^ clearBit z p = z
  have hred : piReduce z p (2 ^ p) = z := by
    unfold piReduce
    rw [if_pos (by rw [Nat.testBit_two_pow_self]), clearBit_eq_xor z p hzp]
    -- 2^p ^^^ (z ^^^ 2^p) = z
    rw [Nat.xor_comm z (2 ^ p), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hred]
  -- z ^^^ x = (x ^^^ y) ^^^ x = y
  rw [hzdef, Nat.xor_comm x y, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- `swapNet` sends `y` to `x`. -/
theorem swapNet_y (k x y : Nat) (hxy : x ≠ y) (hp : lowestBit (x ^^^ y) < k) :
    swapNet k x y y = x := by
  have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
  set z := x ^^^ y with hzdef
  set p := lowestBit z with hpdef
  have hzp : z.testBit p = true := by rw [hpdef]; exact testBit_lowestBit z hz
  unfold swapNet
  rw [← hzdef, ← hpdef]
  -- y ^^^ x = z
  have hyx : y ^^^ x = z := by rw [hzdef, Nat.xor_comm]
  rw [hyx]
  -- piReduce z p z = z ^^^ clearBit z p = 2^p
  have hred1 : piReduce z p z = 2 ^ p := by
    unfold piReduce
    rw [if_pos hzp, clearBit_eq_xor z p hzp, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hred1]
  -- piAnti k p (2^p) = 0  (condition true; 2^p ^^^ 2^p = 0)
  have hanti : piAnti k p (2 ^ p) = 0 := by
    unfold piAnti
    rw [if_pos (andExceptP_two_pow_xor_mask k p hp), Nat.xor_self]
  rw [hanti]
  -- piReduce z p 0 = 0
  have hred2 : piReduce z p 0 = 0 := by unfold piReduce; simp
  rw [hred2, Nat.zero_xor]

/-- If the anti-condition holds for `w < 2^k`, then `w ∈ {0, 2^p}` (`p < k`). -/
theorem andExceptP_xor_mask_cases (k p w : Nat) (hp : p < k) (hw : w < 2 ^ k)
    (hcond : andExceptP (w ^^^ maskAllExceptP k p) p k = true) :
    w = 0 ∨ w = 2 ^ p := by
  -- every bit i ≠ p (i < k) of w is 0; and bits ≥ k are 0 (w < 2^k).
  have hbits : ∀ i, i ≠ p → w.testBit i = false := by
    intro i hip
    by_cases hik : i < k
    · -- use the condition
      unfold andExceptP at hcond
      rw [List.all_eq_true] at hcond
      have hi_mem : i ∈ ctrlIdxs k p := (mem_ctrlIdxs k p i).mpr ⟨hik, hip⟩
      have := hcond i hi_mem
      rw [Nat.testBit_xor, maskAllExceptP_testBit k p i hik] at this
      simp [hip] at this
      exact this
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hik)))
  by_cases hwp : w.testBit p
  · right
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow]
    by_cases hip : i = p
    · subst hip; rw [hwp]; simp
    · rw [hbits i hip]; have : ¬ p = i := fun h => hip h.symm; simp [this]
  · left
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hip : i = p
    · subst hip; exact Bool.not_eq_true _ ▸ hwp
    · exact hbits i hip

/-- `swapNet` fixes every value other than `x` and `y` (in range). -/
theorem swapNet_other (k x y : Nat) (hxy : x ≠ y)
    (hp : lowestBit (x ^^^ y) < k) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (v : Nat) (hv : v < 2 ^ k) (hvx : v ≠ x) (hvy : v ≠ y) :
    swapNet k x y v = v := by
  have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
  set z := x ^^^ y with hzdef
  set p := lowestBit z with hpdef
  -- g v := piReduce z p (v ^^^ x); it is < 2^k.
  set g := piReduce z p (v ^^^ x) with hg
  have hzlt : z < 2 ^ k := hzdef ▸ Nat.xor_lt_two_pow hx hy
  have hg_lt : g < 2 ^ k := by
    rw [hg]; unfold piReduce
    by_cases hb : (v ^^^ x).testBit p
    · rw [if_pos hb]; exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hv hx) (clearBit_lt z p k hzlt)
    · rw [if_neg hb]; exact Nat.xor_lt_two_pow hv hx
  -- the anti-condition must be false, else g ∈ {0, 2^p} ⇒ v ∈ {x, y}.
  have hcond_false : andExceptP (g ^^^ maskAllExceptP k p) p k = false := by
    by_contra hc
    have hc' : andExceptP (g ^^^ maskAllExceptP k p) p k = true := Bool.not_eq_false _ ▸ hc
    rcases andExceptP_xor_mask_cases k p g hp hg_lt hc' with hg0 | hgp
    · -- g = 0 ⇒ v ^^^ x = 0 ⇒ v = x.
      apply hvx
      have : piReduce z p (v ^^^ x) = 0 := hg0
      have h2 : v ^^^ x = 0 := by
        have := congrArg (piReduce z p) this
        rwa [piReduce_involutive, show piReduce z p 0 = 0 from by unfold piReduce; simp] at this
      exact Nat.xor_eq_zero_iff.mp h2
    · -- g = 2^p ⇒ v ^^^ x = z ⇒ v = y.
      apply hvy
      have : piReduce z p (v ^^^ x) = 2 ^ p := hgp
      have h2 : v ^^^ x = z := by
        have hh := congrArg (piReduce z p) this
        rw [piReduce_involutive] at hh
        -- piReduce z p (2^p) = z
        have hzp : z.testBit p = true := by rw [hpdef]; exact testBit_lowestBit z hz
        have hred : piReduce z p (2 ^ p) = z := by
          unfold piReduce
          rw [if_pos (by rw [Nat.testBit_two_pow_self]), clearBit_eq_xor z p hzp,
              Nat.xor_comm z (2 ^ p), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [hred] at hh; exact hh
      -- v = y: v ^^^ x = x ^^^ y ⇒ v = y
      have : v = z ^^^ x := by rw [← h2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [this, hzdef, Nat.xor_comm x y, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  -- with the condition false, piAnti fixes g, and the conjugation collapses.
  unfold swapNet
  rw [← hzdef, ← hpdef, ← hg, piAnti_fix k p g hp (by rw [hcond_false]; simp)]
  rw [hg, piReduce_involutive, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

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

/-! ## §7. Smoke checks (definitional). -/

-- `x = y` ⇒ the gate is the identity.
example (reg anc : List Nat) (x : Nat) : swapGate reg x x anc = Gate.I := by
  unfold swapGate; rw [if_pos rfl]

-- The lowest set bit of `1` is `0`; of `2` is `1`; of `6 = 0b110` is `1`.
example : lowestBit 1 = 0 := by
  unfold lowestBit; rw [dif_pos ⟨0, by decide⟩]; exact Nat.find_eq_zero _ |>.mpr (by decide)

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
