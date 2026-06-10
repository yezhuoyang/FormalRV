/-
  FormalRV.Arithmetic.UnaryLookup.UnaryLookupGrayCode — the GATE-LEVEL
  Gray-code/sawtooth QROM lookup (babbush2018 unary iteration with the
  branch-switch CX trick).

  ## What this file makes real

  The repo's faithful per-row QROM read (`lookupReadAt`, built on
  `BQAlgo.unary_lookup_multi_iteration`) re-runs the full `w`-deep prefix-AND
  cascade for every one of the `2^w` table rows: `14·w·2^w` T
  (= `2·w·2^w` Toffolis) per table read.  The Gray-code amortization that
  Gidney–Ekerå 2021 (and qianxu p. 23) charge for was previously present
  ONLY as the cost formula `BQAlgo.gray_code_unary_lookup_toffoli_count`
  — a number with no circuit behind it.

  This file builds the actual circuit: a recursive unary-iteration tree walk
  (`grayWalk`) over the SAME wire layout as the faithful read
  (`ulookup_ctrl_idx` / `ulookup_address_idx` / `ulookup_and_idx`, word bits at
  caller-chosen positions `pos j`).  Per internal node at level `i` with parent
  wire `p` and address wire `a_i`:

    ENTER  : `X a_i ; CCX p a_i and_i ; X a_i`   -- and_i := p ∧ ¬a_i   (1 Toffoli)
    (recurse into the 0-subtree)
    SWITCH : `CX p and_i`                        -- and_i := p ∧ a_i    (0 Toffolis!)
    (recurse into the 1-subtree)
    EXIT   : `CCX p a_i and_i`                   -- and_i := 0          (1 Toffoli)

  The SWITCH line is the sawtooth trick: moving from the 0-branch to the
  1-branch costs a single CX, not a recompute of the ladder.  Each of the
  `2^w − 1` internal nodes costs exactly 2 Toffolis (enter + exit), so a full
  table read costs `2·(2^w − 1)` Toffolis (`tcount_grayLookupReadAt`) instead
  of the faithful read's `2·w·2^w` — exactly the `lookupReadAt = w ×
  (grayLookupReadAt + ε)` gap proved in `tcount_lookupReadAt_eq_w_mul_gray`.

  ## Contract parity (drop-in for the windowed machinery)

  `grayLookupReadAt_selects_word` / `grayLookupReadAt_frame` have the SAME
  statement shape as the faithful read's `lookupReadAt_selects_word` /
  `lookupReadAt_frame` (FormalRV/Arithmetic/Windowed/WindowedLookupSelect.lean):
  with ctrl set, the address register holding `v < 2^w`, and the AND-ladder
  clean, the read XORs exactly `(T v).testBit j` into `pos j` and restores
  everything else.  So the Gray-code read can replace the faithful read
  inside the windowed multiplier wholesale.

  ## The residual ×2 vs the paper's `2^w`

  Gidney–Ekerå / qianxu (E9, `PaperClaims.qianxu_E9_lookup_gate_derived_count`)
  charge `2^w` Toffolis per lookup, not our `2·(2^w − 1) ≈ 2·2^w`.  The missing
  factor 2 is the measurement-based uncompute (the EXIT Toffolis are replaced
  by X-basis measurements + classically-controlled Cliffords), which is NOT
  expressible in this file's pure X/CX/CCX `Gate` IR — that leg lives in
  `FormalRV/Shor/MeasUncompute.lean` (extended-IR `EGate` with measurement).
  Within the reversible IR, `2·(2^w − 1)` is the honest optimum this
  construction reaches, and the audit-bridge theorems below quantify both
  the ×w saving over the faithful read and the ×2 residual.
-/
import FormalRV.Arithmetic.Windowed.WindowedLookupSelect

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo

/-! ## §0. Boolean and CX-fan-out-layer helpers. -/

/-- SWITCH-line algebra: with the ladder ancilla holding `P ∧ ¬b`, XOR-ing the
    parent `P` in (the sawtooth CX) leaves `P ∧ b`. -/
private theorem gray_switch (P b : Bool) : xor (P && !b) P = (P && b) := by
  cases P <;> cases b <;> rfl

/-- EXIT-line algebra: the ladder ancilla value
    `((c ⊕ (P ∧ ¬b)) ⊕ P) ⊕ (P ∧ b)` collapses back to its initial value `c` —
    the enter/switch/exit cycle is an exact conjugation on the ladder wire,
    whatever the initial state. -/
private theorem gray_anc_restore (c P b : Bool) :
    xor (xor (xor c (P && !b)) P) (P && b) = c := by
  cases c <;> cases P <;> cases b <;> rfl

/-- Frame for the CX fan-out layer: a position not in the target list is
    untouched (no `Nodup` or control-membership conditions needed). -/
theorem grayCxLayer_not_mem (c : Nat) (xs : List Nat) (f : Nat → Bool) (p : Nat)
    (hp : p ∉ xs) :
    Gate.applyNat (cx_gates_from_indices c xs) f p = f p := by
  induction xs generalizing f with
  | nil => rfl
  | cons t rest ih =>
    have hpt : p ≠ t := fun h => hp (by rw [h]; exact List.mem_cons_self ..)
    have hpr : p ∉ rest := fun h => hp (List.mem_cons_of_mem t h)
    show Gate.applyNat (Gate.seq (cx_gates_from_indices c rest) (Gate.CX c t)) f p = f p
    rw [Gate.applyNat_seq, Gate.applyNat_CX, update_neq _ _ _ _ hpt, ih f hpr]

/-- Action of the CX fan-out layer at a member of a duplicate-free target list
    (control not a target): the control is XOR'd in exactly once. -/
theorem grayCxLayer_mem (c : Nat) (xs : List Nat) (f : Nat → Bool) (p : Nat)
    (hnd : xs.Nodup) (hc : c ∉ xs) (hp : p ∈ xs) :
    Gate.applyNat (cx_gates_from_indices c xs) f p = xor (f p) (f c) := by
  induction xs generalizing f with
  | nil => exact absurd hp (by simp)
  | cons t rest ih =>
    obtain ⟨htr, hndr⟩ := List.nodup_cons.mp hnd
    have hcr : c ∉ rest := fun h => hc (List.mem_cons_of_mem t h)
    have hct : c ≠ t := fun h => hc (by rw [h]; exact List.mem_cons_self ..)
    show Gate.applyNat (Gate.seq (cx_gates_from_indices c rest) (Gate.CX c t)) f p
        = xor (f p) (f c)
    rw [Gate.applyNat_seq, Gate.applyNat_CX]
    rcases List.mem_cons.mp hp with hpt | hpr
    · subst hpt
      rw [update_eq, grayCxLayer_not_mem c rest f p htr,
          grayCxLayer_not_mem c rest f c hcr]
    · have hpt : p ≠ t := fun h => htr (h ▸ hpr)
      rw [update_neq _ _ _ _ hpt, ih f hndr hcr hpr]

/-! ## §1. The selected leaf value: `grayMidBits`.

The walk at level `i` with `d` levels remaining selects the leaf whose path
bits are the address bits at levels `i, …, i+d−1`.  `grayMidBits v i d` is the
number those bits contribute: `Σ_{k<d} v.testBit(i+k)·2^(i+k)`. -/

/-- Bits `i, i+1, …, i+d−1` of `v`, in place: the leaf-value contribution of
    the levels the walk has yet to traverse. -/
def grayMidBits (v : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, d + 1 => (if v.testBit i then 2 ^ i else 0) + grayMidBits v (i + 1) d

/-- One binary digit of the mod tower:
    `v % 2^(i+1) = v % 2^i + (bit i of v)·2^i`. -/
private theorem gray_mod_two_pow_succ (v i : Nat) :
    v % 2 ^ i + (if v.testBit i then 2 ^ i else 0) = v % 2 ^ (i + 1) := by
  have hmul : v % 2 ^ (i + 1) = v % 2 ^ i + 2 ^ i * (v / 2 ^ i % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hbit : v.testBit i = decide (v / 2 ^ i % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  have h2 : v / 2 ^ i % 2 = 0 ∨ v / 2 ^ i % 2 = 1 := by omega
  rcases h2 with h | h <;> rw [hmul, h, hbit, h] <;> simp

/-- `v % 2^i` plus the remaining mid-bits reconstructs `v % 2^(i+d)`. -/
theorem grayMidBits_mod (v : Nat) : ∀ (d i : Nat),
    v % 2 ^ i + grayMidBits v i d = v % 2 ^ (i + d)
  | 0, i => by simp [grayMidBits]
  | d + 1, i => by
    calc v % 2 ^ i + grayMidBits v i (d + 1)
        = (v % 2 ^ i + (if v.testBit i then 2 ^ i else 0))
            + grayMidBits v (i + 1) d := by
          simp only [grayMidBits]; omega
      _ = v % 2 ^ (i + 1) + grayMidBits v (i + 1) d := by
          rw [gray_mod_two_pow_succ]
      _ = v % 2 ^ ((i + 1) + d) := grayMidBits_mod v d (i + 1)
      _ = v % 2 ^ (i + (d + 1)) := by rw [show (i + 1) + d = i + (d + 1) from by omega]

/-- From the root (`i = 0`, depth `w`), the walk's selected leaf is `v` itself
    (for in-range addresses `v < 2^w`). -/
theorem grayMidBits_eq_self (v w : Nat) (hv : v < 2 ^ w) : grayMidBits v 0 w = v := by
  have h := grayMidBits_mod v w 0
  rw [pow_zero, Nat.mod_one, Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt hv] at h
  exact h

/-! ## §2. The circuit. -/

/-- **The Gray-code/sawtooth tree walk** (babbush2018 unary iteration with the
    branch-switch CX trick), on the faithful lookup's wire layout.

    `grayWalk pos W T d i parent vPrefix` is the subtree at ladder level `i`
    with `d` levels remaining (`d = w − i` from a root call), parent wire
    `parent` (the ctrl qubit at the root, `ulookup_and_idx (i−1)` below), and
    `vPrefix` the row-value bits accumulated on the path so far (bit `k` of the
    row value is the branch taken at level `k`, LSB-first).

    * Leaf (`d = 0`): word-CNOTs for table row `T vPrefix`, controlled on the
      deepest ladder wire (= `parent`), targets `pos j` for the set bits.
    * Internal node: ENTER (1 Toffoli, computes `parent ∧ ¬a_i` onto the
      ladder), 0-subtree, SWITCH (1 CX — the sawtooth), 1-subtree,
      EXIT (1 Toffoli, returns the ladder wire to its initial value). -/
def grayWalk (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    Nat → Nat → Nat → Nat → Gate
  | 0, _, parent, vPrefix =>
      cx_gates_from_indices parent (wordCnotsAt pos W (T vPrefix))
  | d + 1, i, parent, vPrefix =>
      Gate.seq (Gate.seq (Gate.seq (Gate.seq (Gate.seq (Gate.seq
        (Gate.X (ulookup_address_idx i))
        (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i)))
        (Gate.X (ulookup_address_idx i)))
        (grayWalk pos W T d (i + 1) (ulookup_and_idx i) vPrefix))
        (Gate.CX parent (ulookup_and_idx i)))
        (grayWalk pos W T d (i + 1) (ulookup_and_idx i) (vPrefix + 2 ^ i)))
        (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i))

/-- **The Gray-code QROM read**: position-compatible replacement for the
    faithful `lookupReadAt w pos W T` (same ctrl/address/AND-ladder wires, same
    word positions `pos`), at `2·(2^w − 1)` Toffolis instead of `2·w·2^w`. -/
def grayLookupReadAt (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) : Gate :=
  grayWalk pos W T w 0 ulookup_ctrl_idx 0

/-! ## §3. The ENTER conjugation, collapsed.

`X a_i ; CCX parent a_i and_i ; X a_i` is a single update on the ladder wire:
it XORs `parent ∧ ¬a_i` into `and_i` and restores `a_i` (X is an involution).
Collapsing it to one `update` removes the X-conjugation from all the inductions
below. -/

private theorem grayEnter_state (i parent : Nat) (hpar : parent ≤ 2 * i) (f : Nat → Bool) :
    Gate.applyNat (Gate.X (ulookup_address_idx i))
      (Gate.applyNat (Gate.CCX parent (ulookup_address_idx i) (ulookup_and_idx i))
        (Gate.applyNat (Gate.X (ulookup_address_idx i)) f))
      = update f (ulookup_and_idx i)
          (xor (f (ulookup_and_idx i)) (f parent && !f (ulookup_address_idx i))) := by
  have hA : ulookup_address_idx i = 1 + 2 * i := rfl
  have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
  have hCA : ulookup_and_idx i ≠ ulookup_address_idx i := by omega
  have hAC : ulookup_address_idx i ≠ ulookup_and_idx i := by omega
  have hPA : parent ≠ ulookup_address_idx i := by omega
  funext q
  rw [Gate.applyNat_X, Gate.applyNat_CCX, Gate.applyNat_X,
      update_neq _ _ _ _ hCA,                     -- (update f A _) C   = f C
      update_neq _ _ _ _ hPA,                     -- (update f A _) par = f parent
      update_eq]                                  -- (update f A _) A   = !f A
  by_cases hqA : q = ulookup_address_idx i
  · subst hqA
    rw [update_neq _ _ _ _ hAC,                   -- read-back at A through the C-update
        update_eq,                                -- outer X-update applied at A
        update_eq,                                -- inner X-update applied at A
        update_neq _ _ _ _ hAC,                   -- RHS at A
        Bool.not_not]
  · rw [update_neq _ _ _ _ hAC, update_eq, update_neq _ _ _ _ hqA]
    by_cases hqC : q = ulookup_and_idx i
    · subst hqC
      rw [update_eq, update_eq]
    · rw [update_neq _ _ _ _ hqC, update_neq _ _ _ _ hqA, update_neq _ _ _ _ hqC]

/-! ## §4. Frame: everything except the word positions is restored.

NO state hypotheses: the ENTER/SWITCH/EXIT cycle is an exact conjugation on the
ladder wire (`gray_anc_restore`), the X-pair restores the address wire, and the
subtrees only ever write ladder wires ≥ their level and word positions.  This
matches the faithful read's `lookupReadAt_frame` contract exactly. -/

theorem grayWalk_frame (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (d : Nat) :
    ∀ (i parent vPrefix : Nat) (f : Nat → Bool) (p : Nat),
      parent ≤ 2 * i →
      (∀ j, j < W → 2 * (i + d) < pos j) →
      (∀ j, j < W → p ≠ pos j) →
      Gate.applyNat (grayWalk pos W T d i parent vPrefix) f p = f p := by
  induction d with
  | zero =>
    intro i parent vPrefix f p _ _ hp
    show Gate.applyNat (cx_gates_from_indices parent (wordCnotsAt pos W (T vPrefix))) f p = f p
    refine grayCxLayer_not_mem _ _ _ _ (fun hmem => ?_)
    obtain ⟨j, hj, _, hpj⟩ := (mem_wordCnotsAt pos W (T vPrefix) p).mp hmem
    exact hp j hj hpj
  | succ d ih =>
    intro i parent vPrefix f p hpar hpos hp
    have hA : ulookup_address_idx i = 1 + 2 * i := rfl
    have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
    have hPC : parent ≠ ulookup_and_idx i := by omega
    have hAC : ulookup_address_idx i ≠ ulookup_and_idx i := by omega
    have hpos' : ∀ j, j < W → 2 * ((i + 1) + d) < pos j := fun j hj => by
      have := hpos j hj; omega
    have hsub : ∀ (vP : Nat) (g : Nat → Bool) (q : Nat), (∀ j, j < W → q ≠ pos j) →
        Gate.applyNat (grayWalk pos W T d (i + 1) (ulookup_and_idx i) vP) g q = g q :=
      fun vP g q hq => ih (i + 1) (ulookup_and_idx i) vP g q (by omega) hpos' hq
    have hnwP : ∀ j, j < W → parent ≠ pos j := fun j hj => by
      have := hpos j hj; omega
    have hnwA : ∀ j, j < W → ulookup_address_idx i ≠ pos j := fun j hj => by
      have := hpos j hj; omega
    simp only [grayWalk, Gate.applyNat_seq]
    rw [grayEnter_state i parent hpar f]
    by_cases hpC : p = ulookup_and_idx i
    · -- p is THIS node's ladder wire: the enter/switch/exit cycle restores it.
      subst hpC
      rw [Gate.applyNat_CCX, update_eq,
          hsub _ _ _ hp, hsub _ _ _ hnwP, hsub _ _ _ hnwA,
          Gate.applyNat_CX,
          update_eq, update_neq _ _ _ _ hPC, update_neq _ _ _ _ hAC,
          hsub _ _ _ hp, hsub _ _ _ hnwP, hsub _ _ _ hnwA,
          update_eq, update_neq _ _ _ _ hPC, update_neq _ _ _ _ hAC]
      exact gray_anc_restore (f (ulookup_and_idx i)) (f parent)
        (f (ulookup_address_idx i))
    · -- p is any other non-word wire: every stage is an update at the ladder
      -- wire or (by the sub-frame IH) word-position-only.
      rw [Gate.applyNat_CCX, update_neq _ _ _ _ hpC,
          hsub _ _ p hp,
          Gate.applyNat_CX, update_neq _ _ _ _ hpC,
          hsub _ _ p hp,
          update_neq _ _ _ _ hpC]

/-! ## §5. Selection: the walk XORs exactly the addressed row into the words.

**The subtree invariant** (`grayWalk_selects_word`, proved by induction on the
remaining depth `d`): if the parent wire holds `P`, the address wires at levels
`i..i+d−1` hold the bits of `v`, and the ladder wires at those levels are
clean, then the subtree XORs `P ∧ (T (vPrefix + grayMidBits v i d)).testBit j`
into word position `pos j` — the single leaf selected by the address bits,
gated by the parent.  The branch-switch bookkeeping: after ENTER the ladder
wire holds `P ∧ ¬v_i` (the 0-subtree's parent), after SWITCH it holds
`P ∧ v_i` (`gray_switch`), so exactly one of the two sub-contributions
survives, and it is the one matching bit `i` of `v`. -/

theorem grayWalk_selects_word (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (v : Nat)
    (hinj : ∀ j k, j < W → k < W → pos j = pos k → j = k)
    (j : Nat) (hj : j < W) (d : Nat) :
    ∀ (i parent vPrefix : Nat) (f : Nat → Bool),
      parent ≤ 2 * i →
      (∀ ℓ, i ≤ ℓ → ℓ < i + d → f (ulookup_address_idx ℓ) = v.testBit ℓ) →
      (∀ ℓ, i ≤ ℓ → ℓ < i + d → f (ulookup_and_idx ℓ) = false) →
      (∀ k, k < W → 2 * (i + d) < pos k) →
      Gate.applyNat (grayWalk pos W T d i parent vPrefix) f (pos j)
        = xor (f (pos j))
              (f parent && (T (vPrefix + grayMidBits v i d)).testBit j) := by
  induction d with
  | zero =>
    intro i parent vPrefix f hpar _ _ hpos
    show Gate.applyNat (cx_gates_from_indices parent (wordCnotsAt pos W (T vPrefix))) f (pos j)
        = xor (f (pos j)) (f parent && (T (vPrefix + grayMidBits v i 0)).testBit j)
    rw [show grayMidBits v i 0 = 0 from rfl, Nat.add_zero]
    have hc_not : parent ∉ wordCnotsAt pos W (T vPrefix) := fun hmem => by
      obtain ⟨k, hk, _, hpk⟩ := (mem_wordCnotsAt pos W (T vPrefix) parent).mp hmem
      have := hpos k hk; omega
    by_cases hb : (T vPrefix).testBit j = true
    · rw [grayCxLayer_mem parent _ f (pos j)
            (wordCnotsAt_nodup pos W (T vPrefix) hinj) hc_not
            ((mem_wordCnotsAt pos W (T vPrefix) (pos j)).mpr ⟨j, hj, hb, rfl⟩),
          hb, Bool.and_true]
    · rw [Bool.not_eq_true] at hb
      have hnotmem : pos j ∉ wordCnotsAt pos W (T vPrefix) := fun hmem => by
        obtain ⟨k, hk, hbk, hpk⟩ := (mem_wordCnotsAt pos W (T vPrefix) (pos j)).mp hmem
        rw [hinj j k hj hk hpk, hbk] at hb
        exact Bool.noConfusion hb  -- hb : true = false
      rw [grayCxLayer_not_mem parent _ f (pos j) hnotmem, hb,
          Bool.and_false, Bool.xor_false]
  | succ d ih =>
    intro i parent vPrefix f hpar haddr hand hpos
    -- index bookkeeping
    have hA : ulookup_address_idx i = 1 + 2 * i := rfl
    have hC : ulookup_and_idx i = 1 + 2 * i + 1 := rfl
    have hPC : parent ≠ ulookup_and_idx i := by omega
    have hfa : f (ulookup_address_idx i) = v.testBit i := haddr i (Nat.le_refl i) (by omega)
    have hfc : f (ulookup_and_idx i) = false := hand i (Nat.le_refl i) (by omega)
    have hpos' : ∀ k, k < W → 2 * ((i + 1) + d) < pos k := fun k hk => by
      have := hpos k hk; omega
    have hnw : ∀ q, q ≤ 2 * (i + (d + 1)) → ∀ k, k < W → q ≠ pos k :=
      fun q hq k hk => by have := hpos k hk; omega
    have hposjC : pos j ≠ ulookup_and_idx i :=
      (hnw (ulookup_and_idx i) (by omega) j hj).symm
    have hframe : ∀ (vP : Nat) (g : Nat → Bool) (q : Nat), (∀ k, k < W → q ≠ pos k) →
        Gate.applyNat (grayWalk pos W T d (i + 1) (ulookup_and_idx i) vP) g q = g q :=
      fun vP g q hq =>
        grayWalk_frame pos W T d (i + 1) (ulookup_and_idx i) vP g q (by omega) hpos' hq
    -- expose the node structure and collapse the ENTER conjugation
    simp only [grayWalk, Gate.applyNat_seq]
    rw [grayEnter_state i parent hpar f, hfc, hfa, Bool.false_xor]
    -- name the intermediate states
    set g3 : Nat → Bool :=
      update f (ulookup_and_idx i) (f parent && !v.testBit i) with hg3
    set g4 : Nat → Bool :=
      Gate.applyNat (grayWalk pos W T d (i + 1) (ulookup_and_idx i) vPrefix) g3 with hg4
    set g5 : Nat → Bool :=
      Gate.applyNat (Gate.CX parent (ulookup_and_idx i)) g4 with hg5
    set g6 : Nat → Bool :=
      Gate.applyNat (grayWalk pos W T d (i + 1) (ulookup_and_idx i) (vPrefix + 2 ^ i)) g5
      with hg6
    -- §5a. the post-ENTER state g3
    have hg3_pos : g3 (pos j) = f (pos j) := update_neq _ _ _ _ hposjC
    have hg3_C : g3 (ulookup_and_idx i) = (f parent && !v.testBit i) := update_eq _ _ _
    have hg3_par : g3 parent = f parent := update_neq _ _ _ _ hPC
    have hg3_addr : ∀ ℓ, i + 1 ≤ ℓ → ℓ < (i + 1) + d →
        g3 (ulookup_address_idx ℓ) = v.testBit ℓ := fun ℓ h1 h2 => by
      have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
      rw [hg3, update_neq _ _ _ _ (by omega)]
      exact haddr ℓ (by omega) (by omega)
    have hg3_and : ∀ ℓ, i + 1 ≤ ℓ → ℓ < (i + 1) + d →
        g3 (ulookup_and_idx ℓ) = false := fun ℓ h1 h2 => by
      have e1 : ulookup_and_idx ℓ = 1 + 2 * ℓ + 1 := rfl
      rw [hg3, update_neq _ _ _ _ (by omega)]
      exact hand ℓ (by omega) (by omega)
    -- §5b. the 0-subtree: word effect (IH) + non-word frame
    have hg4_pos : g4 (pos j)
        = xor (f (pos j))
              ((f parent && !v.testBit i)
                && (T (vPrefix + grayMidBits v (i + 1) d)).testBit j) := by
      rw [hg4, ih (i + 1) (ulookup_and_idx i) vPrefix g3 (by omega) hg3_addr hg3_and hpos',
          hg3_pos, hg3_C]
    have hg4_C : g4 (ulookup_and_idx i) = (f parent && !v.testBit i) := by
      rw [hg4, hframe vPrefix g3 _ (fun k hk => hnw _ (by omega) k hk), hg3_C]
    have hg4_par : g4 parent = f parent := by
      rw [hg4, hframe vPrefix g3 parent (fun k hk => hnw parent (by omega) k hk), hg3_par]
    -- §5c. the SWITCH: ladder wire flips from P ∧ ¬v_i to P ∧ v_i
    have hg5_eq : g5 = update g4 (ulookup_and_idx i) (f parent && v.testBit i) := by
      rw [hg5, Gate.applyNat_CX, hg4_C, hg4_par, gray_switch]
    have hg5_pos : g5 (pos j) = g4 (pos j) := by
      rw [hg5_eq, update_neq _ _ _ _ hposjC]
    have hg5_C : g5 (ulookup_and_idx i) = (f parent && v.testBit i) := by
      rw [hg5_eq, update_eq]
    have hg5_addr : ∀ ℓ, i + 1 ≤ ℓ → ℓ < (i + 1) + d →
        g5 (ulookup_address_idx ℓ) = v.testBit ℓ := fun ℓ h1 h2 => by
      have e1 : ulookup_address_idx ℓ = 1 + 2 * ℓ := rfl
      rw [hg5_eq, update_neq _ _ _ _ (by omega), hg4,
          hframe vPrefix g3 _ (fun k hk => hnw _ (by omega) k hk)]
      exact hg3_addr ℓ h1 h2
    have hg5_and : ∀ ℓ, i + 1 ≤ ℓ → ℓ < (i + 1) + d →
        g5 (ulookup_and_idx ℓ) = false := fun ℓ h1 h2 => by
      have e1 : ulookup_and_idx ℓ = 1 + 2 * ℓ + 1 := rfl
      rw [hg5_eq, update_neq _ _ _ _ (by omega), hg4,
          hframe vPrefix g3 _ (fun k hk => hnw _ (by omega) k hk)]
      exact hg3_and ℓ h1 h2
    -- §5d. the 1-subtree: word effect (IH)
    have hg6_pos : g6 (pos j)
        = xor (g5 (pos j))
              ((f parent && v.testBit i)
                && (T (vPrefix + 2 ^ i + grayMidBits v (i + 1) d)).testBit j) := by
      rw [hg6, ih (i + 1) (ulookup_and_idx i) (vPrefix + 2 ^ i) g5 (by omega)
            hg5_addr hg5_and hpos', hg5_C]
    -- §5e. assemble through the EXIT Toffoli (an update at the ladder wire)
    rw [Gate.applyNat_CCX, update_neq _ _ _ _ hposjC, hg6_pos, hg5_pos, hg4_pos]
    simp only [grayMidBits]
    cases hbv : v.testBit i <;> simp [Nat.add_assoc]

/-! ## §5′. The headline contracts — drop-in shape-identical with the faithful
read's `lookupReadAt_selects_word` / `lookupReadAt_frame` / `lookupReadAt_selects`
(FormalRV/Arithmetic/Windowed/WindowedLookupSelect.lean). -/

set_option linter.unusedVariables false in
/-- **HEADLINE (word conjunct).**  With ctrl set, the address register holding
    `v < 2^w`, and the AND-ladder clean, the Gray-code/sawtooth QROM read
    `grayLookupReadAt w pos W T` XORs exactly the addressed table row into the
    word positions: bit `j` of `T v` lands at `pos j`.

    Same contract as the faithful `lookupReadAt_selects_word`, at
    `2·(2^w − 1)` Toffolis instead of `2·w·2^w`.  (`hw` is kept for exact
    contract parity with the faithful read; the Gray-code statement also
    holds at `w = 0`.) -/
theorem grayLookupReadAt_selects_word
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool) (v : Nat)
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k)
    (j : Nat) (hj : j < W) :
    Gate.applyNat (grayLookupReadAt w pos W T) f (pos j)
      = xor (f (pos j)) ((T v).testBit j) := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  have h := grayWalk_selects_word pos W T v hpos_inj j hj w 0 ulookup_ctrl_idx 0 f
    (by omega)
    (fun ℓ _ hℓ => haddr ℓ (by omega))
    (fun ℓ _ hℓ => hand ℓ (by omega))
    (fun k hk => by have := hpos_high k hk; omega)
  rw [grayLookupReadAt, h, hctrl, Bool.true_and, Nat.zero_add,
      grayMidBits_eq_self v w hv]

/-- **HEADLINE (frame conjunct).**  Every position that is not a word target
    (`pos j`, `j < W`) is unchanged by the Gray-code read — ctrl preserved,
    address restored, AND-ladder returned to its initial state, everything
    else untouched.  Same contract as the faithful `lookupReadAt_frame`
    (and like it, requires NO assumptions on the input state). -/
theorem grayLookupReadAt_frame
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (p : Nat) (hp : ∀ j, j < W → p ≠ pos j) :
    Gate.applyNat (grayLookupReadAt w pos W T) f p = f p := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  rw [grayLookupReadAt]
  exact grayWalk_frame pos W T w 0 ulookup_ctrl_idx 0 f p (by omega)
    (fun k hk => by have := hpos_high k hk; omega) hp

/-- **HEADLINE (packaged)** — mirror of the faithful `lookupReadAt_selects`:
    the Gray-code/sawtooth QROM read reads exactly the addressed table row,
    and restores everything else. -/
theorem grayLookupReadAt_selects
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool) (v : Nat)
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    (∀ j, j < W →
      Gate.applyNat (grayLookupReadAt w pos W T) f (pos j)
        = xor (f (pos j)) ((T v).testBit j))
    ∧ (∀ p, (∀ j, j < W → p ≠ pos j) →
        Gate.applyNat (grayLookupReadAt w pos W T) f p = f p) :=
  ⟨fun j hj => grayLookupReadAt_selects_word w W T pos f v hw hv hctrl haddr hand
      hpos_high hpos_inj j hj,
   fun p hp => grayLookupReadAt_frame w W T pos f hpos_high p hp⟩

/-! ## §6. Resource counts. -/

/-- T-count of the walk: each of the `2^d − 1` internal nodes of a depth-`d`
    subtree costs exactly the ENTER + EXIT Toffoli pair (`14` T); the SWITCH
    CX, the X-conjugation, and the leaf word-CNOTs are T-free. -/
theorem tcount_grayWalk (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (d : Nat) :
    ∀ (i parent vPrefix : Nat),
      tcount (grayWalk pos W T d i parent vPrefix) = 14 * (2 ^ d - 1) := by
  induction d with
  | zero =>
    intro i parent vPrefix
    show tcount (cx_gates_from_indices parent (wordCnotsAt pos W (T vPrefix))) = _
    rw [tcount_cx_gates_zero]
    norm_num
  | succ d ih =>
    intro i parent vPrefix
    have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    simp only [grayWalk, tcount, ih]
    omega

/-- **T-count of the Gray-code table read**: `14·(2^w − 1)`
    (vs the faithful read's `14·w·2^w`, `tcount_lookupReadAt`). -/
theorem tcount_grayLookupReadAt (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    tcount (grayLookupReadAt w pos W T) = 14 * (2 ^ w - 1) :=
  tcount_grayWalk pos W T w 0 ulookup_ctrl_idx 0

/-- **Toffoli count of the Gray-code table read**: `2·(2^w − 1)` — one ENTER +
    one EXIT Toffoli per internal node of the depth-`w` binary tree. -/
theorem toffoliCount_grayLookupReadAt (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    toffoliCount (grayLookupReadAt w pos W T) = 2 * (2 ^ w - 1) := by
  rw [toffoliCount, tcount_grayLookupReadAt,
      show 14 * (2 ^ w - 1) = 2 * (2 ^ w - 1) * 7 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-! ## §7. Audit bridge: Gray-code read vs the faithful per-row read.

The faithful `lookupReadAt` costs `14·w·2^w` T (`tcount_lookupReadAt`); the
Gray-code read costs `14·(2^w − 1)`.  The exact relation is
`faithful = w · (gray + 14)` — i.e. the Gray-code circuit beats the faithful
one by strictly MORE than the factor `w` the Gray-code amortization promises.

Against the paper's `2^w` Toffolis (`qianxu_E9_lookup_gate_derived_count`),
our `2·(2^w − 1)` carries the residual ×2 of the reversible (non-measurement)
EXIT uncompute — see the module docstring and `FormalRV/Shor/MeasUncompute.lean`. -/

/-- Toffoli count of the faithful per-row read, for comparison: `2·w·2^w`. -/
theorem toffoliCount_lookupReadAt (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    toffoliCount (lookupReadAt w pos W T) = 2 * w * 2 ^ w := by
  rw [toffoliCount, tcount_lookupReadAt,
      show 14 * w * 2 ^ w = 2 * w * 2 ^ w * 7 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- The Gray-code read is never more expensive than the faithful read. -/
theorem tcount_grayLookupReadAt_le_lookupReadAt
    (w : Nat) (hw : 0 < w) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    tcount (grayLookupReadAt w pos W T) ≤ tcount (lookupReadAt w pos W T) := by
  rw [tcount_grayLookupReadAt, tcount_lookupReadAt]
  calc 14 * (2 ^ w - 1) ≤ 14 * 2 ^ w := by
        have := Nat.two_pow_pos w; omega
    _ ≤ 14 * (w * 2 ^ w) := Nat.mul_le_mul_left 14 (Nat.le_mul_of_pos_left _ hw)
    _ = 14 * w * 2 ^ w := by ring

/-- **Exact-gap identity (T-count)**: the faithful read costs exactly `w`
    times the Gray-code read plus `w` ENTER/EXIT pairs:
    `14·w·2^w = w·(14·(2^w − 1) + 14)`. -/
theorem tcount_lookupReadAt_eq_w_mul_gray
    (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    tcount (lookupReadAt w pos W T)
      = w * (tcount (grayLookupReadAt w pos W T) + 14) := by
  rw [tcount_grayLookupReadAt, tcount_lookupReadAt,
      show 14 * (2 ^ w - 1) + 14 = 14 * 2 ^ w from by
        have := Nat.two_pow_pos w; omega]
  ring

/-- **Exact-gap identity (Toffolis)**: `2·w·2^w = w·(2·(2^w − 1) + 2)`. -/
theorem toffoliCount_lookupReadAt_eq_w_mul_gray
    (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    toffoliCount (lookupReadAt w pos W T)
      = w * (toffoliCount (grayLookupReadAt w pos W T) + 2) := by
  rw [toffoliCount_lookupReadAt, toffoliCount_grayLookupReadAt,
      show 2 * (2 ^ w - 1) + 2 = 2 * 2 ^ w from by
        have := Nat.two_pow_pos w; omega]
  ring

/-- The realized circuit sits within ×2 of the scaffolded cost formula
    `gray_code_unary_lookup_toffoli_count w w = w + (2^w − 1)` — sandwich:
    `w + (2^w − 1) ≤ 2·(2^w − 1) ≤ 2·(w + (2^w − 1))`. -/
theorem toffoliCount_grayLookupReadAt_vs_formula
    (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    gray_code_unary_lookup_toffoli_count w w
        ≤ toffoliCount (grayLookupReadAt w pos W T)
      ∧ toffoliCount (grayLookupReadAt w pos W T)
        ≤ 2 * gray_code_unary_lookup_toffoli_count w w := by
  rw [toffoliCount_grayLookupReadAt, gray_code_unary_lookup_toffoli_count]
  have hlt : w < 2 ^ w := Nat.lt_two_pow_self
  omega

/-! ## §8. Kernel-checked smoke tests (w = 1 and w = 2 instances).

Layout reminder: ctrl = 0, address bits at 1, 3, …, ladder ancillas at 2, 4, …,
words at the caller's `pos`. -/

section SmokeTests

/-- w = 1, table `T v = v + 1`, words at 4,5, address `v = 1`: row `T 1 = 2`
    (bits `01`₂ reversed: bit 0 = 0, bit 1 = 1) lands on the words. -/
private def graySmokeF1 : Nat → Bool := fun p => p == 0 || p == 1

example :  -- word bit 0 of T 1 = 2: stays 0
    Gate.applyNat (grayLookupReadAt 1 (fun j => 4 + j) 2 (fun v => v + 1)) graySmokeF1 4
      = false := by decide
example :  -- word bit 1 of T 1 = 2: flips to 1
    Gate.applyNat (grayLookupReadAt 1 (fun j => 4 + j) 2 (fun v => v + 1)) graySmokeF1 5
      = true := by decide
example :  -- ladder ancilla restored clean
    Gate.applyNat (grayLookupReadAt 1 (fun j => 4 + j) 2 (fun v => v + 1)) graySmokeF1 2
      = false := by decide
example :  -- address wire restored
    Gate.applyNat (grayLookupReadAt 1 (fun j => 4 + j) 2 (fun v => v + 1)) graySmokeF1 1
      = true := by decide

/-- w = 2, table `T v = 3·v`, words at 6,7,8, address `v = 2` (bit 0 = 0 at
    wire 1, bit 1 = 1 at wire 3): row `T 2 = 6 = 110₂`. -/
private def graySmokeF2 : Nat → Bool := fun p => p == 0 || p == 3

example :
    (Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 6,
     Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 7,
     Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 8)
      = (false, true, true) := by decide

example :  -- both ladder ancillas restored, both address wires restored, ctrl kept
    (Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 2,
     Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 4,
     Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 1,
     Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 3,
     Gate.applyNat (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) graySmokeF2 0)
      = (false, false, false, true, true) := by decide

example :  -- the count theorems, instantiated: w = 2 read = 2·(2²−1) = 6 Toffolis
    toffoliCount (grayLookupReadAt 2 (fun j => 6 + j) 3 (fun v => 3 * v)) = 6 := by decide

end SmokeTests

end FormalRV.Shor.WindowedCircuit
