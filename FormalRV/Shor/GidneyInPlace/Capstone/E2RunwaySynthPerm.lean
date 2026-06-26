/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm —
  SYNTH-3 (attempt A): a GENERIC permutation gate on a register, with proven
  CLEAN-ancilla action.
  ════════════════════════════════════════════════════════════════════════════

  Goal: given an arbitrary `σ : Equiv.Perm (Fin (2^k))` (k = reg.length), build a
  reversible gate `permGate reg σ anc : Gate` that, on clean-ancilla inputs,
  applies `σ` to the register VALUE and frames everything else.

  CONSTRUCTION (two layers):

   (1) List-level core (NO Mathlib): a fold of transposition gates.
         permGateOfList reg l anc := l.foldr (fun p g => Gate.seq (swapGate reg p.1 p.2 anc) g) Gate.I
       acts as the foldr composition of the value-transpositions `vswap`.

   (2) Mathlib bridge: factor `σ` into swaps via `Equiv.Perm.truncSwapFactors`,
       extract a concrete `List (Nat × Nat)` (Classical), and show the folded
       value-permutation equals `σ`-on-values.

  Kernel-clean target: axioms ⊆ {propext, Classical.choice, Quot.sound};
  no `sorry`, no `native_decide`.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap
import Mathlib.GroupTheory.Perm.Sign

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthSwap

/-! ## §0. The clean value-transposition `vswap`.

`swapGate_RegAct` exposes the action as `swapNet` (the conjugation-based
permutation).  For composing many of them and bridging to `Equiv.swap`, the
simple if-then-else transposition `vswap` is far easier to reason with.  We
prove `swapGate` realises `vswap` on in-range inputs. -/

/-- The value transposition of `a` and `b`: swaps `a ↔ b`, fixes everything else. -/
def vswap (a b v : Nat) : Nat := if v = a then b else if v = b then a else v

/-- `vswap` preserves the value range `[0, 2^k)`. -/
theorem vswap_lt (a b : Nat) (k : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (v : Nat) (hv : v < 2 ^ k) : vswap a b v < 2 ^ k := by
  unfold vswap
  by_cases h1 : v = a
  · rw [if_pos h1]; exact hb
  · rw [if_neg h1]
    by_cases h2 : v = b
    · rw [if_pos h2]; exact ha
    · rw [if_neg h2]; exact hv

/-- **`swapGate` realises `vswap`.**  For `x, y < 2^k` (and the usual register /
    ancilla side-conditions), `swapGate reg x y anc` acts on the register value
    as the simple transposition `vswap x y`. -/
theorem swapGate_RegAct_vswap (reg : List Nat) (x y : Nat) (anc : List Nat)
    (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hx : x < 2 ^ reg.length) (hy : y < 2 ^ reg.length)
    (hlen : reg.length ≤ anc.length + 1) :
    RegAct (swapGate reg x y anc) reg anc (vswap x y) := by
  -- `swapGate_RegAct` gives the action as `if x = y then id else swapNet k x y`.
  have hbase := swapGate_RegAct reg x y anc hnd hanc hdisj hx hy hlen
  -- it suffices that this permutation AGREES with `vswap x y` pointwise on the
  -- whole `Nat` domain (RegAct's π is total), and we only ever evaluate it on
  -- in-range values; but RegAct requires equality of the π functions, so we
  -- rewrite the π using a pointwise-equality of functions restricted to where it
  -- matters.  Cleaner: prove the two RegActs share the SAME observable behaviour
  -- by replacing π with `vswap x y` via `RegAct_congr` (only need agreement on
  -- in-range inputs).
  refine ⟨vswap_lt x y reg.length hx hy, ?_⟩
  obtain ⟨_, hact⟩ := hbase
  intro f hclean
  rw [hact f hclean]
  -- the two `setReg` agree because the written values agree (regVal f < 2^k).
  have hv : regVal reg f < 2 ^ reg.length := regVal_lt reg f
  congr 1
  -- goal: (if x = y then id else swapNet k x y) (regVal f) = vswap x y (regVal f)
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, id_eq]
    unfold vswap
    by_cases h1 : regVal reg f = x
    · rw [if_pos h1]; exact h1
    · rw [if_neg h1, if_neg h1]
  · rw [if_neg hxy]
    set v := regVal reg f with hvdef
    have hz : x ^^^ y ≠ 0 := fun h => hxy (Nat.xor_eq_zero_iff.mp h)
    have hzlt : x ^^^ y < 2 ^ reg.length := Nat.xor_lt_two_pow hx hy
    have hplt : lowestBit (x ^^^ y) < reg.length := lowestBit_lt _ reg.length hz hzlt
    unfold vswap
    by_cases h1 : v = x
    · rw [if_pos h1, h1, swapNet_x reg.length x y hxy hplt]
    · rw [if_neg h1]
      by_cases h2 : v = y
      · rw [if_pos h2, h2, swapNet_y reg.length x y hxy hplt]
      · rw [if_neg h2, swapNet_other reg.length x y hxy hplt hx hy v hv h1 h2]

/-! ## §1. The list-level permutation gate. -/

/-- The list-level permutation gate: a right-fold of transposition gates over a
    list of value-pairs.  This is the reusable, Mathlib-free core. -/
noncomputable def permGateOfList (reg : List Nat) (l : List (Nat × Nat)) (anc : List Nat) : Gate :=
  l.foldr (fun p g => Gate.seq (swapGate reg p.1 p.2 anc) g) Gate.I

/-- Head-peel for `permGateOfList`. -/
theorem permGateOfList_cons (reg : List Nat) (p : Nat × Nat) (l : List (Nat × Nat))
    (anc : List Nat) :
    permGateOfList reg (p :: l) anc
      = Gate.seq (swapGate reg p.1 p.2 anc) (permGateOfList reg l anc) := by
  unfold permGateOfList; rw [List.foldr_cons]

/-- The folded value-permutation realised by `permGateOfList`: the right-fold of
    the value transpositions `vswap`.  (Composition order matches `RegAct_seq`:
    the head swap is applied FIRST, the tail's composite SECOND.) -/
def permOfList (l : List (Nat × Nat)) : Nat → Nat :=
  l.foldr (fun p π => fun v => π (vswap p.1 p.2 v)) id

/-- Head-peel for `permOfList`. -/
theorem permOfList_cons (p : Nat × Nat) (l : List (Nat × Nat)) :
    permOfList (p :: l) = (fun v => permOfList l (vswap p.1 p.2 v)) := by
  unfold permOfList; rw [List.foldr_cons]

/-- **`permGateOfList_RegAct`.**  On a `Nodup` register with a disjoint, clean,
    big-enough ancilla, `permGateOfList reg l anc` acts on the register value as
    the folded value-transposition `permOfList l`, PROVIDED every pair is in
    range. -/
theorem permGateOfList_RegAct (reg : List Nat) (l : List (Nat × Nat)) (anc : List Nat)
    (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hlen : reg.length ≤ anc.length + 1)
    (hpairs : ∀ p ∈ l, p.1 < 2 ^ reg.length ∧ p.2 < 2 ^ reg.length) :
    RegAct (permGateOfList reg l anc) reg anc (permOfList l) := by
  induction l with
  | nil =>
    -- empty list: identity gate, identity permutation.
    show RegAct (permGateOfList reg [] anc) reg anc (permOfList [])
    have : permOfList ([] : List (Nat × Nat)) = id := rfl
    rw [this]
    -- permGateOfList reg [] anc = Gate.I
    show RegAct Gate.I reg anc id
    exact RegAct_id reg anc hnd
  | cons p l ih =>
    rw [permGateOfList_cons, permOfList_cons]
    have hp := hpairs p (by simp)
    have hhead : RegAct (swapGate reg p.1 p.2 anc) reg anc (vswap p.1 p.2) :=
      swapGate_RegAct_vswap reg p.1 p.2 anc hnd hanc hdisj hp.1 hp.2 hlen
    have htail : RegAct (permGateOfList reg l anc) reg anc (permOfList l) :=
      ih (fun q hq => hpairs q (by simp [hq]))
    -- compose: seq head tail acts as (permOfList l) ∘ (vswap p.1 p.2)
    have := RegAct_seq (swapGate reg p.1 p.2 anc) (permGateOfList reg l anc)
      reg anc (vswap p.1 p.2) (permOfList l) hnd hdisj hhead htail
    -- the resulting π is exactly `fun v => permOfList l (vswap p.1 p.2 v)`.
    exact this

/-! ## §2. Well-typedness of the list-level gate. -/

/-- **`permGateOfList_wellTyped`.**  Every transposition leg is well-typed, so the
    fold is. -/
theorem permGateOfList_wellTyped (reg : List Nat) (l : List (Nat × Nat)) (anc : List Nat)
    (dim : Nat) (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hdim : 0 < dim) (hregb : ∀ q ∈ reg, q < dim) (hancb : ∀ a ∈ anc, a < dim)
    (hlen : reg.length ≤ anc.length + 1)
    (hpairs : ∀ p ∈ l, p.1 < 2 ^ reg.length ∧ p.2 < 2 ^ reg.length) :
    Gate.WellTyped dim (permGateOfList reg l anc) := by
  induction l with
  | nil =>
    show Gate.WellTyped dim (permGateOfList reg [] anc)
    exact hdim
  | cons p l ih =>
    rw [permGateOfList_cons]
    have hp := hpairs p (by simp)
    refine ⟨?_, ih (fun q hq => hpairs q (by simp [hq]))⟩
    exact swapGate_wellTyped reg p.1 p.2 anc dim hp.1 hp.2 hnd hanc hdisj hdim hregb hancb hlen

/-! ## §3. Mathlib bridge: from a `Perm (Fin (2^k))` to a swap-pair list.

We factor `σ` into swaps via `Equiv.Perm.swapFactors` (available because
`Fin (2^k)` is a `LinearOrder`), map each swap `Equiv.swap a b` to the pair
`(a.val, b.val)`, and show the resulting `permOfList` realises `σ` on values. -/

section Bridge

variable {k : Nat}

open Equiv Equiv.Perm

open Classical in
/-- A noncomputable choice of underlying pair of a swap-permutation of `Fin n`,
    returned as a `Nat × Nat` (the two `.val`s).  Junk `(0, 0)` off the swap
    locus. -/
noncomputable def permToPair (g : Equiv.Perm (Fin (2 ^ k))) : Nat × Nat :=
  if h : g.IsSwap then
    ((Classical.choose h).val, (Classical.choose (Classical.choose_spec h)).val)
  else (0, 0)

/-- For a swap `g = swap a b`, `permToPair g` returns `(a.val, b.val)` for the
    chosen witnesses, and `g = swap a b` for those witnesses. -/
theorem permToPair_spec (g : Equiv.Perm (Fin (2 ^ k))) (h : g.IsSwap) :
    ∃ a b : Fin (2 ^ k), a ≠ b ∧ g = Equiv.swap a b ∧
      permToPair g = (a.val, b.val) := by
  refine ⟨Classical.choose h, Classical.choose (Classical.choose_spec h), ?_, ?_, ?_⟩
  · exact (Classical.choose_spec (Classical.choose_spec h)).1
  · exact (Classical.choose_spec (Classical.choose_spec h)).2
  · unfold permToPair; rw [dif_pos h]

/-- **Per-swap value bridge.**  For `g = swap a b` (a, b : Fin (2^k)) and
    `v < 2^k`, the simple value transposition `vswap` of the pair equals applying
    `g` to `⟨v⟩` and reading off `.val`. -/
theorem vswap_permToPair (g : Equiv.Perm (Fin (2 ^ k))) (h : g.IsSwap)
    (v : Nat) (hv : v < 2 ^ k) :
    vswap (permToPair g).1 (permToPair g).2 v = (g ⟨v, hv⟩ : Fin (2 ^ k)).val := by
  obtain ⟨a, b, _hab, hg, hpair⟩ := permToPair_spec g h
  rw [hpair]
  -- now both sides in terms of a, b.
  show vswap a.val b.val v = (g ⟨v, hv⟩).val
  rw [hg, Equiv.swap_apply_def]
  unfold vswap
  -- match the two if-then-else, comparing `v = a.val` with `⟨v,hv⟩ = a`.
  by_cases h1 : (⟨v, hv⟩ : Fin (2 ^ k)) = a
  · have h1' : v = a.val := by rw [← h1]
    rw [if_pos h1', if_pos h1]
  · have h1' : v ≠ a.val := fun heq => h1 (by apply Fin.ext; exact heq)
    rw [if_neg h1', if_neg h1]
    by_cases h2 : (⟨v, hv⟩ : Fin (2 ^ k)) = b
    · have h2' : v = b.val := by rw [← h2]
      rw [if_pos h2', if_pos h2]
    · have h2' : v ≠ b.val := fun heq => h2 (by apply Fin.ext; exact heq)
      rw [if_neg h2', if_neg h2]

/-- Each pair produced by `permToPair` from a list of swaps is in range. -/
theorem permToPair_mem_lt (L : List (Equiv.Perm (Fin (2 ^ k))))
    (hL : ∀ g ∈ L, g.IsSwap) :
    ∀ p ∈ L.map permToPair, p.1 < 2 ^ k ∧ p.2 < 2 ^ k := by
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨g, hgL, rfl⟩ := hp
  obtain ⟨a, b, _, _, hpair⟩ := permToPair_spec g (hL g hgL)
  rw [hpair]
  exact ⟨a.isLt, b.isLt⟩

/-- **The bridge lemma.**  For a list `L` of swap-permutations of `Fin (2^k)`,
    the folded value-permutation of the mapped pair-list equals applying the
    INVERSE of the product to `⟨v⟩` (the order reversal between `permOfList`'s
    head-first composition and `List.prod`'s head-last composition). -/
theorem permOfList_map_eq_inv_prod (L : List (Equiv.Perm (Fin (2 ^ k))))
    (hL : ∀ g ∈ L, g.IsSwap) (v : Nat) (hv : v < 2 ^ k) :
    permOfList (L.map permToPair) v = ((L.prod)⁻¹ ⟨v, hv⟩ : Fin (2 ^ k)).val := by
  induction L generalizing v with
  | nil =>
    -- permOfList [] v = v ; (1⁻¹ ⟨v⟩).val = v
    show v = ((1 : Equiv.Perm (Fin (2 ^ k)))⁻¹ ⟨v, hv⟩).val
    simp
  | cons g L ih =>
    rw [List.map_cons, permOfList_cons]
    simp only []
    -- head g is a swap.
    have hg : g.IsSwap := hL g (by simp)
    -- vswap of the head pair = applying g.
    have hstep : vswap (permToPair g).1 (permToPair g).2 v = (g ⟨v, hv⟩).val :=
      vswap_permToPair g hg v hv
    rw [hstep]
    -- the new value (g ⟨v⟩).val is < 2^k.
    have hgv : (g ⟨v, hv⟩ : Fin (2 ^ k)).val < 2 ^ k := (g ⟨v, hv⟩).isLt
    -- apply IH at this value.
    rw [ih (fun h hmem => hL h (by simp [hmem])) (g ⟨v, hv⟩).val hgv]
    -- ⟨(g⟨v⟩).val, _⟩ = g ⟨v⟩.
    have hcast : (⟨(g ⟨v, hv⟩).val, hgv⟩ : Fin (2 ^ k)) = g ⟨v, hv⟩ := by
      apply Fin.ext; rfl
    rw [hcast]
    -- ((L.prod)⁻¹ (g ⟨v⟩)).val = (((g :: L).prod)⁻¹ ⟨v⟩).val
    congr 1
    -- (g :: L).prod = g * L.prod ; ((g * L.prod)⁻¹) = (L.prod)⁻¹ * g⁻¹ = (L.prod)⁻¹ * g
    rw [List.prod_cons, mul_inv_rev]
    -- g is a swap, so g⁻¹ = g.
    obtain ⟨a, b, _, hgab, _⟩ := permToPair_spec g hg
    rw [hgab, Equiv.swap_inv, ← hgab]
    rfl

/-! ## §4. The generic permutation gate. -/

/-- **The generic permutation gate.**  Factor `σ` (well, `σ⁻¹`, to absorb the
    order reversal) into swaps and apply the corresponding transposition fold. -/
noncomputable def permGate (reg : List Nat) (σ : Equiv.Perm (Fin (2 ^ reg.length)))
    (anc : List Nat) : Gate :=
  permGateOfList reg ((Equiv.Perm.swapFactors σ⁻¹).val.map permToPair) anc

/-- The value-permutation that `permGate` realises: `σ` applied to the register
    value (Fin → Nat via `.val`), identity off-range. -/
def permOnVal (reg : List Nat) (σ : Equiv.Perm (Fin (2 ^ reg.length))) (v : Nat) : Nat :=
  if h : v < 2 ^ reg.length then (σ ⟨v, h⟩ : Fin (2 ^ reg.length)).val else v

/-- **`permGate_RegAct`.**  On a `Nodup` register with a disjoint, clean,
    big-enough ancilla, `permGate reg σ anc` applies `σ` to the register value
    (framing everything else, restoring the ancilla). -/
theorem permGate_RegAct (reg : List Nat) (σ : Equiv.Perm (Fin (2 ^ reg.length)))
    (anc : List Nat) (hnd : reg.Nodup) (hanc : anc.Nodup) (hdisj : ∀ a ∈ anc, a ∉ reg)
    (hlen : reg.length ≤ anc.length + 1) :
    RegAct (permGate reg σ anc) reg anc (permOnVal reg σ) := by
  unfold permGate
  set L := (Equiv.Perm.swapFactors σ⁻¹).val with hLdef
  have hLswap : ∀ g ∈ L, g.IsSwap := (Equiv.Perm.swapFactors σ⁻¹).property.2
  have hLprod : L.prod = σ⁻¹ := (Equiv.Perm.swapFactors σ⁻¹).property.1
  -- list-level RegAct, with the mapped pairs.
  have hbase := permGateOfList_RegAct reg (L.map permToPair) anc hnd hanc hdisj hlen
    (permToPair_mem_lt L hLswap)
  -- it remains to show `permOfList (L.map permToPair) = permOnVal reg σ`.
  -- Use RegAct's tolerance for the π only being evaluated at in-range values:
  -- we show the two π functions agree on `[0, 2^k)` and supply the range bound
  -- for `permOnVal` separately.
  obtain ⟨_, hact⟩ := hbase
  refine ⟨?_, ?_⟩
  · -- range preservation for permOnVal
    intro v hv
    unfold permOnVal; rw [dif_pos hv]; exact (σ ⟨v, hv⟩).isLt
  · intro f hclean
    rw [hact f hclean]
    congr 1
    -- agree at the in-range value `regVal reg f`.
    set v := regVal reg f with hvdef
    have hv : v < 2 ^ reg.length := hvdef ▸ regVal_lt reg f
    rw [permOfList_map_eq_inv_prod L hLswap v hv]
    unfold permOnVal
    rw [dif_pos hv, hLprod, inv_inv]

/-- **`permGate_wellTyped`.**  When every register and ancilla wire is `< dim`. -/
theorem permGate_wellTyped (reg : List Nat) (σ : Equiv.Perm (Fin (2 ^ reg.length)))
    (anc : List Nat) (dim : Nat) (hnd : reg.Nodup) (hanc : anc.Nodup)
    (hdisj : ∀ a ∈ anc, a ∉ reg) (hdim : 0 < dim) (hregb : ∀ q ∈ reg, q < dim)
    (hancb : ∀ a ∈ anc, a < dim) (hlen : reg.length ≤ anc.length + 1) :
    Gate.WellTyped dim (permGate reg σ anc) := by
  unfold permGate
  exact permGateOfList_wellTyped reg _ anc dim hnd hanc hdisj hdim hregb hancb hlen
    (permToPair_mem_lt _ (Equiv.Perm.swapFactors σ⁻¹).property.2)

end Bridge

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthPerm
