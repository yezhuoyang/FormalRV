/-
  FormalRV.QEC.LPCssCondition — toward a PARAMETRIC (native-free) proof that the lifted-
  product LP codes (lp16/lp20) satisfy the CSS condition `H_X H_Z^T = 0`.

  Track (b) of the validity programme: the strengthened verifier's no-native acceptance
  forbids `decide`/`native_decide` on the 2610/4350-column matrices, so `code.valid`
  (= well_shaped ∧ css_condition) must be proven algebraically.  The CSS cancellation of the
  lifted product rests on ONE structural fact — the GF(2) transpose of a lifted circulant
  block equals the lift of the ring conjugate:

      circulant ℓ (circDagger ℓ p) = transpose (circulant ℓ p) ℓ

  currently only `decide`-verified on instances.  This file proves it GENERICALLY (for
  reduced exponent supports `p`, which the real seeds satisfy), via the modular-negation
  bijection `e ↦ (ℓ−e) mod ℓ`.

  Remaining toward `liftedProduct_css_condition` (documented continuation): lift the block
  identity through `liftMat` (`transpose (lift A†) = lift A`), then the ring-level
  cancellation `A⊗A† + A⊗A† = 0` via `circMul` commutativity.

  Needs `Mathlib.Tactic.SplitIfs`.  No `sorry`, no `axiom`, no `native_decide`.
-/

import FormalRV.QEC.FrontendAlgebraic
import Mathlib.Tactic.SplitIfs

namespace FormalRV.QEC.Algebraic

open FormalRV.Framework.LDPC

/-! ## §1. Modular reductions (so `omega` can finish — variable modulus is nonlinear) -/

/-- `(a + ℓ − b) mod ℓ` for `a, b < ℓ`: `a − b` if `b ≤ a`, else `a + ℓ − b`. -/
theorem subMod (a b ℓ : Nat) (hb : b < ℓ) (ha : a < ℓ) :
    (a + ℓ - b) % ℓ = if b ≤ a then a - b else a + ℓ - b := by
  by_cases h : b ≤ a
  · rw [if_pos h]
    have : a + ℓ - b = (a - b) + ℓ := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- `(ℓ − e) mod ℓ` for `e < ℓ`: `0` if `e = 0`, else `ℓ − e` (modular negation). -/
theorem negMod (e ℓ : Nat) (he : e < ℓ) : (ℓ - e) % ℓ = if e = 0 then 0 else ℓ - e := by
  by_cases h : e = 0
  · subst h; simp
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-! ## §2. The conjugate-membership bijection -/

/-- **Entrywise core of the conjugate-transpose identity.**  For reduced `p` (entries `< ℓ`)
    and `i, j < ℓ`, the conjugated support contains the `(i,j)`-circulant offset iff the
    original support contains the transposed `(j,i)` offset — the modular-negation bijection
    `e ↦ (ℓ−e) mod ℓ`. -/
theorem dagger_contains (ℓ : Nat) (p : Circ) (hp : ∀ e ∈ p, e < ℓ)
    (i j : Nat) (hi : i < ℓ) (hj : j < ℓ) :
    (circDagger ℓ p).contains ((j + ℓ - i % ℓ) % ℓ) = p.contains ((i + ℓ - j % ℓ) % ℓ) := by
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  have q2lt : (i + ℓ - j) % ℓ < ℓ := Nat.mod_lt _ (by omega)
  have feq : ∀ e, e < ℓ → ((ℓ - e) % ℓ = (j + ℓ - i) % ℓ ↔ e = (i + ℓ - j) % ℓ) := by
    intro e he
    rw [negMod e ℓ he, subMod j i ℓ hi hj, subMod i j ℓ hj hi]
    split_ifs <;> omega
  unfold circDagger
  simp only [List.contains_eq_mem, decide_eq_decide, List.mem_map]
  constructor
  · rintro ⟨e, hep, hfe⟩
    have hel := hp e hep
    rw [Nat.mod_eq_of_lt hel] at hfe
    rw [← (feq e hel).mp hfe]; exact hep
  · intro hmem
    exact ⟨(i + ℓ - j) % ℓ, hmem, by rw [Nat.mod_eq_of_lt q2lt]; exact (feq _ q2lt).mpr rfl⟩

/-! ## §3. The matrix-level conjugate-transpose identity -/

/-- `getD` of a mapped range at an in-bounds index. -/
private theorem map_range_getD {α : Type _} (n i : Nat) (f : Nat → α) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **The GF(2) transpose of a lifted circulant equals the lift of the ring conjugate**
    (`circulant ℓ (circDagger ℓ p) = transpose (circulant ℓ p) ℓ`), GENERICALLY for reduced
    `p`.  This is the cancellation fact behind the lifted-product CSS condition; previously
    only `decide`-verified on instances. -/
theorem circulant_circDagger_eq_transpose (ℓ : Nat) (p : Circ) (hp : ∀ e ∈ p, e < ℓ) :
    circulant ℓ (circDagger ℓ p) = transpose (circulant ℓ p) ℓ := by
  unfold circulant transpose
  apply List.map_congr_left
  intro i hi_mem
  have hi : i < ℓ := List.mem_range.mp hi_mem
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj_mem
  have hj : j < ℓ := List.mem_range.mp hj_mem
  show (circDagger ℓ p).contains ((j + ℓ - i % ℓ) % ℓ)
      = ((List.range ℓ).map (fun j' => p.contains ((j' + ℓ - j % ℓ) % ℓ))).getD i false
  rw [map_range_getD ℓ i _ false hi]
  exact dagger_contains ℓ p hp i j hi hj

end FormalRV.QEC.Algebraic
