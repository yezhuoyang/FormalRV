/-
  FormalRV.QEC.GF2Linearity — LINEARITY of the GF(2) inner product, the cornerstone of a
  PARAMETRIC nullspace-correctness proof for the logical-operator finder.

  GOAL (task a, fully-clean / no-`native_decide` route demanded by the strengthened
  verifier `ShorLPContract`): prove that every operator the finder computes lies in the
  relevant kernel — `z_in_ker_hx` / `x_in_ker_hz` for lp16/lp20 — PARAMETRICALLY, with no
  `decide`/`native_decide` at 2610/4350 columns.

  The whole development reduces to GF(2) linear algebra over `BoolVec`, whose ATOM is the
  linearity of `dotBit`:  `dotBit (a ⊕ c) b = dotBit a b ⊕ dotBit c b`.  Every later step
  (a vector orthogonal to a set of rows is orthogonal to their GF(2) span; `reduceVec`
  differs from its input by a span element; the kernel-basis vectors are orthogonal to the
  echelon rows; rows are preserved in the rowspace) is an application of this atom plus
  bookkeeping.  This file proves the atom, axiom-free, by a parity induction.

  ## Path to `kernelBasis_in_ker` (the remaining chain, each step built on `dotBit_vec_xor`)
    1. `dotBit_vec_xor`            — linearity (THIS FILE, proven).
    2. `dotBit_row_combination`    — `v ⊥ every row of M  →  v ⊥ (any GF(2) combination of M)`.
    3. `reduceVec_sub_in_span`     — `reduceVec P v = v ⊕ (combination of P)`.
    4. `rowReduce_rows_in_span`    — every original row ∈ rowspace of the echelon pivots.
    5. `kernelBasis_orthogonal`    — each `kernelBasis M n` vector ⊥ every echelon row.
    6. `kernelBasis_in_ker`        — (4)+(5)+(2): each `kernelBasis M n` vector ⊥ every row of M.
    7. `logicalZ_in_ker_hx`        — instantiate at `M = c.hx`  ⇒  `z_in_ker_hx c.logical`.
  Steps 2–7 are the documented continuation; they introduce NO `decide`-at-scale.

  No Mathlib heavy machinery, no `sorry`, no `axiom`.
-/

import FormalRV.QEC.GF2Rank

namespace FormalRV.Framework.LDPC

/-! ## §1. One-step unfolding of `vec_xor` -/

/-- `vec_xor` on cons cells: the head is the per-bit XOR `(x != y)`, the tail recurses. -/
theorem vec_xor_cons (x y : Bool) (xs ys : BoolVec) :
    vec_xor (x :: xs) (y :: ys) = (x != y) :: vec_xor xs ys := rfl

/-! ## §2. The parity identity at the count level -/

/-- The GF(2) overlap count of `(a ⊕ c)` with `b` is, MOD 2, the sum of the overlap counts
    of `a` with `b` and of `c` with `b`.  (Per position `(x≠y)∧z ≡ (x∧z)+(y∧z) (mod 2)`,
    lifted by induction.)  Equal-length lists. -/
theorem count_xor_parity (a c b : BoolVec) (hac : a.length = c.length) (hab : a.length = b.length) :
    ((vec_xor a c).zip b).countP (fun p => p.1 && p.2) % 2
      = (((a.zip b).countP (fun p => p.1 && p.2)) + ((c.zip b).countP (fun p => p.1 && p.2))) % 2 := by
  induction a generalizing c b with
  | nil =>
      obtain rfl : c = [] := List.length_eq_zero_iff.mp hac.symm
      obtain rfl : b = [] := List.length_eq_zero_iff.mp hab.symm
      rfl
  | cons x xs ih =>
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, c = y :: ys := by
        cases c with | nil => simp at hac | cons y ys => exact ⟨y, ys, rfl⟩
      obtain ⟨z, zs, rfl⟩ : ∃ z zs, b = z :: zs := by
        cases b with | nil => simp at hab | cons z zs => exact ⟨z, zs, rfl⟩
      have IH := ih ys zs (by simpa using hac) (by simpa using hab)
      have head : (if ((x != y) && z) = true then (1:Nat) else 0) % 2
        = ((if (x && z) = true then (1:Nat) else 0) + (if (y && z) = true then (1:Nat) else 0)) % 2 := by
        cases x <;> cases y <;> cases z <;> decide
      rw [vec_xor_cons]
      simp only [List.zip_cons_cons, List.countP_cons]
      generalize (if ((x != y) && z) = true then (1:Nat) else 0) = hL at head ⊢
      generalize (if (x && z) = true then (1:Nat) else 0) = hA at head ⊢
      generalize (if (y && z) = true then (1:Nat) else 0) = hC at head ⊢
      omega

/-! ## §3. Parity-of-sum splits as XOR -/

/-- `(m+n)` is odd iff exactly one of `m`, `n` is — i.e. parity is XOR-additive. -/
theorem parity_add (m n : Nat) :
    decide ((m + n) % 2 = 1) = xor (decide (m % 2 = 1)) (decide (n % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [Nat.add_mod, hm, hn]

/-! ## §4. THE CORNERSTONE: linearity of the GF(2) inner product -/

/-- **`dotBit` is GF(2)-LINEAR in its left argument:**
    `dotBit (a ⊕ c) b = dotBit a b ⊕ dotBit c b`  (for equal-length vectors).
    This is the atom every step of the parametric nullspace-correctness proof reduces to. -/
theorem dotBit_vec_xor (a c b : BoolVec) (hac : a.length = c.length) (hab : a.length = b.length) :
    dotBit (vec_xor a c) b = xor (dotBit a b) (dotBit c b) := by
  unfold dotBit
  rw [count_xor_parity a c b hac hab, parity_add]

end FormalRV.Framework.LDPC
