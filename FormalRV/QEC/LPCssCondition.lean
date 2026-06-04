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

/-! ## §4. Commutativity of the ring multiplication `circMul` (for the CSS cancellation) -/

/-- Sum of a pointwise-added map splits. -/
private theorem sum_map_add (l : List Nat) (A B : Nat → Nat) :
    (l.map (fun x => A x + B x)).sum = (l.map A).sum + (l.map B).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- `countP` as a sum of `0/1` indicators. -/
private theorem countP_eq_sum_ite (q : List Nat) (P : Nat → Bool) :
    q.countP P = (q.map (fun j => if P j then 1 else 0)).sum := by
  induction q with
  | nil => simp
  | cons a as ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]; omega

/-- **Fubini for `countP` over a product**: the double count is symmetric in the two lists. -/
private theorem sum_countP_swap (p q : List Nat) (g : Nat → Nat → Bool) :
    (p.map (fun i => q.countP (fun j => g i j))).sum
      = (q.map (fun j => p.countP (fun i => g i j))).sum := by
  induction p with
  | nil =>
      simp only [List.map_nil, List.sum_nil, List.countP_nil]
      induction q with
      | nil => rfl
      | cons a as ihq => simp only [List.map_cons, List.sum_cons]; omega
  | cons i is ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
      rw [sum_map_add q (fun j => is.countP (fun i' => g i' j)) (fun j => if g i j then 1 else 0)]
      rw [← countP_eq_sum_ite q (fun j => g i j)]; omega

/-- **The ring `R = F₂[x]/(xˡ+1)` is COMMUTATIVE**: `circMul ℓ p q = circMul ℓ q p`.  The
    multiset of pairwise-sum exponents is symmetric (`i + j = j + i`), so each residue's
    odd-multiplicity test agrees — by `filter_congr` + the Fubini swap.  This is the
    commutativity behind the lifted-product CSS cancellation `A⊗A† + A⊗A† = 0`. -/
theorem circMul_comm (ℓ : Nat) (p q : Circ) : circMul ℓ p q = circMul ℓ q p := by
  unfold circMul
  apply List.filter_congr
  intro e _
  have key : (p.flatMap (fun i => q.map (fun j => (i + j) % ℓ))).countP (fun x => x = e)
           = (q.flatMap (fun j => p.map (fun i => (j + i) % ℓ))).countP (fun x => x = e) := by
    rw [List.countP_flatMap, List.countP_flatMap]
    simp only [Function.comp_def, List.countP_map]
    rw [sum_countP_swap p q (fun i j => decide ((i + j) % ℓ = e))]
    congr 1
    apply List.map_congr_left
    intro j _
    congr 1
    funext i
    rw [Nat.add_comm]
  rw [key]

/-! ## §5. Shape of `liftMat` (rows are `(#cols)·ℓ` wide) — toward `well_shaped` + transpose -/

/-- Sum of a constant-`a` replicate. -/
private theorem sum_replicate (n a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

/-- A circulant's `r`-th row (for `r < ℓ`) has length `ℓ` (the matrix is `ℓ×ℓ`). -/
theorem circulant_row_length (ℓ : Nat) (e : Circ) (r : Nat) (hr : r < ℓ) :
    ((circulant ℓ e).getD r []).length = ℓ := by
  unfold circulant
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]; simp

/-- One lifted row of a polynomial row `pr` (the `r`-th rows of its circulant blocks,
    concatenated) has length `(#blocks)·ℓ = pr.length·ℓ`. -/
theorem liftRow_length (ℓ : Nat) (pr : List Circ) (r : Nat) (hr : r < ℓ) :
    ((pr.map (fun e => circulant ℓ e)).flatMap (fun blk => blk.getD r [])).length
      = pr.length * ℓ := by
  rw [List.length_flatMap, List.map_map,
      show (fun blk => (blk.getD r []).length) ∘ (fun e => circulant ℓ e) = (fun _ => ℓ) from
        by funext e; exact circulant_row_length ℓ e r hr,
      List.map_const', sum_replicate]

/-- **Every row of `liftMat ℓ A` has length `C·ℓ`** when `A` is rectangular with `C`
    columns — the shape invariant feeding `well_shaped` for the lifted product, and the
    block decomposition needed for the transpose homomorphism. -/
theorem liftMat_row_length (ℓ : Nat) (A : List (List Circ)) (C : Nat)
    (hrect : ∀ pr ∈ A, pr.length = C) :
    ∀ row ∈ liftMat ℓ A, row.length = C * ℓ := by
  intro row hrow
  unfold liftMat at hrow
  rw [List.mem_flatMap] at hrow
  obtain ⟨pr, hpr, hrow2⟩ := hrow
  rw [List.mem_map] at hrow2
  obtain ⟨r, hr, rfl⟩ := hrow2
  rw [List.mem_range] at hr
  rw [liftRow_length ℓ pr r hr, hrect pr hpr]

/-! ## §6. Uniform-block indexing (the crux of the transpose homomorphism)

    `liftMat` and its rows are `flatMap`s of UNIFORM-length-`ℓ` blocks.  Indexing such a
    `flatMap` at position `b·ℓ+s` lands in block `b`, offset `s`.  Used at BOTH nesting
    levels (the outer poly-row `flatMap`, and the inner circulant-block-row `flatMap`). -/

/-- **Uniform-block `getElem?`**: for `f` producing length-`ℓ` lists and `s < ℓ`, the
    `(b·ℓ+s)`-th element of `l.flatMap f` is the `s`-th element of `f`(the `b`-th block).
    By induction over `l`, using the append `getElem?` lemmas. -/
theorem getElem?_flatMap_uniform {α β : Type} (f : α → List β) (ℓ : Nat) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = ℓ) →
      ∀ (b s : Nat) (a : α), s < ℓ → l[b]? = some a →
        (l.flatMap f)[b * ℓ + s]? = (f a)[s]? := by
  intro l
  induction l with
  | nil => intro _ b s a _ hget; simp at hget
  | cons blk rest ih =>
    intro huni b s a hs hget
    have hblk : (f blk).length = ℓ := huni blk (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    cases b with
    | zero =>
        simp only [Nat.zero_mul, Nat.zero_add]
        rw [List.getElem?_append_left (by rw [hblk]; exact hs)]
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [hget]
    | succ b' =>
        have hidx : (b' + 1) * ℓ + s = (f blk).length + (b' * ℓ + s) := by
          rw [hblk, Nat.succ_mul]; omega
        rw [hidx, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        have hrest : ∀ x ∈ rest, (f x).length = ℓ := fun x hx => huni x (List.mem_cons_of_mem _ hx)
        rw [List.getElem?_cons_succ] at hget
        exact ih hrest b' s a hs hget

/-! ## §7. Entry access into `liftMat` (the bridge for the transpose homomorphism) -/

/-- **The `(a·ℓ+r, b·ℓ+s)` entry of `liftMat ℓ A` is `circulant(A[a][b])[r][s]`** — the
    block `(a,b)` is the `ℓ×ℓ` circulant of the ring entry `A[a][b]`, read at `(r,s)`.
    Proved by decomposing both flatMap levels with `getElem?_flatMap_uniform`.  This is the
    bridge that turns the transpose homomorphism into a per-entry application of
    `circulant_circDagger_eq_transpose`. -/
theorem liftMat_entry (ℓ : Nat) (A : List (List Circ)) (C : Nat)
    (hrect : ∀ pr ∈ A, pr.length = C)
    (a r b s : Nat) (ha : a < A.length) (hr : r < ℓ) (hb : b < C) (hs : s < ℓ) :
    ((liftMat ℓ A)[a * ℓ + r]?.getD []).getD (b * ℓ + s) false
      = ((circulant ℓ ((A[a]?.getD []).getD b [])).getD r []).getD s false := by
  have hpra : A[a]? = some (A[a]?.getD []) := by rw [List.getElem?_eq_getElem ha]; rfl
  have houter : (liftMat ℓ A)[a * ℓ + r]?
      = ((List.range ℓ).map (fun r' =>
          ((A[a]?.getD []).map (fun e => circulant ℓ e)).flatMap (fun blk => blk.getD r' [])))[r]? := by
    unfold liftMat
    exact getElem?_flatMap_uniform _ ℓ A (by intro pr _; simp) a r (A[a]?.getD []) hr hpra
  rw [houter, List.getElem?_map, List.getElem?_range hr]
  simp only [Option.map_some, Option.getD_some]
  have hcirc : ∀ blk ∈ (A[a]?.getD []).map (fun e => circulant ℓ e), (blk.getD r []).length = ℓ := by
    intro blk hblk; rw [List.mem_map] at hblk; obtain ⟨e, _, rfl⟩ := hblk
    exact circulant_row_length ℓ e r hr
  have hmem : A[a]?.getD [] ∈ A := by
    have he : A[a]?.getD [] = A[a] := by rw [List.getElem?_eq_getElem ha]; rfl
    rw [he]; exact List.getElem_mem ha
  have hbC : b < (A[a]?.getD []).length := by rw [hrect _ hmem]; exact hb
  have hblkget : ((A[a]?.getD []).map (fun e => circulant ℓ e))[b]?
      = some (circulant ℓ ((A[a]?.getD []).getD b [])) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hbC]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbC]
  have hinner := getElem?_flatMap_uniform (fun blk => blk.getD r []) ℓ
    ((A[a]?.getD []).map (fun e => circulant ℓ e)) hcirc b s _ hs hblkget
  rw [List.getD_eq_getElem?_getD, hinner]
  simp [List.getD_eq_getElem?_getD]

/-! ## §8. `well_shaped` for the lifted product (the other half of `code.valid`) -/

/-- A `pKron` row has length `(#cols A)·(#cols B)` for rectangular `A`, `B`. -/
theorem pKron_row_length (ℓ : Nat) (A B : List (List Circ)) (cA cB : Nat)
    (hA : ∀ arow ∈ A, arow.length = cA) (hB : ∀ brow ∈ B, brow.length = cB) :
    ∀ row ∈ pKron ℓ A B, row.length = cA * cB := by
  intro row hrow; unfold pKron at hrow; rw [List.mem_flatMap] at hrow
  obtain ⟨arow, harow, hrow2⟩ := hrow; rw [List.mem_map] at hrow2
  obtain ⟨brow, hbrow, rfl⟩ := hrow2
  rw [List.length_flatMap,
      show (fun a => (List.map (fun b => circMul ℓ a b) brow).length) = (fun _ => cB) from by
        funext a; rw [List.length_map]; exact hB brow hbrow,
      List.map_const',
      show (List.replicate arow.length cB).sum = arow.length * cB from by
        induction arow.length with
        | zero => simp
        | succ k ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega,
      hA arow harow]

/-- A `pHcat` row has length `cL + cR` for rectangular sides. -/
theorem pHcat_row_length (L R : List (List Circ)) (cL cR : Nat)
    (hL : ∀ row ∈ L, row.length = cL) (hR : ∀ row ∈ R, row.length = cR) :
    ∀ row ∈ pHcat L R, row.length = cL + cR := by
  intro row hrow; unfold pHcat at hrow; rw [List.mem_iff_getElem] at hrow
  obtain ⟨i, hi, rfl⟩ := hrow
  rw [List.getElem_zipWith, List.length_append, hL _ (List.getElem_mem _), hR _ (List.getElem_mem _)]

/-- Each `pIdent n` row has length `n`. -/
theorem pIdent_row_length (n : Nat) : ∀ row ∈ pIdent n, row.length = n := by
  intro row hrow; unfold pIdent at hrow; rw [List.mem_map] at hrow; obtain ⟨i, _, rfl⟩ := hrow; simp

/-- Each `pDagger ℓ A` row has length `A.length` (the conjugate transpose flips dimensions). -/
theorem pDagger_row_length (ℓ : Nat) (A : List (List Circ)) :
    ∀ row ∈ pDagger ℓ A, row.length = A.length := by
  intro row hrow; unfold pDagger at hrow; rw [List.mem_map] at hrow; obtain ⟨j, _, rfl⟩ := hrow; simp

/-- A matrix whose every row has length `n` passes `matrix_has_n_cols`. -/
theorem matrix_has_n_cols_of (M : BoolMat) (n : Nat) (h : ∀ row ∈ M, row.length = n) :
    matrix_has_n_cols M n = true := by
  unfold matrix_has_n_cols; rw [List.all_eq_true]
  intro row hrow; rw [decide_eq_true_eq]; exact h row hrow

/-- **`well_shaped` for the lifted product `LP(A, A†)`, PARAMETRICALLY** (native-free).  Every
    `H_X`/`H_Z` row has length `n = (rA² + nA²)·ℓ`: both check matrices are `liftMat` of a
    `pHcat` of two `pKron`s with column counts `nA·nA` and `rA·rA`, and `liftMat_row_length`
    multiplies by `ℓ`.  This is the first half of `code.valid` for lp16/lp20, with NO
    `decide`/`native_decide` at the 2610/4350-column scale. -/
theorem liftedProduct_well_shaped (ℓ : Nat) (A : List (List Circ)) (rA nA : Nat)
    (hA_rows : A.length = rA) (hA_cols : ∀ row ∈ A, row.length = nA) :
    (liftedProduct ℓ A rA nA).well_shaped = true := by
  have hdag : ∀ brow ∈ pDagger ℓ A, brow.length = rA := fun brow hbrow => by
    rw [pDagger_row_length ℓ A brow hbrow, hA_rows]
  have key : ∀ (P : List (List Circ)), (∀ row ∈ P, row.length = rA * rA + nA * nA) →
      ∀ row ∈ liftMat ℓ P, row.length = (rA * rA + nA * nA) * ℓ :=
    fun P hP => liftMat_row_length ℓ P (rA * rA + nA * nA) hP
  have hHx : ∀ row ∈ pHcat (pKron ℓ A (pIdent nA)) (pKron ℓ (pIdent rA) (pDagger ℓ A)),
      row.length = rA * rA + nA * nA := by
    have := pHcat_row_length (pKron ℓ A (pIdent nA)) (pKron ℓ (pIdent rA) (pDagger ℓ A))
      (nA * nA) (rA * rA)
      (pKron_row_length ℓ A (pIdent nA) nA nA hA_cols (pIdent_row_length nA))
      (pKron_row_length ℓ (pIdent rA) (pDagger ℓ A) rA rA (pIdent_row_length rA) hdag)
    intro row hrow; rw [this row hrow]; omega
  have hHz : ∀ row ∈ pHcat (pKron ℓ (pIdent nA) A) (pKron ℓ (pDagger ℓ A) (pIdent rA)),
      row.length = rA * rA + nA * nA := by
    have := pHcat_row_length (pKron ℓ (pIdent nA) A) (pKron ℓ (pDagger ℓ A) (pIdent rA))
      (nA * nA) (rA * rA)
      (pKron_row_length ℓ (pIdent nA) A nA nA (pIdent_row_length nA) hA_cols)
      (pKron_row_length ℓ (pDagger ℓ A) (pIdent rA) rA rA hdag (pIdent_row_length rA))
    intro row hrow; rw [this row hrow]; omega
  unfold liftedProduct CSSCode.well_shaped
  rw [matrix_has_n_cols_of _ _ (key _ hHx), matrix_has_n_cols_of _ _ (key _ hHz)]
  rfl

end FormalRV.QEC.Algebraic
