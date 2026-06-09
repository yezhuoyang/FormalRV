/-
  FormalRV.Shor.WindowedWidth — the PARAMETRIC structural qubit count of the windowed
  multiplier, proved for ALL `w, bits, numWin` from the `Gate` structure (closing the
  gap left by the per-instance `decide` proofs in `WindowedCircuit`).

  `width (windowedMulCircuit w bits a numWin) = 2*w + 2*bits + numWin*w + 2`
  (for `w ≥ 1`, `bits ≥ 1`, `numWin ≥ 1`).  The proof bounds `maxIdx` of every component
  (Cuccaro adder, unary-lookup read, window copies) from their definitions and shows the
  maximum is the top of the `y`-register, `yBase + numWin*w - 1`.  So the qubit count —
  and in particular its `+ numWin*w` (data) and any padding contribution — is read off the
  verified circuit, not asserted as a formula.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuit

namespace FormalRV.Shor.WindowedWidth

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit FormalRV.Shor.WindowedLookupAdd

/-! ## §1. `maxIdx` of a left-fold of `seq`-appended steps. -/

theorem maxIdx_seq (a b : Gate) : maxIdx (Gate.seq a b) = max (maxIdx a) (maxIdx b) := rfl

theorem maxIdx_init_le_foldl {α : Type} (step : α → Gate) (L : List α) (init : Gate) :
    maxIdx init ≤ maxIdx (L.foldl (fun g x => Gate.seq g (step x)) init) := by
  induction L generalizing init with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons]
    exact le_trans (le_max_left _ _) (ih (Gate.seq init (step a)))

theorem maxIdx_foldl_seq_le {α : Type} (step : α → Gate) (B : Nat) (L : List α) (init : Gate)
    (hinit : maxIdx init ≤ B) (hstep : ∀ x ∈ L, maxIdx (step x) ≤ B) :
    maxIdx (L.foldl (fun g x => Gate.seq g (step x)) init) ≤ B := by
  induction L generalizing init with
  | nil => simpa using hinit
  | cons a rest ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [maxIdx_seq]; exact max_le hinit (hstep a (List.mem_cons.mpr (Or.inl rfl)))
    · intro x hx; exact hstep x (List.mem_cons.mpr (Or.inr hx))

theorem le_maxIdx_foldl_seq {α : Type} (step : α → Gate) (L : List α) (init : Gate)
    (a : α) (ha : a ∈ L) :
    maxIdx (step a) ≤ maxIdx (L.foldl (fun g x => Gate.seq g (step x)) init) := by
  induction L generalizing init with
  | nil => simp at ha
  | cons b rest ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with hb | hb
    · subst hb
      exact le_trans (le_max_right (maxIdx init) (maxIdx (step a)))
        (maxIdx_init_le_foldl step rest (Gate.seq init (step a)))
    · exact ih (Gate.seq init (step b)) hb

/-! ## §2. `maxIdx` bounds for the Cuccaro adder. -/

theorem maxIdx_cuccaro_maj_chain (n q_start : Nat) :
    maxIdx (cuccaro_maj_chain n q_start) ≤ q_start + 2 * n := by
  induction n generalizing q_start with
  | zero => simp [cuccaro_maj_chain, maxIdx]
  | succ k ih =>
    rw [cuccaro_maj_chain, maxIdx_seq]
    apply max_le
    · simp only [cuccaro_MAJ, maxIdx]; omega
    · exact le_trans (ih (q_start + 2)) (by omega)

theorem maxIdx_cuccaro_uma_chain_reverse (n q_start : Nat) :
    maxIdx (cuccaro_uma_chain_reverse n q_start) ≤ q_start + 2 * n := by
  induction n generalizing q_start with
  | zero => simp [cuccaro_uma_chain_reverse, maxIdx]
  | succ k ih =>
    rw [cuccaro_uma_chain_reverse, maxIdx_seq]
    apply max_le
    · exact le_trans (ih (q_start + 2)) (by omega)
    · simp only [cuccaro_UMA, maxIdx]; omega

theorem maxIdx_cuccaro_full (bits q_start : Nat) :
    maxIdx (cuccaro_n_bit_adder_full bits q_start) ≤ q_start + 2 * bits := by
  rw [cuccaro_n_bit_adder_full, maxIdx_seq]
  exact max_le (maxIdx_cuccaro_maj_chain bits q_start) (maxIdx_cuccaro_uma_chain_reverse bits q_start)

/-! ## §3. `maxIdx` bounds for the unary-lookup read. -/

theorem maxIdx_x_gates_le (B : Nat) (xs : List Nat) (h : ∀ i ∈ xs, i ≤ B) :
    maxIdx (x_gates_from_indices xs) ≤ B := by
  induction xs with
  | nil => simp [x_gates_from_indices, maxIdx]
  | cons a rest ih =>
    rw [x_gates_from_indices, maxIdx_seq]
    exact max_le (ih (fun i hi => h i (List.mem_cons.mpr (Or.inr hi))))
      (by simp only [maxIdx]; exact h a (List.mem_cons.mpr (Or.inl rfl)))

theorem maxIdx_cx_gates_le (B ctrl : Nat) (xs : List Nat) (hc : ctrl ≤ B)
    (h : ∀ t ∈ xs, t ≤ B) : maxIdx (cx_gates_from_indices ctrl xs) ≤ B := by
  induction xs with
  | nil => simp [cx_gates_from_indices, maxIdx]
  | cons a rest ih =>
    rw [cx_gates_from_indices, maxIdx_seq]
    exact max_le (ih (fun t ht => h t (List.mem_cons.mpr (Or.inr ht))))
      (by simp only [maxIdx]; exact max_le hc (h a (List.mem_cons.mpr (Or.inl rfl))))

theorem maxIdx_prefix_and_step (i : Nat) : maxIdx (prefix_and_step i) ≤ 2 + 2 * i := by
  unfold prefix_and_step ulookup_ctrl_idx ulookup_address_idx ulookup_and_idx
  split <;> · simp only [maxIdx]; omega

theorem maxIdx_prefix_and_cascade (n : Nat) : maxIdx (prefix_and_cascade n) ≤ 2 * n := by
  induction n with
  | zero => simp [prefix_and_cascade, maxIdx]
  | succ k ih =>
    rw [prefix_and_cascade, maxIdx_seq]
    exact max_le (le_trans ih (by omega)) (le_trans (maxIdx_prefix_and_step k) (by omega))

theorem maxIdx_prefix_and_uncompute (n : Nat) : maxIdx (prefix_and_uncompute n) ≤ 2 * n := by
  induction n with
  | zero => simp [prefix_and_uncompute, maxIdx]
  | succ k ih =>
    rw [prefix_and_uncompute, maxIdx_seq]
    exact max_le (le_trans (maxIdx_prefix_and_step k) (by omega)) (le_trans ih (by omega))

/-- One lookup iteration with flips/cnots bounded by `B` (and `2·w ≤ B` for the cascade
    and CNOT control) has `maxIdx ≤ B`. -/
theorem maxIdx_unary_lookup_iteration_le (w B : Nat) (flips cnots : List Nat)
    (hw1 : 1 ≤ w) (hw : 2 * w ≤ B) (hf : ∀ i ∈ flips, i ≤ B) (hc : ∀ t ∈ cnots, t ≤ B) :
    maxIdx (unary_lookup_iteration w flips cnots) ≤ B := by
  unfold unary_lookup_iteration
  simp only [maxIdx_seq]
  refine max_le (max_le (max_le (max_le (maxIdx_x_gates_le B flips hf)
    (le_trans (maxIdx_prefix_and_cascade w) hw)) ?_) (le_trans (maxIdx_prefix_and_uncompute w) hw))
    (maxIdx_x_gates_le B flips hf)
  -- the CNOT layer: control = ulookup_and_idx (w-1) = 2w ≤ B, targets in cnots ≤ B
  apply maxIdx_cx_gates_le B _ cnots _ hc
  unfold ulookup_and_idx; omega

theorem maxIdx_unary_lookup_multi_iteration_le (w B : Nat)
    (iters : List (List Nat × List Nat)) (hw1 : 1 ≤ w) (hw : 2 * w ≤ B)
    (h : ∀ p ∈ iters, (∀ i ∈ p.1, i ≤ B) ∧ (∀ t ∈ p.2, t ≤ B)) :
    maxIdx (unary_lookup_multi_iteration w iters) ≤ B := by
  induction iters with
  | nil => simp [unary_lookup_multi_iteration, maxIdx]
  | cons hd rest ih =>
    obtain ⟨flips, cnots⟩ := hd
    rw [unary_lookup_multi_iteration, maxIdx_seq]
    refine max_le (ih (fun p hp => h p (List.mem_cons.mpr (Or.inr hp)))) ?_
    obtain ⟨hf, hc⟩ := h (flips, cnots) (List.mem_cons.mpr (Or.inl rfl))
    exact maxIdx_unary_lookup_iteration_le w B flips cnots hw1 hw hf hc

/-! ## §4. Bounds for the lookup table data + the lookup-add gate (specific layout). -/

theorem addrFlips_le (w v i : Nat) (hi : i ∈ addrFlips w v) : i ≤ 2 * w := by
  unfold addrFlips at hi
  rw [List.mem_filterMap] at hi
  obtain ⟨k, hk, heq⟩ := hi
  rw [List.mem_range] at hk
  cases hv : v.testBit k with
  | true => simp [hv] at heq
  | false =>
      simp only [hv, Bool.false_eq_true, if_false, Option.some.injEq] at heq
      subst heq; unfold ulookup_address_idx; omega

theorem wordCnotsAt_addendIdx_le (q_start W Tv t : Nat)
    (ht : t ∈ wordCnotsAt (addendIdx q_start) W Tv) : t ≤ q_start + 2 * W := by
  unfold wordCnotsAt at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨j, hj, heq⟩ := ht
  rw [List.mem_range] at hj
  cases hv : Tv.testBit j with
  | false => simp [hv] at heq
  | true =>
      simp only [hv, if_true, Option.some.injEq] at heq
      subst heq; unfold addendIdx; omega

/-- The lookup read writes only to address/AND/word positions `≤ q_start + 2·W`. -/
theorem maxIdx_lookupReadAt_le (w q_start W : Nat) (T : Nat → Nat)
    (hw1 : 1 ≤ w) (hq : 2 * w ≤ q_start) :
    maxIdx (lookupReadAt w (addendIdx q_start) W T) ≤ q_start + 2 * W := by
  unfold lookupReadAt
  apply maxIdx_unary_lookup_multi_iteration_le w (q_start + 2 * W) _ hw1 (by omega)
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨v, _, hv⟩ := hp
  subst hv
  exact ⟨fun i hi => le_trans (addrFlips_le w v i hi) (by omega),
         fun t ht => wordCnotsAt_addendIdx_le q_start W (T v) t ht⟩

theorem maxIdx_lookupAddAt_le (w q_start W bits : Nat) (T : Nat → Nat)
    (hw1 : 1 ≤ w) (hq : 2 * w ≤ q_start) (hWb : W ≤ bits) :
    maxIdx (lookupAddAt w W T bits q_start) ≤ q_start + 2 * bits := by
  unfold lookupAddAt
  simp only [maxIdx_seq]
  refine max_le (max_le ?_ (maxIdx_cuccaro_full bits q_start)) ?_
  · exact le_trans (maxIdx_lookupReadAt_le w q_start W T hw1 hq) (by omega)
  · exact le_trans (maxIdx_lookupReadAt_le w q_start W T hw1 hq) (by omega)

/-! ## §5. `maxIdx` of `copyWindow` and the parametric width. -/

/-- Every CX index in window `j`'s copy is `≤ yBase + (j+1)·w − 1` (for `w ≥ 1`, `yBase ≥ 2w`). -/
theorem maxIdx_copyWindow_le (w yBase j : Nat) (hw1 : 1 ≤ w) (hy : 2 * w ≤ yBase) :
    maxIdx (copyWindow w yBase j) ≤ yBase + (j + 1) * w - 1 := by
  unfold copyWindow
  apply maxIdx_foldl_seq_le _ _ _ _ (by simp [maxIdx])
  intro i hi
  rw [List.mem_range] at hi
  simp only [maxIdx, ulookup_address_idx]
  have he : (j + 1) * w = j * w + w := by ring
  rw [he]; omega

/-- The CX at slot `w-1` of window `j`'s copy touches `yBase + j·w + (w-1)`. -/
theorem le_maxIdx_copyWindow (w yBase j : Nat) (hw1 : 1 ≤ w) :
    yBase + j * w + (w - 1) ≤ maxIdx (copyWindow w yBase j) := by
  unfold copyWindow
  refine le_trans ?_ (le_maxIdx_foldl_seq _ _ Gate.I (w - 1) (List.mem_range.mpr (by omega)))
  simp only [maxIdx]
  exact le_max_left _ _

/-! ## §6. The parametric structural width. -/

/-- **The structural qubit count of the windowed multiplier, for ALL `w, bits, numWin`**
    (`w, bits, numWin ≥ 1`): `width = 2·w + 2·bits + numWin·w + 2`, read off the `Gate` via
    `maxIdx`.  The `numWin·w` is the data register and `2·bits` the Cuccaro acc+addend; on a
    padded register (`bits = data + g_pad`) this generalizes the `decide`-checked instances. -/
theorem width_windowedMulCircuit (w bits a numWin : Nat)
    (hw1 : 1 ≤ w) (hb : 1 ≤ bits) (hN : 1 ≤ numWin) :
    width (windowedMulCircuit w bits a numWin) = 2 * w + 2 * bits + numWin * w + 2 := by
  have hmax : maxIdx (windowedMulCircuit w bits a numWin) = 2 * w + 2 * bits + numWin * w + 1 := by
    unfold windowedMulCircuit windowedMul
    apply le_antisymm
    · -- UPPER bound: every window step's indices ≤ the y-register top
      apply maxIdx_foldl_seq_le _ _ _ _ (by simp [maxIdx])
      intro j hj
      rw [List.mem_range] at hj
      unfold windowStep
      simp only [maxIdx_seq]
      have hcopy : maxIdx (copyWindow w (1 + 2 * w + 2 * bits + 1) j)
          ≤ 2 * w + 2 * bits + numWin * w + 1 := by
        refine le_trans (maxIdx_copyWindow_le w (1 + 2 * w + 2 * bits + 1) j hw1 (by omega)) ?_
        have he : (j + 1) * w = j * w + w := by ring
        have hjw : j * w + w ≤ numWin * w := by
          calc j * w + w = (j + 1) * w := by ring
            _ ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
        omega
      have hadd : maxIdx (lookupAddAt w bits (fun v => a * (2 ^ w) ^ j * v) bits (1 + 2 * w))
          ≤ 2 * w + 2 * bits + numWin * w + 1 := by
        refine le_trans (maxIdx_lookupAddAt_le w (1 + 2 * w) bits bits _ hw1 (by omega) le_rfl) ?_
        have : 1 ≤ numWin * w := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      exact max_le (max_le hcopy hadd) hcopy
    · -- LOWER bound: the last window's copy reaches the y-register top
      refine le_trans ?_ (le_maxIdx_foldl_seq _ _ Gate.I (numWin - 1) (List.mem_range.mpr (by omega)))
      unfold windowStep
      simp only [maxIdx_seq]
      refine le_trans ?_ (le_max_left _ _)
      refine le_trans ?_ (le_max_left _ _)
      refine le_trans ?_ (le_maxIdx_copyWindow w (1 + 2 * w + 2 * bits + 1) (numWin - 1) hw1)
      -- 2w+2bits+numWin*w+1 ≤ yBase + (numWin-1)*w + (w-1)
      have hge : w ≤ numWin * w := Nat.le_mul_of_pos_left w (by omega)
      have h1 : (numWin - 1) * w = numWin * w - w := by rw [Nat.sub_mul, one_mul]
      omega
  rw [width, hmax]

end FormalRV.Shor.WindowedWidth
