/-
  FormalRV.Arithmetic.Adder.Gidney
  ────────────────────────────────
  The Gidney patched ripple-carry adder, packaged as an instance of the
  layout-parametric `Adder` interface (`FormalRV/Arithmetic/Adder.lean`).

  Layout (width `n`, base offset `q`, span `3n+2`):
  - `q + 3i`     : addend / read bit `i` (`a`, restored).
  - `q + 3i + 1` : augend / target / running-sum bit `i` (becomes `(a+b) mod 2^n`).
  - `q + 3i + 2` : carry bit `i` (`ancClean := f (q+3i+2) = false`; restored clean).

  THE CRUX: the underlying circuit
  `gidney_adder_full_faithful_no_measurement_patched` is hard-wired at base 0
  (`read_idx i = 3i`, `target_idx i = 3i+1`, `carry_idx i = 3i+2`), unlike the
  base-parametric Cuccaro adder.  We therefore introduce a generic
  qubit-relabelling `Gate.shiftBy k` (add `k` to every qubit index) and prove its
  `applyNat` / `WellTyped` transfer lemmas, then place the base-0 adder at base
  `q` as `Gate.shiftBy q (...)`.

  Small widths: for `n ≤ 1` the base adder degenerates to `Gate.I`, which is *not*
  a correct 1-bit adder (a 1-bit add needs `target ← target ⊕ read`).  Since the
  interface lets us choose `circuit n q` per width, we use a bespoke correct
  circuit for `n = 0` (identity) and `n = 1` (`CX (q) (q+1)`), and the shifted
  Gidney adder for `n ≥ 2`.
-/
import FormalRV.Arithmetic.Adder
import FormalRV.Arithmetic.RippleCarryAdder

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Generic qubit relabelling: shift every index up by `k`. -/

/-- Add `k` to every qubit index of a `Gate`. -/
def Gate.shiftBy (k : Nat) : Gate → Gate
  | Gate.I         => Gate.I
  | Gate.X q       => Gate.X (q + k)
  | Gate.CX c t    => Gate.CX (c + k) (t + k)
  | Gate.CCX a b c => Gate.CCX (a + k) (b + k) (c + k)
  | Gate.seq g₁ g₂ => Gate.seq (Gate.shiftBy k g₁) (Gate.shiftBy k g₂)

/-- **Shift transfer (below the base).** The shifted circuit touches no qubit
`< k`. -/
theorem Gate.shiftBy_applyNat_below (k : Nat) (g : Gate) (f : Nat → Bool)
    (p : Nat) (hp : p < k) :
    Gate.applyNat (Gate.shiftBy k g) f p = f p := by
  induction g generalizing f with
  | I => rfl
  | X q =>
      show update f (q + k) (!f (q + k)) p = f p
      exact update_neq f (q + k) p _ (by omega)
  | CX c t =>
      show update f (t + k) (xor (f (t + k)) (f (c + k))) p = f p
      exact update_neq f (t + k) p _ (by omega)
  | CCX a b c =>
      show update f (c + k) (xor (f (c + k)) (f (a + k) && f (b + k))) p = f p
      exact update_neq f (c + k) p _ (by omega)
  | seq g₁ g₂ ih₁ ih₂ =>
      show Gate.applyNat (Gate.shiftBy k g₂) (Gate.applyNat (Gate.shiftBy k g₁) f) p = f p
      rw [ih₂ (Gate.applyNat (Gate.shiftBy k g₁) f), ih₁ f]

/-- **Shift transfer (conjugation).** Running the shifted circuit on `f` and
reading at `p + k` equals running the base circuit on the down-shifted stream
`fun j => f (j + k)` and reading at `p`. -/
theorem Gate.shiftBy_applyNat (k : Nat) (g : Gate) (f : Nat → Bool) :
    ∀ p, Gate.applyNat (Gate.shiftBy k g) f (p + k)
      = Gate.applyNat g (fun j => f (j + k)) p := by
  induction g generalizing f with
  | I => intro p; rfl
  | X q =>
      intro p
      show update f (q + k) (!f (q + k)) (p + k)
        = update (fun j => f (j + k)) q (!f (q + k)) p
      by_cases h : p = q
      · subst h; simp [update]
      · rw [update_neq f (q + k) (p + k) _ (by omega),
            update_neq (fun j => f (j + k)) q p _ h]
  | CX c t =>
      intro p
      show update f (t + k) (xor (f (t + k)) (f (c + k))) (p + k)
        = update (fun j => f (j + k)) t (xor (f (t + k)) (f (c + k))) p
      by_cases h : p = t
      · subst h; simp [update]
      · rw [update_neq f (t + k) (p + k) _ (by omega),
            update_neq (fun j => f (j + k)) t p _ h]
  | CCX a b c =>
      intro p
      show update f (c + k) (xor (f (c + k)) (f (a + k) && f (b + k))) (p + k)
        = update (fun j => f (j + k)) c
            (xor (f (c + k)) (f (a + k) && f (b + k))) p
      by_cases h : p = c
      · subst h; simp [update]
      · rw [update_neq f (c + k) (p + k) _ (by omega),
            update_neq (fun j => f (j + k)) c p _ h]
  | seq g₁ g₂ ih₁ ih₂ =>
      intro p
      show Gate.applyNat (Gate.shiftBy k g₂) (Gate.applyNat (Gate.shiftBy k g₁) f) (p + k)
        = Gate.applyNat g₂ (Gate.applyNat g₁ (fun j => f (j + k))) p
      rw [ih₂ (Gate.applyNat (Gate.shiftBy k g₁) f) p]
      congr 1
      funext j
      exact ih₁ f j

/-- **WellTyped monotonicity** (local helper): enlarging the dimension preserves
well-typedness. -/
theorem Gate.wellTyped_le {dim dim' : Nat} {g : Gate}
    (h : Gate.WellTyped dim g) (hle : dim ≤ dim') : Gate.WellTyped dim' g := by
  induction g with
  | I => show 0 < dim'; have : 0 < dim := h; omega
  | X q => show q < dim'; have : q < dim := h; omega
  | CX a b => obtain ⟨_, _, hab⟩ := h; exact ⟨by omega, by omega, hab⟩
  | CCX a b c =>
      obtain ⟨_, _, _, hab, hac, hbc⟩ := h
      exact ⟨by omega, by omega, by omega, hab, hac, hbc⟩
  | seq g₁ g₂ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := h; exact ⟨ih₁ h₁, ih₂ h₂⟩

/-- **Shift transfer (WellTyped).** If `g` is WellTyped at `dim` then the shifted
circuit is WellTyped at `k + dim`. -/
theorem Gate.shiftBy_wellTyped (k dim : Nat) (g : Gate)
    (h : Gate.WellTyped dim g) : Gate.WellTyped (k + dim) (Gate.shiftBy k g) := by
  induction g with
  | I => show 0 < k + dim; have : 0 < dim := h; omega
  | X q => show q + k < k + dim; have : q < dim := h; omega
  | CX c t =>
      obtain ⟨hc, ht, hct⟩ := h
      exact ⟨by omega, by omega, by omega⟩
  | CCX a b c =>
      obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨ih₁ h₁, ih₂ h₂⟩

/-! ## `applyNat` congruence: the output on `[0, dim)` depends only on the input on `[0, dim)`. -/

/-- For a `Gate` WellTyped at `dim`, the output at positions `< dim` depends only
on the input restricted to `[0, dim)`: if `f` and `f'` agree on `[0, dim)` then
the outputs agree on `[0, dim)`. -/
theorem Gate.applyNat_congr {dim : Nat} {g : Gate}
    (h_wt : Gate.WellTyped dim g) (f f' : Nat → Bool)
    (hagree : ∀ i, i < dim → f i = f' i) :
    ∀ p, p < dim → Gate.applyNat g f p = Gate.applyNat g f' p := by
  induction g generalizing f f' with
  | I => intro p hp; exact hagree p hp
  | X q =>
      have hq : q < dim := h_wt
      intro p hp
      show update f q (!f q) p = update f' q (!f' q) p
      by_cases hpq : p = q
      · rw [hpq, update_eq, update_eq, hagree q hq]
      · rw [update_neq f q p _ hpq, update_neq f' q p _ hpq]
        exact hagree p hp
  | CX c t =>
      obtain ⟨hc, ht, _⟩ := h_wt
      intro p hp
      show update f t (xor (f t) (f c)) p = update f' t (xor (f' t) (f' c)) p
      by_cases hpt : p = t
      · rw [hpt, update_eq, update_eq, hagree t ht, hagree c hc]
      · rw [update_neq f t p _ hpt, update_neq f' t p _ hpt]
        exact hagree p hp
  | CCX a b c =>
      obtain ⟨ha, hb, hc, _, _, _⟩ := h_wt
      intro p hp
      show update f c (xor (f c) (f a && f b)) p
        = update f' c (xor (f' c) (f' a && f' b)) p
      by_cases hpc : p = c
      · rw [hpc, update_eq, update_eq, hagree a ha, hagree b hb, hagree c hc]
      · rw [update_neq f c p _ hpc, update_neq f' c p _ hpc]
        exact hagree p hp
  | seq g₁ g₂ ih₁ ih₂ =>
      obtain ⟨hwt₁, hwt₂⟩ := h_wt
      intro p hp
      show Gate.applyNat g₂ (Gate.applyNat g₁ f) p
         = Gate.applyNat g₂ (Gate.applyNat g₁ f') p
      exact ih₂ hwt₂ (Gate.applyNat g₁ f) (Gate.applyNat g₁ f')
              (fun i hi => ih₁ hwt₁ f f' hagree i hi) p hp

/-! ## Bridge: `decodeReg` over the shifted Gidney layout = the base decoders. -/

/-- `decodeReg (fun i => q + 3i + 1)` agrees with the base-0 `gidney_target_val`
decoder applied to the down-shifted stream `fun j => f (q + j)`. -/
theorem decodeReg_augend_eq_target (n q : Nat) (f : Nat → Bool) :
    decodeReg (fun i => q + 3 * i + 1) n f
      = gidney_target_val n (fun j => f (q + j)) := by
  unfold decodeReg
  have key : ∀ (m : Nat) (init : Nat),
      (List.range m).foldl
          (fun acc i => acc + if f (q + 3 * i + 1) then 2 ^ i else 0) init
        = init + gidney_target_val m (fun j => f (q + j)) := by
    intro m
    induction m with
    | zero => intro init; simp [gidney_target_val]
    | succ k ih =>
        intro init
        rw [List.range_succ, List.foldl_append, ih init]
        simp only [List.foldl_cons, List.foldl_nil, gidney_target_val, target_idx]
        have hidx : q + 3 * k + 1 = q + (3 * k + 1) := by ring
        rw [hidx]; ring_nf
  have := key n 0
  simpa using this

/-- `decodeReg (fun i => q + 3i)` agrees with the base-0 `gidney_read_val`
decoder applied to the down-shifted stream `fun j => f (q + j)`. -/
theorem decodeReg_addend_eq_read (n q : Nat) (f : Nat → Bool) :
    decodeReg (fun i => q + 3 * i) n f
      = gidney_read_val n (fun j => f (q + j)) := by
  unfold decodeReg
  have key : ∀ (m : Nat) (init : Nat),
      (List.range m).foldl
          (fun acc i => acc + if f (q + 3 * i) then 2 ^ i else 0) init
        = init + gidney_read_val m (fun j => f (q + j)) := by
    intro m
    induction m with
    | zero => intro init; simp [gidney_read_val]
    | succ k ih =>
        intro init
        rw [List.range_succ, List.foldl_append, ih init]
        simp only [List.foldl_cons, List.foldl_nil, gidney_read_val, read_idx]
        ring_nf
  have := key n 0
  simpa using this

/-! ## Per-bit extraction of the base decoders (converse direction). -/

/-- Each target bit `i < n` of `gidney_target_val n h` reads back the state bit
at `target_idx i = 3i + 1`. -/
theorem gidney_target_val_testBit (n : Nat) (h : Nat → Bool) (i : Nat) (hi : i < n) :
    (gidney_target_val n h).testBit i = h (target_idx i) := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
      have hTm_lt : gidney_target_val m h < 2 ^ m := gidney_target_val_lt m h
      by_cases hi_eq : i = m
      · subst hi_eq
        unfold gidney_target_val
        by_cases hv : h (target_idx i)
        · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_eq,
              Nat.testBit_lt_two_pow hTm_lt, hv]; rfl
        · rw [if_neg hv, Nat.add_zero, Nat.testBit_lt_two_pow hTm_lt]
          cases hh : h (target_idx i)
          · rfl
          · exact absurd hh hv
      · have hi_lt : i < m := by omega
        unfold gidney_target_val
        by_cases hv : h (target_idx m)
        · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_gt hi_lt, ih i hi_lt]
        · rw [if_neg hv, Nat.add_zero, ih i hi_lt]

/-- Each read bit `i < n` of `gidney_read_val n h` reads back the state bit at
`read_idx i = 3i`. -/
theorem gidney_read_val_testBit (n : Nat) (h : Nat → Bool) (i : Nat) (hi : i < n) :
    (gidney_read_val n h).testBit i = h (read_idx i) := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
      have hRm_lt : gidney_read_val m h < 2 ^ m := gidney_read_val_lt m h
      by_cases hi_eq : i = m
      · subst hi_eq
        unfold gidney_read_val
        by_cases hv : h (read_idx i)
        · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_eq,
              Nat.testBit_lt_two_pow hRm_lt, hv]; rfl
        · rw [if_neg hv, Nat.add_zero, Nat.testBit_lt_two_pow hRm_lt]
          cases hh : h (read_idx i)
          · rfl
          · exact absurd hh hv
      · have hi_lt : i < m := by omega
        unfold gidney_read_val
        by_cases hv : h (read_idx m)
        · rw [if_pos hv, Nat.add_comm, Nat.testBit_two_pow_add_gt hi_lt, ih i hi_lt]
        · rw [if_neg hv, Nat.add_zero, ih i hi_lt]

/-! ## Tight WellTyped: the patched Gidney adder fits in `3*bits` qubits.

The existing `*_wellTyped` corpus is stated at the natural budget
`adder_n_qubits bits = 3*bits + 2`.  The patched adder actually only ever
references qubit indices `< 3*bits` (its highest index is `carry_idx (bits-1) =
3*bits - 1`).  We re-derive WellTyped at the *tight* dimension `3*bits`; this is
what lets `Gate.applyNat_congr` reduce arbitrary block inputs to `adder_input_F`
(the two extra scratch qubits `3*bits`, `3*bits+1` then need not be constrained)
and what makes `Gate.applyNat_oob` frame everything at/above `3*bits`. -/

theorem gidney_first_wt' (bits : Nat) (hbits : 2 ≤ bits) :
    Gate.WellTyped (3 * bits) gidney_adder_bit_step_faithful_first := by
  unfold gidney_adder_bit_step_faithful_first
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_interior_wt' (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits - 1) :
    Gate.WellTyped (3 * bits) (gidney_adder_bit_step_faithful_interior i) := by
  unfold gidney_adder_bit_step_faithful_interior
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_last_wt' (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits) :
    Gate.WellTyped (3 * bits) (gidney_adder_bit_step_faithful_last i) := by
  unfold gidney_adder_bit_step_faithful_last
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_first_rev_wt' (bits : Nat) (hbits : 2 ≤ bits) :
    Gate.WellTyped (3 * bits) gidney_adder_bit_step_faithful_first_reverse_patched := by
  unfold gidney_adder_bit_step_faithful_first_reverse_patched
         gidney_adder_bit_step_faithful_first_reverse
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_interior_rev_wt' (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits - 1) :
    Gate.WellTyped (3 * bits)
      (gidney_adder_bit_step_faithful_interior_reverse_patched i) := by
  unfold gidney_adder_bit_step_faithful_interior_reverse_patched
         gidney_adder_bit_step_faithful_interior_reverse
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_last_rev_wt' (bits i : Nat) (hi_pos : 0 < i) (hi_lt : i < bits) :
    Gate.WellTyped (3 * bits)
      (gidney_adder_bit_step_faithful_last_reverse_patched i) := by
  unfold gidney_adder_bit_step_faithful_last_reverse_patched
         gidney_adder_bit_step_faithful_last_reverse
  simp only [Gate.WellTyped]
  unfold carry_idx target_idx read_idx
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals omega

theorem gidney_fwd_prop_wt' (bits : Nat) (hb2 : 2 ≤ bits) :
    ∀ k, k ≤ bits - 1 →
      Gate.WellTyped (3 * bits) (gidney_adder_forward_with_propagation k) := by
  intro k
  induction k with
  | zero =>
      intro _
      show Gate.WellTyped (3 * bits) Gate.I
      simp only [Gate.WellTyped]; omega
  | succ k' ih =>
      intro hk
      match k' with
      | 0 =>
          show Gate.WellTyped _ gidney_adder_bit_step_faithful_first
          exact gidney_first_wt' bits hb2
      | k'' + 1 =>
          show Gate.WellTyped _ (Gate.seq _ _)
          exact ⟨ih (by omega),
                 gidney_interior_wt' bits (k''+1) (by omega) (by omega)⟩

theorem gidney_fwd_full_wt' (bits : Nat) (hb2 : 2 ≤ bits) :
    Gate.WellTyped (3 * bits) (gidney_adder_forward_faithful_full bits) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  show Gate.WellTyped _ (Gate.seq _ _)
  exact ⟨gidney_fwd_prop_wt' (n + 2) (by omega) (n + 1) (by omega),
         gidney_last_wt' (n + 2) (n + 1) (by omega) (by omega)⟩

theorem gidney_final_cx_wt' (bits : Nat) (hb1 : 1 ≤ bits) :
    ∀ k, k ≤ bits →
      Gate.WellTyped (3 * bits) (gidney_final_cx_cascade k) := by
  intro k
  induction k with
  | zero =>
      intro _
      show Gate.WellTyped _ Gate.I
      simp only [Gate.WellTyped]; omega
  | succ k' ih =>
      intro hk
      show Gate.WellTyped _ (Gate.seq _ _)
      refine ⟨ih (by omega), ?_⟩
      show Gate.WellTyped (3 * bits) (Gate.CX (read_idx k') (target_idx k'))
      unfold read_idx target_idx
      simp only [Gate.WellTyped]
      refine ⟨?_, ?_, ?_⟩ <;> omega

theorem gidney_fwd_prop_rev_wt' (bits : Nat) (hb2 : 2 ≤ bits) :
    ∀ k, k ≤ bits - 1 →
      Gate.WellTyped (3 * bits)
        (gidney_adder_forward_with_propagation_reverse_patched k) := by
  intro k
  induction k with
  | zero =>
      intro _
      show Gate.WellTyped _ Gate.I
      simp only [Gate.WellTyped]; omega
  | succ k' ih =>
      intro hk
      match k' with
      | 0 =>
          show Gate.WellTyped _ gidney_adder_bit_step_faithful_first_reverse_patched
          exact gidney_first_rev_wt' bits hb2
      | k'' + 1 =>
          show Gate.WellTyped _ (Gate.seq _ _)
          exact ⟨gidney_interior_rev_wt' bits (k''+1) (by omega) (by omega),
                 ih (by omega)⟩

theorem gidney_fwd_full_rev_wt' (bits : Nat) (hb2 : 2 ≤ bits) :
    Gate.WellTyped (3 * bits)
      (gidney_adder_forward_faithful_full_reverse_patched bits) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  show Gate.WellTyped _ (Gate.seq _ _)
  exact ⟨gidney_last_rev_wt' (n+2) (n+1) (by omega) (by omega),
         gidney_fwd_prop_rev_wt' (n+2) (by omega) (n+1) (by omega)⟩

/-- **Tight WellTyped**: the patched Gidney adder is WellTyped at `3*bits`. -/
theorem gidney_patched_wt_tight (bits : Nat) (hb2 : 2 ≤ bits) :
    Gate.WellTyped (3 * bits)
      (gidney_adder_full_faithful_no_measurement_patched bits) := by
  obtain ⟨n, rfl⟩ : ∃ n, bits = n + 2 := ⟨bits - 2, by omega⟩
  show Gate.WellTyped _ (Gate.seq (Gate.seq _ _) _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact gidney_fwd_full_wt' (n + 2) (by omega)
  · exact gidney_final_cx_wt' (n + 2) (by omega) (n + 2) (by omega)
  · exact gidney_fwd_full_rev_wt' (n + 2) (by omega)

/-! ## Arbitrary-input correctness of the base-0 patched adder.

The headline `gidney_adder_correct_full` is stated only for the canonical input
`adder_input_F bits a b`.  Below we lift it to an *arbitrary* base-0 stream `h`
whose carry block is clean, by `Gate.applyNat_congr` against
`adder_input_F bits (gidney_read_val bits h) (gidney_target_val bits h)`. -/

/-- On the qubit block `[0, 3*bits)`, any clean-carry stream `h` agrees with the
canonical input `adder_input_F bits a b` for `a = gidney_read_val bits h`,
`b = gidney_target_val bits h`. -/
theorem gidney_input_agree (bits : Nat) (h : Nat → Bool)
    (hcl : ∀ i, i < bits → h (carry_idx i) = false) :
    ∀ p, p < 3 * bits →
      h p = adder_input_F bits (gidney_read_val bits h)
              (gidney_target_val bits h) p := by
  intro p hp
  -- p < 3*bits means p = read_idx i, target_idx i, or carry_idx i for some i < bits.
  have h3 : p / 3 < bits := by omega
  set a := gidney_read_val bits h
  set b := gidney_target_val bits h
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with hm | hm | hm
  · -- p % 3 = 0 : read_idx (p/3)
    have hpe : p = read_idx (p / 3) := by unfold read_idx; omega
    rw [hpe, adder_input_F_at_read_idx _ _ _ _ h3]
    exact (gidney_read_val_testBit bits h (p / 3) h3).symm
  · -- p % 3 = 1 : target_idx (p/3)
    have hpe : p = target_idx (p / 3) := by unfold target_idx; omega
    rw [hpe, adder_input_F_at_target_idx _ _ _ _ h3]
    exact (gidney_target_val_testBit bits h (p / 3) h3).symm
  · -- p % 3 = 2 : carry_idx (p/3)
    have hpe : p = carry_idx (p / 3) := by unfold carry_idx; omega
    rw [hpe, adder_input_F_at_carry_idx]
    exact hcl (p / 3) h3

/-- **Arbitrary-input target correctness** for the base-0 patched adder.  For a
clean-carry stream `h`, the target register decodes to `(read + target) mod
2^bits`. -/
theorem gidney_target_arbitrary (bits : Nat) (hb2 : 2 ≤ bits) (h : Nat → Bool)
    (hcl : ∀ i, i < bits → h (carry_idx i) = false) :
    gidney_target_val bits
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits) h)
      = (gidney_read_val bits h + gidney_target_val bits h) % 2 ^ bits := by
  set a := gidney_read_val bits h
  set b := gidney_target_val bits h
  have ha : a < 2 ^ bits := gidney_read_val_lt bits h
  have hb : b < 2 ^ bits := gidney_target_val_lt bits h
  -- The two states agree on `[0, 3*bits)`, hence after the (tight-WellTyped) adder.
  have hcong := Gate.applyNat_congr (gidney_patched_wt_tight bits hb2)
      h (adder_input_F bits a b)
      (gidney_input_agree bits h hcl)
  -- Decode the target register: every target_idx i has i < bits, so 3i+1 < 3*bits.
  have hdec : gidney_target_val bits
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits) h)
      = gidney_target_val bits
        (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
          (adder_input_F bits a b)) := by
    -- both decoders read only target_idx i (i < bits), where outputs agree.
    clear hcong
    have : ∀ m, m ≤ bits →
        gidney_target_val m
          (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits) h)
        = gidney_target_val m
          (Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits)
            (adder_input_F bits a b)) := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ k ih =>
          intro hk
          unfold gidney_target_val
          rw [ih (by omega)]
          have hidx : target_idx k < 3 * bits := by unfold target_idx; omega
          rw [Gate.applyNat_congr (gidney_patched_wt_tight bits hb2)
                h (adder_input_F bits a b) (gidney_input_agree bits h hcl)
                (target_idx k) hidx]
    exact this bits (le_refl bits)
  rw [hdec]
  exact (gidney_adder_correct_full bits a b hb2 ha hb).2.1

/-- **Arbitrary-input read preservation** for the base-0 patched adder. -/
theorem gidney_read_arbitrary (bits : Nat) (hb2 : 2 ≤ bits) (h : Nat → Bool)
    (hcl : ∀ i, i < bits → h (carry_idx i) = false) (i : Nat) (hi : i < bits) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits) h
        (read_idx i) = h (read_idx i) := by
  set a := gidney_read_val bits h
  set b := gidney_target_val bits h
  have ha : a < 2 ^ bits := gidney_read_val_lt bits h
  have hb : b < 2 ^ bits := gidney_target_val_lt bits h
  have hidx : read_idx i < 3 * bits := by unfold read_idx; omega
  rw [Gate.applyNat_congr (gidney_patched_wt_tight bits hb2)
        h (adder_input_F bits a b) (gidney_input_agree bits h hcl) (read_idx i) hidx]
  rw [(gidney_adder_correct_full bits a b hb2 ha hb).2.2.1 i hi]
  -- goal: a.testBit i = h (read_idx i)
  exact gidney_read_val_testBit bits h i hi

/-- **Arbitrary-input carry clearance** for the base-0 patched adder. -/
theorem gidney_carry_arbitrary (bits : Nat) (hb2 : 2 ≤ bits) (h : Nat → Bool)
    (hcl : ∀ i, i < bits → h (carry_idx i) = false) (i : Nat) (hi : i < bits) :
    Gate.applyNat (gidney_adder_full_faithful_no_measurement_patched bits) h
        (carry_idx i) = false := by
  set a := gidney_read_val bits h
  set b := gidney_target_val bits h
  have ha : a < 2 ^ bits := gidney_read_val_lt bits h
  have hb : b < 2 ^ bits := gidney_target_val_lt bits h
  have hidx : carry_idx i < 3 * bits := by unfold carry_idx; omega
  rw [Gate.applyNat_congr (gidney_patched_wt_tight bits hb2)
        h (adder_input_F bits a b) (gidney_input_agree bits h hcl) (carry_idx i) hidx]
  exact (gidney_adder_correct_full bits a b hb2 ha hb).2.2.2 i hi

/-! ## Placing the base-0 adder at base offset `q`. -/

/-- The width-`n` Gidney circuit at base offset `q`: identity for `n = 0`, a bare
`CX` for the degenerate 1-bit add, and the shifted patched adder for `n ≥ 2`. -/
def gidneyCircuit (n q : Nat) : Gate :=
  match n with
  | 0     => Gate.I
  | 1     => Gate.CX q (q + 1)
  | k + 2 => Gate.shiftBy q (gidney_adder_full_faithful_no_measurement_patched (k + 2))

/-- The down-shifted stream of a clean-carry block input is clean at every base-0
carry index `< n`. -/
theorem downshift_carry_clean (n q : Nat) (f : Nat → Bool)
    (hcl : ∀ i, i < n → f (q + 3 * i + 2) = false) :
    ∀ i, i < n → (fun j => f (q + j)) (carry_idx i) = false := by
  intro i hi
  show f (q + carry_idx i) = false
  have : q + carry_idx i = q + 3 * i + 2 := by unfold carry_idx; ring
  rw [this]; exact hcl i hi

/-- **Base-`q` shift transfer** in the `fun j => f (q + j)` convention used by the
decoders: reading the shifted circuit's output at `q + j` equals the base-0
circuit run on the down-shifted stream, read at `j`. -/
theorem shiftBy_applyNat_base (q : Nat) (g : Gate) (f : Nat → Bool) (j : Nat) :
    Gate.applyNat (Gate.shiftBy q g) f (q + j)
      = Gate.applyNat g (fun i => f (q + i)) j := by
  rw [Nat.add_comm q j, Gate.shiftBy_applyNat q g f j]
  congr 1
  funext i
  rw [Nat.add_comm i q]

/-! ## The Gidney patched ripple adder as an `Adder` instance. -/

/-- **The Gidney patched ripple-carry adder, as an `Adder`.**
The augend (running-sum / target) register lives at `q + 3i + 1`, the addend
(read) register at `q + 3i`, with the carry block at `q + 3i + 2` required clean
(`= false`).  Span `3n + 2`. -/
def gidneyAdder : Adder where
  span      := fun n => 3 * n + 2
  augendIdx := fun q i => q + 3 * i + 1
  addendIdx := fun q i => q + 3 * i
  ancClean  := fun f n q => ∀ i, i < n → f (q + 3 * i + 2) = false
  circuit   := gidneyCircuit
  sumCorrect := by
    intro n q f hcl
    match n, hcl with
    | 0, _ => simp [decodeReg]
    | 1, hcl =>
        -- circuit = CX q (q+1) : augend (q+1) ← augend ⊕ addend (q).
        show decodeReg (fun i => q + 3 * i + 1) 1 (Gate.applyNat (Gate.CX q (q + 1)) f)
          = (decodeReg (fun i => q + 3 * i + 1) 1 f
              + decodeReg (fun i => q + 3 * i) 1 f) % 2 ^ 1
        have hval : Gate.applyNat (Gate.CX q (q + 1)) f (q + 3 * 0 + 1)
            = xor (f (q + 1)) (f q) := by
          rw [Gate.applyNat_CX, show q + 3 * 0 + 1 = q + 1 from by ring, update_eq]
        simp only [decodeReg, List.range_one, List.foldl_cons, List.foldl_nil,
                   Nat.zero_add, pow_zero, hval]
        cases f q <;> cases f (q + 1) <;> simp
    | k + 2, hcl =>
        set bits := k + 2 with hbits
        have hb2 : 2 ≤ bits := by omega
        set G := gidney_adder_full_faithful_no_measurement_patched bits with hG
        show decodeReg (fun i => q + 3 * i + 1) bits
              (Gate.applyNat (Gate.shiftBy q G) f)
          = (decodeReg (fun i => q + 3 * i + 1) bits f
              + decodeReg (fun i => q + 3 * i) bits f) % 2 ^ bits
        -- LHS: decode of the shifted output = base-0 target decode of `applyNat G (down q f)`.
        have hout : (fun j => (Gate.applyNat (Gate.shiftBy q G) f) (q + j))
            = Gate.applyNat G (fun i => f (q + i)) := by
          funext j
          exact shiftBy_applyNat_base q G f j
        rw [decodeReg_augend_eq_target, hout,
            decodeReg_augend_eq_target, decodeReg_addend_eq_read,
            gidney_target_arbitrary bits hb2 (fun i => f (q + i))
              (downshift_carry_clean bits q f hcl),
            Nat.add_comm (gidney_read_val bits (fun i => f (q + i)))
              (gidney_target_val bits (fun i => f (q + i)))]
  addendRestored := by
    intro n q f hcl i hi
    match n, hcl, hi with
    | 0, _, hi => omega
    | 1, _, hi =>
        -- only i = 0 ; CX q (q+1) leaves control q unchanged.
        have : i = 0 := by omega
        subst this
        show Gate.applyNat (Gate.CX q (q + 1)) f (q + 3 * 0) = f (q + 3 * 0)
        rw [Gate.applyNat_CX]
        exact update_neq f (q + 1) (q + 3 * 0) _ (by omega)
    | k + 2, hcl, hi =>
        set bits := k + 2 with hbits
        have hb2 : 2 ≤ bits := by omega
        set G := gidney_adder_full_faithful_no_measurement_patched bits with hG
        show Gate.applyNat (Gate.shiftBy q G) f (q + 3 * i) = f (q + 3 * i)
        have hr : (q : Nat) + 3 * i = q + read_idx i := by unfold read_idx; ring
        rw [hr, shiftBy_applyNat_base q G f (read_idx i)]
        rw [gidney_read_arbitrary bits hb2 (fun j => f (q + j))
              (downshift_carry_clean bits q f hcl) i hi]
  ancRestored := by
    intro n q f hcl
    match n, hcl with
    | 0, _ => intro i hi; omega
    | 1, hcl =>
        intro i hi
        show Gate.applyNat (Gate.CX q (q + 1)) f (q + 3 * i + 2) = false
        rw [Gate.applyNat_CX, update_neq f (q + 1) (q + 3 * i + 2) _ (by omega)]
        exact hcl i hi
    | k + 2, hcl =>
        set bits := k + 2 with hbits
        have hb2 : 2 ≤ bits := by omega
        set G := gidney_adder_full_faithful_no_measurement_patched bits with hG
        intro i hi
        show Gate.applyNat (Gate.shiftBy q G) f (q + 3 * i + 2) = false
        have hc : (q : Nat) + 3 * i + 2 = q + carry_idx i := by unfold carry_idx; ring
        rw [hc, shiftBy_applyNat_base q G f (carry_idx i)]
        exact gidney_carry_arbitrary bits hb2 (fun j => f (q + j))
                (downshift_carry_clean bits q f hcl) i hi
  frame := by
    intro n q f p hp
    unfold inBlock at hp
    simp only [not_and, not_lt] at hp
    match n with
    | 0 => rfl
    | 1 =>
        show Gate.applyNat (Gate.CX q (q + 1)) f p = f p
        rw [Gate.applyNat_CX]
        by_cases hlt : p < q
        · exact update_neq f (q + 1) p _ (by omega)
        · have : q + (3 * 1 + 2) ≤ p := hp (by omega)
          exact update_neq f (q + 1) p _ (by omega)
    | k + 2 =>
        set bits := k + 2 with hbits
        have hb2 : 2 ≤ bits := by omega
        set G := gidney_adder_full_faithful_no_measurement_patched bits with hG
        show Gate.applyNat (Gate.shiftBy q G) f p = f p
        by_cases hlt : p < q
        · exact Gate.shiftBy_applyNat_below q G f p hlt
        · -- p ≥ q + span = q + 3*bits + 2 > q + 3*bits, so out of the tight range.
          have hge : q + (3 * bits + 2) ≤ p := hp (by omega)
          have hpe : p = q + (p - q) := by omega
          rw [hpe, shiftBy_applyNat_base q G f (p - q),
              Gate.applyNat_oob (gidney_patched_wt_tight bits hb2) _ (by omega)]
  wellTyped := by
    intro n q
    match n with
    | 0 =>
        show Gate.WellTyped (q + (3 * 0 + 2)) Gate.I
        show 0 < q + (3 * 0 + 2); omega
    | 1 =>
        show Gate.WellTyped (q + (3 * 1 + 2)) (Gate.CX q (q + 1))
        refine ⟨by omega, by omega, by omega⟩
    | k + 2 =>
        set bits := k + 2 with hbits
        have hb2 : 2 ≤ bits := by omega
        set G := gidney_adder_full_faithful_no_measurement_patched bits with hG
        show Gate.WellTyped (q + (3 * bits + 2)) (Gate.shiftBy q G)
        have hwt := Gate.shiftBy_wellTyped q (3 * bits) G (gidney_patched_wt_tight bits hb2)
        -- hwt : WellTyped (q + 3*bits) (shiftBy q G) ; weaken to q + (3*bits+2).
        exact Gate.wellTyped_le hwt (by omega)
  augendIdx_inBlock := by
    intro n q i hi; unfold inBlock; omega
  addendIdx_inBlock := by
    intro n q i hi; unfold inBlock; omega
  addendIdx_inj := by
    intro q i j h; omega
  augend_addend_disjoint := by
    intro q i j; omega
  ancClean_ext := by
    intro n q f g hagree hclean i hi
    rw [← hagree (q + 3 * i + 2) (by unfold inBlock; omega)
          (by intro j hj; constructor <;> omega)]
    exact hclean i hi

end FormalRV.BQAlgo
