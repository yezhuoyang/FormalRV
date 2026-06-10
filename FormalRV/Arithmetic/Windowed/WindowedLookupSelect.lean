/-
  FormalRV.Shor.WindowedCircuit.WindowedLookupSelect — the QROM-read SELECTION lemma.

  The babbush2018 unary-iteration QROM (`BQAlgo.unary_lookup_multi_iteration`),
  instantiated with the windowed iteration data
  (`lookupReadAt w pos W T = unary_lookup_multi_iteration w
     ((List.range (2^w)).map (fun v => (addrFlips w v, wordCnotsAt pos W (T v))))`),
  reads EXACTLY the addressed table row: with the address register holding `v < 2^w`,

    * every word position `pos j` (j < W) is XOR'd with `(T v).testBit j`, and
    * every position that is NOT a word target is unchanged (ctrl preserved,
      address restored, AND-ancillas returned clean, everything else untouched).

  The mathematical core: row `u`'s flip pattern `addrFlips w u` makes the
  prefix-AND trigger fire iff the effective address is all-ones iff
  `∀ i < w, v.testBit i = u.testBit i` iff `u = v` (testBit extensionality below
  `2^w`).  So the multi-iteration XOR value collapses to the single `u = v`
  contribution, whose word-CNOT pattern is exactly the bits of `T v`.

  Built on the proven headline machinery of
  `FormalRV.Arithmetic.UnaryLookup.UnaryLookupIterationCorrectness`
  (`Lookup.unary_lookup_multi_iteration_correct` + the multi-iter preservation
  lemmas), plus a fresh `Gate.applyNat` ↔ post-state-model bridge proven here.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupIterationCorrectness

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedLookupAdd

/-! ## §1. `Gate.applyNat` ↔ Boolean post-state model bridge.

The UnaryLookup correctness corpus characterizes the lookup via the Boolean
post-state model (`Lookup.iteration_post_state` etc.).  Here we prove the
actual gate semantics `Gate.applyNat` computes exactly that model, layer by
layer, then for the full (multi-)iteration. -/

/-- The project-local `Framework.update` IS Mathlib's `Function.update`
    (on `Nat → Bool`). -/
theorem update_eq_Function_update (f : Nat → Bool) (c : Nat) (v : Bool) :
    update f c v = Function.update f c v := by
  funext j
  by_cases h : j = c
  · subst h; rw [update_eq, Function.update_self]
  · rw [update_neq f c j v h, Function.update_of_ne h]

/-- X-flip layer: gate semantics = `Lookup.x_flip_post_state`. -/
theorem applyNat_x_gates_from_indices (xs : List Nat) (f : Nat → Bool) :
    Gate.applyNat (x_gates_from_indices xs) f = Lookup.x_flip_post_state xs f := by
  induction xs generalizing f with
  | nil => rfl
  | cons i rest ih =>
    show Gate.applyNat (Gate.seq (x_gates_from_indices rest) (Gate.X i)) f
          = Lookup.x_flip_post_state (i :: rest) f
    rw [Gate.applyNat_seq, Gate.applyNat_X, ih]
    show update (Lookup.x_flip_post_state rest f) i
          (!(Lookup.x_flip_post_state rest f i))
        = Function.update (Lookup.x_flip_post_state rest f) i
          (!(Lookup.x_flip_post_state rest f i))
    exact update_eq_Function_update _ _ _

/-- CNOT layer: gate semantics = `Lookup.cnot_layer_post_state`. -/
theorem applyNat_cx_gates_from_indices (c : Nat) (xs : List Nat) (f : Nat → Bool) :
    Gate.applyNat (cx_gates_from_indices c xs) f
      = Lookup.cnot_layer_post_state c xs f := by
  induction xs generalizing f with
  | nil => rfl
  | cons t rest ih =>
    show Gate.applyNat (Gate.seq (cx_gates_from_indices c rest) (Gate.CX c t)) f
          = Lookup.cnot_layer_post_state c (t :: rest) f
    rw [Gate.applyNat_seq, Gate.applyNat_CX, ih]
    show update (Lookup.cnot_layer_post_state c rest f) t
          (xor (Lookup.cnot_layer_post_state c rest f t)
               (Lookup.cnot_layer_post_state c rest f c))
        = Function.update (Lookup.cnot_layer_post_state c rest f) t
          (xor (Lookup.cnot_layer_post_state c rest f t)
               (Lookup.cnot_layer_post_state c rest f c))
    exact update_eq_Function_update _ _ _

/-- Single cascade step: gate semantics = `prefix_and_step_post_state`. -/
theorem applyNat_prefix_and_step (i : Nat) (f : Nat → Bool) :
    Gate.applyNat (prefix_and_step i) f = prefix_and_step_post_state i f := by
  unfold prefix_and_step prefix_and_step_post_state
  split
  · rfl
  · rfl

/-- Forward cascade: gate semantics = `prefix_and_cascade_post_state`. -/
theorem applyNat_prefix_and_cascade (n : Nat) (f : Nat → Bool) :
    Gate.applyNat (prefix_and_cascade n) f = prefix_and_cascade_post_state n f := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat (Gate.seq (prefix_and_cascade k) (prefix_and_step k)) f
          = prefix_and_step_post_state k (prefix_and_cascade_post_state k f)
    rw [Gate.applyNat_seq, ih, applyNat_prefix_and_step]

/-- Reverse cascade: gate semantics = `prefix_and_uncompute_post_state`. -/
theorem applyNat_prefix_and_uncompute (n : Nat) (f : Nat → Bool) :
    Gate.applyNat (prefix_and_uncompute n) f
      = prefix_and_uncompute_post_state n f := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat (Gate.seq (prefix_and_step k) (prefix_and_uncompute k)) f
          = prefix_and_uncompute_post_state k (prefix_and_step_post_state k f)
    rw [Gate.applyNat_seq, applyNat_prefix_and_step, ih]

/-- One full lookup iteration: gate semantics = `Lookup.iteration_post_state`. -/
theorem applyNat_unary_lookup_iteration
    (n_addr : Nat) (flips cnots : List Nat) (f : Nat → Bool) :
    Gate.applyNat (unary_lookup_iteration n_addr flips cnots) f
      = Lookup.iteration_post_state n_addr flips cnots f := by
  show Gate.applyNat
        (Gate.seq (Gate.seq (Gate.seq (Gate.seq
          (x_gates_from_indices flips) (prefix_and_cascade n_addr))
          (cx_gates_from_indices (ulookup_and_idx (n_addr - 1)) cnots))
          (prefix_and_uncompute n_addr)) (x_gates_from_indices flips)) f
      = Lookup.iteration_post_state n_addr flips cnots f
  simp only [Gate.applyNat_seq]
  rw [applyNat_x_gates_from_indices, applyNat_prefix_and_cascade,
      applyNat_cx_gates_from_indices, applyNat_prefix_and_uncompute,
      applyNat_x_gates_from_indices]
  rfl

/-- **The multi-iteration bridge**: gate semantics of the full babbush2018
    unary-iteration QROM = `Lookup.multi_iteration_post_state`. -/
theorem applyNat_unary_lookup_multi_iteration
    (n_addr : Nat) (iters : List (List Nat × List Nat)) (f : Nat → Bool) :
    Gate.applyNat (unary_lookup_multi_iteration n_addr iters) f
      = Lookup.multi_iteration_post_state n_addr iters f := by
  induction iters generalizing f with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show Gate.applyNat
          (Gate.seq (unary_lookup_multi_iteration n_addr rest)
                    (unary_lookup_iteration n_addr flips cnots)) f
        = Lookup.iteration_post_state n_addr flips cnots
            (Lookup.multi_iteration_post_state n_addr rest f)
    rw [Gate.applyNat_seq, ih, applyNat_unary_lookup_iteration]

/-! ## §2. Structure of the windowed iteration data.

Membership and `Nodup` facts for `addrFlips` (the per-row X-flip pattern) and
`wordCnotsAt` (the per-row word-CNOT pattern at positions `pos`). -/

/-- Membership in `addrFlips w u`: exactly the address indices of the
    zero bits of `u` below `w`. -/
theorem mem_addrFlips (w u x : Nat) :
    x ∈ addrFlips w u
      ↔ ∃ i, i < w ∧ u.testBit i = false ∧ x = ulookup_address_idx i := by
  unfold addrFlips
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hsome⟩
    rw [List.mem_range] at hi
    by_cases hbit : u.testBit i
    · rw [if_pos hbit] at hsome; exact absurd hsome (by simp)
    · rw [if_neg hbit] at hsome
      exact ⟨i, hi, by simpa using hbit, (Option.some_inj.mp hsome).symm⟩
  · rintro ⟨i, hi, hbit, rfl⟩
    exact ⟨i, List.mem_range.mpr hi, by rw [hbit]; simp⟩

/-- Every element of `addrFlips w u` is an address index below `w`. -/
theorem addrFlips_flip_addr (w u : Nat) :
    ∀ x ∈ addrFlips w u, ∃ i, i < w ∧ x = ulookup_address_idx i := by
  intro x hx
  obtain ⟨i, hi, _, hxi⟩ := (mem_addrFlips w u x).mp hx
  exact ⟨i, hi, hxi⟩

/-- `addrFlips w u` has no duplicates (`ulookup_address_idx` is injective). -/
theorem addrFlips_nodup (w u : Nat) : (addrFlips w u).Nodup := by
  unfold addrFlips
  refine (List.nodup_range).filterMap ?_
  intro i j x hi hj
  by_cases hbi : u.testBit i
  · rw [if_pos hbi] at hi; exact absurd hi (by simp)
  · rw [if_neg hbi] at hi
    by_cases hbj : u.testBit j
    · rw [if_pos hbj] at hj; exact absurd hj (by simp)
    · rw [if_neg hbj] at hj
      have hxi : x = ulookup_address_idx i := (Option.some_inj.mp hi).symm
      have hxj : x = ulookup_address_idx j := (Option.some_inj.mp hj).symm
      unfold ulookup_address_idx at hxi hxj
      omega

/-- Membership in `wordCnotsAt pos W Tv`: exactly the positions `pos j` of the
    one bits of `Tv` below `W`. -/
theorem mem_wordCnotsAt (pos : Nat → Nat) (W Tv x : Nat) :
    x ∈ wordCnotsAt pos W Tv
      ↔ ∃ j, j < W ∧ Tv.testBit j = true ∧ x = pos j := by
  unfold wordCnotsAt
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hsome⟩
    rw [List.mem_range] at hj
    by_cases hbit : Tv.testBit j
    · rw [if_pos hbit] at hsome
      exact ⟨j, hj, hbit, (Option.some_inj.mp hsome).symm⟩
    · rw [if_neg hbit] at hsome; exact absurd hsome (by simp)
  · rintro ⟨j, hj, hbit, rfl⟩
    exact ⟨j, List.mem_range.mpr hj, by rw [hbit]; simp⟩

/-- `filterMap` of an "if-some-else-none" function = `map` after `filter`.
    (Local helper; lets us prove `Nodup` with injectivity only ON the list.) -/
theorem filterMap_ite_eq_map_filter (p : Nat → Bool) (g : Nat → Nat) :
    ∀ l : List Nat,
      l.filterMap (fun j => if p j then some (g j) else none)
        = (l.filter p).map g
  | [] => rfl
  | j :: l => by
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h : p j
    · rw [if_pos h, if_pos h, List.map_cons, filterMap_ite_eq_map_filter p g l]
    · rw [if_neg h, if_neg h, filterMap_ite_eq_map_filter p g l]

/-- `wordCnotsAt` as `map pos` of the filtered bit positions. -/
theorem wordCnotsAt_eq_map_filter (pos : Nat → Nat) (W Tv : Nat) :
    wordCnotsAt pos W Tv
      = ((List.range W).filter (fun j => Tv.testBit j)).map pos := by
  unfold wordCnotsAt
  exact filterMap_ite_eq_map_filter (fun j => Tv.testBit j) pos (List.range W)

/-- `wordCnotsAt pos W Tv` has no duplicates when `pos` is injective below `W`. -/
theorem wordCnotsAt_nodup (pos : Nat → Nat) (W Tv : Nat)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    (wordCnotsAt pos W Tv).Nodup := by
  rw [wordCnotsAt_eq_map_filter]
  refine List.Nodup.map_on ?_ (List.Nodup.filter _ List.nodup_range)
  intro j hj k hk hjk
  have hjW : j < W := List.mem_range.mp (List.mem_of_mem_filter hj)
  have hkW : k < W := List.mem_range.mp (List.mem_of_mem_filter hk)
  exact hpos_inj j k hjW hkW hjk

/-- Every element of `wordCnotsAt pos W Tv` lies above the ctrl/address/AND
    region when all `pos` positions do (`Lookup.AllWordIdx` form). -/
theorem wordCnotsAt_allWordIdx (w : Nat) (pos : Nat → Nat) (W Tv : Nat)
    (hpos_high : ∀ j, j < W → 2 * w < pos j) :
    Lookup.AllWordIdx w (wordCnotsAt pos W Tv) := by
  intro x hx
  obtain ⟨j, hj, _, rfl⟩ := (mem_wordCnotsAt pos W Tv x).mp hx
  have := hpos_high j hj
  omega

/-- `pos j` is a word-CNOT target for row value `Tv` iff bit `j` of `Tv` is set
    (for `j < W`, with `pos` injective below `W`). -/
theorem pos_mem_wordCnotsAt_iff (pos : Nat → Nat) (W Tv j : Nat) (hj : j < W)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    pos j ∈ wordCnotsAt pos W Tv ↔ Tv.testBit j = true := by
  rw [mem_wordCnotsAt]
  constructor
  · rintro ⟨k, hk, hbit, hpk⟩
    rwa [hpos_inj j k hj hk hpk]
  · intro hbit
    exact ⟨j, hj, hbit, rfl⟩

/-- Boolean form of `pos_mem_wordCnotsAt_iff`. -/
theorem decide_pos_mem_wordCnotsAt (pos : Nat → Nat) (W Tv j : Nat) (hj : j < W)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    decide (pos j ∈ wordCnotsAt pos W Tv) = Tv.testBit j := by
  by_cases hbit : Tv.testBit j = true
  · rw [hbit]
    exact decide_eq_true ((pos_mem_wordCnotsAt_iff pos W Tv j hj hpos_inj).mpr hbit)
  · rw [(Bool.not_eq_true _).mp hbit]
    exact decide_eq_false
      (fun hm => hbit ((pos_mem_wordCnotsAt_iff pos W Tv j hj hpos_inj).mp hm))

/-! ## §3. Trigger selection: row `u` fires iff `u = v`.

Row `u`'s flip pattern makes the effective address all-ones iff the physical
address `v` agrees with `u` on every bit below `w`, i.e. iff `u = v`. -/

/-- `Lookup.address_and` is true iff the ctrl is true and all first `n` bits are set. -/
theorem address_and_eq_true_iff (ctrl : Bool) (addr n : Nat) :
    Lookup.address_and ctrl addr n = true
      ↔ ctrl = true ∧ ∀ i, i < n → addr.testBit i = true := by
  induction n with
  | zero =>
    show ctrl = true ↔ _
    exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ k ih =>
    show (Lookup.address_and ctrl addr k && addr.testBit k) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨⟨hc, hbits⟩, hk⟩
      refine ⟨hc, fun i hi => ?_⟩
      by_cases hik : i < k
      · exact hbits i hik
      · have : i = k := by omega
        subst this
        exact hk
    · rintro ⟨hc, hbits⟩
      exact ⟨⟨hc, fun i hi => hbits i (Nat.lt_succ_of_lt hi)⟩,
             hbits k (Nat.lt_succ_self k)⟩

/-- For `i < w`, the address index `ulookup_address_idx i` is flipped for row
    `u` exactly when bit `i` of `u` is zero. -/
theorem decide_mem_addrFlips (w u i : Nat) (hi : i < w) :
    decide (ulookup_address_idx i ∈ addrFlips w u) = !u.testBit i := by
  by_cases hbit : u.testBit i = true
  · rw [hbit, Bool.not_true]
    apply decide_eq_false
    intro hmem
    obtain ⟨i', hi', hbit', heq⟩ := (mem_addrFlips w u _).mp hmem
    have hii' : i = i' := by unfold ulookup_address_idx at heq; omega
    rw [hii', hbit'] at hbit
    exact Bool.false_ne_true hbit
  · have hbitf : u.testBit i = false := (Bool.not_eq_true _).mp hbit
    rw [hbitf, Bool.not_false]
    exact decide_eq_true ((mem_addrFlips w u _).mpr ⟨i, hi, hbitf, rfl⟩)

/-- Bool helper: `xor a (!b) = true ↔ b = a`. -/
theorem xor_not_eq_true_iff (a b : Bool) : xor a (!b) = true ↔ b = a := by
  cases a <;> cases b <;> decide

/-- **Row-selection at the trigger level**: row `u`'s prefix-AND trigger,
    evaluated on physical address `v` (both `< 2^w`), is `decide (u = v)` —
    only the addressed row fires. -/
theorem addrFlips_trigger_eq_decide (w u v : Nat) (hu : u < 2 ^ w) (hv : v < 2 ^ w) :
    Lookup.address_and true (Lookup.effective_addr v (addrFlips w u) w) w
      = decide (u = v) := by
  have key : Lookup.address_and true
      (Lookup.effective_addr v (addrFlips w u) w) w = true ↔ u = v := by
    rw [address_and_eq_true_iff]
    constructor
    · rintro ⟨-, hbits⟩
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < w
      · have h := hbits i hi
        rw [Lookup.effective_addr_testBit v (addrFlips w u) w i hi,
            decide_mem_addrFlips w u i hi] at h
        exact (xor_not_eq_true_iff (v.testBit i) (u.testBit i)).mp h
      · have hiw : w ≤ i := Nat.le_of_not_lt hi
        rw [Nat.testBit_lt_two_pow
              (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) hiw)),
            Nat.testBit_lt_two_pow
              (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hiw))]
    · intro huv
      subst huv
      refine ⟨rfl, fun i hi => ?_⟩
      rw [Lookup.effective_addr_testBit u (addrFlips w u) w i hi,
          decide_mem_addrFlips w u i hi]
      cases hb : u.testBit i <;> rfl
  by_cases huv : u = v
  · rw [decide_eq_true huv]
    exact key.mpr huv
  · rw [decide_eq_false huv]
    cases h : Lookup.address_and true
        (Lookup.effective_addr v (addrFlips w u) w) w
    · rfl
    · exact absurd (key.mp h) huv

/-! ## §4. The multi-iteration XOR value collapses to the addressed row. -/

/-- Over a duplicate-free row list `L` (all rows `< 2^w`), the cumulative XOR
    value of the windowed iteration data at any position `p` is the single
    `v`-row contribution (if `v ∈ L`). -/
theorem xor_value_rows_collapse
    (w v : Nat) (hv : v < 2 ^ w) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (p : Nat) (L : List Nat) (hL : ∀ u ∈ L, u < 2 ^ w) (hnd : L.Nodup) :
    Lookup.multi_iteration_xor_value_via_address_and true v w
      (L.map (fun u => (addrFlips w u, wordCnotsAt pos W (T u)))) p
      = if v ∈ L then decide (p ∈ wordCnotsAt pos W (T v)) else false := by
  induction L with
  | nil =>
    rw [if_neg (by simp)]
    rfl
  | cons u L ih =>
    rw [List.map_cons]
    show xor (decide (p ∈ wordCnotsAt pos W (T u)) &&
              Lookup.address_and true
                (Lookup.effective_addr v (addrFlips w u) w) w)
             (Lookup.multi_iteration_xor_value_via_address_and true v w
               (L.map (fun u => (addrFlips w u, wordCnotsAt pos W (T u)))) p)
        = _
    have hu : u < 2 ^ w := hL u List.mem_cons_self
    obtain ⟨hvL, hndL⟩ := List.nodup_cons.mp hnd
    rw [addrFlips_trigger_eq_decide w u v hu hv,
        ih (fun x hx => hL x (List.mem_cons_of_mem u hx)) hndL]
    by_cases huv : u = v
    · subst huv
      rw [decide_eq_true (rfl : u = u), Bool.and_true, if_neg hvL,
          if_pos List.mem_cons_self, Bool.xor_false]
    · rw [decide_eq_false huv, Bool.and_false, Bool.false_xor]
      by_cases hvL' : v ∈ L
      · rw [if_pos hvL', if_pos (List.mem_cons_of_mem u hvL')]
      · rw [if_neg hvL', if_neg (fun hmem =>
              (List.mem_cons.mp hmem).elim (fun h => huv h.symm) hvL')]

/-- Specialized to the full row list `List.range (2^w)`: the XOR value at `p`
    is exactly the `v`-row word-CNOT membership bit. -/
theorem xor_value_windowed_rows
    (w v : Nat) (hv : v < 2 ^ w) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (p : Nat) :
    Lookup.multi_iteration_xor_value_via_address_and true v w
      ((List.range (2 ^ w)).map
        (fun u => (addrFlips w u, wordCnotsAt pos W (T u)))) p
      = decide (p ∈ wordCnotsAt pos W (T v)) := by
  rw [xor_value_rows_collapse w v hv pos W T p (List.range (2 ^ w))
        (fun u hu => List.mem_range.mp hu) List.nodup_range,
      if_pos (List.mem_range.mpr hv)]

/-! ## §5. Side conditions for the windowed iteration data, and the headline. -/

section RowIters

variable (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)

private theorem rowIters_flip_addr :
    ∀ flips cnots,
      (flips, cnots) ∈ (List.range (2 ^ w)).map
        (fun u => (addrFlips w u, wordCnotsAt pos W (T u))) →
      ∀ x ∈ flips, ∃ i, i < w ∧ x = ulookup_address_idx i := by
  intro flips cnots hmem x hx
  obtain ⟨u, _, heq⟩ := List.mem_map.mp hmem
  have hf : addrFlips w u = flips := congrArg Prod.fst heq
  rw [← hf] at hx
  exact addrFlips_flip_addr w u x hx

private theorem rowIters_flip_nodup :
    ∀ flips cnots,
      (flips, cnots) ∈ (List.range (2 ^ w)).map
        (fun u => (addrFlips w u, wordCnotsAt pos W (T u))) →
      flips.Nodup := by
  intro flips cnots hmem
  obtain ⟨u, _, heq⟩ := List.mem_map.mp hmem
  have hf : addrFlips w u = flips := congrArg Prod.fst heq
  rw [← hf]
  exact addrFlips_nodup w u

private theorem rowIters_cnots_nodup
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    ∀ flips cnots,
      (flips, cnots) ∈ (List.range (2 ^ w)).map
        (fun u => (addrFlips w u, wordCnotsAt pos W (T u))) →
      cnots.Nodup := by
  intro flips cnots hmem
  obtain ⟨u, _, heq⟩ := List.mem_map.mp hmem
  have hc : wordCnotsAt pos W (T u) = cnots := congrArg Prod.snd heq
  rw [← hc]
  exact wordCnotsAt_nodup pos W (T u) hpos_inj

private theorem rowIters_word
    (hpos_high : ∀ j, j < W → 2 * w < pos j) :
    ∀ flips cnots,
      (flips, cnots) ∈ (List.range (2 ^ w)).map
        (fun u => (addrFlips w u, wordCnotsAt pos W (T u))) →
      Lookup.AllWordIdx w cnots := by
  intro flips cnots hmem
  obtain ⟨u, _, heq⟩ := List.mem_map.mp hmem
  have hc : wordCnotsAt pos W (T u) = cnots := congrArg Prod.snd heq
  rw [← hc]
  exact wordCnotsAt_allWordIdx w pos W (T u) hpos_high

end RowIters

/-- **QROM-read selection, word conjunct**: with the address register holding
    `v < 2^w`, the babbush2018 read `lookupReadAt w pos W T` XORs exactly the
    addressed table row `T v` into the word positions: bit `j` of `T v` lands
    at `pos j`. -/
theorem lookupReadAt_selects_word
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool) (v : Nat)
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k)
    (j : Nat) (hj : j < W) :
    Gate.applyNat (lookupReadAt w pos W T) f (pos j)
      = xor (f (pos j)) ((T v).testBit j) := by
  unfold lookupReadAt
  rw [applyNat_unary_lookup_multi_iteration,
      Lookup.unary_lookup_multi_iteration_correct w hw _
        (rowIters_flip_addr w pos W T)
        (rowIters_flip_nodup w pos W T)
        (rowIters_cnots_nodup w pos W T hpos_inj)
        (rowIters_word w pos W T hpos_high)
        true v f hctrl haddr hand (pos j)
        (by have := hpos_high j hj; omega),
      xor_value_windowed_rows w v hv pos W T (pos j),
      decide_pos_mem_wordCnotsAt pos W (T v) j hj hpos_inj]

/-- **QROM-read selection, frame conjunct**: every position that is not a word
    target (`pos j`, `j < W`) is unchanged by the read — the ctrl is preserved,
    the address register is restored, the AND-ancillas are returned clean, and
    everything outside the lookup's registers is untouched. -/
theorem lookupReadAt_frame
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (p : Nat) (hp : ∀ j, j < W → p ≠ pos j) :
    Gate.applyNat (lookupReadAt w pos W T) f p = f p := by
  unfold lookupReadAt
  rw [applyNat_unary_lookup_multi_iteration]
  by_cases hp_word : 1 + 2 * w ≤ p
  · -- p lies in the word region but is not any iteration's CNOT target.
    refine Lookup.multi_iteration_post_state_preserves_outside_all_cnots w _
      (rowIters_flip_addr w pos W T) f p hp_word ?_
    intro flips cnots hmem hpin
    obtain ⟨u, _, heq⟩ := List.mem_map.mp hmem
    have hc : wordCnotsAt pos W (T u) = cnots := congrArg Prod.snd heq
    rw [← hc] at hpin
    obtain ⟨j', hj', _, hpj'⟩ := (mem_wordCnotsAt pos W (T u) p).mp hpin
    exact hp j' hj' hpj'
  · -- p ≤ 2·w: p is the ctrl, an address bit, or an AND-ancilla.
    by_cases hp0 : p = 0
    · have h0 : p = ulookup_ctrl_idx := by unfold ulookup_ctrl_idx; omega
      rw [h0]
      exact Lookup.multi_iteration_post_state_preserves_ctrl w _
        (rowIters_flip_addr w pos W T) (rowIters_word w pos W T hpos_high) f
    · by_cases hodd : p % 2 = 1
      · obtain ⟨i, hi, hpi⟩ : ∃ i, i < w ∧ p = ulookup_address_idx i :=
          ⟨p / 2, by omega, by unfold ulookup_address_idx; omega⟩
        rw [hpi]
        exact Lookup.multi_iteration_post_state_preserves_address w _
          (rowIters_flip_nodup w pos W T) (rowIters_word w pos W T hpos_high)
          f i hi
      · obtain ⟨k, hk, hpk⟩ : ∃ k, k < w ∧ p = ulookup_and_idx k :=
          ⟨p / 2 - 1, by omega, by unfold ulookup_and_idx; omega⟩
        rw [hpk]
        exact Lookup.multi_iteration_post_state_preserves_and w _
          (rowIters_flip_addr w pos W T) (rowIters_word w pos W T hpos_high)
          f k hk

/-- **HEADLINE — QROM-read selection lemma.**  The babbush2018 unary-iteration
    QROM `unary_lookup_multi_iteration`, instantiated with the windowed
    iteration data (`lookupReadAt w pos W T`), reads exactly the addressed
    table row: with ctrl set, the address register holding `v < 2^w`, and the
    AND-ancillas clean,

    1. each word position `pos j` (`j < W`) is XOR'd with `(T v).testBit j`, and
    2. every position that is NOT a word target is unchanged (ctrl, address,
       AND-ancillas restored; everything else untouched). -/
theorem lookupReadAt_selects
    (w W : Nat) (T : Nat → Nat) (pos : Nat → Nat) (f : Nat → Bool) (v : Nat)
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hctrl : f ulookup_ctrl_idx = true)
    (haddr : ∀ i, i < w → f (ulookup_address_idx i) = v.testBit i)
    (hand : ∀ i, i < w → f (ulookup_and_idx i) = false)
    (hpos_high : ∀ j, j < W → 2 * w < pos j)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) :
    (∀ j, j < W →
      Gate.applyNat (lookupReadAt w pos W T) f (pos j)
        = xor (f (pos j)) ((T v).testBit j))
    ∧ (∀ p, (∀ j, j < W → p ≠ pos j) →
        Gate.applyNat (lookupReadAt w pos W T) f p = f p) :=
  ⟨fun j hj => lookupReadAt_selects_word w W T pos f v hw hv hctrl haddr hand
      hpos_high hpos_inj j hj,
   fun p hp => lookupReadAt_frame w W T pos f hpos_high p hp⟩

end FormalRV.Shor.WindowedCircuit
