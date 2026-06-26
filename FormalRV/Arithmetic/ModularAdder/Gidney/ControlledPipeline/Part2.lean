/- ControlledPipeline — Part2 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline.Part1

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! #### Tick 7b — multiplier-level commute lemma. -/

/-- **Commute lemma for `modMultConstGateAux`.**  At positions strictly
above the multiplier circuit's flag (i.e., `p > adder_n_qubits (bits+1)
+ multBits`), an `update _ p v` commutes through the full multiplier
auxiliary gate.  Proven directly via `applyNat_commute_update_above_dim`
applied to `modMultConstGateAux_wellTyped`. -/
theorem modMultConstGateAux_commute_update_outer
    (bits N a multBits k p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hk : k ≤ multBits) (hp : adder_n_qubits (bits + 1) + multBits < p) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGateAux bits N a multBits k) (update f p v)
      = update (Gate.applyNat (modMultConstGateAux bits N a multBits k) f) p v := by
  intro f
  have h_wt := modMultConstGateAux_wellTyped bits N a multBits k hbits hk
  exact applyNat_commute_update_above_dim
    (adder_n_qubits (bits + 1) + multBits + 1)
    (modMultConstGateAux bits N a multBits k) h_wt f p v (by omega)

/-- **Commute lemma for `modMultConstGate`.**  Specialization of the
aux-level commute lemma at `k = multBits`. -/
theorem modMultConstGate_commute_update_outer
    (bits N a multBits p : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hp : adder_n_qubits (bits + 1) + multBits < p) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGate bits N a multBits) (update f p v)
      = update (Gate.applyNat (modMultConstGate bits N a multBits) f) p v := by
  intro f
  unfold modMultConstGate
  exact modMultConstGateAux_commute_update_outer bits N a multBits multBits p v
    hbits (le_refl _) hp f

/-- **`modMultConstGateAux` commute lemma at a multiplier-bit position.**
For positions in the multiplier-bit range
`p = adder_n_qubits (bits+1) + j` with `j < multBits` AND `j ≥ k`
(i.e., a multiplier bit that has NOT yet been touched by iterations
`0, 1, ..., k-1`), `update _ p v` commutes through
`modMultConstGateAux bits N a multBits k`.  Proven by induction on `k`,
using `controlledModAddConstGate_commute_update_outer` for the step. -/
theorem modMultConstGateAux_commute_update_mult_pos_above
    (bits N a multBits k j : Nat) (v : Bool) (hbits : 1 ≤ bits)
    (hk : k ≤ multBits) (hjk : k ≤ j) (hj : j < multBits) :
    ∀ (f : Nat → Bool),
      Gate.applyNat (modMultConstGateAux bits N a multBits k)
          (update f (adder_n_qubits (bits + 1) + j) v)
      = update (Gate.applyNat (modMultConstGateAux bits N a multBits k) f)
          (adder_n_qubits (bits + 1) + j) v := by
  induction k with
  | zero =>
      intro f
      show Gate.applyNat Gate.I _ = update (Gate.applyNat Gate.I f) _ v
      rfl
  | succ k ih =>
      intro f
      have hk' : k ≤ multBits := by omega
      have hjk' : k ≤ j := by omega
      have h_step_ne_ctrl :
          adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + k := by omega
      have h_step_ne_flag :
          adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + multBits := by omega
      have h_p_dim :
          adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + j := by omega
      -- Unfold modMultConstGateAux at (k+1) on BOTH sides.
      simp only [modMultConstGateAux_apply_succ]
      -- Apply IH to the inner update on the LHS.
      rw [ih hk' hjk' f]
      -- Apply step commute to push update past the outer controlled-mod-add.
      exact controlledModAddConstGate_commute_update_outer bits N ((a * 2^k) % N)
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              (adder_n_qubits (bits + 1) + j) v hbits h_p_dim h_step_ne_ctrl h_step_ne_flag
              (Gate.applyNat (modMultConstGateAux bits N a multBits k) f)

/-- Recursion unfolding for the aux at `i+1`. -/
theorem mult_input_F_aux_succ (bits multBits m i : Nat) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m (i + 1) f
    = update (mult_input_F_aux bits multBits m i f)
             (adder_n_qubits (bits + 1) + i) (Nat.testBit m i) := rfl

/-- Decoder at multiplier-bit positions: `mult_input_F_aux ... i f` at
position `adder_n_qubits (bits+1) + j` returns `Nat.testBit m j`, when
`j < i` (i.e., bit `j` has been written by some iteration ≤ i-1). -/
theorem mult_input_F_aux_at_mult_pos
    (bits multBits m i j : Nat) (hj : j < i) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i f (adder_n_qubits (bits + 1) + j)
    = Nat.testBit m j := by
  induction i with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ i ih =>
      rw [mult_input_F_aux_succ]
      by_cases h_j_eq_i : j = i
      · subst h_j_eq_i
        exact update_eq _ _ _
      · have h_j_lt_i : j < i := by omega
        have h_ne : adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + i := by
          omega
        rw [update_neq _ _ _ _ h_ne]
        exact ih h_j_lt_i

/-- Decoder at non-multiplier positions: `mult_input_F_aux ... i f` at
position `p` outside the multiplier-bit range
`[adder_n_qubits (bits+1), adder_n_qubits (bits+1) + i)` equals `f p`. -/
theorem mult_input_F_aux_at_non_mult_pos
    (bits multBits m i p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1) ∨ adder_n_qubits (bits + 1) + i ≤ p)
    (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i f p = f p := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [mult_input_F_aux_succ]
      have h_outside_i : p < adder_n_qubits (bits + 1) ∨ adder_n_qubits (bits + 1) + i ≤ p := by
        rcases h_outside with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_p_ne : p ≠ adder_n_qubits (bits + 1) + i := by
        rcases h_outside with h | h
        · omega
        · omega
      rw [update_neq _ _ _ _ h_p_ne]
      exact ih h_outside_i

/-- Top-level decoder at multiplier-bit position. -/
theorem mult_input_F_at_mult_pos
    (bits multBits x m j : Nat) (hj : j < multBits) :
    mult_input_F bits multBits x m (adder_n_qubits (bits + 1) + j)
    = Nat.testBit m j := by
  unfold mult_input_F
  exact mult_input_F_aux_at_mult_pos bits multBits m multBits j hj _

/-- Top-level decoder at non-multiplier positions: equal to
`adder_input_F (bits+1) 0 x`. -/
theorem mult_input_F_at_non_mult_pos
    (bits multBits x m p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1)
                 ∨ adder_n_qubits (bits + 1) + multBits ≤ p) :
    mult_input_F bits multBits x m p = adder_input_F (bits + 1) 0 x p := by
  unfold mult_input_F
  exact mult_input_F_aux_at_non_mult_pos bits multBits m multBits p h_outside _

/-! #### Tick 7d — `mult_input_F` reordering (pulling out the k-th
multiplier update). -/

/-- `mult_input_F_aux` commutes with an `update _ (adder_n_qubits (bits+1) + j) v`
when `j ≥ i` (i.e., the iteration hasn't touched position `pos j` yet). -/
theorem mult_input_F_aux_commute_update_above
    (bits multBits m i j : Nat) (hj : i ≤ j) (v : Bool) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m i (update f (adder_n_qubits (bits + 1) + j) v)
    = update (mult_input_F_aux bits multBits m i f)
             (adder_n_qubits (bits + 1) + j) v := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hj_succ : i ≤ j := by omega
      have h_ne_succ : adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + j := by
        have : i < j := by omega
        omega
      have h_ne_succ' : adder_n_qubits (bits + 1) + j ≠ adder_n_qubits (bits + 1) + i :=
        Ne.symm h_ne_succ
      rw [mult_input_F_aux_succ, ih hj_succ]
      rw [update_update_comm _ _ _ _ _ h_ne_succ']
      rw [← mult_input_F_aux_succ]

/-- **`mult_input_F` isolation at position `k`.**  For `k < multBits`,
the full multiplier-encoded input is equal to `mult_input_F_aux` at
iteration `multBits` applied to a base that already carries the k-th
multiplier update on `adder_input_F`.  The k-th iteration of the aux
overwrites position `adder_n_qubits (bits+1) + k` to the same value
(`Nat.testBit m k`), so the additional update is absorbed; outside the
multiplier range the update at `pos k` is transparent. -/
theorem mult_input_F_isolate_k
    (bits multBits x m k : Nat) (hk : k < multBits) :
    mult_input_F bits multBits x m
    = mult_input_F_aux bits multBits m multBits
        (update (adder_input_F (bits + 1) 0 x)
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  funext q
  unfold mult_input_F
  by_cases h_q_in : adder_n_qubits (bits + 1) ≤ q
                    ∧ q < adder_n_qubits (bits + 1) + multBits
  · -- q in the multiplier range: q = pos j for some j < multBits.
    obtain ⟨h_q_lo, h_q_hi⟩ := h_q_in
    obtain ⟨j, hj_eq⟩ : ∃ j, q = adder_n_qubits (bits + 1) + j :=
      ⟨q - adder_n_qubits (bits + 1), by omega⟩
    have hj : j < multBits := by omega
    rw [hj_eq]
    rw [mult_input_F_aux_at_mult_pos bits multBits m multBits j hj
         (adder_input_F (bits + 1) 0 x)]
    rw [mult_input_F_aux_at_mult_pos bits multBits m multBits j hj
         (update (adder_input_F (bits + 1) 0 x)
                 (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))]
  · -- q outside the multiplier range: both sides reduce to the base function at q.
    have h_outside : q < adder_n_qubits (bits + 1)
                   ∨ adder_n_qubits (bits + 1) + multBits ≤ q := by
      by_cases h_lo : q < adder_n_qubits (bits + 1)
      · exact Or.inl h_lo
      · push_neg at h_lo
        exact Or.inr (by
          rcases Nat.lt_or_ge q (adder_n_qubits (bits + 1) + multBits) with h | h
          · exact absurd ⟨h_lo, h⟩ h_q_in
          · exact h)
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m multBits q h_outside
         (adder_input_F (bits + 1) 0 x)]
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m multBits q h_outside
         (update (adder_input_F (bits + 1) 0 x)
                 (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))]
    -- Goal: adder_input_F ... q = (update (adder_input_F) (pos k) (testBit m k)) q.
    have h_q_ne_k : q ≠ adder_n_qubits (bits + 1) + k := by
      rcases h_outside with h | h
      · omega
      · omega
    rw [update_neq _ _ _ _ h_q_ne_k]

/-! #### Tick 7e — full single-step correctness on `mult_input_F`. -/

/-- Absorption lemma: when an outer `update` at the k-th multiplier
position rewrites a value that the inner aux-at-iteration-k already
carries (because the inner has `update f (pos k) (testBit m k)` as base
and aux at k doesn't touch pos k), the outer update is a no-op. -/
theorem mult_input_F_aux_absorb_at_k_position
    (bits multBits m k : Nat) (f : Nat → Bool) :
    mult_input_F_aux bits multBits m (k + 1)
        (update f (adder_n_qubits (bits + 1) + k) (Nat.testBit m k))
    = mult_input_F_aux bits multBits m k
        (update f (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  rw [mult_input_F_aux_succ]
  funext q
  by_cases hq : q = adder_n_qubits (bits + 1) + k
  · subst hq
    rw [update_eq]
    rw [mult_input_F_aux_at_non_mult_pos bits multBits m k
          (adder_n_qubits (bits + 1) + k) (Or.inr (le_refl _)) _]
    rw [update_eq]
  · rw [update_neq _ _ _ _ hq]

/-- Inductive helper for the single-step correctness on `mult_input_F`. -/
theorem CMAcg_on_mult_input_F_aux_iso
    (bits N c x m multBits k : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N) (hk : k < multBits) :
    ∀ i, i ≤ multBits →
    Gate.applyNat
      (controlledModAddConstGate bits N c
        (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits))
      (mult_input_F_aux bits multBits m i
        (update (adder_input_F (bits + 1) 0 x)
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)))
    = mult_input_F_aux bits multBits m i
        (update (adder_input_F (bits + 1) 0
                  (if Nat.testBit m k then (x + c) % N else x))
                (adder_n_qubits (bits + 1) + k) (Nat.testBit m k)) := by
  intro i hi
  induction i with
  | zero =>
      have h_ctrl_ge_adder :
          adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + k := by omega
      have h_flag_ge_ctrl :
          adder_n_qubits (bits + 1) + k + 1 ≤ adder_n_qubits (bits + 1) + multBits := by omega
      show Gate.applyNat _ (update _ _ _) = update _ _ _
      exact controlledModAddConstGate_correct bits N c x
              (Nat.testBit m k)
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              hbits hN_pos hN hx hc_pos hc h_ctrl_ge_adder (by omega)
  | succ i ih =>
      have hi' : i ≤ multBits := by omega
      have ih' := ih hi'
      by_cases hi_eq_k : i = k
      · -- Outer update at pos i = pos k is absorbed via the absorption lemma.
        subst hi_eq_k
        rw [mult_input_F_aux_absorb_at_k_position bits multBits m i
              (adder_input_F (bits + 1) 0 x)]
        rw [mult_input_F_aux_absorb_at_k_position bits multBits m i
              (adder_input_F (bits + 1) 0 (if Nat.testBit m i then (x + c) % N else x))]
        exact ih'
      · -- Pos i ≠ controlIdx and ≠ flagIdx. Commute CMAcg past the outer update.
        rw [mult_input_F_aux_succ]
        rw [mult_input_F_aux_succ]
        have h_pos_i_above_adder :
            adder_n_qubits (bits + 1) ≤ adder_n_qubits (bits + 1) + i := by omega
        have h_pos_i_ne_ctrl :
            adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + k := by
          intro h_eq; apply hi_eq_k; omega
        have h_pos_i_ne_flag :
            adder_n_qubits (bits + 1) + i ≠ adder_n_qubits (bits + 1) + multBits := by
          have : i < multBits := by omega
          omega
        rw [controlledModAddConstGate_commute_update_outer bits N c
              (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits)
              (adder_n_qubits (bits + 1) + i) (Nat.testBit m i) hbits
              h_pos_i_above_adder h_pos_i_ne_ctrl h_pos_i_ne_flag _]
        rw [ih']

/-- **Single-step correctness for `controlledModAddConstGate` on
`mult_input_F`.**  Applied to the multiplier-encoded input
`mult_input_F bits multBits x m`, the controlled modular-add gate
(controlled by the `k`-th multiplier qubit, with shared flag at
position `adder_n_qubits (bits+1) + multBits`) advances the adder's
target register from `x` to `(x + c) % N` when bit `k` of `m` is set,
or leaves it unchanged otherwise. -/
theorem controlledModAddConstGate_on_mult_input_F
    (bits N c x m multBits k : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < N) (hc_pos : 0 < c) (hc : c < N) (hk : k < multBits) :
    Gate.applyNat
      (controlledModAddConstGate bits N c
        (adder_n_qubits (bits + 1) + k) (adder_n_qubits (bits + 1) + multBits))
      (mult_input_F bits multBits x m)
    = mult_input_F bits multBits
        (if Nat.testBit m k then (x + c) % N else x) m := by
  rw [mult_input_F_isolate_k bits multBits x m k hk]
  rw [mult_input_F_isolate_k bits multBits
        (if Nat.testBit m k then (x + c) % N else x) m k hk]
  exact CMAcg_on_mult_input_F_aux_iso bits N c x m multBits k
          hbits hN_pos hN hx hc_pos hc hk multBits (le_refl _)


end FormalRV.BQAlgo
