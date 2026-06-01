import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise
import FormalRV.Arithmetic.ModularAdder.Defs
import FormalRV.Arithmetic.ModularAdder.Proofs3

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ### Tick 18 — SWAP semantics on `mult_input_F`. -/

/-- **HEADLINE: SWAP exchanges multiplier-register and target-register
values on `mult_input_F`.** Applied to `mult_input_F bits multBits x m`
(multiplier holds `m`, target holds `x`), the multiplier-target SWAP
produces `mult_input_F bits multBits m x` (multiplier holds `x`,
target holds `m`).  Requires `multBits ≤ bits + 1` (multiplier no
wider than adder) and `x, m < 2^multBits` (so they fit in the
multBits-wide register and have no high bits leaking into unswapped
positions). -/
theorem mult_target_swap_on_mult_input_F
    (bits multBits x m : Nat)
    (h_multBits_le : multBits ≤ bits + 1)
    (hx : x < 2^multBits) (hm : m < 2^multBits) :
    Gate.applyNat (mult_target_swap bits multBits)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits m x := by
  unfold mult_target_swap
  funext q
  -- Case 1: q = adder_n_qubits + j for some j < multBits (multiplier-side swap).
  by_cases h_mult : ∃ j, j < multBits ∧ q = adder_n_qubits (bits + 1) + j
  · obtain ⟨j, hj, hq_eq⟩ := h_mult
    rw [hq_eq]
    rw [mult_target_swap_aux_at_mult bits multBits _ j hj h_multBits_le]
    -- LHS: mult_input_F bits multBits x m (target_idx j) = adder_input_F (bits+1) 0 x (target_idx j)
    --      = x.testBit j (since (3j+1)%3 = 1, j < bits+1).
    -- RHS: mult_input_F bits multBits m x (adder_n_qubits + j) = Nat.testBit x j.
    have h_target_in_adder : target_idx j < adder_n_qubits (bits + 1) := by
      show 3 * j + 1 < 3 * (bits + 1) + 2
      omega
    have h_lhs_decode :
        mult_input_F bits multBits x m (target_idx j) = Nat.testBit x j := by
      rw [mult_input_F_at_non_mult_pos bits multBits x m (target_idx j)
            (Or.inl h_target_in_adder)]
      -- adder_input_F (bits+1) 0 x (target_idx j) = x.testBit j.
      unfold adder_input_F target_idx
      have h_mod : (3 * j + 1) % 3 = 1 := by omega
      have h_div : (3 * j + 1) / 3 = j := by omega
      rw [h_mod, h_div]
      have h_decide : decide (j < bits + 1) = true := by
        apply decide_eq_true; omega
      rw [h_decide]
      simp
    rw [h_lhs_decode]
    -- RHS via mult_input_F_at_mult_pos.
    rw [mult_input_F_at_mult_pos bits multBits m x j hj]
  -- Case 2: q = target_idx j for some j < multBits (target-side swap).
  · by_cases h_target : ∃ j, j < multBits ∧ q = target_idx j
    · obtain ⟨j, hj, hq_eq⟩ := h_target
      rw [hq_eq]
      rw [mult_target_swap_aux_at_target bits multBits _ j hj h_multBits_le]
      -- LHS: mult_input_F bits multBits x m (adder_n_qubits + j) = Nat.testBit m j.
      -- RHS: mult_input_F bits multBits m x (target_idx j) = m.testBit j.
      rw [mult_input_F_at_mult_pos bits multBits x m j hj]
      -- Now RHS.
      have h_target_in_adder : target_idx j < adder_n_qubits (bits + 1) := by
        show 3 * j + 1 < 3 * (bits + 1) + 2
        omega
      rw [mult_input_F_at_non_mult_pos bits multBits m x (target_idx j)
            (Or.inl h_target_in_adder)]
      unfold adder_input_F target_idx
      have h_mod : (3 * j + 1) % 3 = 1 := by omega
      have h_div : (3 * j + 1) / 3 = j := by omega
      rw [h_mod, h_div]
      have h_decide : decide (j < bits + 1) = true := by
        apply decide_eq_true; omega
      rw [h_decide]
      simp
    -- Case 3: identity case (q not a swap position).
    · push_neg at h_mult h_target
      -- Apply at_other: the gate is identity at q.
      have h_outside : ∀ k, k < multBits →
          q ≠ adder_n_qubits (bits + 1) + k ∧ q ≠ target_idx k := by
        intro k hk
        refine ⟨?_, ?_⟩
        · exact h_mult k hk
        · exact h_target k hk
      rw [mult_target_swap_aux_at_other bits multBits _ q h_multBits_le h_outside]
      -- Now need: mult_input_F bits multBits x m q = mult_input_F bits multBits m x q.
      -- Case-split on q's relation to the multiplier range and adder block.
      by_cases h_in_mult_range : adder_n_qubits (bits + 1) ≤ q
                                ∧ q < adder_n_qubits (bits + 1) + multBits
      · -- q in multiplier range: contradicts h_mult (q = adder_n_qubits + j for some j).
        obtain ⟨h_q_lo, h_q_hi⟩ := h_in_mult_range
        exfalso
        apply h_mult (q - adder_n_qubits (bits + 1)) (by omega)
        omega
      · -- q outside multiplier range.
        have h_outside_range : q < adder_n_qubits (bits + 1)
                               ∨ adder_n_qubits (bits + 1) + multBits ≤ q := by
          by_cases h_lo : q < adder_n_qubits (bits + 1)
          · exact Or.inl h_lo
          · push_neg at h_lo
            exact Or.inr (by
              rcases Nat.lt_or_ge q (adder_n_qubits (bits + 1) + multBits) with h | h
              · exact absurd ⟨h_lo, h⟩ h_in_mult_range
              · exact h)
        rw [mult_input_F_at_non_mult_pos bits multBits x m q h_outside_range]
        rw [mult_input_F_at_non_mult_pos bits multBits m x q h_outside_range]
        -- adder_input_F (bits+1) 0 x q = adder_input_F (bits+1) 0 m q.
        -- Case-split on q's adder-block role (read/target/carry/oob).
        unfold adder_input_F
        rcases Nat.lt_or_ge q (3 * (bits + 1)) with h_in_adder | h_above_adder
        · -- q in adder positions [0, 3*(bits+1)). Case-split on q % 3.
          have h_div_lt : q / 3 < bits + 1 := by omega
          rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega)
            with h_mod | h_mod | h_mod
          · -- read position: both sides return 0.testBit (q/3) = false.
            rw [h_mod]
          · -- target position: returns x.testBit (q/3) vs m.testBit (q/3).
            have h_q_eq_target : q = target_idx (q / 3) := by
              unfold target_idx
              have : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
              omega
            have h_q_div_ge : q / 3 ≥ multBits := by
              by_contra h_lt
              push_neg at h_lt
              apply h_target (q / 3) h_lt
              exact h_q_eq_target
            have h_x_bit : x.testBit (q / 3) = false :=
              Nat.testBit_lt_two_pow (by
                calc x < 2^multBits := hx
                  _ ≤ 2^(q / 3) := Nat.pow_le_pow_right (by omega) h_q_div_ge)
            have h_m_bit : m.testBit (q / 3) = false :=
              Nat.testBit_lt_two_pow (by
                calc m < 2^multBits := hm
                  _ ≤ 2^(q / 3) := Nat.pow_le_pow_right (by omega) h_q_div_ge)
            rw [h_mod]
            simp [h_x_bit, h_m_bit]
          · -- carry position (q % 3 = 2): both sides return false.
            rw [h_mod]
        · -- q ≥ 3*(bits+1): adder_input_F returns false regardless.
          have h_div_ge : q / 3 ≥ bits + 1 := by omega
          have h_decide_false : decide (q / 3 < bits + 1) = false := by
            apply decide_eq_false; omega
          rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by omega)
            with h_mod | h_mod | h_mod
          · rw [h_mod, h_decide_false]
          · rw [h_mod, h_decide_false]; simp
          · rw [h_mod]

/-! ### Tick 19 — End-to-end in-place modular multiplier correctness. -/

/-- **HEADLINE: `modMultInPlace` is a correct in-place modular
multiplier.**  Applied to `mult_state_init bits multBits x` (multiplier
register holds `x`, adder zeroed), the gate produces `mult_input_F
bits multBits 0 ((a * x) % N)` — the multiplier register now holds the
result `a*x mod N` and the adder is zeroed.

Hypotheses:
- Structural: `1 ≤ bits`, `multBits ≤ bits + 1`, `N ≤ 2^multBits`.
- Modular: `0 < N`, `N ≤ 2^bits`, `0 < a < N`, `0 < ainv < N`,
  `a * ainv ≡ 1 (mod N)`.
- Input: `x < N`.
- Coprimality of each per-bit constant `(a * 2^j) % N` and
  `((N - ainv) % N * 2^j) % N` is non-zero, used by the
  `modMultConstGate_correct` invocations. -/
theorem modMultInPlace_correct
    (bits N a ainv multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (ha_pos : 0 < a) (ha_lt : a < N)
    (hainv_pos : 0 < ainv) (hainv_lt : ainv < N)
    (h_inv : a * ainv % N = 1)
    (hx_lt : x < N)
    (h_const_pos_a : ∀ j, j < multBits → 0 < (a * 2^j) % N)
    (h_const_pos_inv : ∀ j, j < multBits → 0 < ((N - ainv) % N * 2^j) % N) :
    Gate.applyNat (modMultInPlace bits N a ainv multBits)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits 0 ((a * x) % N) := by
  -- Derive x < 2^multBits from x < N ≤ 2^multBits.
  have hx_lt_pow : x < 2^multBits :=
    lt_of_lt_of_le hx_lt h_N_le_pow_multBits
  -- Unfold and apply Step 1: modMultConstGate(a) on mult_state_init x.
  unfold modMultInPlace
  rw [Gate.applyNat_seq]
  rw [modMultConstGate_on_init_correct bits N a multBits x
        hbits hN_pos hN hx_lt_pow h_const_pos_a]
  -- State after Step 1: mult_input_F bits multBits (a*x mod N) x.
  rw [Gate.applyNat_seq]
  -- Step 2: SWAP exchanges target and multiplier.  Need both values
  -- < 2^multBits.
  have h_ax_mod_N_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_mod_N_lt_pow : (a * x) % N < 2^multBits :=
    lt_of_lt_of_le h_ax_mod_N_lt_N h_N_le_pow_multBits
  rw [mult_target_swap_on_mult_input_F bits multBits ((a * x) % N) x
        h_multBits_le h_ax_mod_N_lt_pow hx_lt_pow]
  -- State after Step 2: mult_input_F bits multBits x (a*x mod N).
  -- Step 3: modMultConstGate((N - ainv) % N).
  rw [modMultConstGate_correct bits N ((N - ainv) % N) multBits x ((a * x) % N)
        hbits hN_pos hN hx_lt h_ax_mod_N_lt_pow h_const_pos_inv]
  -- Result: mult_input_F ((x + ((N - ainv) % N) * ((a*x) % N)) % N) ((a*x) % N).
  -- We need this to equal mult_input_F 0 ((a*x) % N).
  congr 1
  -- (N - ainv) % N = N - ainv (since 0 < N - ainv < N).
  rw [show (N - ainv) % N = N - ainv from Nat.mod_eq_of_lt (by omega)]
  -- Apply mod_inv_cancel_identity.
  exact mod_inv_cancel_identity a ainv N x hN_pos hx_lt hainv_lt h_inv

/-- Recursion unfolding for `reverse_register_swap_aux`. -/
theorem reverse_register_swap_aux_succ
    (n offsetA offsetB k : Nat) :
    reverse_register_swap_aux n offsetA offsetB (k + 1)
    = Gate.seq (reverse_register_swap_aux n offsetA offsetB k)
               (qubit_swap (offsetA + k) (offsetB + (n - 1 - k))) := rfl

/-- **WellTyped for `reverse_register_swap_aux`.**  Disjoint ranges
suffice. -/
theorem reverse_register_swap_aux_wellTyped
    (dim n offsetA offsetB k : Nat) (hdim : 0 < dim)
    (hA : offsetA + n ≤ dim) (hB : offsetB + n ≤ dim)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n) :
    Gate.WellTyped dim (reverse_register_swap_aux n offsetA offsetB k) := by
  induction k with
  | zero =>
      show 0 < dim
      exact hdim
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have h_ih := ih hk'
      have h_swap : Gate.WellTyped dim
          (qubit_swap (offsetA + k) (offsetB + (n - 1 - k))) := by
        apply qubit_swap_wellTyped
        · -- offsetA + k < dim
          omega
        · -- offsetB + (n - 1 - k) < dim
          have : n - 1 - k < n := by omega
          omega
        · -- offsetA + k ≠ offsetB + (n - 1 - k)
          rcases h_disjoint with h | h
          · -- offsetA + n ≤ offsetB: offsetA + k < offsetB ≤ offsetB + (n-1-k).
            have : offsetA + k < offsetB := by omega
            omega
          · -- offsetB + n ≤ offsetA: offsetB + (n-1-k) < offsetA ≤ offsetA + k.
            have : offsetB + (n - 1 - k) < offsetA := by omega
            omega
      show Gate.WellTyped dim
        (Gate.seq (reverse_register_swap_aux n offsetA offsetB k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `reverse_register_swap`.** -/
theorem reverse_register_swap_wellTyped
    (dim n offsetA offsetB : Nat) (hdim : 0 < dim)
    (hA : offsetA + n ≤ dim) (hB : offsetB + n ≤ dim)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.WellTyped dim (reverse_register_swap n offsetA offsetB) :=
  reverse_register_swap_aux_wellTyped dim n offsetA offsetB n hdim hA hB
    h_disjoint (le_refl _)

/-- **Correctness at "other" positions** of `reverse_register_swap_aux`.
At positions outside both `[offsetA, offsetA + k)` and `[offsetB +
n - k, offsetB + n)` (the touched range up to iteration `k`), the gate
is identity. -/
theorem reverse_register_swap_aux_at_other
    (n offsetA offsetB k : Nat) (f : Nat → Bool) (q : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n)
    (h_outside : ∀ i, i < k →
      q ≠ offsetA + i ∧ q ≠ offsetB + (n - 1 - i)) :
    Gate.applyNat (reverse_register_swap_aux n offsetA offsetB k) f q = f q := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have h_outside_k : ∀ i, i < k →
          q ≠ offsetA + i ∧ q ≠ offsetB + (n - 1 - i) := by
        intro i hi; exact h_outside i (by omega)
      have h_q_ne_Ak : q ≠ offsetA + k := (h_outside k (by omega)).1
      have h_q_ne_Bk : q ≠ offsetB + (n - 1 - k) := (h_outside k (by omega)).2
      have hAk_ne_Bk : offsetA + k ≠ offsetB + (n - 1 - k) := by
        rcases h_disjoint with h | h
        · -- offsetA + n ≤ offsetB
          have hk_lt : k < n := by omega
          omega
        · -- offsetB + n ≤ offsetA
          have hk_lt : k < n := by omega
          omega
      rw [reverse_register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih hk' h_outside_k

/-- **At A-side position**: at `offsetA + j` (j < k), the gate returns
`f (offsetB + (n - 1 - j))`.  The reversed-pairing semantics. -/
theorem reverse_register_swap_aux_at_A
    (n offsetA offsetB k : Nat) (f : Nat → Bool) (j : Nat) (hj : j < k)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n) :
    Gate.applyNat (reverse_register_swap_aux n offsetA offsetB k) f
      (offsetA + j)
    = f (offsetB + (n - 1 - j)) := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have hk_n : k ≤ n := by omega
      have hk_lt : k < n := by omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + (n - 1 - k) := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [reverse_register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ hAk_ne_Bk]
        rw [update_eq]
        apply reverse_register_swap_aux_at_other n offsetA offsetB k f
                (offsetB + (n - 1 - k)) h_disjoint hk_n
        intro i hi
        have hi_lt_n : i < n := by omega
        refine ⟨?_, ?_⟩
        · rcases h_disjoint with h | h
          · omega
          · omega
        · -- offsetB + (n - 1 - k) ≠ offsetB + (n - 1 - i), since i < k.
          have h_ne_idx : n - 1 - k ≠ n - 1 - i := by omega
          omega
      · have hj' : j < k := by omega
        have h_pos_Aj_ne_Bk : offsetA + j ≠ offsetB + (n - 1 - k) := by
          rcases h_disjoint with h | h
          · omega
          · omega
        have h_pos_Aj_ne_Ak : offsetA + j ≠ offsetA + k := by omega
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Ak]
        exact ih hj' hk_n

/-- **At B-side position (reversed)**: at `offsetB + (n - 1 - j)`
(j < k), the gate returns `f (offsetA + j)`.  The dual of `_at_A`. -/
theorem reverse_register_swap_aux_at_B
    (n offsetA offsetB k : Nat) (f : Nat → Bool) (j : Nat) (hj : j < k)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (hk : k ≤ n) :
    Gate.applyNat (reverse_register_swap_aux n offsetA offsetB k) f
      (offsetB + (n - 1 - j))
    = f (offsetA + j) := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have hk_n : k ≤ n := by omega
      have hk_lt : k < n := by omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + (n - 1 - k) := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [reverse_register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        apply reverse_register_swap_aux_at_other n offsetA offsetB k f
                (offsetA + k) h_disjoint hk_n
        intro i hi
        have hi_lt_n : i < n := by omega
        refine ⟨?_, ?_⟩
        · omega
        · rcases h_disjoint with h | h
          · omega
          · omega
      · have hj' : j < k := by omega
        have h_pos_B_ne_Bk : offsetB + (n - 1 - j)
                            ≠ offsetB + (n - 1 - k) := by
          have h_ne_idx : n - 1 - j ≠ n - 1 - k := by omega
          omega
        have h_pos_B_ne_Ak : offsetB + (n - 1 - j) ≠ offsetA + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        rw [update_neq _ _ _ _ h_pos_B_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_B_ne_Ak]
        exact ih hj' hk_n

end FormalRV.BQAlgo
