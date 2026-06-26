/- ControlledPipeline — Part4 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline.Part3

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ### Tick 15 — Modular-inverse algebraic identities.

Two arithmetic facts about modular inverses that justify the third
stage of the in-place wrapper `OOPmul(a) ; SWAP ; OOPmul(N - a⁻¹)`:

(1) `ainv * (a*x mod N) mod N = x` — the modular inverse undoes the
    forward multiplication when `x < N` and `a * ainv ≡ 1 (mod N)`.

(2) `(x + (N - ainv) * (a*x mod N)) mod N = 0` — adding `(N - ainv) *
    (a*x mod N)` to `x` modular-cancels (where `N - ainv` plays the
    role of the additive inverse of `ainv` mod `N`).

Both are purely Nat arithmetic. -/

/-- **Modular-inverse "undo" identity.**  If `a * ainv ≡ 1 (mod N)`,
`x < N`, and `ainv < N`, then `ainv * (a*x mod N) mod N = x`. -/
theorem inv_mul_mod_eq_self (a ainv N x : Nat) (hN : 0 < N)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    ainv * (a * x % N) % N = x := by
  -- Step 1: pull the inner `% N` out via Nat.mul_mod.
  have step : ainv * (a * x % N) % N = ainv * (a * x) % N := by
    conv_rhs => rw [Nat.mul_mod ainv (a * x) N]
    conv_lhs => rw [Nat.mul_mod ainv (a * x % N) N]
    rw [Nat.mod_mod]
  rw [step]
  -- Step 2: regroup and apply h_inv.
  rw [show ainv * (a * x) = (ainv * a) * x from by ring]
  rw [Nat.mul_mod (ainv * a) x N]
  rw [show ainv * a = a * ainv from Nat.mul_comm _ _]
  rw [h_inv, Nat.one_mul, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hx

/-- **Modular cancellation by the additive-inverse-mod-N coefficient.**
If `a * ainv ≡ 1 (mod N)`, `x < N`, `ainv < N`, then
`(x + (N - ainv) * (a*x mod N)) mod N = 0`.  This is the algebraic
identity that justifies the third stage of the in-place modular
multiplier wrapper. -/
theorem mod_inv_cancel_identity (a ainv N x : Nat) (hN : 0 < N)
    (hx : x < N) (hainv : ainv < N) (h_inv : a * ainv % N = 1) :
    (x + (N - ainv) * (a * x % N)) % N = 0 := by
  have h1 := inv_mul_mod_eq_self a ainv N x hN hx hainv h_inv
  have hainv_le : ainv ≤ N := Nat.le_of_lt hainv
  set y := a * x % N with hy_def
  have h_sub : (N - ainv) * y = N * y - ainv * y := by rw [Nat.sub_mul]
  rw [h_sub]
  have h_le : ainv * y ≤ N * y := Nat.mul_le_mul_right _ hainv_le
  have h_add_sub : x + (N * y - ainv * y) = (x + N * y) - ainv * y := by omega
  rw [h_add_sub]
  -- ainv * y = N * (ainv * y / N) + (ainv * y % N) = N * (ainv * y / N) + x  (by h1)
  have h_ainv_y_decomp : ainv * y = N * (ainv * y / N) + x := by
    have := Nat.div_add_mod (ainv * y) N
    rw [h1] at this
    omega
  rw [h_ainv_y_decomp]
  have h_div_le : ainv * y / N ≤ y := by
    have h := Nat.div_le_div_right (c := N) h_le
    rw [Nat.mul_div_cancel_left _ hN] at h
    exact h
  have h_y_ge : N * (ainv * y / N) ≤ N * y := Nat.mul_le_mul_left N h_div_le
  -- (x + N*y - (N * (ainv*y / N) + x)) = N * y - N * (ainv*y / N) = N * (y - ainv*y/N).
  have h_collapse :
      (x + N * y - (N * (ainv * y / N) + x)) % N
      = (N * (y - ainv * y / N)) % N := by
    congr 1
    rw [Nat.mul_sub]
    omega
  rw [h_collapse]
  exact Nat.mul_mod_right _ _

/-- Recursion unfolding for `mult_target_swap_aux`. -/
theorem mult_target_swap_aux_succ (bits k : Nat) :
    mult_target_swap_aux bits (k + 1)
    = Gate.seq (mult_target_swap_aux bits k)
               (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k)) := rfl

/-- **WellTyped for `mult_target_swap_aux`.**  At dimension
`adder_n_qubits (bits + 1) + multBits + 1` (Shor-compatible), each
constituent `qubit_swap (adder_n_qubits + k) (target_idx k)` is
well-typed when `k ≤ multBits ≤ bits + 1`. -/
theorem mult_target_swap_aux_wellTyped
    (bits multBits k : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) (hk : k ≤ multBits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (mult_target_swap_aux bits k) := by
  induction k with
  | zero =>
      show 0 < adder_n_qubits (bits + 1) + multBits + 1
      unfold adder_n_qubits
      omega
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have h_ih := ih hk'
      have hk_lt_multBits : k < multBits := by omega
      have h_swap : Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
          (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k)) := by
        apply qubit_swap_wellTyped
        · -- adder_n_qubits + k < dim = adder_n_qubits + multBits + 1
          omega
        · -- target_idx k = 3*k + 1 < dim.  k ≤ multBits ≤ bits + 1, so
          -- 3*k + 1 ≤ 3*(bits + 1) + 1 < 3*(bits + 1) + 2 = adder_n_qubits.
          unfold target_idx adder_n_qubits
          omega
        · -- adder_n_qubits + k ≠ target_idx k:  RHS ≤ 3*bits + 1 < adder_n_qubits + 0 ≤ LHS.
          unfold target_idx adder_n_qubits
          omega
      show Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
        (Gate.seq (mult_target_swap_aux bits k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `mult_target_swap`.** -/
theorem mult_target_swap_wellTyped
    (bits multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (mult_target_swap bits multBits) :=
  mult_target_swap_aux_wellTyped bits multBits multBits hbits h_multBits_le
    (le_refl _)

/-- **WellTyped for `modMultInPlace`.** -/
theorem modMultInPlace_wellTyped
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (modMultInPlace bits N a ainv multBits) := by
  unfold modMultInPlace
  refine ⟨?_, ?_, ?_⟩
  · exact modMultConstGate_wellTyped bits N a multBits hbits
  · exact mult_target_swap_wellTyped bits multBits hbits h_multBits_le
  · exact modMultConstGate_wellTyped bits N ((N - ainv) % N) multBits hbits

/-- **In-place WellTyped at the Shor-compatible dimension.** -/
theorem modMultInPlace_wellTyped_at_shor_dim
    (bits N a ainv multBits : Nat) (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultInPlace bits N a ainv multBits) := by
  have h := modMultInPlace_wellTyped bits N a ainv multBits hbits h_multBits_le
  have h_eq : adder_n_qubits (bits + 1) + multBits + 1
             = multBits + (adder_n_qubits (bits + 1) + 1) := by ring
  rw [← h_eq]
  exact h

/-! ### Tick 17 — Position-level correctness for `mult_target_swap_aux`. -/

/-- **At-other for `mult_target_swap_aux`.**  If `q` is not equal to
any swap-paired position (multiplier-side or target-side) up to
iteration `n`, then the gate is identity at `q`.  Requires
`n ≤ bits + 1` to ensure each swap-pair has distinct positions. -/
theorem mult_target_swap_aux_at_other
    (bits n : Nat) (f : Nat → Bool) (q : Nat)
    (h_n_le : n ≤ bits + 1)
    (h_outside : ∀ k, k < n →
      q ≠ adder_n_qubits (bits + 1) + k ∧ q ≠ target_idx k) :
    Gate.applyNat (mult_target_swap_aux bits n) f q = f q := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have h_outside_k : ∀ j, j < k →
          q ≠ adder_n_qubits (bits + 1) + j ∧ q ≠ target_idx j := by
        intro j hj; exact h_outside j (by omega)
      have h_q_ne_Ak : q ≠ adder_n_qubits (bits + 1) + k :=
        (h_outside k (by omega)).1
      have h_q_ne_Tk : q ≠ target_idx k :=
        (h_outside k (by omega)).2
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      rw [update_neq _ _ _ _ h_q_ne_Tk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih h_n_le' h_outside_k

/-- **At multiplier-side position**: at `adder_n_qubits + j` for
`j < n`, the gate returns `f (target_idx j)`.  Requires
`n ≤ bits + 1`. -/
theorem mult_target_swap_aux_at_mult
    (bits n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_n_le : n ≤ bits + 1) :
    Gate.applyNat (mult_target_swap_aux bits n) f
      (adder_n_qubits (bits + 1) + j)
    = f (target_idx j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ h_Ak_ne_Tk]
        rw [update_eq]
        apply mult_target_swap_aux_at_other bits k f (target_idx k) h_n_le'
        intro k' hk'
        have hk'_le_bits : k' ≤ bits := by omega
        refine ⟨?_, ?_⟩
        · show target_idx k ≠ adder_n_qubits (bits + 1) + k'
          show 3 * k + 1 ≠ 3 * (bits + 1) + 2 + k'
          omega
        · show target_idx k ≠ target_idx k'
          show 3 * k + 1 ≠ 3 * k' + 1
          omega
      · have hj' : j < k := by omega
        have hj_le_bits : j ≤ bits := by omega
        have h_pos_Aj_ne_Tk : adder_n_qubits (bits + 1) + j ≠ target_idx k := by
          show 3 * (bits + 1) + 2 + j ≠ 3 * k + 1
          omega
        have h_pos_Aj_ne_Ak : adder_n_qubits (bits + 1) + j
                             ≠ adder_n_qubits (bits + 1) + k := by omega
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Tk]
        rw [update_neq _ _ _ _ h_pos_Aj_ne_Ak]
        exact ih hj' h_n_le'

/-- **At target-side position**: at `target_idx j` for `j < n`, the
gate returns `f (adder_n_qubits + j)`.  Requires `n ≤ bits + 1`. -/
theorem mult_target_swap_aux_at_target
    (bits n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_n_le : n ≤ bits + 1) :
    Gate.applyNat (mult_target_swap_aux bits n) f (target_idx j)
    = f (adder_n_qubits (bits + 1) + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_n_le' : k ≤ bits + 1 := by omega
      have hk_le_bits : k ≤ bits := by omega
      have h_Ak_ne_Tk : adder_n_qubits (bits + 1) + k ≠ target_idx k := by
        show 3 * (bits + 1) + 2 + k ≠ 3 * k + 1
        omega
      rw [mult_target_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ h_Ak_ne_Tk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        apply mult_target_swap_aux_at_other bits k f
          (adder_n_qubits (bits + 1) + k) h_n_le'
        intro k' hk'
        have hk'_le_bits : k' ≤ bits := by omega
        refine ⟨?_, ?_⟩
        · show adder_n_qubits (bits + 1) + k ≠ adder_n_qubits (bits + 1) + k'
          omega
        · show adder_n_qubits (bits + 1) + k ≠ target_idx k'
          show 3 * (bits + 1) + 2 + k ≠ 3 * k' + 1
          omega
      · have hj' : j < k := by omega
        have hj_le_bits : j ≤ bits := by omega
        have h_pos_Tj_ne_Tk : target_idx j ≠ target_idx k := by
          show 3 * j + 1 ≠ 3 * k + 1
          omega
        have h_pos_Tj_ne_Ak : target_idx j ≠ adder_n_qubits (bits + 1) + k := by
          show 3 * j + 1 ≠ 3 * (bits + 1) + 2 + k
          omega
        rw [update_neq _ _ _ _ h_pos_Tj_ne_Tk]
        rw [update_neq _ _ _ _ h_pos_Tj_ne_Ak]
        exact ih hj' h_n_le'


end FormalRV.BQAlgo
