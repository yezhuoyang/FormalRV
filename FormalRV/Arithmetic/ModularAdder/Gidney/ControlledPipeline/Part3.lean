/- ControlledPipeline — Part3 (re-export shim part; same namespace, opens de-duplicated). -/
import FormalRV.Arithmetic.ModularAdder.Gidney.ControlledPipeline.Part2

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! #### Tick 7f — full multiplier correctness. -/

/-- **Bit decomposition for the next power of two.**
`m mod 2^(k+1) = m mod 2^k + (testBit m k as Nat) * 2^k`. -/
lemma m_mod_two_pow_succ_eq (m k : Nat) :
    m % 2^(k+1) = m % 2^k + (m / 2^k % 2) * 2^k := by
  have h_pow : 2^(k+1) = 2^k * 2 := by ring
  have h_pos : 0 < 2^k := Nat.two_pow_pos k
  have h_div_div : m / 2^(k+1) = m / 2^k / 2 := by
    rw [h_pow]; exact (Nat.div_div_eq_div_mul m (2^k) 2).symm
  have h1 : 2^k * (m / 2^k) + m % 2^k = m := Nat.div_add_mod m (2^k)
  have h2 : 2^(k+1) * (m / 2^(k+1)) + m % 2^(k+1) = m := Nat.div_add_mod m (2^(k+1))
  have h3 : 2 * (m / 2^k / 2) + m / 2^k % 2 = m / 2^k := Nat.div_add_mod (m / 2^k) 2
  have h2' : 2^k * 2 * (m / 2^k / 2) + m % 2^(k+1) = m := by
    rw [← h_pow, ← h_div_div]; exact h2
  nlinarith [h1, h2', h3, h_pos]

/-- **Inductive correctness for `modMultConstGateAux`.**  At iteration
`k ≤ multBits`, the aux gate has advanced the adder's target from `x`
to `(x + a * (m mod 2^k)) mod N`, given that each per-bit constant
`(a * 2^j) % N` is non-zero for `j < multBits`. -/
theorem modMultConstGateAux_correct
    (bits N a multBits x m : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    ∀ k, k ≤ multBits →
    Gate.applyNat (modMultConstGateAux bits N a multBits k)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits ((x + a * (m % 2^k)) % N) m := by
  intro k hk
  induction k with
  | zero =>
      show Gate.applyNat Gate.I _ = _
      rw [Gate.applyNat_I]
      have h_mod : m % 2^0 = 0 := by rw [pow_zero]; exact Nat.mod_one m
      rw [h_mod, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hx]
  | succ k ih =>
      have hk' : k ≤ multBits := by omega
      have ih' := ih hk'
      rw [modMultConstGateAux_apply_succ, ih']
      have h_step_c_pos : 0 < (a * 2^k) % N := h_const_pos k (by omega)
      have h_step_c_lt : (a * 2^k) % N < N := Nat.mod_lt _ hN_pos
      have h_T_k_lt_N : (x + a * (m % 2^k)) % N < N := Nat.mod_lt _ hN_pos
      have hk_lt : k < multBits := by omega
      rw [controlledModAddConstGate_on_mult_input_F bits N ((a * 2^k) % N)
            ((x + a * (m % 2^k)) % N) m multBits k
            hbits hN_pos hN h_T_k_lt_N h_step_c_pos h_step_c_lt hk_lt]
      congr 1
      have h_decomp : m % 2^(k+1) = m % 2^k + (m / 2^k % 2) * 2^k :=
        m_mod_two_pow_succ_eq m k
      cases h_bit : Nat.testBit m k with
      | true =>
          have h_tb : (m / 2^k) % 2 = 1 := by
            rw [Nat.testBit_eq_decide_div_mod_eq] at h_bit
            exact of_decide_eq_true h_bit
          simp only [if_true]
          rw [h_decomp, h_tb, Nat.one_mul, Nat.mul_add]
          rw [show x + (a * (m % 2 ^ k) + a * 2 ^ k)
                = (x + a * (m % 2 ^ k)) + a * 2 ^ k from by ring]
          rw [← Nat.add_mod]
      | false =>
          have h_tb : (m / 2^k) % 2 = 0 := by
            rw [Nat.testBit_eq_decide_div_mod_eq] at h_bit
            have h := of_decide_eq_false h_bit
            omega
          rw [if_neg (by decide : ¬((false : Bool) = true))]
          rw [h_decomp, h_tb, Nat.zero_mul, Nat.add_zero]

/-- **Modular multiplier correctness.**  When `m < 2^multBits`, the
modular multiplier gate sends the adder's target from `x` to
`(x + a * m) mod N`, while preserving the multiplier register `m` and
the flag.  Equivalent form: each multiplier-bit `i` contributes
`(a * 2^i) mod N` to the target when set. -/
theorem modMultConstGate_correct
    (bits N a multBits x m : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < N)
    (hm : m < 2^multBits)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    Gate.applyNat (modMultConstGate bits N a multBits)
                  (mult_input_F bits multBits x m)
    = mult_input_F bits multBits ((x + a * m) % N) m := by
  unfold modMultConstGate
  rw [modMultConstGateAux_correct bits N a multBits x m
        hbits hN_pos hN hx h_const_pos multBits (le_refl _)]
  rw [Nat.mod_eq_of_lt hm]

/-- Decoder at multiplier-bit positions. -/
theorem mult_state_init_at_mult_pos
    (bits multBits x j : Nat) (hj : j < multBits) :
    mult_state_init bits multBits x (adder_n_qubits (bits + 1) + j)
    = Nat.testBit x j := by
  unfold mult_state_init
  exact mult_input_F_at_mult_pos bits multBits 0 x j hj

/-- Decoder at non-multiplier positions: zero. -/
theorem mult_state_init_at_non_mult_pos
    (bits multBits x p : Nat)
    (h_outside : p < adder_n_qubits (bits + 1)
                 ∨ adder_n_qubits (bits + 1) + multBits ≤ p) :
    mult_state_init bits multBits x p = adder_input_F (bits + 1) 0 0 p := by
  unfold mult_state_init
  exact mult_input_F_at_non_mult_pos bits multBits 0 x p h_outside

/-- **Modular multiplier on the initial input state.**  When applied to
`mult_state_init bits multBits x` (multiplier register holds `x`,
adder zeroed), the gate produces a state whose adder-target register
encodes `(a * x) mod N` while the multiplier register `x` is
preserved.  Hypotheses ensure each per-bit constant `(a * 2^j) % N`
is positive (Shor's coprimality condition) and `x < 2^multBits`. -/
theorem modMultConstGate_on_init_correct
    (bits N a multBits x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < 2^multBits)
    (h_const_pos : ∀ j, j < multBits → 0 < (a * 2^j) % N) :
    Gate.applyNat (modMultConstGate bits N a multBits)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits ((a * x) % N) x := by
  unfold mult_state_init
  have h_0_lt_N : 0 < N := hN_pos
  rw [modMultConstGate_correct bits N a multBits 0 x
        hbits hN_pos hN (by omega) hx h_const_pos]
  congr 1
  rw [Nat.zero_add]

/-- **WellTyped corollary at the Shor-compatible dimension.**  Setting
`n := multBits` (the data register size) and `anc := adder_n_qubits
(bits+1) + 1` (the workspace including the flag), the modular
multiplier gate is well-typed at dimension `n + anc`, matching the
shape required by `encodeDataZeroAnc n anc` and
`MultiplyCircuitProperty a N n anc`. -/
theorem modMultConstGate_wellTyped_at_shor_dim
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (modMultConstGate bits N a multBits) := by
  have h := modMultConstGate_wellTyped bits N a multBits hbits
  -- adder_n_qubits (bits+1) + multBits + 1 = multBits + (adder_n_qubits (bits+1) + 1)
  have h_eq : adder_n_qubits (bits + 1) + multBits + 1
             = multBits + (adder_n_qubits (bits + 1) + 1) := by ring
  rw [← h_eq]
  exact h

/-- **WellTyped** for the step gate at the Shor-compatible dimension. -/
theorem f_modmult_step_gate_wellTyped
    (bits N a multBits i : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
      (f_modmult_step_gate bits N a multBits i) := by
  unfold f_modmult_step_gate
  exact modMultConstGate_wellTyped_at_shor_dim bits N (a^(2^i) % N) multBits hbits

/-- **WellTyped** at the original aux dimension. -/
theorem f_modmult_step_gate_wellTyped_aux
    (bits N a multBits i : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (adder_n_qubits (bits + 1) + multBits + 1)
      (f_modmult_step_gate bits N a multBits i) := by
  unfold f_modmult_step_gate
  exact modMultConstGate_wellTyped bits N (a^(2^i) % N) multBits hbits

/-- **Step correctness on the initial state.**  Applied to
`mult_state_init bits multBits x`, the step gate at iterate `i`
produces a state whose adder-target register holds `(a^(2^i) * x) % N`
while the multiplier register `x` is preserved.  Hypotheses ensure
each per-bit constant `((a^(2^i)) * 2^j) % N` is positive (the
analogue of Shor's coprimality condition for the squared base). -/
theorem f_modmult_step_gate_on_init_correct
    (bits N a multBits i x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (hx : x < 2^multBits)
    (h_const_pos :
      ∀ j, j < multBits → 0 < ((a^(2^i) % N) * 2^j) % N) :
    Gate.applyNat (f_modmult_step_gate bits N a multBits i)
                  (mult_state_init bits multBits x)
    = mult_input_F bits multBits ((a^(2^i) * x) % N) x := by
  unfold f_modmult_step_gate
  rw [modMultConstGate_on_init_correct bits N (a^(2^i) % N) multBits x
        hbits hN_pos hN hx h_const_pos]
  -- Goal: mult_input_F bits multBits ((a^(2^i) % N) * x % N) x
  --     = mult_input_F bits multBits ((a^(2^i) * x) % N) x
  congr 1
  -- ((a^(2^i) % N) * x) % N = (a^(2^i) * x) % N
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- **Family-level WellTyped.**  For every iterate `i`, the gate
`f_modmult_gate_family bits N a multBits i` is `Gate.WellTyped` at
the Shor-compatible dimension `n + anc = multBits +
(adder_n_qubits (bits+1) + 1)`. -/
theorem f_modmult_gate_family_wellTyped
    (bits N a multBits : Nat) (hbits : 1 ≤ bits) :
    ∀ i, Gate.WellTyped (multBits + (adder_n_qubits (bits + 1) + 1))
            (f_modmult_gate_family bits N a multBits i) := by
  intro i
  unfold f_modmult_gate_family
  exact f_modmult_step_gate_wellTyped bits N a multBits i hbits

/-- **Family-level out-of-place correctness on the initial state.**
For each iterate `i`, applied to `mult_state_init bits multBits x`,
the family member produces a state with adder-target register holding
`(a^(2^i) * x) mod N` and multiplier register `x` preserved. -/
theorem f_modmult_gate_family_on_init_correct
    (bits N a multBits : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_const_pos :
      ∀ i, ∀ j, j < multBits → 0 < ((a^(2^i) % N) * 2^j) % N) :
    ∀ i x, x < 2^multBits →
      Gate.applyNat (f_modmult_gate_family bits N a multBits i)
                    (mult_state_init bits multBits x)
      = mult_input_F bits multBits ((a^(2^i) * x) % N) x := by
  intro i x hx
  unfold f_modmult_gate_family
  exact f_modmult_step_gate_on_init_correct bits N a multBits i x
          hbits hN_pos hN hx (h_const_pos i)

/-- Well-typedness for `qubit_swap`. -/
theorem qubit_swap_wellTyped (dim a b : Nat)
    (ha : a < dim) (hb : b < dim) (hab : a ≠ b) :
    Gate.WellTyped dim (qubit_swap a b) := by
  refine ⟨⟨ha, hb, hab⟩, ⟨hb, ha, ?_⟩, ⟨ha, hb, hab⟩⟩
  exact fun h => hab h.symm

/-- **Boolean-state correctness for SWAP.**  Applied to `f`, the swap
gate produces a state with values at positions `a` and `b` exchanged. -/
theorem qubit_swap_correct (a b : Nat) (f : Nat → Bool) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) f
    = update (update f a (f b)) b (f a) := by
  unfold qubit_swap
  simp only [Gate.applyNat_seq, Gate.applyNat_CX]
  -- After unfolding, LHS is three nested updates with CX semantics:
  --   update (update (update f b (f b ⊕ f a)) a (...)) b (...)
  -- Evaluate the intermediate values that the inner CXs read.
  have hba : b ≠ a := Ne.symm hab
  -- After 1st CX(a,b): at position a still f a, at position b is f b ⊕ f a.
  have h_g1_a : update f b (xor (f b) (f a)) a = f a := update_neq _ _ _ _ hab
  have h_g1_b : update f b (xor (f b) (f a)) b = xor (f b) (f a) := update_eq _ _ _
  rw [h_g1_a, h_g1_b]
  -- After 2nd CX(b,a): writes (f a) ⊕ (f b ⊕ f a) = f b at position a.
  -- After 3rd CX(a,b): writes (intermediate at b) ⊕ (intermediate at a) at position b.
  have h_g2_a : update (update f b (xor (f b) (f a))) a (xor (f a) (xor (f b) (f a))) a
                = xor (f a) (xor (f b) (f a)) := update_eq _ _ _
  have h_g2_b : update (update f b (xor (f b) (f a))) a (xor (f a) (xor (f b) (f a))) b
                = xor (f b) (f a) := by
    rw [update_neq _ _ _ _ hba]; exact update_eq _ _ _
  rw [h_g2_b, h_g2_a]
  -- Now the LHS is fully expanded. Funext + case split on the queried position.
  funext q
  by_cases hqa : q = a
  · -- q = a: outer update at b (different), middle update at a (returns the xor expression).
    rw [hqa]
    rw [update_neq _ _ _ _ hab]
    rw [update_eq]
    -- RHS at a: update (update f a (f b)) b (f a) a = (update f a (f b)) a = f b.
    rw [update_neq _ _ _ _ hab]
    rw [update_eq]
    -- Goal: f a ⊕ (f b ⊕ f a) = f b. Boolean fact.
    cases h_fa : f a <;> cases h_fb : f b <;> rfl
  · by_cases hqb : q = b
    · -- q = b: outer update at b returns the xor expression.
      rw [hqb]
      rw [update_eq]
      -- RHS at b: f a.
      rw [update_eq]
      -- Goal: (f b ⊕ f a) ⊕ (f a ⊕ (f b ⊕ f a)) = f a. Boolean fact.
      cases h_fa : f a <;> cases h_fb : f b <;> rfl
    · -- q ≠ a, q ≠ b: all updates skip, both sides equal f q.
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqa]
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqb]
      rw [update_neq _ _ _ _ hqa]

/-- Recursion unfolding for `register_swap_aux`. -/
theorem register_swap_aux_succ
    (offsetA offsetB k : Nat) :
    register_swap_aux offsetA offsetB (k + 1)
    = Gate.seq (register_swap_aux offsetA offsetB k)
               (qubit_swap (offsetA + k) (offsetB + k)) := rfl

/-- **WellTyped for `register_swap_aux`.**  Requires non-empty
`dim`, both offset ranges fitting inside `dim`, and the two ranges
being disjoint. -/
theorem register_swap_aux_wellTyped
    (dim offsetA offsetB k : Nat) (hdim : 0 < dim)
    (hA : offsetA + k ≤ dim) (hB : offsetB + k ≤ dim)
    (h_disjoint : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA) :
    Gate.WellTyped dim (register_swap_aux offsetA offsetB k) := by
  induction k with
  | zero =>
      show 0 < dim
      exact hdim
  | succ k ih =>
      have hA' : offsetA + k ≤ dim := by omega
      have hB' : offsetB + k ≤ dim := by omega
      have h_disjoint' :
          offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have h_ih := ih hA' hB' h_disjoint'
      have h_swap : Gate.WellTyped dim
          (qubit_swap (offsetA + k) (offsetB + k)) := by
        have hAk : offsetA + k < dim := by omega
        have hBk : offsetB + k < dim := by omega
        have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        exact qubit_swap_wellTyped dim (offsetA + k) (offsetB + k) hAk hBk hAk_ne_Bk
      show Gate.WellTyped dim
        (Gate.seq (register_swap_aux offsetA offsetB k) _)
      exact ⟨h_ih, h_swap⟩

/-- **WellTyped for `register_swap`.** -/
theorem register_swap_wellTyped
    (dim multBits offsetA offsetB : Nat) (hdim : 0 < dim)
    (hA : offsetA + multBits ≤ dim) (hB : offsetB + multBits ≤ dim)
    (h_disjoint : offsetA + multBits ≤ offsetB ∨ offsetB + multBits ≤ offsetA) :
    Gate.WellTyped dim (register_swap multBits offsetA offsetB) :=
  register_swap_aux_wellTyped dim offsetA offsetB multBits hdim hA hB h_disjoint

/-- **Correctness at "other" positions** of `register_swap_aux`.  At
any position outside both `[offsetA, offsetA + n)` and `[offsetB,
offsetB + n)`, the gate is identity. -/
theorem register_swap_aux_at_other
    (offsetA offsetB n : Nat) (f : Nat → Bool) (q : Nat)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA)
    (h_outside_A : q < offsetA ∨ offsetA + n ≤ q)
    (h_outside_B : q < offsetB ∨ offsetB + n ≤ q) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f q = f q := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have h_outside_A' : q < offsetA ∨ offsetA + k ≤ q := by
        rcases h_outside_A with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_outside_B' : q < offsetB ∨ offsetB + k ≤ q := by
        rcases h_outside_B with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have h_q_ne_Ak : q ≠ offsetA + k := by
        rcases h_outside_A with h | h
        · omega
        · omega
      have h_q_ne_Bk : q ≠ offsetB + k := by
        rcases h_outside_B with h | h
        · omega
        · omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Bk]
      rw [update_neq _ _ _ _ h_q_ne_Ak]
      exact ih h_disjoint_k h_outside_A' h_outside_B'

/-- **Correctness at A positions**: at `offsetA + j` for `j < n`, the
gate returns `f (offsetB + j)`. -/
theorem register_swap_aux_at_A
    (offsetA offsetB n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f (offsetA + j)
    = f (offsetB + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_neq _ _ _ _ (by omega : offsetA + k ≠ offsetB + k)]
        rw [update_eq]
        have h_outside_A_q : offsetB + k < offsetA ∨ offsetA + k ≤ offsetB + k := by
          rcases h_disjoint with h | h
          · right; omega
          · left; omega
        have h_outside_B_q : offsetB + k < offsetB ∨ offsetB + k ≤ offsetB + k := by
          right; omega
        exact register_swap_aux_at_other offsetA offsetB k f (offsetB + k)
                h_disjoint_k h_outside_A_q h_outside_B_q
      · have hj' : j < k := by omega
        have h_pos_A_ne_Bk : offsetA + j ≠ offsetB + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        have h_pos_A_ne_Ak : offsetA + j ≠ offsetA + k := by omega
        rw [update_neq _ _ _ _ h_pos_A_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_A_ne_Ak]
        exact ih hj' h_disjoint_k

/-- **Correctness at B positions**: at `offsetB + j` for `j < n`, the
gate returns `f (offsetA + j)`. -/
theorem register_swap_aux_at_B
    (offsetA offsetB n : Nat) (f : Nat → Bool) (j : Nat) (hj : j < n)
    (h_disjoint : offsetA + n ≤ offsetB ∨ offsetB + n ≤ offsetA) :
    Gate.applyNat (register_swap_aux offsetA offsetB n) f (offsetB + j)
    = f (offsetA + j) := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      have h_disjoint_k : offsetA + k ≤ offsetB ∨ offsetB + k ≤ offsetA := by
        rcases h_disjoint with h | h
        · left; omega
        · right; omega
      have hAk_ne_Bk : offsetA + k ≠ offsetB + k := by
        rcases h_disjoint with h | h
        · omega
        · omega
      rw [register_swap_aux_succ]
      rw [Gate.applyNat_seq]
      rw [qubit_swap_correct _ _ _ hAk_ne_Bk]
      by_cases hjk : j = k
      · rw [hjk]
        rw [update_eq]
        have h_outside_A_q : offsetA + k < offsetA ∨ offsetA + k ≤ offsetA + k := by
          right; omega
        have h_outside_B_q : offsetA + k < offsetB ∨ offsetB + k ≤ offsetA + k := by
          rcases h_disjoint with h | h
          · left; omega
          · right; omega
        exact register_swap_aux_at_other offsetA offsetB k f (offsetA + k)
                h_disjoint_k h_outside_A_q h_outside_B_q
      · have hj' : j < k := by omega
        have h_pos_B_ne_Bk : offsetB + j ≠ offsetB + k := by omega
        have h_pos_B_ne_Ak : offsetB + j ≠ offsetA + k := by
          rcases h_disjoint with h | h
          · omega
          · omega
        rw [update_neq _ _ _ _ h_pos_B_ne_Bk]
        rw [update_neq _ _ _ _ h_pos_B_ne_Ak]
        exact ih hj' h_disjoint_k


end FormalRV.BQAlgo
