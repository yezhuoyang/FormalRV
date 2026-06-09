/-
  FormalRV.Arithmetic.ModExp.ModExpCorrectness
  Semantic correctness of the modexp oracle family: it is a `ModMulImpl` (every
  iterate multiplies by a^(2^i) mod N), and the resulting Shor success-probability
  bound. HEADLINE: `our_modmult_family_ModMulImpl`, `Shor_correct_with_verified_modexp`.
-/
import FormalRV.Arithmetic.ModExp.ModExpDef

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.SQIRPort

/-- **`MultiplyCircuitProperty` is invariant under modular reduction
of the multiplier**.  Since the MCP property mentions `a` only inside
`(a * x) % N`, reducing `a` modulo `N` doesn't change the property. -/
theorem MultiplyCircuitProperty_mod_invariance
    (a N n anc : Nat) (c : FormalRV.SQIRPort.BaseUCom (n + anc))
    (h : FormalRV.SQIRPort.MultiplyCircuitProperty (a % N) N n anc c) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N n anc c := by
  intro x hx
  have h_x_mod : x % N = x := Nat.mod_eq_of_lt hx
  have h_mod_eq : a * x % N = a % N * x % N := by
    rw [Nat.mul_mod a x N, h_x_mod]
  rw [h_mod_eq]
  exact h x hx


/-- **`our_modmult_family` satisfies `MultiplyCircuitProperty` at every
iterate.**  Combined with the WellTyped from Tick 26, this is the
`ModMulImpl` evidence required by `Shor_correct_var`. -/
theorem our_modmult_family_mcp_per_iterate
    (bits N a ainv multBits : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (h_inv_pow : ∀ i, (a^(2^i) % N) * (ainv^(2^i) % N) % N = 1)
    (h_pow_a_pos : ∀ i, 0 < a^(2^i) % N)
    (h_pow_ainv_pos : ∀ i, 0 < ainv^(2^i) % N)
    (h_const_pos_a_iter : ∀ i j, j < multBits → 0 < (a^(2^i) % N * 2^j) % N)
    (h_const_pos_inv_iter :
      ∀ i j, j < multBits → 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N) :
    ∀ i, FormalRV.SQIRPort.MultiplyCircuitProperty (a^(2^i)) N multBits
            (adder_n_qubits (bits + 1) + 1)
            (our_modmult_family bits N a ainv multBits i) := by
  intro i
  apply MultiplyCircuitProperty_mod_invariance
  unfold our_modmult_family
  exact modMultInPlaceShor_MultiplyCircuitProperty
    bits N (a^(2^i) % N) (ainv^(2^i) % N) multBits
    hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
    (h_pow_a_pos i) (Nat.mod_lt _ hN_pos)
    (h_pow_ainv_pos i) (Nat.mod_lt _ hN_pos)
    (h_inv_pow i)
    (h_const_pos_a_iter i)
    (h_const_pos_inv_iter i)


/-- **`our_modmult_family` is a `ModMulImpl`.**  Direct reformulation
of `our_modmult_family_mcp_per_iterate`. -/
theorem our_modmult_family_ModMulImpl
    (bits N a ainv multBits : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (h_inv_pow : ∀ i, (a^(2^i) % N) * (ainv^(2^i) % N) % N = 1)
    (h_pow_a_pos : ∀ i, 0 < a^(2^i) % N)
    (h_pow_ainv_pos : ∀ i, 0 < ainv^(2^i) % N)
    (h_const_pos_a_iter : ∀ i j, j < multBits → 0 < (a^(2^i) % N * 2^j) % N)
    (h_const_pos_inv_iter :
      ∀ i j, j < multBits → 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N) :
    FormalRV.SQIRPort.ModMulImpl a N multBits (adder_n_qubits (bits + 1) + 1)
      (our_modmult_family bits N a ainv multBits) :=
  our_modmult_family_mcp_per_iterate bits N a ainv multBits
    hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
    h_inv_pow h_pow_a_pos h_pow_ainv_pos
    h_const_pos_a_iter h_const_pos_inv_iter


/-- **HEADLINE: Shor's success-probability bound for our concrete
in-place modular multiplier family.**  Direct application of
`Shor_correct_var` with `u := our_modmult_family bits N a ainv
multBits`, using Tick 26's WellTyped and Tick 27's `ModMulImpl`.

The user must supply `BasicSetting a r N m multBits` — the
order-and-bounds hypothesis on `(a, r, N, m, multBits)` — plus the
modular-arithmetic conditions required by Tick 27. -/
theorem Shor_correct_with_our_family
    (bits N a ainv multBits m r : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m multBits)
    (h_inv_pow : ∀ i, (a^(2^i) % N) * (ainv^(2^i) % N) % N = 1)
    (h_pow_a_pos : ∀ i, 0 < a^(2^i) % N)
    (h_pow_ainv_pos : ∀ i, 0 < ainv^(2^i) % N)
    (h_const_pos_a_iter : ∀ i j, j < multBits → 0 < (a^(2^i) % N * 2^j) % N)
    (h_const_pos_inv_iter :
      ∀ i j, j < multBits → 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N) :
    FormalRV.SQIRPort.probability_of_success a r N m multBits
        (adder_n_qubits (bits + 1) + 1)
        (our_modmult_family bits N a ainv multBits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  apply FormalRV.SQIRPort.Shor_correct_var
  · exact h_basic
  · exact our_modmult_family_ModMulImpl bits N a ainv multBits
      hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
      h_inv_pow h_pow_a_pos h_pow_ainv_pos
      h_const_pos_a_iter h_const_pos_inv_iter
  · intro i _
    exact our_modmult_family_uc_well_typed bits N a ainv multBits
      hbits h_multBits_le h_multBits_pos i


/-- **Coprime + 1 < N implies `0 < a % N`.**  If `N ∣ a` then `N ≤ gcd
a N = 1`, contradicting `1 < N`. -/
theorem coprime_mod_pos (a N : Nat) (hN : 1 < N) (h_cop : Nat.Coprime a N) :
    0 < a % N := by
  by_contra h_zero
  push_neg at h_zero
  have h_eq_zero : a % N = 0 := by omega
  have h_dvd : N ∣ a := Nat.dvd_of_mod_eq_zero h_eq_zero
  have h_gcd : Nat.gcd a N = N := Nat.gcd_eq_right h_dvd
  unfold Nat.Coprime at h_cop
  rw [h_gcd] at h_cop
  omega


/-- **`gcd(a, N) = 1 → gcd(a^k, N) = 1`** via `Nat.Coprime.pow_left`. -/
theorem coprime_pow (a N k : Nat) (h_cop : Nat.Coprime a N) :
    Nat.Coprime (a^k) N := h_cop.pow_left k


/-- **`gcd(a, N) = 1 + 1 < N → 0 < a^k % N` for all `k`.**  Combines
`coprime_pow` and `coprime_mod_pos`. -/
theorem coprime_pow_mod_pos (a N k : Nat) (hN : 1 < N) (h_cop : Nat.Coprime a N) :
    0 < a^k % N :=
  coprime_mod_pos (a^k) N hN (coprime_pow a N k h_cop)


/-- **`gcd(a, N) = 1 + gcd(2, N) = 1 → 0 < (a^k % N * 2^j) % N`.**
The per-bit coprimality condition needed by `our_modmult_family`'s
hypotheses, derived from a base coprimality of `a` and `2` with `N`. -/
theorem coprime_mul_pow_two_mod_pos
    (a N k j : Nat) (hN : 1 < N) (h_cop : Nat.Coprime a N)
    (h_cop_two : Nat.Coprime 2 N) :
    0 < (a^k % N * 2^j) % N := by
  apply coprime_mod_pos
  · exact hN
  · -- Coprime (a^k % N * 2^j) N
    apply Nat.Coprime.mul_left
    · -- Coprime (a^k % N) N
      have h_ak_cop : Nat.Coprime (a^k) N := coprime_pow a N k h_cop
      exact (ZMod.coprime_mod_iff_coprime (a^k) N).mpr h_ak_cop
    · -- Coprime (2^j) N
      exact h_cop_two.pow_left j


/-- **`a * ainv % N = 1` implies `Nat.Coprime a N`.** -/
theorem coprime_of_mul_mod_one (a ainv N : Nat) (h_inv : a * ainv % N = 1) :
    Nat.Coprime a N := by
  unfold Nat.Coprime
  have h_d1 : Nat.gcd a N ∣ a := Nat.gcd_dvd_left _ _
  have h_d2 : Nat.gcd a N ∣ N := Nat.gcd_dvd_right _ _
  have h_d_ainv : Nat.gcd a N ∣ a * ainv := Dvd.dvd.mul_right h_d1 ainv
  have h_d_qN : Nat.gcd a N ∣ N * (a * ainv / N) := Dvd.dvd.mul_right h_d2 _
  have h_d_diff : Nat.gcd a N ∣ a * ainv - N * (a * ainv / N) :=
    Nat.dvd_sub h_d_ainv h_d_qN
  have h_diff_eq : a * ainv - N * (a * ainv / N) = 1 := by
    have h_eq : a * ainv = N * (a * ainv / N) + a * ainv % N := (Nat.div_add_mod _ _).symm
    rw [h_inv] at h_eq
    omega
  rw [h_diff_eq] at h_d_diff
  exact Nat.dvd_one.mp h_d_diff


/-- **`a * ainv % N = 1` implies `Nat.Coprime ainv N`.** -/
theorem coprime_inv_of_mul_mod_one (a ainv N : Nat) (h_inv : a * ainv % N = 1) :
    Nat.Coprime ainv N := by
  rw [Nat.mul_comm] at h_inv
  exact coprime_of_mul_mod_one ainv a N h_inv


/-- **`a * ainv % N = 1 + 1 < N → ∀ k, (a^k % N) * (ainv^k % N) % N = 1`.** -/
theorem mul_pow_mod_one (a ainv N k : Nat) (hN : 1 < N) (h_inv : a * ainv % N = 1) :
    (a^k % N) * (ainv^k % N) % N = 1 := by
  rw [← Nat.mul_mod, ← mul_pow, Nat.pow_mod, h_inv]
  simp [Nat.mod_eq_of_lt hN]


/-- **HEADLINE: Shor success-probability bound from minimal
coprimality hypotheses.**  Bundles Tick 28's `Shor_correct_with_our_family`
with the derivations from `1 < N`, `Nat.Coprime a N`, `Nat.Coprime 2 N`
(N odd), and `a * ainv % N = 1`.

This is the SIMPLEST user-facing Shor success-probability theorem for
our concrete in-place modular multiplier construction. -/
theorem Shor_correct_with_our_family_coprime
    (bits N a ainv multBits m r : Nat)
    (hbits : 1 ≤ bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (hN : N ≤ 2^bits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (h_N_gt_one : 1 < N)
    (h_cop_a : Nat.Coprime a N)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv : a * ainv % N = 1)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m multBits) :
    FormalRV.SQIRPort.probability_of_success a r N m multBits
        (adder_n_qubits (bits + 1) + 1)
        (our_modmult_family bits N a ainv multBits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_cop_ainv : Nat.Coprime ainv N := coprime_inv_of_mul_mod_one a ainv N h_inv
  have hN_pos : 0 < N := by omega
  apply Shor_correct_with_our_family bits N a ainv multBits m r
    hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits h_basic
  · intro i
    exact mul_pow_mod_one a ainv N (2^i) h_N_gt_one h_inv
  · intro i
    exact coprime_pow_mod_pos a N (2^i) h_N_gt_one h_cop_a
  · intro i
    exact coprime_pow_mod_pos ainv N (2^i) h_N_gt_one h_cop_ainv
  · intro i j _
    exact coprime_mul_pow_two_mod_pos a N (2^i) j h_N_gt_one h_cop_a h_cop_two
  · intro i j _
    -- Goal: 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N.
    apply coprime_mod_pos _ _ h_N_gt_one
    apply Nat.Coprime.mul_left
    · -- Coprime ((N - ainv^(2^i) % N) % N) N.
      have h_cop_ainv_i : Nat.Coprime (ainv^(2^i)) N := h_cop_ainv.pow_left _
      have h_cop_ainv_i_mod : Nat.Coprime (ainv^(2^i) % N) N :=
        (ZMod.coprime_mod_iff_coprime _ _).mpr h_cop_ainv_i
      have h_ainv_i_lt : ainv^(2^i) % N ≤ N :=
        Nat.le_of_lt (Nat.mod_lt _ hN_pos)
      have h_sub_cop : Nat.Coprime (N - ainv^(2^i) % N) N :=
        (Nat.coprime_self_sub_left h_ainv_i_lt).mpr h_cop_ainv_i_mod
      exact (ZMod.coprime_mod_iff_coprime _ _).mpr h_sub_cop
    · exact h_cop_two.pow_left _


/-- **HEADLINE: Shor success-probability bound at canonical Shor
parameters.**  Specializes `Shor_correct_with_our_family_coprime` at
`multBits := Nat.log2 (2 * N)` and `m := Nat.log2 (2 * N^2)` (the
canonical Shor sizing), automatically deriving the `BasicSetting` log2
bounds from `1 < N`.  This mirrors the canonical-dim choice in
`Shor_correct` but uses our concrete in-place gate. -/
theorem Shor_correct_with_our_family_at_canonical_dim
    (N a ainv : Nat)
    (h_N_gt_one : 1 < N)
    (h_a_pos : 0 < a) (h_a_lt : a < N)
    (h_cop_a : Nat.Coprime a N)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a
        (FormalRV.SQIRPort.ord a N) N
        (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N))
        (adder_n_qubits (Nat.log2 (2 * N) + 1) + 1)
        (our_modmult_family (Nat.log2 (2 * N)) N a ainv (Nat.log2 (2 * N)))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  -- Standard log2 derivations (same as in `Shor_correct`'s proof body).
  have h_N_pos : 0 < N := by omega
  have h_N_ne : N ≠ 0 := by omega
  have h_2N_ne : (2 * N) ≠ 0 := by omega
  have h_Nsq_ne : N^2 ≠ 0 := by positivity
  have h_2Nsq_ne : (2 * N^2) ≠ 0 := by positivity
  have h_log2_m : Nat.log2 (2 * N^2) = Nat.log2 (N^2) + 1 :=
    Nat.log2_two_mul h_Nsq_ne
  have h_log2_n : Nat.log2 (2 * N) = Nat.log2 N + 1 :=
    Nat.log2_two_mul h_N_ne
  have h_n_lower : 2 ^ (Nat.log2 (2 * N)) ≤ 2 * N :=
    Nat.log2_self_le h_2N_ne
  have h_n_upper : N < 2 ^ (Nat.log2 (2 * N)) := by
    rw [h_log2_n, pow_succ]
    have h1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le h_N_ne
    have h2 : N < 2 ^ (Nat.log2 N + 1) := by
      rw [← Nat.log2_lt h_N_ne]; omega
    rw [pow_succ] at h2
    omega
  have h_m_lower : 2 ^ (Nat.log2 (2 * N^2)) ≤ 2 * N^2 :=
    Nat.log2_self_le h_2Nsq_ne
  have h_m_upper : N^2 < 2 ^ (Nat.log2 (2 * N^2)) := by
    rw [h_log2_m, pow_succ]
    have h1 : 2 ^ Nat.log2 (N^2) ≤ N^2 := Nat.log2_self_le h_Nsq_ne
    have h2 : N^2 < 2 ^ (Nat.log2 (N^2) + 1) := by
      rw [← Nat.log2_lt h_Nsq_ne]; omega
    rw [pow_succ] at h2
    omega
  -- multBits = log2(2*N) ≥ 1 from N ≥ 2.
  have h_multBits_pos : 0 < Nat.log2 (2 * N) := by
    by_contra h_neg
    push_neg at h_neg
    have h_lt_1 : Nat.log2 (2 * N) < 1 := by omega
    rw [Nat.log2_lt h_2N_ne] at h_lt_1
    omega
  -- Order derived from coprimality via ord_Order.
  have h_ord : FormalRV.SQIRPort.Order a (FormalRV.SQIRPort.ord a N) N :=
    FormalRV.SQIRPort.ord_Order a N h_a_pos h_a_lt h_cop_a
  -- Assemble BasicSetting.
  have h_basic : FormalRV.SQIRPort.BasicSetting a
        (FormalRV.SQIRPort.ord a N) N
        (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N)) :=
    BasicSetting_intro a (FormalRV.SQIRPort.ord a N) N
      (Nat.log2 (2 * N^2)) (Nat.log2 (2 * N))
      h_a_pos h_a_lt h_ord h_m_upper h_m_lower h_n_upper h_n_lower
  -- Apply the bundled theorem with bits := multBits = log2(2*N).
  apply Shor_correct_with_our_family_coprime
    (Nat.log2 (2 * N)) N a ainv (Nat.log2 (2 * N))
    (Nat.log2 (2 * N^2)) (FormalRV.SQIRPort.ord a N)
  · -- 1 ≤ multBits.
    exact h_multBits_pos
  · -- multBits ≤ bits + 1 = multBits + 1.
    omega
  · -- 0 < multBits.
    exact h_multBits_pos
  · -- N ≤ 2^bits = 2^multBits.
    omega
  · -- N ≤ 2^multBits.
    omega
  · exact h_N_gt_one
  · exact h_cop_a
  · exact h_cop_two
  · exact h_inv
  · exact h_basic


/-- **Our family instantiated via the parametric Shor theorem.**

A thin wrapper around:
- `Shor_correct_parametric_modmult` (the parametric Shor theorem).
- `our_modmult_family_ModMulImpl` (Tick 27 — ModMulImpl evidence).
- `our_modmult_family_uc_well_typed` (Tick 26 — WellTyped evidence).

The user supplies the standard Shor hypotheses plus the per-iterate
coprimality conditions; this theorem packages everything for our
concrete `our_modmult_family`. -/
theorem Shor_correct_with_our_family_from_parametric
    (bits N a ainv multBits m r : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m multBits)
    (h_inv_pow : ∀ i, (a^(2^i) % N) * (ainv^(2^i) % N) % N = 1)
    (h_pow_a_pos : ∀ i, 0 < a^(2^i) % N)
    (h_pow_ainv_pos : ∀ i, 0 < ainv^(2^i) % N)
    (h_const_pos_a_iter : ∀ i j, j < multBits → 0 < (a^(2^i) % N * 2^j) % N)
    (h_const_pos_inv_iter :
      ∀ i j, j < multBits → 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N) :
    FormalRV.SQIRPort.probability_of_success a r N m multBits
        (adder_n_qubits (bits + 1) + 1)
        (our_modmult_family bits N a ainv multBits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_parametric_modmult a r N m multBits
    (adder_n_qubits (bits + 1) + 1)
    (our_modmult_family bits N a ainv multBits)
    h_basic
    (our_modmult_family_ModMulImpl bits N a ainv multBits
      hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
      h_inv_pow h_pow_a_pos h_pow_ainv_pos
      h_const_pos_a_iter h_const_pos_inv_iter)
    (fun i _ => our_modmult_family_uc_well_typed bits N a ainv multBits
      hbits h_multBits_le h_multBits_pos i)


/-- **Deliverable A: bundled per-iterate hypothesis generator.**

Given `1 < N`, `a * ainv % N = 1`, and `Nat.Coprime 2 N`, derives all
5 of the per-iterate hypotheses required by
`Shor_correct_with_our_family_from_parametric`. -/
theorem our_modmult_family_hypotheses_from_inverse
    (N a ainv multBits : Nat)
    (h_N_gt_one : 1 < N)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv : a * ainv % N = 1) :
    (∀ i, (a^(2^i) % N) * (ainv^(2^i) % N) % N = 1)
    ∧ (∀ i, 0 < a^(2^i) % N)
    ∧ (∀ i, 0 < ainv^(2^i) % N)
    ∧ (∀ i j, j < multBits → 0 < (a^(2^i) % N * 2^j) % N)
    ∧ (∀ i j, j < multBits → 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N) := by
  have hN_pos : 0 < N := by omega
  have h_cop_a : Nat.Coprime a N := coprime_of_mul_mod_one a ainv N h_inv
  have h_cop_ainv : Nat.Coprime ainv N := coprime_inv_of_mul_mod_one a ainv N h_inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact mul_pow_mod_one a ainv N (2^i) h_N_gt_one h_inv
  · intro i
    exact coprime_pow_mod_pos a N (2^i) h_N_gt_one h_cop_a
  · intro i
    exact coprime_pow_mod_pos ainv N (2^i) h_N_gt_one h_cop_ainv
  · intro i j _
    exact coprime_mul_pow_two_mod_pos a N (2^i) j h_N_gt_one h_cop_a h_cop_two
  · intro i j _
    -- Goal: 0 < ((N - ainv^(2^i) % N) % N * 2^j) % N.
    apply coprime_mod_pos _ _ h_N_gt_one
    apply Nat.Coprime.mul_left
    · have h_cop_ainv_i : Nat.Coprime (ainv^(2^i)) N := h_cop_ainv.pow_left _
      have h_cop_ainv_i_mod : Nat.Coprime (ainv^(2^i) % N) N :=
        (ZMod.coprime_mod_iff_coprime _ _).mpr h_cop_ainv_i
      have h_ainv_i_lt : ainv^(2^i) % N ≤ N :=
        Nat.le_of_lt (Nat.mod_lt _ hN_pos)
      have h_sub_cop : Nat.Coprime (N - ainv^(2^i) % N) N :=
        (Nat.coprime_self_sub_left h_ainv_i_lt).mpr h_cop_ainv_i_mod
      exact (ZMod.coprime_mod_iff_coprime _ _).mpr h_sub_cop
    · exact h_cop_two.pow_left _


/-- **HEADLINE Deliverable B: Clean final theorem for the verified
modular-exponentiation family.**

The minimal-assumption form of the end-to-end Shor success-probability
bound for our concrete in-place modular multiplier construction.

Mathematical assumptions (genuinely necessary):
- `1 < N` — non-trivial Shor instance.
- `Nat.Coprime 2 N` — N is odd (required so that `2^j` is coprime to
  N for the per-bit constant positivity).
- `a * ainv % N = 1` — the modular inverse relation. From this,
  `Nat.Coprime a N` and `Nat.Coprime ainv N` are derived internally.
- `BasicSetting a r N m multBits` — the standard Shor order + log2
  bounds.

Structural sizing assumptions:
- `1 ≤ bits`, `multBits ≤ bits + 1`, `0 < multBits`.
- `N ≤ 2^bits`, `N ≤ 2^multBits`. -/
theorem Shor_correct_with_verified_modexp
    (bits N a ainv multBits m r : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N)
    (hN : N ≤ 2^bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2^multBits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m multBits)
    (h_N_gt_one : 1 < N)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m multBits
        (adder_n_qubits (bits + 1) + 1)
        (our_modmult_family bits N a ainv multBits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    our_modmult_family_hypotheses_from_inverse N a ainv multBits
      h_N_gt_one h_cop_two h_inv
  exact Shor_correct_with_our_family_from_parametric
    bits N a ainv multBits m r
    hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
    h_basic h1 h2 h3 h4 h5


/-- **Deliverable A: explicit ancilla count mismatch.**

For all `n ≥ 0`, our family's ancilla budget `adder_n_qubits (n + 1) +
1 = 3n + 6` is strictly greater than SQIR's `modmult_rev_anc n = 2n +
1`.  Difference: `n + 5 ≥ 5` ancillas. -/
theorem our_modmult_family_anc_strictly_exceeds_sqir (n : Nat) :
    FormalRV.SQIRPort.modmult_rev_anc n + (n + 5)
    = adder_n_qubits (n + 1) + 1 := by
  unfold FormalRV.SQIRPort.modmult_rev_anc adder_n_qubits
  ring


/-- **Total-dimension mismatch.**  With `bits = multBits = n`, our
total dimension `n + (adder_n_qubits (n + 1) + 1) = 4n + 6` exceeds
SQIR's `n + modmult_rev_anc n = 3n + 1` by `n + 5`. -/
theorem our_modmult_family_dim_strictly_exceeds_sqir (n : Nat) :
    n + FormalRV.SQIRPort.modmult_rev_anc n + (n + 5)
    = n + (adder_n_qubits (n + 1) + 1) := by
  unfold FormalRV.SQIRPort.modmult_rev_anc adder_n_qubits
  ring


/-- **No `BaseUCom` of one dimension can inhabit another.**  Type
nonequality at the dimension level: `BaseUCom (3n + 1)` and `BaseUCom
(4n + 6)` are DIFFERENT TYPES.  This is the formal obstacle that
PREVENTS pointing `f_modmult_circuit` (return type `BaseUCom (n +
modmult_rev_anc n) = BaseUCom (3n + 1)`) at our gate (return type
`BaseUCom (n + (adder_n_qubits (n + 1) + 1)) = BaseUCom (4n + 6)`). -/
theorem sqir_anc_ne_our_anc (n : Nat) (h_n_pos : 0 < n) :
    n + FormalRV.SQIRPort.modmult_rev_anc n
    ≠ n + (adder_n_qubits (n + 1) + 1) := by
  unfold FormalRV.SQIRPort.modmult_rev_anc adder_n_qubits
  omega


/-- **Closure obstruction theorem (Deliverable C as a Lean statement).**

Composite documentation theorem stating three facts about the closure
of the original SQIR axioms:

1. SQIR's expected oracle type is `BaseUCom (n + modmult_rev_anc n) =
   BaseUCom (3n + 1)`.
2. Our family's oracle type is `BaseUCom (n + (adder_n_qubits (n + 1)
   + 1)) = BaseUCom (4n + 6)`.
3. These types are not equal for any `n ≥ 1` (witnessed by `n + 5`
   strictly positive ancilla excess).

Combined effect: any further closure of `f_modmult_circuit`,
`f_modmult_circuit_MMI`, `f_modmult_circuit_uc_well_typed` must construct
a new oracle family at the EXACT SQIR type, not embed our family. -/
theorem sqir_axiom_closure_obstruction
    (a ainv N n : Nat) (_h_a_lt : a < N) (_h_ainv_lt : ainv < N)
    (_h_inv : a * ainv % N = 1) (h_n_pos : 0 < n) :
    -- SQIR's expected oracle type:
    let sqir_dim := n + FormalRV.SQIRPort.modmult_rev_anc n
    -- Our family's actual oracle type:
    let our_dim := n + (adder_n_qubits (n + 1) + 1)
    -- These are not equal:
    sqir_dim ≠ our_dim := by
  exact sqir_anc_ne_our_anc n h_n_pos


/-! ## ModExp reuses ANY verified modmult (the modularized-design point).

    The generic construction below is parametric over the modmult gate; both
    `modMultInPlaceShor` (Gidney/Shor layout, via `our_modmult_family`) AND
    `modmult_MCP_gate` (SQIR layout, via `modexpFamilyMCP`) instantiate it. The
    ancilla counts differ (`adder_n_qubits (bits+1)+1` vs `sqir_modmult_rev_anc bits`)
    but `ModMulImpl` / `Shor_correct_var` are parametric over `anc`, so — exactly as
    you noted — the ancilla count does not matter, only the multiply correctness. -/

/-- **Generic: any verified per-constant modmult yields a `ModMulImpl`.** If each
iterate's gate satisfies `MultiplyCircuitProperty` for the reduced constant
`a^(2^i) mod N`, the squared-power family is a valid Shor modexp oracle, at ANY
ancilla count `anc`. -/
theorem modexpOracleFamily_ModMulImpl (n anc N a ainv : Nat) (gate : Nat → Nat → Gate)
    (h : ∀ i, FormalRV.SQIRPort.MultiplyCircuitProperty (a ^ (2 ^ i) % N) N n anc
                (Gate.toUCom (n + anc) (gate (a ^ (2 ^ i) % N) (ainv ^ (2 ^ i) % N)))) :
    FormalRV.SQIRPort.ModMulImpl a N n anc (modexpOracleFamily (n + anc) N a ainv gate) :=
  fun i => MultiplyCircuitProperty_mod_invariance (a ^ (2 ^ i)) N n anc _ (h i)

/-- **`modmult_MCP_gate` is a valid modexp oracle.** The SQIR-layout ModMult gadget
plugs into the SAME generic modexp (ancilla `sqir_modmult_rev_anc bits`); its
per-iterate `MultiplyCircuitProperty` comes straight from `modmult_correct`. -/
theorem modexpFamilyMCP_ModMulImpl (bits N a ainv : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv_pow : ∀ i, (a ^ (2 ^ i) % N) * (ainv ^ (2 ^ i) % N) % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N bits (sqir_modmult_rev_anc bits)
      (modexpFamilyMCP bits N a ainv) :=
  modexpOracleFamily_ModMulImpl bits (sqir_modmult_rev_anc bits) N a ainv
    (fun c cinv => modmult_MCP_gate bits N c cinv)
    (fun i => modmult_correct bits N (a ^ (2 ^ i) % N) (ainv ^ (2 ^ i) % N)
                hbits hN_pos hN hN2 (le_of_lt (Nat.mod_lt _ hN_pos)) (h_inv_pow i))

/-- **Shor success with the SQIR-layout modmult.** ModExp's order-finding oracle
works with `modmult_MCP_gate` exactly as with `modMultInPlaceShor`, only the
ancilla count differs. (Uses the gadget's sizing `2N ≤ 2^bits`.) -/
theorem Shor_correct_with_mcp_family (bits N a ainv m r : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (h_inv_pow : ∀ i, (a ^ (2 ^ i) % N) * (ainv ^ (2 ^ i) % N) % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits (sqir_modmult_rev_anc bits)
        (modexpFamilyMCP bits N a ainv)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4 :=
  FormalRV.SQIRPort.Shor_correct_var a r N m bits (sqir_modmult_rev_anc bits)
    (modexpFamilyMCP bits N a ainv) h_basic
    (modexpFamilyMCP_ModMulImpl bits N a ainv hbits hN_pos hN hN2 h_inv_pow)
    (fun i _ => uc_well_typed_toUCom_of_Gate_WellTyped _ _
      (modmult_MCP_gate_wellTyped bits N (a ^ (2 ^ i) % N) (ainv ^ (2 ^ i) % N)
        hbits hN_pos hN hN2))


end FormalRV.BQAlgo
