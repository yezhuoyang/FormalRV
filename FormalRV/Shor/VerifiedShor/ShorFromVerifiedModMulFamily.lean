import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModMult

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## Tick 79 — Verified ModMulImpl family.

### Layout and sizing decision (documented as Route B)

The original SQIR axiom site (`Shor.lean:4570`) declares:
  axiom f_modmult_circuit : (a ainv N n : Nat) → Nat → BaseUCom (n + modmult_rev_anc n)
where `modmult_rev_anc n = 2 * n + 1`, giving total dim `3 * n + 1`.

Our verified MCP gate has total dim `(n + 1) + sqir_modmult_rev_anc (n + 1) = 4 * n + 15`
because:
1. `BasicSetting` only guarantees `2^n ≤ 2 * N`, NOT `2 * N ≤ 2^n`.  The
   `BasicSetting_twoN_le_pow_succ` lemma gives `2 * N ≤ 2 ^ (n + 1)`, so
   we instantiate at `bits = n + 1`.
2. The SQIR-faithful workspace requires `3 * (n + 1) + 11 = 3 * n + 14`
   ancilla bits, which exceeds the placeholder's `2 * (n+1) + 1`.

**Route B (verified parallel family)**: we land a new family
`f_modmult_circuit_verified` at dimension `(n + 1) + sqir_modmult_rev_anc (n + 1)`,
prove `ModMulImpl` + `uc_well_typed` at that dimension, and document the
exact dimension mismatch with the original placeholder.  The original
axiom names remain untouched; downstream theorems that take
`ModMulImpl ... f` as a hypothesis can be instantiated with our family
at dimension `n + 1` (with appropriate dimension/ancilla bookkeeping). -/

/-- **Per-iterate modular inverse arithmetic.**

If `(a * ainv) % N = 1` and `N ≥ 2`, then for every `i`,
`((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1`. -/
theorem pow_iter_inverse_mod
    (a ainv N i : Nat) (hN_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 := by
  rw [← Nat.mul_mod]
  rw [← Nat.mul_pow]
  rw [Nat.pow_mod]
  rw [h_inv]
  rw [one_pow]
  exact Nat.mod_eq_of_lt hN_ge_2

/-- **MCP up-to-mod lifting.**  If a unitary satisfies
`MultiplyCircuitProperty (c % N)`, then it also satisfies
`MultiplyCircuitProperty c` (since `(c * x) % N = ((c % N) * x) % N`). -/
theorem MultiplyCircuitProperty_of_mod
    {c N n anc : Nat} {U : FormalRV.Framework.BaseUCom (n + anc)}
    (hN_pos : 0 < N) (h_modN : FormalRV.SQIRPort.MultiplyCircuitProperty (c % N) N n anc U) :
    FormalRV.SQIRPort.MultiplyCircuitProperty c N n anc U := by
  unfold FormalRV.SQIRPort.MultiplyCircuitProperty at h_modN ⊢
  intro x hx
  have h_eq : c * x % N = c % N * x % N := by
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod]
    rw [Nat.mod_mod]
  rw [h_eq]
  exact h_modN x hx

/-- **Per-iterate `MultiplyCircuitProperty` for the verified family.** -/
theorem f_modmult_circuit_verified_per_iterate
    (a ainv N n i : Nat) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty
      (a^(2^i)) N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n i) := by
  unfold f_modmult_circuit_verified
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  -- Reframe via mod-up-to lift.
  apply MultiplyCircuitProperty_of_mod hN_pos
  -- Goal: MultiplyCircuitProperty ((a^(2^i)) % N) N (n+1) anc (Gate.toUCom ... MCP_gate)
  show FormalRV.SQIRPort.MultiplyCircuitProperty
    ((a^(2^i)) % N) N (n + 1) (sqir_modmult_rev_anc (n + 1))
    (Gate.toUCom ((n + 1) + sqir_modmult_rev_anc (n + 1))
      (modmult_MCP_gate (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N)))
  have h_mcp := modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    (n + 1) N ((a^(2^i)) % N) ((ainv^(2^i)) % N)
    (by omega : 1 ≤ n + 1) hN_pos hN hN2 h_ainv_le h_inv_i
  unfold modmult_total_dim at h_mcp
  exact h_mcp

/-- **`ModMulImpl` for the verified family.** -/
theorem f_modmult_circuit_verified_MMI
    (a ainv N n : Nat) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n) := by
  intro i
  exact f_modmult_circuit_verified_per_iterate a ainv N n i hN_ge_2 hN hN2 h_inv

/-- **`uc_well_typed` for every iterate of the verified family.** -/
theorem f_modmult_circuit_verified_uc_well_typed
    (a ainv N n : Nat) (hN_pos : 0 < N) (hN : N ≤ 2^(n + 1)) (hN2 : 2 * N ≤ 2^(n + 1)) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified a ainv N n i) := by
  intro i
  unfold f_modmult_circuit_verified
  apply uc_well_typed_toUCom_of_Gate_WellTyped
  have h_wt := modmult_MCP_gate_wellTyped (n + 1) N
    ((a^(2^i)) % N) ((ainv^(2^i)) % N) (by omega : 1 ≤ n + 1) hN_pos hN hN2
  unfold modmult_total_dim at h_wt
  exact h_wt

/-! ### BasicSetting bridge for the verified family. -/

/-- **`ModMulImpl` from `BasicSetting`** (n+1 dimension). -/
theorem f_modmult_circuit_verified_MMI_from_BasicSetting
    (a r N m n ainv : Nat) (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N (n + 1) (sqir_modmult_rev_anc (n + 1))
      (f_modmult_circuit_verified a ainv N n) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  have hN : N ≤ 2 ^ (n + 1) := by
    have h1 : N ≤ 2 * N := by omega
    have h2 : 2 * N ≤ 2 ^ (n + 1) := hN2
    omega
  exact f_modmult_circuit_verified_MMI a ainv N n h_N_ge_2 hN hN2 h_inv

/-- **`uc_well_typed` from `BasicSetting`**. -/
theorem f_modmult_circuit_verified_uc_well_typed_from_BasicSetting
    (a r N m n ainv : Nat) (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified a ainv N n i) := by
  have hN2 : 2 * N ≤ 2 ^ (n + 1) := BasicSetting_twoN_le_pow_succ a r N m n h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _, _, hN_lt, _⟩ := h_basic
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have hN : N ≤ 2 ^ (n + 1) := by
    have h1 : N ≤ 2 * N := by omega
    have h2 : 2 * N ≤ 2 ^ (n + 1) := hN2
    omega
  exact f_modmult_circuit_verified_uc_well_typed a ainv N n hN_pos hN hN2

/-- **MMI for the bits-parameterized family.** -/
theorem f_modmult_circuit_verified_bits_MMI
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.ModMulImpl a N bits (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits) := by
  intro i
  unfold f_modmult_circuit_verified_bits
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  apply MultiplyCircuitProperty_of_mod hN_pos
  have h_mcp := modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    bits N ((a^(2^i)) % N) ((ainv^(2^i)) % N) hbits hN_pos hN hN2 h_ainv_le h_inv_i
  unfold modmult_total_dim at h_mcp
  exact h_mcp

/-- **uc_well_typed for the bits-parameterized family.** -/
theorem f_modmult_circuit_verified_bits_uc_well_typed
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    ∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified_bits a ainv N bits i) := by
  intro i
  unfold f_modmult_circuit_verified_bits
  apply uc_well_typed_toUCom_of_Gate_WellTyped
  have h_wt := modmult_MCP_gate_wellTyped bits N
    ((a^(2^i)) % N) ((ainv^(2^i)) % N) hbits hN_pos hN hN2
  unfold modmult_total_dim at h_wt
  exact h_wt

/-- **Verified Shor probability bound — bits-parameterized.**

If the user provides `BasicSetting a r N m bits` (which is generally
INCOMPATIBLE with our sizing requirement `2 * N ≤ 2^bits` — see the
documentation block above), the Shor success-probability bound holds
for the verified family at dimension `bits + sqir_modmult_rev_anc bits`.

In practice, both hypotheses can be simultaneously satisfied ONLY when
`2 * N = 2^bits` (i.e., `N` is a power of 2).  For general `N`, this
theorem is vacuous — see Status D in PROGRESS.md / Tick 80 commit. -/
theorem Shor_correct_with_sqir_verified_modmult_bits
    (a r N m bits ainv : Nat) (hbits : 1 ≤ bits)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (hN2 : 2 * N ≤ 2^bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_basic_destruct := h_basic
  unfold FormalRV.SQIRPort.BasicSetting at h_basic_destruct
  obtain ⟨⟨h_a_pos, h_a_lt⟩, _h_ord, _, hN_lt, _⟩ := h_basic_destruct
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  have hN : N ≤ 2 ^ bits := Nat.le_of_lt hN_lt
  exact FormalRV.SQIRPort.Shor_correct_var a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

end FormalRV.BQAlgo
