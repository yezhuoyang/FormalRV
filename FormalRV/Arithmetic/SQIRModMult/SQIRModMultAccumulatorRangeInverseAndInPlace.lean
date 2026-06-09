import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultPrefixInvariant
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultAccumulatorRangeSwapConcrete

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ## Tick 77 — Task 4: Modular inverse arithmetic. -/

/-- **Modular inverse clear arithmetic.**

If `(a * ainv) % N = 1`, then
`(x + ((N - ainv) % N) * ((a * x) % N)) % N = 0`. -/
theorem sqir_modmult_inverse_clear_arith
    (N a ainv x : Nat) (hN_pos : 0 < N) (hx : x < N) (h_ainv_le : ainv ≤ N)
    (h_inv : (a * ainv) % N = 1) :
    (x + ((N - ainv) % N) * ((a * x) % N)) % N = 0 := by
  -- Step 0: combine the inner mods.
  have h_combined :
      (x + ((N - ainv) % N) * ((a * x) % N)) % N
        = (x + (N - ainv) * (a * x)) % N := by
    rw [Nat.add_mod x (((N - ainv) % N) * ((a * x) % N)) N]
    rw [← Nat.mul_mod]
    rw [← Nat.add_mod]
  rw [h_combined]
  -- Step 1: (N - ainv) * (a * x) = N*(a*x) - ainv*(a*x).
  have h_sub : (N - ainv) * (a * x) = N * (a * x) - ainv * (a * x) :=
    Nat.sub_mul N ainv (a * x)
  rw [h_sub]
  -- Step 2: x + (N * (a*x) - ainv * (a*x)).
  -- Since ainv * (a*x) ≤ N * (a*x) (because ainv ≤ N), and N*(a*x) ≤ x + N*(a*x):
  have h_le1 : ainv * (a * x) ≤ N * (a * x) := Nat.mul_le_mul_right _ h_ainv_le
  have h_le2 : ainv * (a * x) ≤ x + N * (a * x) := by omega
  -- Rewrite: x + (N * (a*x) - ainv * (a*x)) = (x + N * (a*x)) - ainv * (a*x).
  have h_assoc : x + (N * (a * x) - ainv * (a * x))
                = (x + N * (a * x)) - ainv * (a * x) := by omega
  rw [h_assoc]
  -- Now: ((x + N*(a*x)) - ainv*(a*x)) % N = 0.
  -- Let A = x + N*(a*x), B = ainv*(a*x).  Then A ≥ B and we want (A - B) % N = 0.
  set A := x + N * (a * x) with hA_def
  set B := ainv * (a * x) with hB_def
  have hB_le_A : B ≤ A := h_le2
  -- A % N = x.
  have hA_mod : A % N = x := by
    rw [hA_def, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hx
  -- B % N = x.
  have hB_mod : B % N = x := by
    rw [hB_def]
    rw [show ainv * (a * x) = (a * ainv) * x by ring]
    rw [Nat.mul_mod, h_inv, Nat.one_mul, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hx
  -- ((A - B) % N + B % N) % N = A % N (by sub_add_cancel + add_mod).
  have h_sub_add : (A - B) + B = A := Nat.sub_add_cancel hB_le_A
  have h_eq : ((A - B) + B) % N = A % N := by rw [h_sub_add]
  have h_eq_split : ((A - B) % N + B % N) % N = A % N := by
    rw [← Nat.add_mod]; exact h_eq
  rw [hA_mod, hB_mod] at h_eq_split
  -- h_eq_split : ((A - B) % N + x) % N = x.  Let R = (A - B) % N.
  set R := (A - B) % N with hR_def
  have hR_lt : R < N := Nat.mod_lt _ hN_pos
  -- (R + x) % N = x, R < N, x < N → R = 0.
  by_contra h_R_ne
  have h_R_pos : R > 0 := Nat.pos_of_ne_zero h_R_ne
  rcases Nat.lt_or_ge (R + x) N with h_lt | h_ge
  · rw [Nat.mod_eq_of_lt h_lt] at h_eq_split
    omega
  · have h_RpX_eq : (R + x) % N = R + x - N := by
      rw [Nat.mod_eq_sub_mod h_ge]
      exact Nat.mod_eq_of_lt (by omega : R + x - N < N)
    rw [h_RpX_eq] at h_eq_split
    omega

/-! ## Tick 77 — Task 5: In-place target theorem. -/

/-- **In-place modular multiplier candidate target theorem.**

After applying the in-place wrapper to `(x, 0)`, the resulting state is
`((a*x) % N, 0)` — i.e., the original "multiplier" register now holds
the product, and the accumulator is cleared. -/
theorem sqir_modmult_inplace_candidate_state_eq
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv) (sqir_mult_input_F bits x 0)
      = sqir_mult_input_F bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate
  simp only [Gate.applyNat_seq]
  -- Step 1: Compute (x, 0) → (x, (a*x) % N).
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_modmult_const_gate_state_eq_from bits N a x 0 hbits hN_pos hN hN2 hN_pos hx_lt_pow]
  simp only [Nat.zero_add]
  -- Step 2: Swap → ((a*x) % N, x).
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply bits x ((a * x) % N) hbits hx_lt_pow hax_lt_pow]
  -- Step 3: Uncompute with c = (N - ainv) % N.
  -- Now input is sqir_mult_input_F bits ((a*x) % N) x.
  rw [sqir_modmult_const_gate_state_eq_from bits N ((N - ainv) % N) ((a * x) % N) x
        hbits hN_pos hN hN2 hx hax_lt_pow]
  -- Result: sqir_mult_input_F bits ((a*x) % N) ((x + ((N - ainv) % N) * ((a*x) % N)) % N).
  -- By inverse arithmetic, the accumulator = 0.
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

/-! ## R7d^xxix-L-3.15g.2 — Headline: q_start in-place modular
       multiplier state equality.

Built on:
- `sqir_modmult_const_gate_state_eq_from_qstart` (this file, L-3.15g).
- `sqir_swap_acc_mult_apply_qstart` (this file, L-3.15g.2 above).
- `sqir_modmult_inverse_clear_arith` (q_start-INDEPENDENT, above). -/

/-- q_start port of `sqir_modmult_inplace_candidate_state_eq`.

After applying the q_start in-place wrapper to `(x, 0)`, the resulting
state is `((a*x) % N, 0)` — the original "multiplier" register now
holds the product, and the accumulator is cleared. -/
theorem sqir_modmult_inplace_candidate_state_eq_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat
        (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
        (sqir_mult_input_F_qstart bits q_start x 0)
      = sqir_mult_input_F_qstart bits q_start ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate_qstart
  simp only [Gate.applyNat_seq]
  -- Step 1: compute (x, 0) → (x, (a*x) % N).
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqir_modmult_const_gate_state_eq_from_qstart bits q_start N a x 0 flagPos dim
        hbits hN_pos hN hN2 hN_pos hx_lt_pow h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  simp only [Nat.zero_add]
  -- Step 2: swap → ((a*x) % N, x).
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply_qstart bits q_start x ((a * x) % N) hbits
        hx_lt_pow hax_lt_pow]
  -- Step 3: uncompute with c = (N - ainv) % N.
  rw [sqir_modmult_const_gate_state_eq_from_qstart bits q_start N ((N - ainv) % N)
        ((a * x) % N) x flagPos dim
        hbits hN_pos hN hN2 hx hax_lt_pow h_flag_lt_qstart h_workspace
        h_dim_covers_mult]
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

/-! ## R7d^xxix-L-3.15h — q_start in-place-clean bundle (the MCP
       prerequisite immediately below the MCP layer).

The hard-coded MCP headline at line 4218 wraps the in-place candidate
inside a `Gate.shift bits ∘ reverse_register_swap` adapter (which
re-encodes between the external `encodeDataZeroAnc` layout and the
internal SQIR layout).  That outer adapter is built on the fixed
`q_start = 2` constants in `sqir_mult_control_idx bits 0 = 2*bits + 1`
and would need a parallel q_start-parametric reverse-register adapter
plus its disjointness / well-typed / correctness chain to lift.

Per the L-3.15h fallback policy, this sub-tick lands the **clean
bundle immediately below the MCP layer** (the q_start port of
`sqir_modmult_inplace_candidate_clean`, line 3733).  The bundle
restates the in-place state-eq pointwise via the existing q_start
decoded-helper layer (lines 2488–2640), and is the input that an
adapter-bridge MCP port would consume verbatim.

Concretely the bundle yields:
- decoded target = 0;
- decoded read = 0;
- every position below `q_start` is `false` (the q_start generalisation
  of the old `flag_0`/`flag_1` conjuncts);
- top-carry = `false`;
- multiplier register decodes to `((a*x) % N).testBit k`.

Deferred to L-3.15h.2 (full MCP port):
- `sqir_modmult_rev_anc_qstart`, `sqir_total_dim_qstart`;
- `sqir_mult_input_F_shifted_qstart` (shift by `bits`);
- `sqir_encode_to_mult_adapter_qstart` + disjointness/WellTyped/
  correctness/involution/reverse chain;
- `sqir_modmult_inplace_shifted_qstart` + `_correct` + `_wellTyped`;
- `sqir_modmult_MCP_gate_qstart` + `_apply_encode` + `_wellTyped`;
- `sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty_qstart`. -/

/-- q_start port of `sqir_modmult_inplace_candidate_target_decode`
(line 3708): after the in-place wrapper, the decoded target value is `0`. -/
theorem sqir_modmult_inplace_candidate_target_decode_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0))
      = 0 := by
  rw [sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
        flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
        h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_mult_input_target_decode_qstart bits q_start ((a * x) % N) 0
          (Nat.two_pow_pos bits)

/-- q_start port of `sqir_modmult_inplace_candidate_mult_bit` (line 3721):
the multiplier register decodes bit-by-bit to `((a*x) % N).testBit k`. -/
theorem sqir_modmult_inplace_candidate_mult_bit_qstart
    (bits q_start N a ainv x k flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) (hk : k < bits)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    Gate.applyNat
        (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
        (sqir_mult_input_F_qstart bits q_start x 0)
        (sqir_mult_control_idx_qstart bits q_start k)
      = ((a * x) % N).testBit k := by
  rw [sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
        flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
        h_flag_lt_qstart h_workspace h_dim_covers_mult]
  exact sqir_mult_input_control_bit_qstart bits q_start ((a * x) % N) 0 k hk

/-- q_start port of `sqir_modmult_inplace_candidate_clean` (line 3733).

The clean bundle restating the in-place state-eq pointwise:
* `cuccaro_target_val = 0`;
* `cuccaro_read_val = 0`;
* every position below `q_start` is `false` (q_start generalisation of
  the old `flag_0`/`flag_1` conjuncts at positions 0 and 1);
* top-carry position `q_start + 2*bits` is `false`;
* multiplier-bit decoding at every `sqir_mult_control_idx_qstart bits q_start k`
  equals `((a*x) % N).testBit k`. -/
theorem sqir_modmult_inplace_candidate_clean_qstart
    (bits q_start N a ainv x flagPos dim : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1)
    (h_flag_lt_qstart : flagPos < q_start)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_dim_covers_mult : q_start + (2 * bits + 1) + bits ≤ dim) :
    cuccaro_target_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)) = 0
    ∧ cuccaro_read_val bits q_start
        (Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)) = 0
    ∧ (∀ q, q < q_start →
        Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0) q = false)
    ∧ Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0) (q_start + 2 * bits) = false
    ∧ ∀ k, k < bits →
        Gate.applyNat
          (sqir_modmult_inplace_candidate_qstart bits q_start N a ainv flagPos)
          (sqir_mult_input_F_qstart bits q_start x 0)
          (sqir_mult_control_idx_qstart bits q_start k)
          = ((a * x) % N).testBit k := by
  have h_state := sqir_modmult_inplace_candidate_state_eq_qstart bits q_start N a ainv x
    flagPos dim hbits hN_pos hN hN2 h_ainv_le hx h_inv
    h_flag_lt_qstart h_workspace h_dim_covers_mult
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_state]
    exact sqir_mult_input_target_decode_qstart bits q_start ((a * x) % N) 0
            (Nat.two_pow_pos bits)
  · rw [h_state]; exact sqir_mult_input_read_decode_qstart bits q_start ((a * x) % N) 0
  · intro q hq
    rw [h_state]
    exact sqir_mult_input_at_below_qstart_eq_false_qstart bits q_start
            ((a * x) % N) 0 q hq
  · rw [h_state]
    exact sqir_mult_input_top_carry_false_qstart bits q_start ((a * x) % N) 0 hbits
  · intro k hk
    rw [h_state]
    exact sqir_mult_input_control_bit_qstart bits q_start ((a * x) % N) 0 k hk

end FormalRV.BQAlgo
