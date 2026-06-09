import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultEncoding
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSpec
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultFamily
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultSizing
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultAccumulatorRange
import FormalRV.Shor.VerifiedShor.RelaxedQPE_MMI

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
/-! ### Task 8 — Final usable verified SQIR Shor theorem. -/

/-- **Fully usable verified SQIR Shor theorem** — no residual upper
bound on `2^bits` from BasicSetting. -/
theorem Shor_correct_with_sqir_verified_modmult_usable
    (a r N m bits ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m bits)
    (h_sizing : VerifiedCircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (sqir_modmult_rev_anc bits)
      (f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hbits : 1 ≤ bits := h_sizing.1
  have hN : N ≤ 2^bits := h_sizing.2.1
  have hN2 : 2 * N ≤ 2^bits := h_sizing.2.2
  have hN_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact Shor_correct_var_relaxed a r N m bits
    (sqir_modmult_rev_anc bits) (f_modmult_circuit_verified_bits a ainv N bits)
    h_basic_r
    (f_modmult_circuit_verified_bits_MMI a ainv N bits hbits h_N_ge_2 hN hN2 h_inv)
    (fun i _ => f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits
                  hbits hN_pos hN hN2 i)

/-! ### Task 9 — Canonical bits corollary. -/

/-- **Canonical-bits corollary**: bits = `Nat.log2 (2*N) + 1`. -/
theorem Shor_correct_with_sqir_verified_modmult_canonical_bits
    (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2*N) + 1)
      (sqir_modmult_rev_anc (Nat.log2 (2*N) + 1))
      (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2*N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have hN_pos : 0 < N := BasicSettingRelaxed_N_pos h_basic_r
  exact Shor_correct_with_sqir_verified_modmult_usable a r N m
    (Nat.log2 (2*N) + 1) ainv h_basic_r
    (VerifiedCircuitSizing_canonical_pow2_succ N hN_pos) h_inv

/-! ## Tick 84 — Final review, alias, and Phase summary.

### Documentation: which Shor theorem to cite

The original SQIR `Shor_correct` and `Shor_correct_var` theorems
(`PostQFT.lean`) depend on the placeholder axioms
`f_modmult_circuit`, `f_modmult_circuit_MMI`, and
`f_modmult_circuit_uc_well_typed` (declared in `Shor.lean:4570-4711`).
Confirmed by `lean_verify Shor_correct` listing these axioms.

The **verified** Shor theorem to cite for the kernel-clean,
axiom-free result is one of:

- `Shor_correct_with_sqir_verified_modmult_usable`: takes
  `BasicSettingRelaxed`, `VerifiedCircuitSizing`, and the modular
  inverse hypothesis.
- `Shor_correct_with_sqir_verified_modmult_canonical_bits`: same but
  the sizing is auto-discharged at `bits = Nat.log2 (2*N) + 1`.

These theorems use the verified SQIR modular multiplier
(`f_modmult_circuit_verified_bits` → `sqir_modmult_MCP_gate`) and
NOT the placeholder `f_modmult_circuit`.  Their axiom dependency is
exactly `[propext, Classical.choice, Quot.sound]` (the standard kernel).

**Do not cite `Shor_correct` or `Shor_correct_var` as the verified
result** — they remain in the codebase for historical compatibility
but rely on placeholder axioms. -/

/-- **Verified Shor's algorithm correctness theorem (no placeholder
axioms).**  Alias for `Shor_correct_with_sqir_verified_modmult_canonical_bits`
under a name that signals its axiom-free status. -/
theorem Shor_correct_verified_no_modmult_axioms
    (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2*N) + 1)
      (sqir_modmult_rev_anc (Nat.log2 (2*N) + 1))
      (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2*N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  Shor_correct_with_sqir_verified_modmult_canonical_bits a r N m ainv h_basic_r h_inv

end FormalRV.BQAlgo
