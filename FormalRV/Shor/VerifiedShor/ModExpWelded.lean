/-
  FormalRV.Arithmetic.SQIRModMult.ModExpWelded — WS1a: the WELDED modexp theorem.

  Audit gap H5/H6: the verified Shor *semantics* rode on the family
  `f_modmult_circuit_verified_bits`, while the RSA-2048 *resource counts* rode on
  DIFFERENT, never-semantically-verified `Gate`/`EGate` chains. This file welds
  semantics + well-typedness + resource count onto ONE term — the same family the
  headline `Shor_correct_verified_no_modmult_axioms` already consumes.

  The weld is airtight by `family_iterate_gate` (rfl): the gate the count is taken
  on IS the gate underlying iterate `i` of the verified family.

  No `sorry`, no new `axiom`, no `native_decide`. Reuses:
    • semantics:  `f_modmult_circuit_verified_bits_MMI`        (ModMulImpl)
    • well-typed: `f_modmult_circuit_verified_bits_uc_well_typed`
    • per-gate T-count: `tcount_sqir_modmult_MCP_gate_shor` = 112·bits² (constant)
-/
import FormalRV.Arithmetic.SQIRModMult.ToffoliCount
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultAccumulatorRange
import FormalRV.Shor.VerifiedShor.VerifiedShorTheorem
import FormalRV.Shor.VerifiedShor.ShorFromVerifiedModMulFamily
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Verifier.ProofGate

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- **The weld is on the SAME term.** Iterate `i` of the verified family is, by
definition, `Gate.toUCom` of exactly the gate the count below is taken on. -/
theorem family_iterate_gate (a ainv N bits i : Nat) :
    f_modmult_circuit_verified_bits a ainv N bits i
      = Gate.toUCom (bits + sqir_modmult_rev_anc bits)
          (sqir_modmult_MCP_gate bits N ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N)) := rfl

/-- **Per-iterate T-count is the constant `112·bits²`**, for every Shor iterate `i`,
whenever `a`, `ainv` are coprime to the odd modulus `N > 1`. -/
theorem tcount_verified_family_iterate (a ainv N bits i : Nat)
    (hcop_a : Nat.Coprime a N) (hcop_ainv : Nat.Coprime ainv N)
    (hodd : Odd N) (h1 : 1 < N) :
    tcount (sqir_modmult_MCP_gate bits N ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N))
      = 112 * bits ^ 2 := by
  apply tcount_sqir_modmult_MCP_gate_shor
  · exact (ZMod.coprime_mod_iff_coprime (a ^ (2 ^ i)) N).mpr (coprime_pow a N (2 ^ i) hcop_a)
  · exact (ZMod.coprime_mod_iff_coprime (ainv ^ (2 ^ i)) N).mpr (coprime_pow ainv N (2 ^ i) hcop_ainv)
  · exact coprime_pow_mod_pos ainv N (2 ^ i) h1 hcop_ainv
  · exact Nat.mod_lt _ (by omega)
  · exact hodd
  · exact h1

/-- **Total T-count of the verified modular-exponentiation over `m` iterates** is
`m · 112·bits²` — proven on the verified family's own gates, not a separate chain. -/
theorem tcount_verified_modexp_chain (a ainv N bits m : Nat)
    (hcop_a : Nat.Coprime a N) (hcop_ainv : Nat.Coprime ainv N)
    (hodd : Odd N) (h1 : 1 < N) :
    (∑ i ∈ Finset.range m,
        tcount (sqir_modmult_MCP_gate bits N ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N)))
      = m * (112 * bits ^ 2) := by
  have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range m) =>
      tcount_verified_family_iterate a ainv N bits i hcop_a hcop_ainv hodd h1)
  rw [h, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **★ WS1a — the WELDED modexp theorem.** ONE family
(`f_modmult_circuit_verified_bits`, the term the verified Shor success theorem
consumes) simultaneously carries:
  (i)   the modular-multiplication SEMANTICS (`ModMulImpl`: iterate `i` is `×a^(2^i) mod N`);
  (ii)  well-typedness at the Shor dimension;
  (iii) the exact total T-count `m · 112·bits²` of its own gates over `m` iterates.
Closes audit findings H5/H6: count and semantics now ride the SAME circuit. -/
theorem shor_modexp_welded (a ainv N m bits : Nat)
    (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv : a * ainv % N = 1)
    (hcop_a : Nat.Coprime a N) (hcop_ainv : Nat.Coprime ainv N) (hodd : Odd N) :
    FormalRV.SQIRPort.ModMulImpl a N bits (sqir_modmult_rev_anc bits)
        (f_modmult_circuit_verified_bits a ainv N bits)
    ∧ (∀ i, FormalRV.SQIRPort.uc_well_typed (f_modmult_circuit_verified_bits a ainv N bits i))
    ∧ (∑ i ∈ Finset.range m,
        tcount (sqir_modmult_MCP_gate bits N ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N)))
        = m * (112 * bits ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact f_modmult_circuit_verified_bits_MMI a ainv N bits hbits hN_ge_2 hN hN2 h_inv
  · exact f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits hbits (by omega) hN hN2
  · exact tcount_verified_modexp_chain a ainv N bits m hcop_a hcop_ainv hodd (by omega)

/-- **★ WS1a — success bound AND resource count, one theorem, one circuit.**
Chains the welded family into the verified Shor success theorem: at the canonical
register size `bits = log₂(2N)+1`, the SAME family `f_modmult_circuit_verified_bits`
both (i) drives order-finding to success probability `≥ κ/(log₂N)⁴` and (ii) has the
exact total T-count `m·112·bits²`. This is the end-to-end weld: the resource number
is reported for the very circuit proven to make Shor succeed. -/
theorem shor_resource_welded (a r N m ainv : Nat)
    (h_basic_r : BasicSettingRelaxed a r N m (Nat.log2 (2 * N) + 1))
    (h_inv : a * ainv % N = 1)
    (hcop_a : Nat.Coprime a N) (hcop_ainv : Nat.Coprime ainv N)
    (hodd : Odd N) (h1 : 1 < N) :
    FormalRV.SQIRPort.probability_of_success a r N m (Nat.log2 (2 * N) + 1)
        (sqir_modmult_rev_anc (Nat.log2 (2 * N) + 1))
        (f_modmult_circuit_verified_bits a ainv N (Nat.log2 (2 * N) + 1))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
    ∧ (∑ i ∈ Finset.range m,
        tcount (sqir_modmult_MCP_gate (Nat.log2 (2 * N) + 1) N
          ((a ^ (2 ^ i)) % N) ((ainv ^ (2 ^ i)) % N)))
        = m * (112 * (Nat.log2 (2 * N) + 1) ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact Shor_correct_verified_no_modmult_axioms a r N m ainv h_basic_r h_inv
  · exact tcount_verified_modexp_chain a ainv N (Nat.log2 (2 * N) + 1) m
      hcop_a hcop_ainv hodd h1

/-! ## Anti-cheat gate: the build FAILS if these stop being axiom-clean. -/

#verify_clean shor_modexp_welded
#verify_clean tcount_verified_modexp_chain
#verify_clean shor_resource_welded

end FormalRV.BQAlgo
