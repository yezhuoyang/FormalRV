/-
  FormalRV.Arithmetic.ModExp.ModExpExample
  Worked instances of the verified modexp oracle family. OFF the default path.
-/
import FormalRV.Arithmetic.ModExp.ModExpCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.SQIRPort

/-- **Concrete instantiation: Shor's bound at N=15, a=7, ainv=13.**
Demonstrates that the canonical-dim theorem's hypotheses are
fully decidable for concrete small N — every hypothesis closes by
`decide`.  N=15 is the smallest non-prime odd N > 2 with a
nontrivial `Z*_N` structure (the standard Shor warm-up example);
a=7 is coprime to 15 with order 4 (`7^4 = 2401 ≡ 1 mod 15`);
ainv = 13 (since `7 * 13 = 91 = 6*15 + 1`). -/
example :
    FormalRV.SQIRPort.probability_of_success 7
        (FormalRV.SQIRPort.ord 7 15) 15
        (Nat.log2 (2 * 15^2)) (Nat.log2 (2 * 15))
        (adder_n_qubits (Nat.log2 (2 * 15) + 1) + 1)
        (our_modmult_family (Nat.log2 (2 * 15)) 15 7 13 (Nat.log2 (2 * 15)))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 15 : ℝ)^4 := by
  apply Shor_correct_with_our_family_at_canonical_dim
  · decide  -- 1 < 15
  · decide  -- 0 < 7
  · decide  -- 7 < 15
  · decide  -- Nat.Coprime 7 15
  · decide  -- Nat.Coprime 2 15
  · decide  -- 7 * 13 % 15 = 1


/-- **Concrete instantiation: Shor's bound at N=21, a=2, ainv=11.**
N=21 = 3·7 is the second-smallest non-prime odd composite useful for
Shor; a=2 has order 6 mod 21 (since 2^6 = 64 = 3·21 + 1); ainv = 11
(since 2 · 11 = 22 = 21 + 1).  As in Tick 33, every hypothesis closes
by `decide`. -/
example :
    FormalRV.SQIRPort.probability_of_success 2
        (FormalRV.SQIRPort.ord 2 21) 21
        (Nat.log2 (2 * 21^2)) (Nat.log2 (2 * 21))
        (adder_n_qubits (Nat.log2 (2 * 21) + 1) + 1)
        (our_modmult_family (Nat.log2 (2 * 21)) 21 2 11 (Nat.log2 (2 * 21)))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 21 : ℝ)^4 := by
  apply Shor_correct_with_our_family_at_canonical_dim
  · decide  -- 1 < 21
  · decide  -- 0 < 2
  · decide  -- 2 < 21
  · decide  -- Nat.Coprime 2 21
  · decide  -- Nat.Coprime 2 21 (the gcd(2, N) one)
  · decide  -- 2 * 11 % 21 = 1


/-! ## Double-verification: BOTH ModMult variants give a valid modexp oracle.

    Same generic modexp construction, N=3, a=2, a⁻¹=2 (since 2·2 ≡ 1 mod 3). Each
    `ModMulImpl` proof closes — the semantic correctness goes through for both
    modmults; they differ ONLY in the ancilla count. -/

/-- ✔ Gidney/Shor-layout modmult (`modMultInPlaceShor`) → valid modexp oracle,
ancilla `adder_n_qubits (3+1) + 1`. -/
example : FormalRV.SQIRPort.ModMulImpl 2 3 3 (adder_n_qubits (3 + 1) + 1)
            (our_modmult_family 3 3 2 2 3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    our_modmult_family_hypotheses_from_inverse 3 2 2 3 (by decide) (by decide) (by decide)
  exact our_modmult_family_ModMulImpl 3 3 2 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h1 h2 h3 h4 h5

/-- ✔ SQIR-layout modmult (`modmult_MCP_gate`) → valid modexp oracle, ancilla
`sqir_modmult_rev_anc 3`. Same N, a — only the ancilla count differs. -/
example : FormalRV.SQIRPort.ModMulImpl 2 3 3 (sqir_modmult_rev_anc 3)
            (modexpFamilyMCP 3 3 2 2) :=
  modexpFamilyMCP_ModMulImpl 3 3 2 2 (by decide) (by decide) (by decide) (by decide)
    (our_modmult_family_hypotheses_from_inverse 3 2 2 3 (by decide) (by decide) (by decide)).1


end FormalRV.BQAlgo
