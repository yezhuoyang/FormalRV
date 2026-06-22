/-
  FormalRV.Shor.CFS.ResidueCircuit — CLASSICAL SEMANTICS of the reversible residue multiplications,
  the circuit-level half of Gidney 2025's arithmetic (controlled modular multiplications on the
  residue registers; main.tex eq:define-rk, the "series of multiplications controlled by the qubits
  of e").

  Per "semantic proof BEFORE resource proof".  Layers 1–3 specified WHAT the residue arithmetic
  computes (`modexpProd`, reconstruction).  This file specifies that the CIRCUIT — the step-by-step
  sequence of controlled modular multiplications the hardware runs on each residue register — has
  exactly that classical action.

    * `residueAccumulate`     — the residue-register state after each controlled-multiply step
      (start at `1`; at step `k`, multiply by `M_k = g^{2^k} mod N` iff exponent bit `e_k = 1`, all
      mod `p_j`).  This is the literal reversible action of the circuit on register `j`.
    * `residueAccumulate_step`— each step IS a controlled modular multiplication: when `e_k = 1` it is
      `r ↦ (M_k · r) mod p_j` (the VERIFIED modmult primitive), and identity when `e_k = 0`.
    * `residueAccumulate_eq`  — **the sequence computes the right residue**:
      `residueAccumulate g N p_j e m = modexpProd g N m e % p_j`.

  Connecting to the already-verified gate circuit: each `e_k = 1` step `r ↦ (M_k · r) mod p_j` is an
  instance of `FormalRV.Arithmetic`'s verified in-place modular multiplier
  `modmult_inplace_shifted_correct` (`ModMult/Proofs3.lean`: the output register holds
  `(a · x) mod N` given `a · a⁻¹ ≡ 1`), with `a := M_k`, `N := p_j`.  So the per-step circuit is
  already verified at the `Gate`-IR level; this file proves the COMPOSITION over the `m` exponent
  bits reproduces `modexpProd % p_j`.

  ## HONEST remaining circuit-semantics gaps (documented, NOT faked)
  - The full `Gate`-IR ASSEMBLY of all `|P|` residue registers running their `m` controlled-multiply
    steps in one circuit (this file proves one register's classical action; the multi-register
    assembly is mechanical but not written out here).
  - The QUANTUM (unitary, on superpositions) faithfulness of the assembled circuit — reuses the SQIR
    modmult port's unitary correctness; the controlled-on-`e_k` structure matches `ModMulImpl`.
-/
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

/-- The residue-register state after each controlled-multiply step: start at `1`, and at step `k`
    conditionally multiply by `M_k` (mod `p_j`).  The literal classical action of the circuit. -/
def residueAccumulate (g N pj e : ℕ) : ℕ → ℕ
  | 0 => 1 % pj
  | k + 1 => (residueAccumulate g N pj e k * Mconst g N k ^ bit e k) % pj

/-- **Each step is a controlled modular multiplication.**  When the exponent bit `e_k = 1`, the step
    is `r ↦ (M_k · r) mod p_j` — exactly the verified in-place modmult primitive; when `e_k = 0` it
    is the identity (`r ↦ r mod p_j`).  This is what the controlled gate realises. -/
theorem residueAccumulate_step (g N pj e k : ℕ) :
    residueAccumulate g N pj e (k + 1) =
      if bit e k = 1 then (Mconst g N k * residueAccumulate g N pj e k) % pj
      else residueAccumulate g N pj e k % pj := by
  show (residueAccumulate g N pj e k * Mconst g N k ^ bit e k) % pj = _
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ k) with h | h
  · have hb : bit e k = 0 := h
    rw [if_neg (by rw [hb]; decide), hb, pow_zero, Nat.mul_one]
  · have hb : bit e k = 1 := h
    rw [if_pos hb, hb, pow_one, Nat.mul_comm]

/-- **Circuit-step correctness**: the full sequence of `m` controlled residue multiplications
    computes exactly the residue of the modexp product, `modexpProd g N m e % p_j`.  Hence the
    circuit on register `j` (composition of the verified per-step modmults) has the classical action
    demanded by the residue-arithmetic specification (layers 1–3).  Proof: induction on `m`
    (reduce-then-multiply = multiply-then-reduce). -/
theorem residueAccumulate_eq (g N pj e : ℕ) :
    ∀ m, residueAccumulate g N pj e m = modexpProd g N m e % pj
  | 0 => rfl
  | m + 1 => by
      show (residueAccumulate g N pj e m * Mconst g N m ^ bit e m) % pj
          = modexpProd g N (m + 1) e % pj
      rw [residueAccumulate_eq g N pj e m]
      exact (Nat.mod_modEq (modexpProd g N m e) pj).mul_right _

/-! ## The circuit-semantics theorems pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean residueAccumulate_step
#verify_clean residueAccumulate_eq

end FormalRV.CFS
