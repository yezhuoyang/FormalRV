/-
  FormalRV.PPM.Gadgets.ModExp.ShorOracleModExpPPM — per-ITERATE compiled-PPM
  semantic correctness for the SECOND modular-exponentiation implementation:
  the Gidney-adder Shor-layout family `our_modmult_family` (squared-power
  family over `modMultInPlaceShor`).

  Iterate `i` of the family is
      our_modmult_family bits N a ainv multBits i
        = Gate.toUCom … (modMultInPlaceShor bits N (a^(2^i) % N) (ainv^(2^i) % N) multBits)
  and this file proves the compiled PPM program of that gate observes
  `x ↦ (a^(2^i) · x) mod N`, for EVERY iterate, from the minimal
  hypotheses (`1 < N`, `N` odd via `Coprime 2 N`, `a·ainv ≡ 1`) — all the
  per-iterate side conditions are derived by the existing bundled generator
  `our_modmult_family_hypotheses_from_inverse`.

  Together with `SqirModExpPPM` this covers BOTH verified modexp
  implementations, per John's "support all existing implementations"
  directive.  The QPE control structure above the iterates stays at the
  unitary layer (honest boundary).

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.ModMul.ShorOracleModMulPPM
import FormalRV.Arithmetic.ModExp.ModExpCorrectness

namespace FormalRV.PPM.Gadgets.ModExpPPM

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.PPM.Gadgets.ModMulPPM

/-- **Every iterate of the Gidney/Shor-layout modexp family, compiled by
    any contract compiler, observes `x ↦ (a^(2^i)·x) mod N`.** -/
theorem shorOracleModExp_iterate_compiles_to_PPM (S : PPMCompilerSpec)
    (bits N a ainv multBits i x : Nat)
    (hbits : 1 ≤ bits) (hN : N ≤ 2 ^ bits)
    (h_multBits_le : multBits ≤ bits + 1)
    (h_multBits_pos : 0 < multBits)
    (h_N_le_pow_multBits : N ≤ 2 ^ multBits)
    (h_N_gt_one : 1 < N)
    (h_cop_two : Nat.Coprime 2 N)
    (h_inv : a * ainv % N = 1) (hx : x < N) :
    S.Observes
      (S.compile (modMultInPlaceShor bits N (a ^ 2 ^ i % N) (ainv ^ 2 ^ i % N) multBits))
      (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1) x)
      (encodeDataZeroAnc multBits (adder_n_qubits (bits + 1) + 1)
        ((a ^ 2 ^ i * x) % N)) := by
  have hN_pos : 0 < N := by omega
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    our_modmult_family_hypotheses_from_inverse N a ainv multBits
      h_N_gt_one h_cop_two h_inv
  have h := shorOracleModMul_compiles_to_PPM S bits N
      (a ^ 2 ^ i % N) (ainv ^ 2 ^ i % N) multBits x
      hbits hN_pos hN h_multBits_le h_multBits_pos h_N_le_pow_multBits
      (h2 i) (Nat.mod_lt _ hN_pos) (h3 i) (Nat.mod_lt _ hN_pos)
      (h1 i) hx (h4 i) (h5 i)
  rwa [Nat.mod_mul_mod] at h

end FormalRV.PPM.Gadgets.ModExpPPM
