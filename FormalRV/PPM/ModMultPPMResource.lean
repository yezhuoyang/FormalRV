/-
  FormalRV.PPM.ModMultPPMResource — END-TO-END semantically-verified PPM resource bound
  for the modular multiplier (the substantive mod-exp building block).

  Welds two proofs about the SAME Gate IR term `sqir_modmult_const_gate bits N a`:
    * SEMANTICS: `sqir_modmult_const_gate_target_decode` — it computes `(a · m) % N` into
      the accumulator register (no sorry, axiom-clean);
    * RESOURCE:  `tcount_sqir_modmult_const_gate_le` — its T-count is `≤ 56·bits²`, hence
      its Toffoli count is `≤ 8·bits²`, hence (through the verified `Gate → PPM` bridge)
      its PPM compilation uses `≤ 8·bits²` CCZ magic states.

  So the per-modmult factor of the un-windowed schoolbook count is no longer an abstract
  `def`: it is a proved upper bound on a circuit PROVED to multiply.  The relation to the
  whole-algorithm figure is exact: `16·n³ = 2n · (8·n²)`, i.e. (exponent register `2n`) ·
  (this per-modmult bound at `bits = n`).  Only the `×2n` mod-exp multiplicity — iterating
  the verified modmult into a verified modular exponentiation — remains structural; it is
  the one link of the 137-billion figure not yet welded to a verified circuit term.

  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.GateToPPMResource
import FormalRV.Arithmetic.SQIRModMult.ToffoliCount
import FormalRV.Arithmetic.SQIRModMult.ModExpCount
import FormalRV.Arithmetic.SQIRModMult.Proofs2

namespace FormalRV.PPM.ModMultPPMResource

open FormalRV.PPM.GateToPPMResource
open FormalRV.PPM.CircuitToPPMResource
open FormalRV.PPM.PPMResourceCount
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo

/-- Toffoli count of the verified modular multiplier `≤ 8·bits²` (from `tcount ≤ 56·bits²`
    and `tcount = 7·toffCount`). -/
theorem toffCount_sqir_modmult_const_gate_le (bits N a : Nat) :
    toffCount (sqir_modmult_const_gate bits N a) ≤ 8 * bits ^ 2 := by
  have h := tcount_sqir_modmult_const_gate_le bits N a
  rw [tcount_eq_seven_mul_toffCount] at h
  omega

/-- PPM CCZ-magic states to teleport-compile the verified modular multiplier `≤ 8·bits²`. -/
theorem numCCZMagic_sqir_modmult_const_gate_le (na bits N a : Nat) :
    numCCZMagic (circuitToPPM na (gateToHL (sqir_modmult_const_gate bits N a))) ≤ 8 * bits ^ 2 := by
  rw [numCCZMagic_circuitToPPM_gateToHL]
  exact toffCount_sqir_modmult_const_gate_le bits N a

/-- **END-TO-END SEMANTICALLY-VERIFIED PPM RESOURCE BOUND (modular multiplier).**

    For the verified out-of-place modular multiplier (under the SQIR sizing hypotheses),
    ONE Gate IR term simultaneously
    (a) computes `(a · m) % N` into the accumulator, AND
    (b) costs `≤ 8·bits²` CCZ magic states when compiled to PPM.
    Both conjuncts are about the SAME `sqir_modmult_const_gate bits N a`. -/
theorem verified_modmult_end_to_end
    (bits N a m : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (hm : m < 2 ^ bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m 0))
      = (a * m) % N
    ∧ numCCZMagic (circuitToPPM 0
          (gateToHL (sqir_modmult_const_gate bits N a))) ≤ 8 * bits ^ 2 :=
  ⟨sqir_modmult_const_gate_target_decode bits N a m hbits hN_pos hN hN2 hm,
   numCCZMagic_sqir_modmult_const_gate_le 0 bits N a⟩

/-! ## RSA-2048 instantiation of the verified per-modmult bound. -/

/-- At the RSA-2048 modulus width `bits = 2048`, the verified modular multiplier uses
    `≤ 8·2048² = 33 554 432` CCZ magic states.  Multiplying by the `2n = 4096` exponent
    register (structural, not welded) reproduces the whole-algorithm `137 438 953 472`. -/
theorem shor2048_per_modmult_CCZMagic_le (na N a : Nat) :
    numCCZMagic (circuitToPPM na (gateToHL (sqir_modmult_const_gate 2048 N a))) ≤ 33554432 := by
  have h := numCCZMagic_sqir_modmult_const_gate_le na 2048 N a
  norm_num at h
  exact h

-- 2n · (per-modmult bound) = the un-windowed whole-algorithm figure, exactly.
example : 4096 * 33554432 = 137438953472 := by norm_num

/-! ## §6. THE FULL CONCRETE MOD-EXP: EXACT (not bounded) PPM magic-state count.

    `shorModExp bits N a` is the concrete `Gate` IR chain of `2·bits` verified modular
    multipliers.  Its PPM CCZ-magic and measurement counts are EXACT closed forms in `bits`
    for every valid Shor base — i.e. provably equal to the count of the actual compiled
    circuit. -/

/-- EXACT Toffoli count of the concrete Shor mod-exp: `16·bits³` (from `tcount = 112·bits³`
    and `tcount = 7·toffCount`). -/
theorem toffCount_shorModExp (bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    toffCount (shorModExp bits N a) = 16 * bits ^ 3 := by
  have h := tcount_shorModExp bits N a hcop hodd h1
  rw [tcount_eq_seven_mul_toffCount] at h
  omega

/-- EXACT CCZ-magic count of the PPM-compiled concrete Shor mod-exp: `16·bits³`. -/
theorem numCCZMagic_shorModExp (na bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    numCCZMagic (circuitToPPM na (gateToHL (shorModExp bits N a))) = 16 * bits ^ 3 := by
  rw [numCCZMagic_circuitToPPM_gateToHL, toffCount_shorModExp bits N a hcop hodd h1]

/-- EXACT Z-basis Pauli-measurement count of the PPM-compiled concrete Shor mod-exp:
    `48·bits³`. -/
theorem numMeas_shorModExp (na bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    numMeas (circuitToPPM na (gateToHL (shorModExp bits N a))) = 48 * bits ^ 3 := by
  rw [numMeas_circuitToPPM_gateToHL, toffCount_shorModExp bits N a hcop hodd h1]; ring

/-- **THE SINGLE LITERAL RSA-2048 NUMBER — EXACT.**

    For ANY valid RSA-2048 base (`N` a 2048-bit odd modulus, `a` coprime to `N`), the
    concrete Shor modular-exponentiation circuit `shorModExp 2048 N a` compiles to EXACTLY
    `137 438 953 472` CCZ magic states (= its Toffoli count) and `412 316 860 416` Z-basis
    Pauli measurements.  This is `numCCZMagic` of the actual compiled PPM program — if you
    built and counted the circuit you would get exactly these numbers; the proof derives
    them by induction without ever building the 2048-bit term. -/
theorem shor2048_CCZMagic_exact (na N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    numCCZMagic (circuitToPPM na (gateToHL (shorModExp 2048 N a))) = 137438953472 := by
  rw [numCCZMagic_shorModExp na 2048 N a hcop hodd h1]; norm_num

theorem shor2048_Meas_exact (na N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    numMeas (circuitToPPM na (gateToHL (shorModExp 2048 N a))) = 412316860416 := by
  rw [numMeas_shorModExp na 2048 N a hcop hodd h1]; norm_num

end FormalRV.PPM.ModMultPPMResource
