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
  `def`: it is a proved upper bound on a circuit PROVED to multiply.  Later sections make
  these EXACT (`= 56·bits²`/`112·bits²`) for valid Shor bases, bind the count to the actual
  verified oracle `sqir_modmult_MCP_gate` (§7), and count the whole arithmetic mod-exp on
  that oracle (§8 → `32·bits³` Toffolis, `274 877 906 944` at 2048).

  ## Honest note on the control overhead (why the arithmetic count is the clean one)

  The verified Shor algorithm's modular exponentiation is `controlled_powers m u`, which
  applies the GENERIC `control i` (UnitaryOps) to each oracle.  `control` of a CNOT is a
  Toffoli, but `control` of a rotation is `controlled_R`, which emits `R(±θ/2)`.  Since the
  oracle's Toffolis are decomposed to `7·T` (BaseUCom.CCX) before control, controlling a `T`
  (θ=π/4) yields `R(π/8)` — NOT a Clifford+T angle.  So the FULL controlled mod-exp is not a
  Clifford+T circuit, and a magic-state count of it is ill-posed for this implementation
  without an extra rotation-synthesis layer.  The clean, exact, Clifford+T resource is the
  ARITHMETIC (uncontrolled-oracle) count here; claiming a single magic-state number for the
  generic-control overhead would be unsound, so it is deliberately excluded and flagged.

  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.GateToPPMResource
import FormalRV.Arithmetic.SQIRModMult.ToffoliCount
import FormalRV.Arithmetic.SQIRModMult.ModExpCount
import FormalRV.Arithmetic.SQIRModMult.Proofs2
import FormalRV.Arithmetic.SQIRModMult.Proofs3

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

/-! ## §7. Count welded onto the ACTUAL verified Shor oracle term `sqir_modmult_MCP_gate`.

    The verified Shor theorem `Shor_correct_verified_no_modmult_axioms` uses
    `f_modmult_circuit_verified_bits → sqir_modmult_MCP_gate` (the in-place modular
    multiplier) as its oracle, and that whole theorem is axiom-clean / sorry-free.  Here the
    EXACT Toffoli count is bound to THAT same term, paired with its semantic proof
    `sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty`. -/

theorem toffCount_sqir_modmult_MCP_gate (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    toffCount (sqir_modmult_MCP_gate bits N a ainv) = 16 * bits ^ 2 := by
  have h := tcount_sqir_modmult_MCP_gate_shor bits N a ainv hcop hcopinv hpos hlt hodd h1
  rw [tcount_eq_seven_mul_toffCount] at h
  omega

/-- **END-TO-END on the ACTUAL verified Shor oracle.**  ONE term `sqir_modmult_MCP_gate
    bits N a ainv` simultaneously (a) computes `|x⟩ ↦ |a·x mod N⟩` (its `Gate.toUCom`
    satisfies `MultiplyCircuitProperty` — the property the verified Shor algorithm relies
    on) and (b) costs EXACTLY `16·bits²` CCZ magic states in PPM. -/
theorem verified_MCP_oracle_end_to_end
    (bits N a ainv : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hodd : Odd N) (h1 : 1 < N) (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (sqir_modmult_rev_anc bits)
        (Gate.toUCom (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv))
    ∧ numCCZMagic (circuitToPPM 0 (gateToHL (sqir_modmult_MCP_gate bits N a ainv)))
        = 16 * bits ^ 2 :=
  ⟨sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2
      (le_of_lt hlt) h_inv,
   by rw [numCCZMagic_circuitToPPM_gateToHL,
          toffCount_sqir_modmult_MCP_gate bits N a ainv hcop hcopinv hpos hlt hodd h1]⟩

/-! ## §8. Whole mod-exp ARITHMETIC magic-state count on the verified in-place oracle.

    `shorModExpVerified` chains `2·bits` of the verified MCP oracle.  Its PPM CCZ-magic count
    is EXACTLY `32·bits³` — the arithmetic (data) magic states of the verified Shor circuit.
    (This is the Clifford+T arithmetic cost; see the file header note: the generic `control`
    of `controlled_powers` is non-Clifford+T, so the control overhead is a separate regime
    not included here.) -/

theorem toffCount_shorModExpVerified (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    toffCount (shorModExpVerified bits N a ainv) = 32 * bits ^ 3 := by
  have h := tcount_shorModExpVerified bits N a ainv hcop hcopinv hpos hlt hodd h1
  rw [tcount_eq_seven_mul_toffCount] at h
  omega

theorem numCCZMagic_shorModExpVerified (na bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    numCCZMagic (circuitToPPM na (gateToHL (shorModExpVerified bits N a ainv))) = 32 * bits ^ 3 := by
  rw [numCCZMagic_circuitToPPM_gateToHL, toffCount_shorModExpVerified bits N a ainv hcop hcopinv hpos hlt hodd h1]

/-- **RSA-2048 arithmetic magic states on the verified oracle**: `32·2048³ = 274 877 906 944`. -/
theorem shor2048_CCZMagic_verified (na N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    numCCZMagic (circuitToPPM na (gateToHL (shorModExpVerified 2048 N a ainv))) = 274877906944 := by
  rw [numCCZMagic_shorModExpVerified na 2048 N a ainv hcop hcopinv hpos hlt hodd h1]; norm_num

end FormalRV.PPM.ModMultPPMResource
