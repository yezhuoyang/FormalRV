/-
  FormalRV.PPM.Resource.GateToPPMResource — weld the PPM resource count onto the SAME Gate IR
  term that carries a semantic-correctness proof.

  The honesty gap flagged by the semantic audit was: `ModExpToffoliCount`'s `16n³` is an
  ABSTRACT cost model, and the term fed to the PPM formula (`modmultBlock`) is an
  index-(0,1,2) repetition with NO semantics — so the count and the correctness ran on
  DIFFERENT terms.  This file closes that gap at the layer where a verified Gate IR term
  exists: it compiles an arbitrary `Gate` (the IR the arithmetic circuits are PROVED
  correct in) to the PPM front-end and shows the PPM CCZ-magic / measurement counts equal
  the Gate's own Toffoli count.  Applied to the verified Gidney adder, the result is a PPM
  resource count of the EXACT term proved to compute addition — genuinely end to end.

  ## What is and isn't end-to-end verified (honest)

  * VERIFIED end to end (this file): the n-bit Gidney adder
    `gidney_adder_full_faithful_no_measurement (n+2)` — the SAME `Gate` term is proved to
    write the correct sum bits (`gidney_adder_full_faithful_no_measurement_target_correct`,
    no sorry) AND its PPM resource cost is derived from its proved Toffoli count
    (`tcount_… = 14(n+2)` ⇒ `2(n+2)` Toffolis ⇒ `2(n+2)` CCZ magic states).
  * STILL a cost model (NOT welded): the full mod-exp `16n³` of `ModExpToffoliCount`.  The
    verified modular multiplier `modmult_MCP_gate` exists and is semantically proved,
    but it has no Toffoli-count theorem yet, and no Gate term iterates it `2n` times into a
    verified modular exponentiation.  So the 137-billion figure is an un-windowed upper
    bound, not a count read off a verified mod-exp circuit.  This file welds the adder
    building block; the modmult / mod-exp welds remain future work.

  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.Resource.CircuitToPPMResource
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPropagationReverse

namespace FormalRV.PPM.Resource.GateToPPMResource

open FormalRV.PPM.Resource.CircuitToPPMResource
open FormalRV.PPM.Resource.PPMResourceCount
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo

/-! ## §1. The Gate IR → PPM resource bridge.

    `Gate` (the IR the arithmetic circuits are verified in) has `CCX` as its only Toffoli,
    so a Gate's Toffoli count is exactly `tcount / 7`.  We compile each `CCX a b t` to
    `H·CCZ·H` (one CCZ magic state), `CX→CNOT`, `X→X`, `I→·`, and prove the PPM counts of
    the compiled program equal the Gate's Toffoli count. -/

/-- Toffoli (CCX) count of a Gate IR circuit. -/
def toffCount : Gate → Nat
  | .I => 0
  | .X _ => 0
  | .CX _ _ => 0
  | .CCX _ _ _ => 1
  | .seq g₁ g₂ => toffCount g₁ + toffCount g₂

/-- `tcount = 7 · toffCount`: each Toffoli is 7 T, everything else is 0. -/
theorem tcount_eq_seven_mul_toffCount (g : Gate) : tcount g = 7 * toffCount g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX c t => rfl
  | CCX a b t => rfl
  | seq g₁ g₂ ih₁ ih₂ => simp only [tcount, toffCount, ih₁, ih₂]; ring

/-- Compile a Gate IR circuit to the PPM front-end (`HLGate` list): every Toffoli becomes
    `H·CCZ·H`, `CX→CNOT`, `X→X`, `I` vanishes. -/
def gateToHL : Gate → List HLGate
  | .I => []
  | .X q => [.X q]
  | .CX c t => [.CNOT c t]
  | .CCX a b t => [.H t, .CCZ a b t, .H t]
  | .seq g₁ g₂ => gateToHL g₁ ++ gateToHL g₂

theorem cczMagic_sum_gateToHL (g : Gate) :
    ((gateToHL g).map gateCCZMagic).sum = toffCount g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX c t => rfl
  | CCX a b t => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
      simp only [gateToHL, List.map_append, List.sum_append, ih₁, ih₂, toffCount]

theorem meas_sum_gateToHL (g : Gate) :
    ((gateToHL g).map gateMeas).sum = 3 * toffCount g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX c t => rfl
  | CCX a b t => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
      simp only [gateToHL, List.map_append, List.sum_append, ih₁, ih₂, toffCount]; ring

/-- PPM CCZ-magic count of a compiled Gate IR circuit = its Toffoli count. -/
theorem numCCZMagic_circuitToPPM_gateToHL (na : Nat) (g : Gate) :
    numCCZMagic (circuitToPPM na (gateToHL g)) = toffCount g := by
  rw [numCCZMagic_circuitToPPM, cczMagic_sum_gateToHL]

/-- PPM Pauli-measurement count of a compiled Gate IR circuit = `3 ×` its Toffoli count. -/
theorem numMeas_circuitToPPM_gateToHL (na : Nat) (g : Gate) :
    numMeas (circuitToPPM na (gateToHL g)) = 3 * toffCount g := by
  rw [numMeas_circuitToPPM, meas_sum_gateToHL]

/-! ## §2. The verified adder, END TO END: PPM cost of the SAME term proved to add. -/

/-- Toffoli count of the verified Gidney adder = `2(n+2)`, derived from its proved
    T-count `14(n+2)` (`tcount_gidney_adder_full_faithful_no_measurement`) via `7 T`/Toffoli. -/
theorem toffCount_gidney_adder (n : Nat) :
    toffCount (gidney_adder_full_faithful_no_measurement (n + 2)) = 2 * (n + 2) := by
  have h := tcount_gidney_adder_full_faithful_no_measurement n
  rw [tcount_eq_seven_mul_toffCount] at h
  omega

/-- PPM CCZ-magic states to teleport-compile the verified adder = `2(n+2)`. -/
theorem verified_adder_ppm_CCZMagic (na n : Nat) :
    numCCZMagic (circuitToPPM na (gateToHL (gidney_adder_full_faithful_no_measurement (n + 2))))
      = 2 * (n + 2) := by
  rw [numCCZMagic_circuitToPPM_gateToHL, toffCount_gidney_adder]

/-- PPM Pauli measurements to teleport-compile the verified adder = `6(n+2)`. -/
theorem verified_adder_ppm_Meas (na n : Nat) :
    numMeas (circuitToPPM na (gateToHL (gidney_adder_full_faithful_no_measurement (n + 2))))
      = 6 * (n + 2) := by
  rw [numMeas_circuitToPPM_gateToHL, toffCount_gidney_adder]; ring

/-- **END-TO-END SEMANTICALLY-VERIFIED PPM RESOURCE COUNT (adder).**

    For the verified `n`-bit (`n ≥ 2`) Gidney adder, ONE Gate IR term simultaneously
    (a) computes the correct sum bits on the standard two-operand encoding, and
    (b) has PPM resource cost `2(n+2)` CCZ magic states + `6(n+2)` Z-basis measurements.
    Both conjuncts are about the SAME `gidney_adder_full_faithful_no_measurement (n+2)`. -/
theorem verified_adder_end_to_end
    (n a b : Nat) (hn : 1 < n + 2) (ha : a < 2 ^ (n + 2)) (hb : b < 2 ^ (n + 2)) :
    (∀ i, i < n + 2 →
        Gate.applyNat (gidney_adder_full_faithful_no_measurement (n + 2))
          (adder_input_F (n + 2) a b) (target_idx i)
        = adder_sum_bit_classical a b i)
    ∧ numCCZMagic (circuitToPPM 0
          (gateToHL (gidney_adder_full_faithful_no_measurement (n + 2)))) = 2 * (n + 2)
    ∧ numMeas (circuitToPPM 0
          (gateToHL (gidney_adder_full_faithful_no_measurement (n + 2)))) = 6 * (n + 2) :=
  ⟨gidney_adder_full_faithful_no_measurement_target_correct (n + 2) a b hn ha hb,
   verified_adder_ppm_CCZMagic 0 n,
   verified_adder_ppm_Meas 0 n⟩

end FormalRV.PPM.Resource.GateToPPMResource
