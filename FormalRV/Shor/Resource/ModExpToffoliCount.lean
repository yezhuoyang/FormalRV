/-
  FormalRV.Shor.ModExpToffoliCount — a SINGLE LITERAL Toffoli/PPM-resource number
  for factoring RSA-2048, derived layer by layer and fed into the proved PPM formula.

  ## What this delivers

  A closed-form Toffoli count for full Shor modular exponentiation on an `n`-bit
  modulus, built UP from the one adder the repo has a no-sorry parametric Toffoli
  count for (Gidney 2018 ripple-carry), instantiated at `n = 2048`, and pushed
  through the already-proved PPM resource formula
  (`CircuitToPPMResource.modmult_CCZMagic`/`modmult_Meas`) to a literal magic-state
  and Pauli-measurement count.

      adder            = 2n      Toffolis   (PROVED: tcount_gidney_adder_full = 14n T, 7 T/Toffoli)
      ctrl-mod-add     = 4·adder = 8n       (4 sub-blocks of sqir_style_controlledModAddConst_candidate)
      ctrl-mod-mult    = n·(ctrl-mod-add) = 8n²   (n multiplier bits, modmult_prefix_gate)
      mod-exp          = 2n·(ctrl-mod-mult) = 16n³ (2n exponent-register control qubits)

      n = 2048  ⇒  16·2048³ = 137 438 953 472 Toffolis
                ⇒  numCCZMagic = 137 438 953 472 magic states
                ⇒  numMeas     = 412 316 860 416 Z-basis Pauli measurements

  ## Honest tiering (per CLAUDE.md hard rules — do not overclaim)

  * VERIFIED: the adder unit `2n` is the proved Gidney-adder Toffoli count
    (`adderToff_eq` binds it to `tcount_gidney_adder_full`, no sorry); the
    Toffoli→{magic state, measurement} step is the fully-proved PPM formula
    (induction over the gate list, no `decide` on a 137-billion-element list).
  * SCAFFOLDED: the composition multiplicities (×4, ×n, ×2n) are read off the
    repo's circuit `def`s (`sqir_style_controlledModAddConst_candidate`,
    `modmult_prefix_gate`, the 2n exponent register), whose FULL semantic
    correctness is only partially established (flag-dirty disclosures in
    `CuccaroSQIRDirtyFlag`).  Treating compare/sub as adder-equivalent is a
    structural approximation, not a separately-proved per-block Toffoli count.
  * This is an UN-WINDOWED schoolbook UPPER BOUND.  `16n³ = 1.374·10¹¹` is ≈51×
    Gidney–Ekerå 2021's published windowed `2.7·10⁹` (≈0.3n³, recorded in
    `PaperClaims.gidney_ekera_2021_RSA2048_toffolis_billions`).  The gap is exactly
    the windowing + coset-representative + measurement-uncompute optimizations this
    construction deliberately omits — see §4 for the same formula evaluated at the
    published windowed count, and the ratio.

  UPDATE — the lower layers are now WELDED to verified circuit terms:
  `PPM/GateToPPMResource.verified_adder_end_to_end` (the adder computes a+b AND costs
  2(n+2) magic states, ONE term) and `PPM/ModMultPPMResource.verified_modmult_end_to_end`
  (the modular multiplier `modmult_const_gate` computes (a·m) % N AND costs ≤ 8·bits²
  magic states, ONE term).  Since `16n³ = 2n · (8n²)`, the per-modmult factor of the
  figure below is now a PROVED bound on a circuit PROVED to multiply; only the `×2n`
  exponent-register multiplicity (iterating the verified modmult into a verified mod-exp)
  remains structural.

  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.Resource.CircuitToPPMResource
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderForwardAndCost

namespace FormalRV.Shor.ModExpToffoliCount

open FormalRV.PPM.Resource.CircuitToPPMResource
open FormalRV.PPM.Resource.PPMResourceCount
open FormalRV.BQAlgo
open FormalRV.Framework.Gate

/-! ## §1. The per-layer Toffoli cost, built up from the PROVED adder unit. -/

/-- Toffoli count of one `n`-bit Gidney ripple-carry adder = `2n`. -/
def adderToff (n : Nat) : Nat := 2 * n

/-- The `2n` is the PROVED Toffoli count of the **semantically-correct** Gidney adder:
    `7·adderToff (n+2) = tcount (gidney_adder (n+2)) = 14(n+2)` (7 T per Toffoli, `2(n+2)`
    Toffolis).  **Rebound** to the faithful, basis-state-proven adder
    (`gidney_adder` = `gidney_adder_full_faithful_no_measurement`) via
    `tcount_gidney_adder_full_faithful_no_measurement` — no longer the cost-only skeleton. -/
theorem adderToff_eq (n : Nat) :
    7 * adderToff (n + 2) = tcount (gidney_adder (n + 2)) := by
  unfold gidney_adder
  rw [tcount_gidney_adder_full_faithful_no_measurement]; unfold adderToff; ring

/-- Controlled modular addition: 4 adder-equivalent sub-blocks (conditional-add,
    compare, conditional-sub, controlled-compare) — the structure of
    `sqir_style_controlledModAddConst_candidate`. -/
def ctrlModAddToff (n : Nat) : Nat := 4 * adderToff n

/-- Controlled modular multiplication: shift-and-accumulate, `n` controlled modular
    additions (one per multiplier bit) — `modmult_prefix_gate`. -/
def ctrlModMultToff (n : Nat) : Nat := n * ctrlModAddToff n

/-- Modular exponentiation: `2n` controlled modular multiplications (one per
    full-precision exponent-register control qubit). -/
def modExpToff (n : Nat) : Nat := 2 * n * ctrlModMultToff n

/-- Closed form: `modExpToff n = 16·n³`. -/
theorem modExpToff_closed (n : Nat) : modExpToff n = 16 * n ^ 3 := by
  unfold modExpToff ctrlModMultToff ctrlModAddToff adderToff; ring

/-! ## §2. THE SINGLE LITERAL RSA-2048 NUMBER. -/

/-- RSA-2048 modulus bit-width. -/
def shor2048Toff : Nat := modExpToff 2048

/-- The literal Toffoli count: `16·2048³ = 137 438 953 472`. -/
theorem shor2048Toff_eq : shor2048Toff = 137438953472 := by
  unfold shor2048Toff; rw [modExpToff_closed]; norm_num

/-! ## §3. Fed into the PROVED PPM resource formula ⇒ literal PPM resources.

    `modmult_CCZMagic`/`modmult_Meas` hold for ANY Toffoli count by induction, so the
    137-billion figure drops in with only an `rw` — no list of that length is ever
    built or evaluated. -/

/-- CCZ magic states consumed by the PPM-compiled Shor-2048 = the Toffoli count. -/
theorem shor2048_CCZMagic :
    numCCZMagic (circuitToPPM 8 (modmultBlock shor2048Toff 0)) = 137438953472 := by
  rw [modmult_CCZMagic, shor2048Toff_eq]

/-- Z-basis (syndrome) Pauli measurements = 3 × Toffoli count = `412 316 860 416`. -/
theorem shor2048_Meas :
    numMeas (circuitToPPM 8 (modmultBlock shor2048Toff 0)) = 412316860416 := by
  rw [modmult_Meas, shor2048Toff_eq]

/-! ## §4. Cross-check: the SAME proved formula at GE2021's published windowed count.

    `PaperClaims.gidney_ekera_2021_RSA2048_toffolis_billions` records 2.7·10⁹ Toffolis
    (≈0.3n³).  Feeding it through the identical formula gives the windowed PPM totals;
    the ratio to §3 is the un-windowed-vs-windowed optimization headroom. -/

theorem shor2048_CCZMagic_GE2021published :
    numCCZMagic (circuitToPPM 8 (modmultBlock 2700000000 0)) = 2700000000 := by
  rw [modmult_CCZMagic]

theorem shor2048_Meas_GE2021published :
    numMeas (circuitToPPM 8 (modmultBlock 2700000000 0)) = 8100000000 := by
  rw [modmult_Meas]

/-- The un-windowed upper bound is ≈51× the GE2021 published windowed count
    (`137438953472 = 50·2700000000 + 2438953472`, i.e. ratio 50.9). -/
theorem shor2048_vs_GE2021_gap :
    shor2048Toff = 50 * 2700000000 + 2438953472 := by
  rw [shor2048Toff_eq]

-- Resource vector (un-windowed): (Toffolis = CCZ magic states, Pauli measurements).
#eval (shor2048Toff, 3 * shor2048Toff)        -- (137438953472, 412316860416)
-- GE2021 windowed cross-check: (magic states, measurements).
#eval (2700000000, 3 * 2700000000)            -- (2700000000, 8100000000)

end FormalRV.Shor.ModExpToffoliCount
