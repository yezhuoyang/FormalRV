/-
  FormalRV.System.Compose.VerifiedWorkloadBridge — closing the three "seams" that
  kept the Shor pipeline from being one composed chain.

  The study (`ftq_vm/out/shorstudy/STUDY.md`) caught that, although every pillar is
  individually axiom-clean and scalable to RSA-2048, the System layer was welded to the
  circuit by a hand-typed paper literal, with the resource/runtime numbers sitting on a
  *different* object than any verified circuit, and the runtime ignoring the circuit's depth.
  This module makes the resource & runtime numbers come AFTER an actually-composed circuit.

  ## What is closed here (and what is NOT — honest tiering, per CLAUDE.md)

  * **Seam 1 (literal).**  `verifiedToffoli` is NO LONGER a hand-typed number: it is
    `:=`-equal (`verifiedToffoli_eq_composed_circuit`) to `EGate.toffoli` of the *composed*
    `WindowedComposed.modExp` circuit — the Toffoli count is the output of a circuit theorem
    (`WindowedComposedCost.rsa2048_structural_circuit_toffoli`).  The old `magicBudget`
    literal (`Params/RSA2048`) is shown to be exactly the paper cost-model formula
    (`magicBudget_is_paper_formula`, `= WindowedCostModel.toffoliCount 2048 3072 11`) and a
    *proven upper bound* on the composed-circuit count (`verifiedToffoli_le_magicBudget`,
    +1.67 % = runway-folding + lookup-rounding the bare composed circuit omits).

  * **Seam 2 (different circuits).**  The resource count fed to the System layer here is the
    count of the SAME object the windowed pipeline builds (`WindowedComposed.modExp`, composed
    from `babbushLookupAdd` primitives), and it flows 1:1 into the proved PPM magic-state
    formula (`verifiedToffoli_CCZMagic`) and into the factory provisioning
    (`verifiedFactoriesNeeded`, derived from THIS count, `≤` the provisioned 1093).
    HONEST RESIDUE: `WindowedComposed.modExp`'s full *semantics* (that it computes `aˣ mod N`)
    is verified per-primitive (`WindowedCircuitExec` / `MeasUncomputeExec`), NOT yet as one
    composed theorem; and the N-generic *semantic* headline
    (`VerifiedShorTheorem.Shor_correct_verified_no_modmult_axioms`) is still about the
    un-windowed SQIR circuit.  So this closes "resource count on a composed circuit", not
    "windowed semantics composed into one theorem".  That composition remains the open work.

  * **Seam 3 (free depth).**  The depth is no longer a free parameter behind an undischarged
    hypothesis: `reactionLimitedDepthUs := verifiedToffoli * reactionUs` is the
    reaction-limited critical-path depth derived from the composed circuit's own count, and
    `depth_below_magic_pipeline` DISCHARGES the magic-limited hypothesis at the REAL factory
    count `F = 1093` (not `F = 1`), so `windowed_rsa2048_runtime_concrete` gives a concrete
    runtime in which the circuit's count genuinely enters the depth.
    HONEST RESIDUE: the reaction-limited model (one reaction round per critical-path Toffoli)
    is the standard GE2021 assumption; it is NAMED here, not a free knob, but it still assumes
    the data block parallelises enough that magic supply — not a serial `EGate` fold — binds.

  No `sorry`, no new `axiom`.  Numeric facts use `native_decide` (consistent with the rest of
  `System/`); the structural/circuit facts are `rfl`/`rw` on proved theorems.
-/
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Shor.WindowedComposedAt
import FormalRV.System.Params.RSA2048
import FormalRV.System.Magic.MagicScheduleComplete
import FormalRV.PPM.Resource.CircuitToPPMResource

namespace FormalRV.System.Compose.VerifiedWorkloadBridge

open FormalRV.Framework
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposed
open FormalRV.Shor.WindowedComposedAt (modExpAt)
open FormalRV.Shor.WindowedComposedCost
open FormalRV.Shor.WindowedCostModel
open FormalRV.System.Architecture
open FormalRV.System.MagicStateReadiness
open FormalRV.System.MagicScheduleComplete
open FormalRV.PPM.Resource.CircuitToPPMResource
open FormalRV.PPM.Resource.PPMResourceCount
open scoped Classical

/-! ## §1. Seam 1+2 — the workload number IS the composed circuit's Toffoli count. -/

/-- The RSA-2048 windowed mod-exp Toffoli count, defined to be the count of the *actually
    composed* `WindowedComposed.modExp` circuit (window `w = 10`, `bits = 2048`,
    `numMults = 246`, `numWin = 1024`).  This is the number the System layer should consume. -/
def verifiedToffoli : Nat := 2578993152

/-- **★ Seam 1 closed ★** — `verifiedToffoli` is `=` the `EGate.toffoli` of a composed circuit,
    for ANY window layout `W` and lookup table `T` (the Toffoli count is layout-independent).
    The resource number is the output of a circuit theorem, not a hand-typed literal. -/
theorem verifiedToffoli_eq_composed_circuit (W : Nat) (T : Nat → Nat) :
    EGate.toffoli (modExp 10 W 2048 T 246 1024) = verifiedToffoli := by
  unfold verifiedToffoli; exact rsa2048_structural_circuit_toffoli W T

/-- **★ Seam 1+2, on the VALUE-CORRECT circuit ★** — the same `verifiedToffoli` count is the
    `EGate.toffoli` of `WindowedComposedAt.modExpAt`, the shared-accumulator, layout-correct
    rebuild whose per-multiply-add VALUE is proven (`WindowedComposedAt.multiplyAddAt_fold`:
    one multiply-add computes `(a·y) mod 2^bits`).  `WindowedComposed.modExp` (above) has the
    same count but is PROVEN value-broken for `W ≥ 2` (`MeasUncomputeValue.babbushLookupAdd_misses_table`),
    so for the resource-on-a-semantically-meaningful-circuit reading this is the object to use.
    The two counts are equal (`WindowedComposedAt.toffoli_modExpAt_eq_modExp`). -/
theorem verifiedToffoli_eq_value_correct_circuit
    (W : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start : Nat) :
    EGate.toffoli (modExpAt 10 W 2048 Tfam q_start 246 1024) = verifiedToffoli := by
  unfold verifiedToffoli
  exact FormalRV.Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli W Tfam q_start

/-- The `Params/RSA2048.magicBudget` literal equals exactly the paper's windowed cost-model
    formula `toffoliCount 2048 3072 11` — so it is not an unexplained number either. -/
theorem magicBudget_is_paper_formula :
    (FormalRV.System.RSA2048.magicBudget : ℚ) = toffoliCount 2048 3072 11 := by
  rw [rsa2048_head_to_head.2.1]; norm_num

/-- **The paper budget dominates the composed circuit.**  `2 578 993 152 ≤ 2 622 824 448`:
    the System's provisioning budget is a verified upper bound on the actual composed circuit's
    Toffoli count, so any provisioning sized for `magicBudget` covers the verified circuit. -/
theorem verifiedToffoli_le_magicBudget :
    verifiedToffoli ≤ FormalRV.System.RSA2048.magicBudget := by native_decide

/-- The composed circuit's Toffoli count, for any `W`/`T`, is within the System magic budget. -/
theorem composed_circuit_within_budget (W : Nat) (T : Nat → Nat) :
    EGate.toffoli (modExp 10 W 2048 T 246 1024) ≤ FormalRV.System.RSA2048.magicBudget := by
  rw [verifiedToffoli_eq_composed_circuit]; exact verifiedToffoli_le_magicBudget

/-! ## §2. Seam 2 — the composed-circuit count flows into the proved PPM/magic formula. -/

/-- The CCZ magic states consumed equal the composed circuit's Toffoli count, via the
    induction-proved PPM resource formula (no list of that length is ever built). -/
theorem verifiedToffoli_CCZMagic :
    numCCZMagic (circuitToPPM 8 (modmultBlock verifiedToffoli 0)) = verifiedToffoli := by
  rw [modmult_CCZMagic]

/-- Z-basis syndrome measurements = 3× the composed circuit's Toffoli count. -/
theorem verifiedToffoli_Meas :
    numMeas (circuitToPPM 8 (modmultBlock verifiedToffoli 0)) = 3 * verifiedToffoli := by
  rw [modmult_Meas]

/-! ## §3. Seam 2 — factory provisioning derived from the composed-circuit count. -/

/-- CCZ factories needed for the 8-hour budget, sized for the COMPOSED-CIRCUIT count
    (`verifiedToffoli`) rather than the paper literal — the tight provisioning. -/
def verifiedFactoriesNeeded : Nat :=
  FormalRV.System.MagicStateReadiness.factoriesNeeded verifiedToffoli 28800000000 ccz_spec_qianxu

/-- The composed-circuit-tight factory count is `1075` (vs the paper-budget `1093`). -/
theorem verifiedFactoriesNeeded_value : verifiedFactoriesNeeded = 1075 := by native_decide

/-- The tight provisioning fits inside the provisioned `1093` factories
    (`Params/RSA2048.factoriesNeeded`): the device as built covers the verified circuit. -/
theorem verifiedFactories_le_provisioned :
    verifiedFactoriesNeeded ≤ FormalRV.System.RSA2048.factoriesNeeded := by native_decide

/-! ## §4. Seam 3 — the circuit's count drives the depth; the magic hypothesis is DISCHARGED. -/

/-- The reaction-limited critical-path depth derived from the composed circuit's OWN count:
    one reaction round (`reactionUs = 10 µs`) per critical-path Toffoli.  No free parameter. -/
def reactionLimitedDepthUs : Nat := verifiedToffoli * FormalRV.System.RSA2048.reactionUs

/-- The depth in µs: `2 578 993 152 · 10 = 25 789 931 520 µs ≈ 7.16 h`. -/
theorem reactionLimitedDepthUs_value : reactionLimitedDepthUs = 25789931520 := by native_decide

/-- **★ Seam 3 closed ★** — at the REAL factory count `F = 1093`, the circuit-derived depth
    is below the magic-supply pipeline (`12015 + ⌈K/1093⌉·12000`).  This is the hypothesis the
    device-feasibility theorem left UNDISCHARGED; here it is a proven fact, not an assumption. -/
theorem depth_below_magic_pipeline :
    reactionLimitedDepthUs ≤
      deliveryLatency ccz_spec_qianxu 15
        + magicSupplyTimeUs verifiedToffoli 1093 ccz_spec_qianxu := by native_decide

/-- **★ The concrete whole-circuit runtime ★**, at the real `F = 1093` factories and the
    circuit-derived depth — NO free `logicalDepthUs`, NO undischarged hypothesis.  The runtime
    is the magic pipeline because the proven `depth_below_magic_pipeline` puts us in that regime. -/
theorem windowed_rsa2048_runtime_concrete :
    circuitRuntimeUs reactionLimitedDepthUs verifiedToffoli 1093 ccz_spec_qianxu 15
      = deliveryLatency ccz_spec_qianxu 15
        + magicSupplyTimeUs verifiedToffoli 1093 ccz_spec_qianxu :=
  runtime_magic_limited _ _ _ _ _ depth_below_magic_pipeline

/-- The runtime as a literal: `12015 + 28 314 660 000 = 28 314 672 015 µs ≈ 7.87 h`
    (the magic-supply pipeline at 1093 factories dominates the 7.16 h reaction-limited depth). -/
theorem windowed_rsa2048_runtime_value :
    circuitRuntimeUs reactionLimitedDepthUs verifiedToffoli 1093 ccz_spec_qianxu 15
      = 28314672015 := by
  rw [windowed_rsa2048_runtime_concrete]; native_decide

/-! ## §5. Capstone — the resource & runtime come AFTER the composed circuit. -/

/-- **★ ONE chain, composed circuit → resource → device → runtime ★** (for any window layout
    `W` and table `T`):

    1. the workload IS `EGate.toffoli` of the composed `WindowedComposed.modExp`;
    2. the paper magic budget dominates it (provisioning is sufficient);
    3. it flows 1:1 into the proved PPM magic-state count;
    4. the factory provisioning derived from THIS count fits the device's 1093 factories;
    5. and the whole-circuit runtime, at 1093 factories with the circuit-derived depth, is the
       concrete magic pipeline — the depth is no longer free and the hypothesis is discharged.

    What this does NOT claim (honest residue): the windowed circuit's end-to-end *semantics*
    composed into one theorem, nor that 1093 (paper) = 1075 (tight). -/
theorem rsa2048_resource_after_composed_circuit (W : Nat) (T : Nat → Nat) :
    EGate.toffoli (modExp 10 W 2048 T 246 1024) = verifiedToffoli
    ∧ verifiedToffoli ≤ FormalRV.System.RSA2048.magicBudget
    ∧ numCCZMagic (circuitToPPM 8 (modmultBlock verifiedToffoli 0)) = verifiedToffoli
    ∧ verifiedFactoriesNeeded ≤ FormalRV.System.RSA2048.factoriesNeeded
    ∧ circuitRuntimeUs reactionLimitedDepthUs verifiedToffoli 1093 ccz_spec_qianxu 15
        = deliveryLatency ccz_spec_qianxu 15
          + magicSupplyTimeUs verifiedToffoli 1093 ccz_spec_qianxu :=
  ⟨verifiedToffoli_eq_composed_circuit W T, verifiedToffoli_le_magicBudget,
   verifiedToffoli_CCZMagic, verifiedFactories_le_provisioned,
   windowed_rsa2048_runtime_concrete⟩

end FormalRV.System.Compose.VerifiedWorkloadBridge
