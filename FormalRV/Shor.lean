import FormalRV.QFT.AQFTCompile
import FormalRV.QFT.AQFTCompileSemantics
import FormalRV.Shor.Approx
import FormalRV.Shor.ApproxTransfer
import FormalRV.Shor.CosetBornWeight
import FormalRV.Shor.Resource.CliffordTControlledModExp
import FormalRV.Shor.Resource.ShorTCountHeadline
import FormalRV.QPE.ControlledGates
import FormalRV.Shor.Resource.ControlledModExpCount
import FormalRV.Shor.OrderFinding.Eigenstate
import FormalRV.Shor.OrderFinding.EncodingAgnostic
import FormalRV.Shor.Main
import FormalRV.Shor.MeasUncompute
import FormalRV.Shor.MeasuredWindowedModN
import FormalRV.Shor.MeasuredWindowedShorCapstone
import FormalRV.Shor.MeasuredWindowedModExpResource
-- Babbush-measured in-place windowed multiplier: the unary-iteration QROM (arXiv:1805.03662
-- §III.A/§III.C, `2^w − 1` Toffolis) + Gidney's 4-T temporary AND (`4L − 4` T) + measurement
-- uncompute + the in-place mod-N structure — value AND count on one syntactic object.
import FormalRV.Shor.GidneyTCount
import FormalRV.Shor.MeasuredBabbushRead
import FormalRV.Shor.MeasuredBabbushWindowedModN
import FormalRV.Shor.MeasuredBabbushHonestTCount
-- Route (2): the ALL-temporary-AND windowed lookup-add step at the Gidney 3-per-bit layout
-- (Babbush merged-AND load + measured Gidney adder + mz-clear) — value `acc+T[v] mod 2^bits`,
-- count `4·((2^w−1)+bits)`, with the uniform 4-T model GADGET-BY-GADGET HONEST (every gadget a
-- genuine temporary AND), closing the route-(1) adder-accounting residue.
import FormalRV.Shor.GidneyMeasuredLookupAdd
-- The lookup-add step FOLDED into a whole windowed mod-N multiplier via the single-wide-runway
-- coset bridge: accumulator = Σⱼ tableValueⱼ (no per-step reduce), residue mod N = (a·y) mod N
-- (`gidneyRunwayMul_residue`), all-temporary-AND, gidneyTCount = numWin·4·((2^w−1)+bits) honest.
import FormalRV.Shor.GidneyRunwayMul
-- The IN-PLACE form y ↦ (a·y) mod N: two-pass (multiply-add a · swap · multiply-add N−a⁻¹) at the
-- Gidney layout. y-register residue = (a·y) mod N, accumulator residue = 0 (coset level), the swap
-- T-free; gidneyTCount = 2·numWin·4·((2^w−1)+bits) gadget-by-gadget honest.
import FormalRV.Shor.GidneyRunwayMulInPlace
-- The CHEAP value-composed windowed mod-N multiplier `y ↦ (a·y) mod N` EXACTLY (per-step reduced,
-- accumulator stays `< N`, NO coset readout), at the all-temporary-AND Gidney 3-per-bit layout,
-- built on the register-register MEASURED modular adder keystone `gidneyModAddRegMeasured`.
-- VALUE (`gcMul_value_init`) AND COUNT (`toffoli_gcMul = numWin·((2^w−1)+3·(bits+1))`) on the SAME
-- `EGate` (`gcMul_value_and_count`); cheapest honest per-step-reduced cost, gadget-by-gadget honest.
import FormalRV.Shor.GidneyCheapModMul
-- The IN-PLACE form `x ↦ (a·x) mod N` (Bennett `mul(a) ; swap ; mul(N−ainv)`, subtract = add of the
-- negated inverse mod N — both passes reuse `gcMul`, no second keystone) wrapped into the canonical
-- `encodeDataZeroAnc` Shor layout, WIRED to the full Shor success bound: `gcMul_shor_resource_capstone`
-- gives `probability_of_success ≥ κ/(log₂N)⁴` (the MEASURED `gcMulEncodeGate` certified to compute
-- `(a^(2^i)·x) mod N` on every encoded basis state) ∧ the cheap measured Toffoli count — Shor success
-- and count on ONE composed syntactic circuit, axiom-clean.
import FormalRV.Shor.GidneyCheapModMulInPlace
import FormalRV.Shor.GidneyCheapModMulShor
import FormalRV.Shor.MeasuredBabbushWindowedShorCapstone
import FormalRV.Shor.MeasuredBabbushWindowedModExpResource
-- The two ripple-adder-lineage modular multipliers as instances of the
-- canonical `EncodeRoundTripModMul` multiplier interface.
import FormalRV.Shor.MultiplierInstances
import FormalRV.Shor.Resource.ModExpToffoliCount
import FormalRV.Shor.PPM.PPMShorMaster
import FormalRV.Shor.PPM.ShorLPAllocation
import FormalRV.QPE.PhaseKickback
import FormalRV.Shor.PostQFT
import FormalRV.Shor.OrderFinding.ProbabilityTransfer
import FormalRV.QPE.QPE
import FormalRV.QPE.QPEAmplitude
import FormalRV.Shor.MainAlgorithm
import FormalRV.Shor.OrderFinding.SuccessSensitivity
import FormalRV.Shor.OrderFinding.TotientLowerBound
import FormalRV.Shor.VerifiedShor
-- Windowed arithmetic gadgets relocated to FormalRV.Arithmetic.Windowed (2026-06-09);
-- the Shor-specific windowed glue stays here.
import FormalRV.Shor.WindowedCapstone
import FormalRV.Shor.WindowedComposed
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Shor.WindowedEndToEnd
import FormalRV.Shor.WindowedPPM
import FormalRV.Shor.WindowedShorConnection
import FormalRV.Shor.WindowedTimeCost
import FormalRV.Shor.PPM.ShorPPMEndToEnd
import FormalRV.Shor.PPM.ShorPPMUnitaryReduction
import FormalRV.Shor.PPM.ShorModMulPPMFactoryE2E
import FormalRV.Shor.WindowedShorPPMFactoryE2E
import FormalRV.Shor.PPM.TeleportCCXGrounded
import FormalRV.Shor.Resource.ShorCriticalPathFloor
import FormalRV.Shor.Resource.ShorFullMachineRequirement
-- THE WELD: the in-place QROM-lookup windowed mod-N multiplier as an
-- `EncodeRoundTripModMul` instance + its Shor success bound.
import FormalRV.Shor.WindowedModNShor

/-!
# FormalRV.Shor

The main result: Shor order-finding success probability (see `Shor/Main.lean`), QPE, phase kickback, inverse-QFT.

This umbrella imports every module under `Shor/`.
-/
