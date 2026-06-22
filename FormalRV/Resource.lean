/-
  FormalRV.Resource — the SEPARATE, INDEPENDENT resource-counting system.

  ## Why a separate folder

  A resource count must be an honest tree-walk over a syntactic object and
  NOTHING else.  Everything in this folder imports ONLY the circuit IRs (`Gate`,
  `BaseUCom`, …) — never the gadget constructors and never the correctness
  proofs.  Because the counters live in their own world, a resource theorem
  `countT (gadget n) = 14·n` cannot fudge the count: the number is forced by the
  syntax tree, and a skeptic can `#eval` the counter on a constructed circuit to
  check it WITHOUT reading any proof.

  ## The verification shape this enforces

  Each verified resource claim carries a TRIPLE: (1) a concrete syntactic object
  (or a generator that builds it), (2) a proof it is semantically correct against
  the spec, and (3) a proof that THESE counters, applied to THAT object, equal the
  closed form.  No formula like `3n` is ever asserted without a real object behind
  it.  The per-gadget count THEOREMS (item 3) live with their gadget (e.g.
  `Arithmetic/Cuccaro/CuccaroAdderResource.lean`, `QFT/IQFTResource.lean`); this
  folder owns the COUNTERS they use.

  ## Contents
    • `GateCount`       — TIME `countT` / `countCNOT` / `countToffoli` / `countX` /
                          `gateCount` / `depth` + SPACE `width`, on the reversible
                          `Gate` IR (with bridges to the legacy `Gate.tcount` / `gcount`).
    • `UComCount`       — TIME `gateCountU` / `cnotCountU` / `oneQCountU` + SPACE
                          `widthU`, on the unitary `BaseUCom` IR (the QFT/QPE
                          counters — previously ABSENT).
    • `UComCombinators` — count laws for the core combinators (`SWAP`, `CCX`,
                          `controlled_R`, `control`, `npar`, `npar_H`) — what lets
                          a structured circuit's count reduce to its parts'.
    • `Interface`       — the `HasResourceCount` typeclass unifying the IRs
                          (`cnot`, `gates` = time; `qubits` = space).
    • `QECCircuitCount` — TIME `cxCountC` / `measCountC` / `prepCountC` /
                          `opCountC` + SPACE `widthC`, on the QEC physical-
                          circuit IR (`QEC/Circuit/PhysCircuit.lean`) — the
                          layer at which syndrome/surgery-ancilla overhead is
                          explicit in the syntax tree and therefore counted.

  Per-gadget closed-form count theorems live with their gadgets:
  `Arithmetic/*Resource*.lean` (Gate IR), `QFT/IQFTCount.lean` (the inverse QFT:
  CNOTs = 3⌊n/2⌋+n(n−1), qubits = n), `QPE/QPECount.lean` (QPE over a black-box
  oracle), `QEC/Circuit/ExtractionCount.lean` (the compiled syndrome-extraction
  circuit of a surgery gadget: width = `surgeryPhysQubits`, CNOTs =
  `surgeryCNOTs`, measurements = `surgeryMeasPerRound`/`surgeryTotalMeas`).

    • `SysCallCount`    — the SYSTEM (L4) layer, on `List SysCall`:
                          TIME `wallclockUs` / `totalBusyUs` + per-kind op
                          counters (`countGate2q`, `countMeasure`,
                          `countDecode`, `countMagicReq`, …); SPACE
                          `qubitFootprint` / `peakSiteOccupancy` (sites via
                          `syscall_acts_on`); channel ids `decodeIds` /
                          `pfuCorrs`; syndrome volume `syndromeBitsTotal`.
                          Consumers re-pointed to these (the wallclock alias
                          `scheduleWallclockUs`, `resourceOfSysCalls`'s
                          fields, `FTSchedule.countKind`, the GE2021 PPM
                          block counts) — no parallel counting walks remain
                          at the SysCall level.  The FTQ-VM computes the
                          same quantities independently from the same
                          DEVICE-PROGRAM files (`test_resource_counts.py`).

  Migration TODO (tracked): re-home the PPM measurement/magic-T counters
  (`ppmProgramResourceSummary`, `numMeas`) and the system `CostModel` under this
  folder behind the same `HasResourceCount`-style interface.  (The lattice-
  surgery gadget-field counters are now THEOREM-tied to the syntactic
  extraction circuit via `QEC/Circuit/ExtractionCount.lean`.)
-/
import FormalRV.Resource.GateCount
import FormalRV.Resource.UComCount
import FormalRV.Resource.UComCombinators
import FormalRV.Resource.Interface
import FormalRV.Resource.QECCircuitCount
import FormalRV.Resource.PPMCount
import FormalRV.Resource.SysCallCount
import FormalRV.Resource.SysCallCountLaws
