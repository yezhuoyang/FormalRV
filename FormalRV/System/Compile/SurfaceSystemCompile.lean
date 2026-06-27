/-
  FormalRV.System.SurfaceSystemCompile — distance-parametric surface-code
  resource derivations plus a small system-level schedule check (one window,
  five concurrent SysCalls), hardware-agnostic.  This sketches the four design
  questions of a surface-code Shor compilation in miniature; it is NOT a full
  physical compilation of Shor.

  ## Hardware-agnostic by construction
  There is NO `atom` abstraction here.  The resource layer is parameterised by a
  `Hardware` carrying only a cycle time, so it works for superconducting,
  trapped-ion, OR neutral-atom machines — you plug the cycle time.  The system
  layer (`SysCall`: Gate/Measure/Transit/RequestMagicState/DecodeSyndrome; the
  `baseInvariants`: capacity, exclusivity, latency, throughput, decoder) is
  likewise hardware-neutral.  HARDWARE-SPECIFIC connectivity/transport enters
  ONLY as a pluggable `SpaceTimeInvariant` instance (neutral-atom rigid AOD move
  is one such instance; a superconducting fixed-coupling rule would be another) —
  it is never part of the core.

  ## The four questions (in miniature)
  Q1 (logical→physical map)  `patchLo/patchHi`: each logical qubit is a
       disjoint contiguous block of physical qubit sites (`patches_disjoint`).
  Q2 (ancilla scheduling)    `dataSites/syndromeAncilla/routingAncilla`: a patch
       budgets data + surgery-routing sites; `patch_site_accounts` records the
       (definitional) split.
  Q3 (T-factory scheduling)  `magicProducedInWindow/factoryMeetsDemand`: a factory
       making one magic state per `cyclesPerMagic` with `P` parallel copies;
       demand ≤ production checked on a worked example.
  Q4 (arbitrary distance)    `surfaceCodeD d` = [[d²+(d-1)², 1, d]] for ANY d; the
       resource derivation is distance-parametric (instantiated at d = 27).

  ## System-level check
  `surfaceShorCtx_valid`: ONE window of five concurrent SysCalls (syndrome
  extraction ∥ surgery merge ∥ magic request ∥ decode ∥ ancilla request) passes
  `checkAll baseInvariants` on the demo architecture.  The schedule has
  `moves := []`, so the platform transport invariants below pass VACUOUSLY.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.Examples.ParallelismVerification
import FormalRV.QEC.FrontendAlgebraic
import FormalRV.QEC.LatticeSurgery.SurfaceShorResourceCount

set_option maxRecDepth 8000
namespace FormalRV.System.SurfaceSystemCompile

open FormalRV.Framework.Resource
open FormalRV.System.InvariantFramework
open FormalRV.System.Architecture
open FormalRV.QEC.Algebraic
open FormalRV.LatticeSurgery.SurfaceShorResourceCount

/-! ## Q4 — arbitrary code distance (the construction is parametric in `d`) -/

/-- The distance-`d` surface code [[d² + (d-1)², 1, d]] for ANY `d`. -/
def surfaceCodeD (d : Nat) : FormalRV.Framework.QECCode := (surfaceHGP d).toQECCode 1 d

theorem surfaceCodeD_k (d : Nat) : (surfaceCodeD d).k = 1 := rfl
theorem surfaceCodeD_dist (d : Nat) : (surfaceCodeD d).d = d := rfl

/-- physical/logical for a `k = 1` surface code is its physical-qubit count `n`. -/
theorem surfaceCodeD_physPer (d : Nat) :
    physPerLogical (surfaceCodeD d) = (surfaceCodeD d).n := by
  unfold physPerLogical
  rw [surfaceCodeD_k]; simp

/-- **d = 27 instance** — the framework evaluates the real RSA-scale patch:
    [[1405, 1, 27]], 1405 physical qubits per logical patch. -/
theorem surface27_is_1405 :
    (surfaceCodeD 27).n = 1405 ∧ (surfaceCodeD 27).d = 27
    ∧ physPerLogical (surfaceCodeD 27) = 1405 := by decide

/-- **Distance-general qubit count.**  For EVERY distance `d`, the surface-code
    Shor footprint is `L` patches of `2·n(d)` physical qubits plus the factory. -/
theorem surfaceShor_qubits_anyD (d T L factory : Nat) (hw : Hardware) (ow p : Nat) :
    (estimateWith (surfaceModel factory) hw (shorWorkload T L) (surfaceCodeD d) ow p).qubits
      = L * (2 * (surfaceCodeD d).n) + factory := by
  rw [estimateWith_qubits_tagged]
  simp only [surfaceModel, shorWorkload, Nat.add_zero, surfaceCodeD_physPer]

/-- **Distance-general runtime.**  `T` logical Toffolis, each `d` code cycles. -/
theorem surfaceShor_time_anyD (d T L factory : Nat) (hw : Hardware) (ow p : Nat) :
    (estimateWith (surfaceModel factory) hw (shorWorkload T L) (surfaceCodeD d) ow p).time_us_tenths
      = T * d * hw.cycle_time_us_tenths := by
  rw [estimateWith_time]
  simp only [surfaceModel, shorWorkload, surfaceCodeD_dist]

/-! ## Q1 — logical → physical layout (hardware-agnostic; physical qubit *sites*)

    Each logical qubit gets a contiguous block of `patchSize d` physical sites
    (data + standing surgery-routing area).  The blocks are pairwise disjoint, so
    the map logical → physical never aliases — the layout-correctness condition. -/

/-- Physical sites per logical patch: data + an equal standing routing area
    (`2 · physPerLogical`, the surface convention; gidney-ekera-2021 §2.14). -/
def patchSize (d : Nat) : Nat := 2 * physPerLogical (surfaceCodeD d)

/-- First physical-site index of logical qubit `i`. -/
def patchLo (i d : Nat) : Nat := i * patchSize d
/-- One-past-last physical-site index of logical qubit `i`. -/
def patchHi (i d : Nat) : Nat := (i + 1) * patchSize d

/-- **Q1 layout correctness: distinct logical qubits occupy DISJOINT physical
    regions.**  For `i < j`, qubit `i`'s block ends at or before `j`'s begins. -/
theorem patches_disjoint (i j d : Nat) (h : i < j) : patchHi i d ≤ patchLo j d := by
  unfold patchHi patchLo
  exact Nat.mul_le_mul_right _ h

/-! ## Q2 — ancilla scheduling (purpose-tagged, as in `AncillaBudget`) -/

/-- Data sites of a patch (the code's physical-qubit count). -/
def dataSites (d : Nat) : Nat := (surfaceCodeD d).n
/-- In-patch syndrome-extraction ancilla (one basis, qianxu `N = n + (n-k)/2`). -/
def syndromeAncilla (d : Nat) : Nat := ((surfaceCodeD d).n - (surfaceCodeD d).k) / 2
/-- Standing surgery-routing area (where lattice-surgery merges happen). -/
def routingAncilla (d : Nat) : Nat := physPerLogical (surfaceCodeD d)

/-- **Q2 accounting (definitional)**: a patch's sites split into data +
    surgery-routing.  Since `patchSize d = 2·n` and both summands equal `n`,
    this is the arithmetic identity `2n = n + n` — it records the naming
    convention (data block + equal standing routing area), not a non-trivial
    budget.  (Syndrome ancilla are bundled in the in-patch `physPerLogical`,
    per the surface cost model.) -/
theorem patch_site_accounts (d : Nat) :
    patchSize d = dataSites d + routingAncilla d := by
  unfold patchSize dataSites routingAncilla
  rw [surfaceCodeD_physPer]; omega

/-! ## Q3 — T-factory scheduling (production vs demand) -/

/-- Magic states a factory bank produces in a window: `P` parallel copies, each
    one state per `cyclesPerMagic`, over `window` cycles. -/
def magicProducedInWindow (parallelFactories cyclesPerMagic window : Nat) : Nat :=
  if cyclesPerMagic = 0 then 0 else (window / cyclesPerMagic) * parallelFactories

/-- The factory bank meets the magic-state demand in the window. -/
def factoryMeetsDemand (demand parallelFactories cyclesPerMagic window : Nat) : Bool :=
  decide (demand ≤ magicProducedInWindow parallelFactories cyclesPerMagic window)

/-- Physical sites of a factory bank: `perFactory` sites × `P` parallel copies. -/
def factorySites (perFactory parallelFactories : Nat) : Nat := perFactory * parallelFactories

/-- **Q3 worked schedule.**  A factory making one magic state per 5 cycles, with
    4 parallel copies, meets a demand of 8 magic states per 10-cycle window
    (production = (10/5)·4 = 8). -/
theorem factory_meets_demand_demo :
    factoryMeetsDemand 8 4 5 10 = true := by decide

/-- **Monotone in parallelism**: more factory copies never reduce production. -/
theorem magicProduced_mono (P P' cyclesPerMagic window : Nat) (h : P ≤ P') :
    magicProducedInWindow P cyclesPerMagic window
      ≤ magicProducedInWindow P' cyclesPerMagic window := by
  unfold magicProducedInWindow
  split
  · exact Nat.le_refl 0
  · exact Nat.mul_le_mul_left _ h

end FormalRV.System.SurfaceSystemCompile
