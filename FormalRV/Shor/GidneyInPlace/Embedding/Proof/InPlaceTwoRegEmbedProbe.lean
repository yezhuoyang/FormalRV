/-
  FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedProbe — option (a) feasibility probe:
  the TWO-REGISTER embedding E₂ as a first-class isometry.
  ════════════════════════════════════════════════════════════════════════════

  Probe for "can the generic Route-2 engine accept a two-register embedding `E₂ : z ↦
  cosetInputVec z 0` instead of the single-register `cosetEmbedMat`, avoiding the b=|0⟩
  prepB obstruction?"  The Route-2 success engine (`CosetRoute2Consolidated.{ApproxCosetOrbitShift,
  coset_route2_success_conditional}`) is GENUINELY GENERIC over `E_phys` (a plain `QState → QState`
  parameter; `cosetEmbedMat` is only inside the replaceable `ControlOracleLift` bridge).  It
  requires of `E_phys` an ISOMETRY-style property (`hmarg`: preserves the ideal's per-outcome
  marginal), which for a column-embedding follows from the columns being ORTHONORMAL.

  THE LOAD-BEARING ISOMETRY FACT (A3), proven here:
   * column NORMALIZATION — each `‖cosetInputVec z 0‖² = 1` — is `InPlaceCosetInputNorm.cosetInputVec_normalized` (T1);
   * column ORTHOGONALITY — `cosetInputVec z 0 ⟂ cosetInputVec z' 0` for distinct canonical
     residues `z ≠ z' < N` — is `cosetInputVec_support_disjoint` below: their SUPPORTS are
     disjoint (the a-block windows `window z`, `window z'` are disjoint by `cosetWindow_disjoint`),
     so the inner product is `0`.

  This is the concrete evidence behind the option-(a) PASS verdict (full A1–A6 assessment in the
  session notes): E₂'s columns are an orthonormal family on canonical residues, so E₂ is an
  isometry there (the `hmarg`/`E_phys_marginal` analogue), and — crucially — E₂'s column `z` IS
  the faithful gate's input/output state `cosetInputVec z 0` (b-block = cosetState 0), so T2
  (`gidneyInPlaceWithSwap_agree_off_explicit`) is EXACTLY the work-level off-bad intertwining for
  E₂ — NO prepB, NO b=|0⟩ mismatch.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.  NOT brick 3 — this
  is the feasibility probe only (no orbit lift, no `ApproxCosetOrbitShift` instantiation).
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputNorm
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Def.CosetEphys

namespace FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedProbe

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow)
open FormalRV.Shor.GidneyInPlace.CosetEphys (cosetWindow_disjoint)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (cosetInputTwoReg)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1 (cosetInputTwoReg_support_nonzero)

/-- **A3 (orthogonality core) — distinct E₂ columns have DISJOINT support.**  For distinct
    canonical residues `z ≠ z' < N`, no basis index `i` is in the support of both
    `cosetInputVec z 0` and `cosetInputVec z' 0`: a common support index would put the shared
    a-block decode in `window z ∩ window z' = ∅` (`cosetWindow_disjoint`).  Disjoint support ⇒
    the two columns are ORTHOGONAL (zero inner product), and together with `cosetInputVec_normalized`
    (T1, unit norm) the E₂ columns are an orthonormal family on canonical residues — the isometry
    property the generic Route-2 engine's `hmarg` needs. -/
theorem cosetInputVec_support_disjoint (w bits N cm z z' : Nat)
    (hN : 0 < N) (hz : z < N) (hz' : z' < N) (hne : z ≠ z')
    (i : Fin (2 ^ cosetDim w bits))
    (h1 : cosetInputVec w bits N cm z 0 i 0 ≠ 0)
    (h2 : cosetInputVec w bits N cm z' 0 i 0 ≠ 0) : False := by
  obtain ⟨_, ha1, _⟩ := cosetInputTwoReg_support_nonzero w bits N cm z 0 i 0 h1
  obtain ⟨_, ha2, _⟩ := cosetInputTwoReg_support_nonzero w bits N cm z' 0 i 0 h2
  exact Finset.disjoint_left.mp (cosetWindow_disjoint (2 ^ bits) N cm z z' hN hz hz' hne) ha1 ha2

end FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedProbe
