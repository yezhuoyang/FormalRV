/-
  FormalRV.Corpus.GidneyEkera2021Reproduction — reproduce Gidney–Ekerå 2021's
  RSA-2048 resource estimate with our VERIFIED surface-code framework, and pin the
  gap.  (gidney-ekera-2021, arXiv:1905.09749, "How to factor 2048-bit RSA integers
  in 8 hours using 20 million noisy qubits.")

  ## What "reproduce" means here — and what it does NOT
  This is a RESOURCE reproduction: we plug GE2021's OWN inputs (Toffoli count,
  logical-qubit count, the distance-27 surface tile, 1 µs cycle) into our
  rfl-VERIFIED resource derivation (`estimateWith (surfaceModel …)`,
  `Framework/CostModel.lean`) and compare the output to the paper's headline.
  The derivation FORMULA is verified; the gap is the part the paper achieves that
  the simple model does not capture.

  It is NOT a claim that we verified GE2021's full circuit SEMANTICALLY end-to-end
  in Hilbert space.  Our semantic chain is: PPM-level Shor success
  (`shor_succeeds_with_ppm_realized_modmult`) → logical PPMs realised by verified
  surface-code surgery (`surgery_implements_logical_measurement`,
  `schedule_runs_as_surgeries`) → `teleportCCX` as magic-injection surgery
  (`MagicInjectionSurgery`) → a system schedule passing resource + causality
  (`SurfaceShorFullSchedule`).  The DELIMITED contracts (unchanged) are: the
  Gottesman–Knill Hilbert-space faithfulness, merged-code distance / fault
  tolerance, the non-Clifford magic-state correctness (`teleportCCXRel`), and the
  enumeration of EVERY RSA-scale PPM into one schedule (covered only by the
  PARAMETRIC depth/area laws, not a literal 2.7×10⁹-Toffoli term).  So the resource
  reproduction below stands on verified FORMULAS + cited inputs, not on a closed
  whole-circuit semantic theorem.

  ## The finding
  • QUBITS: the verified surface area-ceiling = 6200 · (2·1568) = 19.44 M, within
    ~3 % of the reported 20 M (residual = the magic factory).  GE2021's qubit count
    IS essentially our verified ceiling — NO unverified qubit-side optimization.
  • TIME: the verified naive-SEQUENTIAL ceiling = 2.7×10⁹ · 27 · 1 µs = 20.25 h;
    the reported 8 h sits 2–3× under it.  That ≈2.5× speed-up is reaction-limited
    PIPELINING of the Toffoli critical path — expressible in our schedule layer
    (`SurfaceShorFullSchedule`: parallel windows subject to causality) but NOT yet
    verified at full RSA scale.  THE GAP = this pipelining factor, made explicit.

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.NaiveUpperBound
import FormalRV.Audit.Common.SurfaceSystemCompile

namespace FormalRV.Corpus.GidneyEkera2021Reproduction

open FormalRV.System.NaiveUpperBound
open FormalRV.Audit.Common.SurfaceSystemCompile

/-! ## The distance-27 code is a REAL verified construction, not a stub -/

/-- GE2021 runs at distance 27.  Our `surfaceCodeD 27` is an actual surface-code
    construction `[[1405, 1, 27]]` (unrotated HGP `surfaceHGP 27`); the paper's
    per-logical tile `2(d+1)² = 1568` is the ROTATED patch including routing. -/
theorem ge2021_distance_is_verified_code :
    (surfaceCodeD 27).d = 27 ∧ (surfaceCodeD 27).k = 1 ∧ (surfaceCodeD 27).n = 1405 := by
  decide

/-! ## QUBITS — reproduced within ~3 % (no unverified qubit-side optimization) -/

/-- The verified surface area-ceiling for GE2021: 6200 logical × (2·1568) = 19.44 M. -/
theorem ge2021_qubits_derived : ge2021_naive.qubits = 19_443_200 := by decide

/-- It sits below the reported 20 M and within ~600 k (≈3 %) — the residual is the
    magic factory the area model folds out.  So the reported qubit count IS the
    verified ceiling: no unverified qubit-side speed-up. -/
theorem ge2021_qubits_reproduce_reported :
    ge2021_naive.qubits ≤ ge2021_reported_qubits
    ∧ ge2021_reported_qubits - ge2021_naive.qubits ≤ 600_000 := by decide

/-! ## TIME — the reported 8 h is 2–3× under the verified sequential ceiling -/

/-- The verified naive-sequential time ceiling: 2.7×10⁹ Toffolis · 27 cycles · 1 µs
    = 729×10⁹ tenths-µs ≈ 20.25 h. -/
theorem ge2021_time_ceiling : ge2021_naive.time_us_tenths = 729_000_000_000 := by decide

/-- The reported 8 h (288×10⁹ tenths-µs) is 2–3× UNDER the verified sequential
    ceiling.  That factor (~2.5×) is the reaction-limited pipelining the paper
    achieves but we do not verify at full scale — THE GAP. -/
theorem ge2021_time_gap_2_to_3x :
    2 * ge2021_reported_time_us_tenths ≤ ge2021_naive.time_us_tenths
    ∧ ge2021_naive.time_us_tenths ≤ 3 * ge2021_reported_time_us_tenths := by decide

/-! ## The reproduction capstone -/

/-- **GIDNEY–EKERÅ 2021 REPRODUCED, gap pinned.**  From the verified surface-code
    resource derivation and the paper's own inputs:
    (i) QUBITS — derived 19.44 M ≤ reported 20 M, within ~3 % (factory residual):
        the reported footprint IS the verified area ceiling, no unverified gap;
    (ii) TIME — reported 8 h is 2–3× under the verified sequential ceiling of
        20.25 h: the ≈2.5× gap is pipelining, claimed but not verified at scale.
    This is a verified-formula reproduction; the end-to-end Hilbert-space semantic
    closure remains the delimited chain (see the file header). -/
theorem gidney_ekera_2021_reproduced :
    (ge2021_naive.qubits ≤ ge2021_reported_qubits
      ∧ ge2021_reported_qubits - ge2021_naive.qubits ≤ 600_000)
    ∧ (2 * ge2021_reported_time_us_tenths ≤ ge2021_naive.time_us_tenths
      ∧ ge2021_naive.time_us_tenths ≤ 3 * ge2021_reported_time_us_tenths) :=
  ⟨ge2021_qubits_reproduce_reported, ge2021_time_gap_2_to_3x⟩

end FormalRV.Corpus.GidneyEkera2021Reproduction
