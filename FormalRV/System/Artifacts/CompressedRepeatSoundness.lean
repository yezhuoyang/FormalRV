/-
  FormalRV.System.CompressedRepeatSoundness — umbrella module.

  Re-exports the CompressedRepeat split (shift-invariance core,
  feedback-after-decode, freshness state-equivalence + repeat,
  exclusivity / capacity / remaining-conjunct seq chains, the
  parametric symbolic-repeat soundness headlines, the recursive
  compressed-schedule certificate, and the concrete adder
  regressions).  All declarations keep their original fully-qualified
  names in namespace `FormalRV.System.CompressedRepeatSoundness`, so
  existing `import` / `open` sites are unaffected.

  Status: the parametric symbolic-repeat soundness program is CLOSED
  (former Obligations A, B, C all proven).  General entry point:
  `compressed_schedule_strict_soundness` — certificate acceptance
  implies the strict invariant bundle on the expansion.  No `sorry`,
  no custom `axiom`.
-/

import FormalRV.System.Artifacts.CompressedRepeat.ShiftInvariance
import FormalRV.System.Artifacts.CompressedRepeat.FeedbackAfterDecode
import FormalRV.System.Artifacts.CompressedRepeat.FreshnessSoundness
import FormalRV.System.Artifacts.CompressedRepeat.ExclusivitySeq
import FormalRV.System.Artifacts.CompressedRepeat.CapacitySeq
import FormalRV.System.Artifacts.CompressedRepeat.InvariantChains
import FormalRV.System.Artifacts.CompressedRepeat.SymbolicRepeatSoundness
import FormalRV.System.Artifacts.CompressedRepeat.CertificateSoundness
import FormalRV.System.Artifacts.CompressedRepeat.AdderRegressions
