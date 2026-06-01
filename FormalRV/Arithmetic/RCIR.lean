/-
  FormalRV.BQAlgo.RCIR — backward-compat shim.

  The IR `RCIRGate` and its `tcount` originally lived here; they have been
  promoted to the `Framework` layer (see `Framework/Gate.lean` and
  `Framework/Semantics.lean`) so that BQ-Arch and BQ-Code modules can also
  reason about gates / circuits semantically.

  This file just re-exports `Gate` under the legacy name `RCIRGate`. New
  code should `import FormalRV.Core.Gate` directly and use `Gate`.
-/
import FormalRV.Core.Gate

namespace FormalRV.BQAlgo

/-- Legacy alias — use `FormalRV.Framework.Gate` for new code. -/
abbrev RCIRGate := FormalRV.Framework.Gate

end FormalRV.BQAlgo
