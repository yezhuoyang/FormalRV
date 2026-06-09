import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.McpAdapterLayerIntro

namespace VerifiedShor
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)


/-! ## MCP / Shor adapter layer (Phase R5d)

`VerifiedShor.MCPAdapter` is the **Level-3** layout abstraction
above `MultiplierStep`.  It connects the internal multiplier
layout (Level 2) to the Shor/MCP-facing `encodeDataZeroAnc`
encoding via a shift adapter and a register-reversal swap.

### Scope (R5d)
R5d ONLY exposes the layout and re-exports existing MCP-bridge
facts.  It does NOT yet build a generic `VerifiedModMulFamily` from
a `MultiplierStepLayout` + `ControlledModAddImpl` — that remains
R6 work.

### Layer position
```
VerifiedModMulFamily              (Shor-level contract, Phase R3)
  └── MCPAdapterLayout             (this layer, Phase R5d)
      └── MultiplierStepLayout     (Phase R5c)
          └── ControlledModAddLayout (Phase R5b)
``` -/

end VerifiedShor
