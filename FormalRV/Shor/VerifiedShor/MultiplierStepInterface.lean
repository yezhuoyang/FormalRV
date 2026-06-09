import FormalRV.Arithmetic.ModMult
import FormalRV.Shor.VerifiedShor.MultiplierStepLayerIntro

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


/-! ## Multiplier-step layer (Phase R5c)

`VerifiedShor.MultiplierStep` is the **Level-2** layout abstraction
above `ControlledModAdd`.  It adds the multiplier register
(positions for the per-bit `m.testBit j` controls), the accumulator
target positions, the multiplier input encoding, and the
install/skip-j machinery.

### Scope (R5c)
R5c ONLY exposes the layout.  The existing multiplier proof chain
(`modmult_step_target_decode`, `modmult_step_workspace`,
etc.) still uses the SQIR-specific names directly.  Refactoring
those is later work.

### Layer position
```
VerifiedModMulFamily              (Shor-level contract, Phase R3)
  └── MultiplierStepLayout         (this layer, Phase R5c)
      └── ControlledModAddLayout   (Phase R5b)
          └── (future) MCPAdapterLayout   (Phase R5d)
``` -/

end VerifiedShor
