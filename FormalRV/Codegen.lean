import FormalRV.Codegen.SysCallEmit
import FormalRV.Codegen.DeviceProgramParse
import FormalRV.Codegen.QASMEmit

/-!
# FormalRV.Codegen

Code-emission and the shared-syntax bridge: the `DEVICE-PROGRAM` serializer
(`SysCallEmit`), its PARSER + backend-JSON reader (`DeviceProgramParse`, the Lean side of
the Lean ↔ FTQ-VM interop loop), and the QASM serializers.  This umbrella imports the
*library* codegen modules that are part of the umbrella `lake build`.  The `#eval`-driven
demo modules (`SysCallEmitDemo.lean`, `WindowedEmitDemo.lean`, the QASM demos) are
intentionally NOT imported here — they print on elaboration and are run on demand with
`lake env lean <file>`.
-/
