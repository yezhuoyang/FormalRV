import FormalRV.Codegen.SysCallEmit

/-!
# FormalRV.Codegen

Code-emission (the `DEVICE-PROGRAM` / QASM serializers).  This umbrella imports the *library*
codegen modules that are part of the umbrella `lake build`.  The `#eval`-driven demo modules
(`SysCallEmitDemo.lean`, `WindowedEmitDemo.lean`, the QASM demos) are intentionally NOT imported
here — they print on elaboration and are run on demand with `lake env lean <file>`.
-/
