/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultExample
  ──────────────────────────────────────────────────
  The modular multiplier as a uniform emittable `Gadget`, a worked resource
  example, and native-QASM emission for diagram rendering.

  OFF the default build path (`#eval` demos). Build / run on demand:
    lake build FormalRV.Arithmetic.SQIRModMult.SQIRModMultExample
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultResource
import FormalRV.Codegen.QASMEmit

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Codegen (Gadget emitQASM)

/-- The SQIR-faithful in-place modular multiplier `×a mod N` as a uniform
emittable `Gadget`, parameterized by modulus `N`, base `a`, and inverse
`ainv`. `circuit bits` is the multiplier at register width `bits`. -/
def SQIRModMult (N a ainv : Nat) : Gadget :=
  { name := "sqir_modmult", circuit := fun bits => sqir_modmult_MCP_gate bits N a ainv }

-- Exact resource for the verified multiplier `×2 mod 3` at `bits = 3`
-- (`T = 112 · 3² = 1008`).
#eval IO.println ((SQIRModMult 3 2 2).resourceReport 3)

/-- The descriptor's exact T-count matches the proven closed form `112·bits²`. -/
example (N a ainv : Nat) (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) (bits : Nat) :
    (SQIRModMult N a ainv).tcount bits = 112 * bits ^ 2 := by
  simpa [Gadget.tcount, SQIRModMult] using
    sqir_modmult_tcount bits N a ainv hcop hcopinv hpos hlt hodd h1

/-! ## Emit native-basis QASM (bits=3, N=3, ×2): the full circuit and its REAL
    top-level sub-gadgets at full dimension, for a faithful modular diagram. -/

#eval (do
  let dir := "FormalRV/Arithmetic/SQIRModMult/diagrams"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sqir_modmult_b3_N3.qasm") ((SQIRModMult 3 2 2).toQASMNative 3)
  -- the two real top-level sub-gadgets at NATURAL size (so each `to_gate` box
  -- faithfully shows the qubits it actually touches):
  IO.FS.writeFile (dir ++ "/blk_adapter.qasm")
    (FormalRV.Codegen.toQasm (sqir_encode_to_mult_adapter 3) (cliffT := false))
  IO.FS.writeFile (dir ++ "/blk_inplace.qasm")
    (FormalRV.Codegen.toQasm (sqir_modmult_inplace_shifted 3 3 2 2) (cliffT := false))
  IO.println s!"full SQIR budget sqir_total_dim 3 = {sqir_total_dim 3}; circuit uses q0..14" : IO Unit)

end FormalRV.BQAlgo
