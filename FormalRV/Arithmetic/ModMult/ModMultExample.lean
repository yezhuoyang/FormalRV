/-
  FormalRV.Arithmetic.ModMult.ModMultExample
  ──────────────────────────────────────────────────
  The modular multiplier as a uniform emittable `Gadget`, a worked resource
  example, and native-QASM emission for diagram rendering.

  OFF the default build path (`#eval` demos). Build / run on demand:
    lake build FormalRV.Arithmetic.ModMult.ModMultExample
-/
import FormalRV.Arithmetic.ModMult.ModMultResource
import FormalRV.Codegen.QASMEmit

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Codegen (Gadget emitQASM)

/-- The SQIR-faithful in-place modular multiplier `×a mod N` as a uniform
emittable `Gadget`, parameterized by modulus `N`, base `a`, and inverse
`ainv`. `circuit bits` is the multiplier at register width `bits`. -/
def ModMult (N a ainv : Nat) : Gadget :=
  { name := "sqir_modmult", circuit := fun bits => modmult_MCP_gate bits N a ainv }

-- Exact resource for the verified multiplier `×2 mod 3` at `bits = 3`
-- (`T = 112 · 3² = 1008`).
#eval IO.println ((ModMult 3 2 2).resourceReport 3)

/-- The descriptor's exact T-count matches the proven closed form `112·bits²`. -/
example (N a ainv : Nat) (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) (bits : Nat) :
    (ModMult N a ainv).tcount bits = 112 * bits ^ 2 := by
  simpa [Gadget.tcount, ModMult] using
    modmult_tcount bits N a ainv hcop hcopinv hpos hlt hodd h1

/-! ## Emit native-basis QASM (bits=3, N=3, ×2) for a structure-revealing diagram.

    Because `Gate.shift` distributes over `seq`, the full multiplier is exactly
      encode ; shift(step₀) ; shift(step₁) ; shift(step₂) ; shift(swap) ; shift(uncompute) ; decode
    so emitting each REAL sub-gadget (at natural size) and composing them as
    Qiskit `to_gate` boxes reconstructs the circuit while exposing the
    shift-and-add-of-modular-adders structure. -/

#eval (do
  let dir := "FormalRV/Arithmetic/ModMult/diagrams"
  IO.FS.createDirAll dir
  let emit := fun (name : String) (g : Gate) =>
    IO.FS.writeFile (dir ++ "/" ++ name ++ ".qasm")
      (FormalRV.Codegen.toQasm g (cliffT := false) (dim := 15))
  emit "blk_full"      (modmult_MCP_gate 3 3 2 2)
  emit "blk_encode"    (encode_to_mult_adapter 3)
  emit "blk_step0"     (Gate.shift 3 (modmult_step_gate 3 3 2 0))   -- c-MODADD( 2·2^0 mod 3 = 2 )
  emit "blk_step1"     (Gate.shift 3 (modmult_step_gate 3 3 2 1))   -- c-MODADD( 2·2^1 mod 3 = 1 )
  emit "blk_step2"     (Gate.shift 3 (modmult_step_gate 3 3 2 2))   -- c-MODADD( 2·2^2 mod 3 = 2 )
  emit "blk_swap"      (Gate.shift 3 (modmult_swap_acc_mult 3))     -- SWAP accumulator ↔ x register
  -- uncompute = const-multiply by (N - a⁻¹) mod N = 1, exposed per-bit:
  emit "blk_unstep0"   (Gate.shift 3 (modmult_step_gate 3 3 ((3 - 2) % 3) 0))  -- c-MODADD( 1·2^0 mod 3 = 1 )
  emit "blk_unstep1"   (Gate.shift 3 (modmult_step_gate 3 3 ((3 - 2) % 3) 1))  -- c-MODADD( 1·2^1 mod 3 = 2 )
  emit "blk_unstep2"   (Gate.shift 3 (modmult_step_gate 3 3 ((3 - 2) % 3) 2))  -- c-MODADD( 1·2^2 mod 3 = 1 )
  IO.println s!"full budget modmult_total_dim 3 = {modmult_total_dim 3}; circuit uses q0..14" : IO Unit)

end FormalRV.BQAlgo
