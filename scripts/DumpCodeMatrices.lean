/-
  scripts/DumpCodeMatrices.lean — dump named CSS codes' check matrices for the
  EXTERNAL logical-operator solver (`scripts/find_logicals.py`).

  Division of labour (John, 2026-06-10): heavy GF(2) search (kernel bases,
  symplectic pairing) runs OUTSIDE Lean; Lean re-verifies the imported result
  via the cheap `LogicalBasis.valid` certificate (dot products only) and the
  parametric `LogicalGenuine.valid_basis_genuine`.  No `native_decide`.

  Run:  lake env lean --run scripts/DumpCodeMatrices.lean > PyCircuits/code_matrices.txt
-/
import FormalRV.QEC.Instances
import FormalRV.QEC.LogicalFinder

open FormalRV.QEC FormalRV.QEC.Instances FormalRV.QEC.Algebraic
open FormalRV.QEC.LogicalFinder

def dumpCode (name : String) (c : CSSCode) : IO Unit := do
  IO.println s!"CODE {name} {c.n}"
  IO.println s!"HX {repr c.hx}"
  IO.println s!"HZ {repr c.hz}"

def main : IO Unit := do
  dumpCode "lpTiny" lpTiny
  dumpCode "bbSmall" bbSmall
  -- paper-scale targets (matrices are large; same pipeline):
  dumpCode "lp16" lp16
  dumpCode "lp20" lp20
