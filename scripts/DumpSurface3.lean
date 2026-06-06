import FormalRV.QEC.FrontendAlgebraic
open FormalRV.QEC.Algebraic
def rowSupp (r : List Bool) : List Nat := (r.zipIdx.filter (fun p => p.1)).map (fun p => p.2)
def main : IO Unit := do
  let c := surfaceHGP 3
  IO.println s!"n {c.n}"
  IO.println "HX"
  for r in c.hx do IO.println s!"{rowSupp r}"
  IO.println "HZ"
  for r in c.hz do IO.println s!"{rowSupp r}"
