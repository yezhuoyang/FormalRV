import FormalRV.Corpus.ShorEmitDistance

open FormalRV.Corpus.ShorEmitDistance
open FormalRV.Corpus.ShorEmit

-- End-to-end at ANY DISTANCE: emit the first k merges of Shor(N,a) as a
-- distance-d surface-code lattice-surgery Stim circuit.
def N : Nat := 15
def a : Nat := 2
def d : Nat := 5
def k : Nat := 3

def main : IO Unit := do
  let stim := emitShorPrefixAtDistance N a d k
  IO.FS.writeFile "PyCircuits/shor_distance5_demo.stim" stim
  IO.println s!"Shor(N={N}, a={a}) at surface-code distance d={d}: full schedule = {shorMergeCount N} merges; emitted first {k} (each a verified distance-{d} surface_d_x_surgery)."
