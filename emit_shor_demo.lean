import FormalRV.Corpus.ShorEmit

open FormalRV.Corpus.ShorEmit

-- End-to-end: hand the framework a LITERAL (N, a) and emit the scheduled circuit.
def N : Nat := 15
def a : Nat := 2
def demoSurgeries : Nat := 5   -- emit the first 5 surgeries (full Shor(15) = 3072)

def main : IO Unit := do
  IO.FS.writeFile "PyCircuits/shor_demo_schedule.stim" (emitShorPrefix N a demoSurgeries)
  IO.println s!"Shor(N={N}, a={a}): full schedule = {shorMergeCount N} surgery merges; emitted first {demoSurgeries}."
