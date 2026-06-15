/-
  Audit · gidney-ekera-2021 · LAYER 2 — ARITHMETIC
  GE2021 uses windowed surface-code arithmetic; the underlying adder is the SHARED
  verified Cuccaro adder (✅, FormalRV.StandardShor.cuccaroAdderCorrect).  The full
  RSA-scale windowed circuit's literal enumeration is out of scope (see README GAP).
-/
import FormalRV.Shor.StandardShor
#check @FormalRV.StandardShor.cuccaroAdderCorrect      -- ✅ shared: the n-bit adder computes a+b
