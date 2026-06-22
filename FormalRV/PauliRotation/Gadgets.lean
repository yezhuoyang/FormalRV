/-
  FormalRV.PauliRotation.Gadgets — umbrella.

  ALL existing arithmetic gadget families, compiled to Pauli rotations
  through the verified pipeline (`GateBridge.lean`), ONE FILE PER FAMILY:

    • `Gadgets/CuccaroAdder.lean`        — n-bit adder + const-arithmetic variants
    • `Gadgets/GidneyAdder.lean`         — faithful / patched Gidney ripple adders
    • `Gadgets/ModularAdderCuccaro.lean` — THE LIVE (x+c) mod N + controlled form
    • `Gadgets/ModularAdderGidney.lean`  — the standalone Gidney mod-add pipeline
    • `Gadgets/ModMult.lean`             — const multiplier + in-place MCP oracle
    • `Gadgets/ModExp.lean`              — Shor mod-exp chains (verified-oracle + counting model)
    • `Gadgets/UnaryLookup.lean`         — faithful QROM + Gray-code read
    • `Gadgets/Windowed.lean`            — windowed mul, mod-N, in-place weld, Gray-code

  Uniform shape per gadget: `<g>Rot` (the parallelized rotation program),
  `<g>Rot_countPi8` (SYMBOLIC rotation T-count, composing the family's
  existing anchored `tcount` theorem), and where small, an anchored
  `gateRotSchedule_denote` correctness instance with `decide` side
  conditions.
-/
import FormalRV.PauliRotation.Gadgets.CuccaroAdder
import FormalRV.PauliRotation.Gadgets.GidneyAdder
import FormalRV.PauliRotation.Gadgets.ModularAdderCuccaro
import FormalRV.PauliRotation.Gadgets.ModularAdderGidney
import FormalRV.PauliRotation.Gadgets.ModMult
import FormalRV.PauliRotation.Gadgets.ModExp
import FormalRV.PauliRotation.Gadgets.UnaryLookup
import FormalRV.PauliRotation.Gadgets.Windowed
