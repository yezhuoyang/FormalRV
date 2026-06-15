import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderSpec
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPostStates
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCostSkeleton
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderForwardAndCost
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderClassicalBridge
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDecideWitnesses
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderPropagationReverse
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderUncomputeCascade
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCorrectness
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderResource

/-!
# FormalRV.Arithmetic.RippleCarryAdder

The verified **Gidney** ripple-carry adder gadget. Auditors should read the
thin spine — `RippleCarryAdderDef` (THE definition `gidney_adder`),
`RippleCarryAdderCorrectness` (THE correctness theorems), and
`RippleCarryAdderResource` (T-count / qubits / RSA-2048) — plus the
folder `README.md`. The remaining files are heavy supporting proofs.
-/
