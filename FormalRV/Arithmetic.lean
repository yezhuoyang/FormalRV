import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst
import FormalRV.Arithmetic.Cuccaro.CuccaroCompare
import FormalRV.Arithmetic.Cuccaro.CuccaroCorrectness
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.Arithmetic.Cuccaro.CuccaroModReduce
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRModAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRStyle
import FormalRV.Arithmetic.Cuccaro.CuccaroSubConst
import FormalRV.Arithmetic.GateToUCom
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.RCIR
import FormalRV.Arithmetic.RippleCarryAdder
import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Arithmetic.UnaryLookup

/-!
# FormalRV.Arithmetic

Logical arithmetic gadgets (Cuccaro/Gidney adders, modular multiplier, unary lookup) and their semantic-correctness proofs.

This umbrella imports every module under `Arithmetic/`.
-/
