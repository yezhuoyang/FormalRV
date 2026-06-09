import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderDef
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderCorrectness
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderResource
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
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderCorrectness
import FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderResource
import FormalRV.Arithmetic.RippleCarryAdder
import FormalRV.Arithmetic.ModMult
import FormalRV.Arithmetic.ModExp
import FormalRV.Arithmetic.UnaryLookup
import FormalRV.Arithmetic.Windowed

/-!
# FormalRV.Arithmetic

Logical arithmetic gadgets (Cuccaro/Gidney adders, modular multiplier, unary lookup) and their semantic-correctness proofs.

This umbrella imports every module under `Arithmetic/`.
-/
