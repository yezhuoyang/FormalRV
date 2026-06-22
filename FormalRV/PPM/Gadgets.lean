import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.PPM.Gadgets.Adder.AdderPPM
import FormalRV.PPM.Gadgets.ModularAdder.CuccaroModAddPPM
import FormalRV.PPM.Gadgets.ModularAdder.GidneyModAddPPM
import FormalRV.PPM.Gadgets.ModMul.SqirModMulPPM
import FormalRV.PPM.Gadgets.ModMul.ShorOracleModMulPPM
import FormalRV.PPM.Gadgets.ModExp.SqirModExpPPM
import FormalRV.PPM.Gadgets.ModExp.ShorOracleModExpPPM
import FormalRV.PPM.Gadgets.Windowed.WindowedMulPPM
import FormalRV.PPM.Gadgets.Windowed.WindowedInplaceModMulPPM
import FormalRV.PPM.Gadgets.QFT.AQFTCliffordTBoundary
import FormalRV.PPM.Gadgets.QPE.UnitaryPPMBoundary
import FormalRV.PPM.Gadgets.Compose

/-!
# FormalRV.PPM.Gadgets

Per-gadget COMPILED-PPM semantic correctness (modularized, John 2026-06-10):
every verified arithmetic gadget — adders, modular adders, BOTH modular
multipliers, BOTH modexp families, windowed arithmetic — gets its own
"compiled to PPM, observes the right arithmetic" theorem, stated ONCE against
the compiler contract `PPMCompilerSpec` and therefore inherited by every
compiler instance (the proven magic-factory compiler today; the Phase-D
new-syntax `compilePPM` the day it lands).  `Compose` glues them back into
full Shor; `QFT`/`QPE` pin the unitary↔PPM boundary.
-/
