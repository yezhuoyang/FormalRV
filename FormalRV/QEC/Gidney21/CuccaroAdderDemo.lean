/-
  FormalRV.QEC.Gidney21.CuccaroAdderDemo
  --------------------------------------
  **★ THE CUCCARO ADDER, LOWERED TO PPM, ROUTES ENTIRELY TO VERIFIED LATTICE
  SURGERY. ★**

  The Cuccaro ripple-carry adder (`cuccaro_n_bit_adder_full`, CNOTs + Toffolis)
  is lowered to a PPM program by the repo's OWN `gadgetPPM = lowerFlat ∘
  gateRots` (the PauliRotation→PPM pipeline — the same object the `LoweredOK`
  instances verify).  We route the LOWERED program's every measurement through
  `progGadgets` and prove the WHOLE thing is covered: nothing left over.

  The lowered T-injections produce measurements of weight 1 (`Z`/`X`/`Y`
  readouts), weight 2/3 (`Z`-axis + mixed branches), and weight 4 (rotation-axis
  + magic-ancilla join) — every one routes to a single verified gadget.
-/
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.QEC.Gidney21.Compiler.Lower
import FormalRV.Arithmetic.Cuccaro.CuccaroAdderDef

namespace FormalRV.QEC.Gidney21

open FormalRV.BQAlgo

/-! ## §1. The MAJ building block. -/

/-- The Cuccaro MAJ block (2 CNOTs + 1 Toffoli) lowered to PPM (68 statements). -/
def majPPM : FormalRV.PPM.Prog.PPMProg := gadgetPPM (cuccaro_MAJ 0 1 2)

theorem majPPM_fully_covered : uncoveredMeasurements majPPM = [] := by native_decide

/-- **The lowered Cuccaro MAJ block routes ENTIRELY to verified lattice
surgery.** -/
theorem majPPM_routes_to_verified :
    (∀ k ∈ progGadgets majPPM, ScheduleImplementsSpec (gadgetFor k) = true)
      ∧ uncoveredMeasurements majPPM = [] :=
  fully_covered_program_routes_to_verified majPPM majPPM_fully_covered

/-! ## §2. THE FULL 2-bit Cuccaro adder. -/

/-- **The full 2-bit Cuccaro adder** (MAJ chain + reverse UMA chain) lowered to
PPM — a real multi-Toffoli arithmetic circuit. -/
def adderPPM : FormalRV.PPM.Prog.PPMProg := gadgetPPM (cuccaro_n_bit_adder_full 2 0)

theorem adderPPM_fully_covered : uncoveredMeasurements adderPPM = [] := by native_decide

/-- **★ THE FULL CUCCARO ADDER, LOWERED TO PPM, ROUTES ENTIRELY TO VERIFIED
LATTICE SURGERY ★** — every measurement of the real, repo-lowered ripple-carry
adder routes to a single verified-LaS gadget, with NOTHING uncovered.  Shor's
modular arithmetic is built from exactly these adders. -/
theorem adderPPM_routes_to_verified :
    (∀ k ∈ progGadgets adderPPM, ScheduleImplementsSpec (gadgetFor k) = true)
      ∧ uncoveredMeasurements adderPPM = [] :=
  fully_covered_program_routes_to_verified adderPPM adderPPM_fully_covered

#eval adderPPM.length                 -- statement count of the lowered adder
#eval (progGadgets adderPPM).length   -- verified-gadget count

end FormalRV.QEC.Gidney21
