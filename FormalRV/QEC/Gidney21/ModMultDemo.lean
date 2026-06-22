/-
  FormalRV.QEC.Gidney21.ModMultDemo
  ---------------------------------
  **★ THE MODULAR MULTIPLIER, LOWERED TO PPM, ROUTES ENTIRELY TO VERIFIED
  LATTICE SURGERY. ★**

  `modmult_inplace_candidate` (the in-place modular multiplier — Shor's
  workhorse, built from Cuccaro modular adders) is lowered to PPM by the repo's
  own `gadgetPPM = lowerFlat ∘ gateRots` and routed through `progGadgets`.  Every
  one of its thousands of measurements routes to a single verified-LaS gadget,
  with NOTHING uncovered.
-/
import FormalRV.QEC.Gidney21.GadgetToLaS
import FormalRV.QEC.Gidney21.Compiler.Lower
import FormalRV.Arithmetic.ModMult.ModMultDef
import FormalRV.Arithmetic.ModExp.ModExpResource

namespace FormalRV.QEC.Gidney21

open FormalRV.BQAlgo

/-! ## §1. The modular multiplier (bits = 2). -/

/-- The in-place modular multiplier (bits = 2, N = 3, a = 2, a⁻¹ = 2) → PPM:
4866 statements lowering to 3156 verified gadgets. -/
def modmultPPM : FormalRV.PPM.Prog.PPMProg := gadgetPPM (modmult_inplace_candidate 2 3 2 2)

theorem modmultPPM_fully_covered : uncoveredMeasurements modmultPPM = [] := by native_decide

/-- **★ THE MODULAR MULTIPLIER ROUTES ENTIRELY TO VERIFIED LATTICE SURGERY ★** —
every measurement of the repo-lowered in-place modular multiplier routes to a
single verified-LaS gadget, NOTHING uncovered.  Shor's order-finding is a
controlled product of exactly these. -/
theorem modmultPPM_routes_to_verified :
    (∀ k ∈ progGadgets modmultPPM, ScheduleImplementsSpec (gadgetFor k) = true)
      ∧ uncoveredMeasurements modmultPPM = [] :=
  fully_covered_program_routes_to_verified modmultPPM modmultPPM_fully_covered

/-! ## §2. THE FULL Shor modular EXPONENTIATION. -/

/-- The full Shor modular exponentiation `a^x mod N` (bits = 1) lowered to PPM —
the complete order-finding arithmetic (1198 statements). -/
def modexpPPM : FormalRV.PPM.Prog.PPMProg := gadgetPPM (shorModExp 1 3 2)

theorem modexpPPM_fully_covered : uncoveredMeasurements modexpPPM = [] := by native_decide

/-- **★★ THE FULL SHOR MODULAR EXPONENTIATION ROUTES ENTIRELY TO VERIFIED
LATTICE SURGERY ★★** — every measurement of the repo-lowered complete
`a^x mod N` arithmetic (the heart of Shor's order-finding) routes to a single
verified-LaS gadget, with NOTHING left uncovered.  The whole arithmetic spine of
fault-tolerant Shor, compiled end to end onto the verified-gadget catalog. -/
theorem modexpPPM_routes_to_verified :
    (∀ k ∈ progGadgets modexpPPM, ScheduleImplementsSpec (gadgetFor k) = true)
      ∧ uncoveredMeasurements modexpPPM = [] :=
  fully_covered_program_routes_to_verified modexpPPM modexpPPM_fully_covered

end FormalRV.QEC.Gidney21
