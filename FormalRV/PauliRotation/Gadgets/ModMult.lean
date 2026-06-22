/-
  FormalRV.PauliRotation.Gadgets.ModMult
  ──────────────────────────────────────
  THE MODULAR MULTIPLIER — the shift-and-accumulate constant multiplier and
  THE in-place MCP multiplier (`modmult_MCP_gate`, the verified Shor oracle
  building block) — compiled to Pauli rotations (`GateBridge.lean`).

  The T-count theorems inherit the family's number-theoretic hypotheses
  (`Coprime`, `Odd N`, `1 < N`, …): exactly the hypotheses under which the
  source `tcount` theorems hold (no step constant degenerates to 0).
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.ModMult.ModMultResource

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. The out-of-place constant multiplier `acc += (a·m) mod N`. -/

/-- The shift-and-accumulate constant multiplier as a rotation program. -/
def modMultConstRot (bits N a : Nat) : RotProg :=
  gateRotSchedule (modmult_const_gate bits N a)

/-- **Rotation T-count = `56·bits²`** for any valid Shor base
(`gcd(a,N) = 1`, `N` odd, `N > 1`). -/
theorem modMultConstRot_countPi8 (bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    countPi8 (modMultConstRot bits N a) = 56 * bits ^ 2 := by
  rw [modMultConstRot, gateRotSchedule_countPi8]
  exact tcount_sqir_modmult_const_gate_shor bits N a hcop hodd h1

/-- Correctness instance: the 108-gate `x ↦ 7·x mod 15` multiplier (the
README's worked example) parallelizes soundly. -/
theorem modMultConstRot_denote_2_15_7 :
    RotProg.denote (width (modmult_const_gate 2 15 7)) (modMultConstRot 2 15 7)
      = seqDenote _ (gateRots (modmult_const_gate 2 15 7)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

/-! ## §2. THE in-place MCP multiplier (the verified Shor oracle). -/

/-- The in-place MCP modular multiplier as a rotation program. -/
def modMultMCPRot (bits N a ainv : Nat) : RotProg :=
  gateRotSchedule (modmult_MCP_gate bits N a ainv)

/-- **Rotation T-count = `112·bits²`** for valid Shor parameters — the
rotation-level restatement of the family's `modmult_tcount`, about EXACTLY
the gate term the verified `modmult_correct` is about. -/
theorem modMultMCPRot_countPi8 (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    countPi8 (modMultMCPRot bits N a ainv) = 112 * bits ^ 2 := by
  rw [modMultMCPRot, gateRotSchedule_countPi8]
  exact modmult_tcount bits N a ainv hcop hcopinv hpos hlt hodd h1

/-- Correctness instance at the Shor-15 parameters (`a = 7`, `ainv = 13`). -/
theorem modMultMCPRot_denote_2_15 :
    RotProg.denote (width (modmult_MCP_gate 2 15 7 13)) (modMultMCPRot 2 15 7 13)
      = seqDenote _ (gateRots (modmult_MCP_gate 2 15 7 13)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

-- the count theorem instantiates at the anchor (hypotheses by `decide`):
example : countPi8 (modMultMCPRot 2 15 7 13) = 448 :=
  modMultMCPRot_countPi8 2 15 7 13 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end FormalRV.PauliRotation
