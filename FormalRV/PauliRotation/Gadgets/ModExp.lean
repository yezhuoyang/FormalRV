/-
  FormalRV.PauliRotation.Gadgets.ModExp
  ─────────────────────────────────────
  MODULAR EXPONENTIATION (Shor's order-finding oracle layer), compiled to
  Pauli rotations (`GateBridge.lean`):

    • `shorModExpVerified` — the chain of `2·bits` VERIFIED in-place MCP
      multipliers (each step is the term the verified Shor theorem uses);
      rotation T-count `224·bits³`.
    • `shorModExp` — the out-of-place COUNTING-MODEL chain; `112·bits³`.

  HONESTY (inherited from the family's own headers, restated here): the
  chains have EXACT per-term T-counts, but the chain-computes-`a^x mod N`
  theorem is NOT proven (count-only/scaffolded); `shorModExp` additionally
  has no feedback (counting model only).  The rotation programs below are
  faithful compilations of THOSE terms — no more, no less.
-/
import FormalRV.PauliRotation.Compiler.GateBridge
import FormalRV.Arithmetic.ModExp.ModExpResource

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource
open FormalRV.BQAlgo

/-! ## §1. The verified-oracle chain. -/

/-- The `2·bits`-fold chain of verified in-place MCP multipliers as a
rotation program. -/
def shorModExpVerifiedRot (bits N a ainv : Nat) : RotProg :=
  gateRotSchedule (shorModExpVerified bits N a ainv)

/-- **Rotation T-count = `224·bits³`** for valid Shor parameters. -/
theorem shorModExpVerifiedRot_countPi8 (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    countPi8 (shorModExpVerifiedRot bits N a ainv) = 224 * bits ^ 3 := by
  rw [shorModExpVerifiedRot, gateRotSchedule_countPi8]
  exact tcount_shorModExpVerified bits N a ainv hcop hcopinv hpos hlt hodd h1

/-- Correctness instance at 1-bit Shor-15 parameters (kept small: the
side-condition `decide` walks the whole gate term). -/
theorem shorModExpVerifiedRot_denote_1 :
    RotProg.denote (width (shorModExpVerified 1 15 7 13))
        (shorModExpVerifiedRot 1 15 7 13)
      = seqDenote _ (gateRots (shorModExpVerified 1 15 7 13)) :=
  gateRotSchedule_denote _ _ (by decide) (Nat.le_refl _)

-- the count theorem at the Shor-15 anchor: 224·2³ = 1792 T-level rotations
example : countPi8 (shorModExpVerifiedRot 2 15 7 13) = 1792 :=
  shorModExpVerifiedRot_countPi8 2 15 7 13 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ## §2. The counting-model chain. -/

/-- The out-of-place counting-model chain as a rotation program
(⚠ counting model: not a valid mod-exp; see header). -/
def shorModExpRot (bits N a : Nat) : RotProg :=
  gateRotSchedule (shorModExp bits N a)

/-- **Rotation T-count = `112·bits³`** for any valid Shor base. -/
theorem shorModExpRot_countPi8 (bits N a : Nat)
    (hcop : Nat.Coprime a N) (hodd : Odd N) (h1 : 1 < N) :
    countPi8 (shorModExpRot bits N a) = 112 * bits ^ 3 := by
  rw [shorModExpRot, gateRotSchedule_countPi8]
  exact tcount_shorModExp bits N a hcop hodd h1

end FormalRV.PauliRotation
