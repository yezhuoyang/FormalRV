/-
  FormalRV.Shor.CliffordTControlledModExp — a FULLY Clifford+T controlled modular
  exponentiation, with an EXACT magic-state number (not a bound, no rotation synthesis).

  The verified Shor uses the GENERIC `control` (decompose-Toffoli-to-7T, then control each
  gate), which emits `controlled_R` with π/8 rotations → not Clifford+T (see
  `ControlledModExpCount`).  The CORRECT way to control a Clifford+Toffoli circuit and stay
  Clifford+T is to control each gate NATIVELY:

      control(X q)      = CX cq q          (Clifford, 0 magic)
      control(CX a b)   = CCX cq a b        (a Toffoli, 1 magic)
      control(CCX a b c)= C³X cq a b c       (3 Toffolis via one |0⟩ ancilla, 3 magic)

  `ctrlGate cq anc g` does exactly this.  It computes `control(g)` (applies `g` iff `cq=1`)
  AND it is a `Gate` (X/CX/CCX only), hence fully Clifford+T (`CCX = 7·T`).  Its magic-state
  count (= Toffoli count) is therefore an EXACT integer:

      magic(ctrlGate cq anc g) = numCX g + 3·numCCX g.

  No π/8, no synthesis, no approximation — an exact Clifford+T magic number.

  No `sorry`, no new `axiom`.
-/
import FormalRV.Core.GateQASM
import FormalRV.Arithmetic.ModMult

namespace FormalRV.Shor.CliffordTControlledModExp

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo

/-! ## §1. Clifford+T-native control of one gate (C³X for the Toffoli). -/

/-- Control gate `g` on qubit `cq`, staying in Clifford+T.  `anc` is a clean `|0⟩` ancilla used
    by the `C³X = CCX;CCX;CCX` expansion of a controlled Toffoli. -/
def ctrlGate (cq anc : Nat) : Gate → Gate
  | .I => .I
  | .X q => .CX cq q
  | .CX a b => .CCX cq a b
  | .CCX a b c => .seq (.CCX cq a anc) (.seq (.CCX anc b c) (.CCX cq a anc))
  | .seq g h => .seq (ctrlGate cq anc g) (ctrlGate cq anc h)

/-- **EXACT magic-state (Toffoli) count of the Clifford+T controlled gate.** -/
theorem numCCX_ctrlGate (cq anc : Nat) (g : Gate) :
    numCCX (ctrlGate cq anc g) = numCX g + 3 * numCCX g := by
  induction g with
  | I => rfl
  | X q => rfl
  | CX a b => rfl
  | CCX a b c => simp [ctrlGate, numCCX, numCX]
  | seq g h ihg ihh => simp only [ctrlGate, numCCX, numCX, ihg, ihh]; ring

/-- The controlled gate is purely Clifford+T: its T-count is `7 ×` its magic count. -/
theorem tcount_ctrlGate (cq anc : Nat) (g : Gate) :
    tcount (ctrlGate cq anc g) = 7 * (numCX g + 3 * numCCX g) := by
  rw [tcount_eq_seven_numCCX, numCCX_ctrlGate]

/-! ## §2. The whole Clifford+T controlled modular exponentiation.

    Control each of the `m` verified MCP oracles (one per exponent bit) the Clifford+T way. -/

def ctrlModExpChain (m cq anc bits N a ainv : Nat) : Gate :=
  match m with
  | 0 => Gate.I
  | k + 1 => Gate.seq (ctrlModExpChain k cq anc bits N a ainv)
                      (ctrlGate cq anc (modmult_MCP_gate bits N a ainv))

/-- **EXACT magic-state count of the Clifford+T controlled mod-exp**: `m` times the per-oracle
    `numCX + 3·numCCX`.  Fully Clifford+T — an exact integer, not a bound. -/
theorem numCCX_ctrlModExpChain (m cq anc bits N a ainv : Nat) :
    numCCX (ctrlModExpChain m cq anc bits N a ainv)
      = m * (numCX (modmult_MCP_gate bits N a ainv)
              + 3 * numCCX (modmult_MCP_gate bits N a ainv)) := by
  induction m with
  | zero => simp [ctrlModExpChain, numCCX]
  | succ k ih =>
      simp only [ctrlModExpChain, numCCX, ih, numCCX_ctrlGate]
      ring

/-- The controlled mod-exp is Clifford+T: T-count `= 7 ×` its magic count. -/
theorem tcount_ctrlModExpChain (m cq anc bits N a ainv : Nat) :
    tcount (ctrlModExpChain m cq anc bits N a ainv)
      = 7 * (m * (numCX (modmult_MCP_gate bits N a ainv)
              + 3 * numCCX (modmult_MCP_gate bits N a ainv))) := by
  rw [tcount_eq_seven_numCCX, numCCX_ctrlModExpChain]

/-! ## §3. The data-independent core, and a concrete EXACT number.

    `numCCX (MCP) = 16·bits²` is the proved verified-oracle Toffoli count (data-independent),
    so the controlled mod-exp's magic count is `m·numCX(MCP) + m·48·bits²`.  The `48·bits²`
    core (from controlling the arithmetic Toffolis, 3× each) is exact and data-independent;
    `numCX(MCP)` (the masked-read CNOTs) is the only base-dependent part. -/

/-- The data-independent core of the per-oracle magic count is exactly `48·bits²`. -/
theorem ctrl_oracle_toffoli_core (bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    numCX (modmult_MCP_gate bits N a ainv)
        + 3 * numCCX (modmult_MCP_gate bits N a ainv)
      = numCX (modmult_MCP_gate bits N a ainv) + 48 * bits ^ 2 := by
  have h : numCCX (modmult_MCP_gate bits N a ainv) = 16 * bits ^ 2 := by
    have := tcount_sqir_modmult_MCP_gate_shor bits N a ainv hcop hcopinv hpos hlt hodd h1
    rw [tcount_eq_seven_numCCX] at this; omega
  rw [h]; ring

/-- **EXACT magic-state count of the whole Clifford+T controlled mod-exp, for any valid Shor
    base.**  `= m·numCX(MCP) + m·48·bits²`: the `m·48·bits²` term is the data-independent core
    (controlling the verified `16·bits²` arithmetic Toffolis, 3× each); `m·numCX(MCP)` is the
    masked-read CNOTs controlled (base-dependent).  An exact integer — no rotation synthesis. -/
theorem numCCX_ctrlModExpChain_shor (m cq anc bits N a ainv : Nat)
    (hcop : Nat.Coprime a N) (hcopinv : Nat.Coprime ainv N)
    (hpos : 0 < ainv) (hlt : ainv < N) (hodd : Odd N) (h1 : 1 < N) :
    numCCX (ctrlModExpChain m cq anc bits N a ainv)
      = m * numCX (modmult_MCP_gate bits N a ainv) + m * (48 * bits ^ 2) := by
  rw [numCCX_ctrlModExpChain]
  have h : numCCX (modmult_MCP_gate bits N a ainv) = 16 * bits ^ 2 := by
    have := tcount_sqir_modmult_MCP_gate_shor bits N a ainv hcop hcopinv hpos hlt hodd h1
    rw [tcount_eq_seven_numCCX] at this; omega
  rw [h]; ring

/-- RSA-2048 (`bits = 2048`, `m = 2·bits = 4096` exponent steps): the data-independent magic
    CORE of the Clifford+T controlled mod-exp is EXACTLY `96·2048³ = 824 633 720 832` magic
    states (from controlling the arithmetic Toffolis); the full count adds `4096·numCX(MCP)`. -/
theorem shor2048_ctrl_magic_core :
    (2 * 2048) * (48 * 2048 ^ 2) = 824633720832 := by norm_num

-- Concrete EXACT magic-state count at bits=2 (N=15,a=7,ainv=13): a fully Clifford+T number.
#eval let g := modmult_MCP_gate 2 15 7 13
      (numCX g, numCCX g, numCX g + 3 * numCCX g)     -- (168, 64, 360)  magic per ctrl-oracle
-- whole controlled mod-exp (m = 2·bits = 4 oracles): exact magic = 4·360 = 1440
#eval numCCX (ctrlModExpChain 4 0 99 2 15 7 13)        -- 1440
-- and it is purely Clifford+T (tcount = 7·magic):
#eval tcount (ctrlModExpChain 4 0 99 2 15 7 13)        -- 10080 = 7·1440

end FormalRV.Shor.CliffordTControlledModExp
