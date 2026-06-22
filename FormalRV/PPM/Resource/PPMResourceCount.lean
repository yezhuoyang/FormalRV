/-
  FormalRV.PPM.Resource.PPMResourceCount — resource accounting on the PPM IR.

  Resource counts are carried on the SAME `QasmOp` IR we emit (`PPMToQASM`) and
  prove semantically correct (`GadgetChannel`).  This is the "resource count after
  the correctness proof" layer: every count is a pure function of the program, the
  per-gadget counts are proved by `decide`, and they are ADDITIVE over program
  concatenation (`*_append`), so the cost of any composed PPM program is the sum of
  its parts — the parametric formula a full-scale estimate instantiates.

  ## What is and isn't provable at full RSA-2048 scale (honest)

  * EXACT and proved here: the per-gadget resource vector (logical qubits, magic
    states consumed, Pauli measurements, Clifford gates, feed-forward corrections)
    for the T and CCZ teleportation gadgets, and additivity.
  * For the full 2048-bit circuit: the total = (per-component counts, already
    proved elsewhere, e.g. 462 T / windowed adder) × (the modexp/QFT structure).
    That whole-circuit assembly is the SAME residual as the semantic side — the
    full Shor→Clifford+T→PPM program is not assembled gate-by-gate — so a single
    proved 2048 total is not delivered; the per-gadget vector + additivity ARE.

  No `sorry`, no new `axiom`.
-/
import FormalRV.PPM.Codegen.PPMToQASM

namespace FormalRV.PPM.Resource.PPMResourceCount

open FormalRV.PPM.PPMToQASM

/-! ## §1. Per-op classifiers (plain functions; `QasmOp` lives in `PPMToQASM`). -/

/-- `T` magic state consumed (the `|T⟩` prep). -/
def isTMagic : QasmOp → Bool | .opT _ => true | _ => false
/-- `CCZ` magic state consumed. -/
def isCCZMagic : QasmOp → Bool | .opCCZ _ _ _ => true | _ => false
/-- Destructive Z-basis (ancilla) measurement. -/
def isMeas : QasmOp → Bool | .opMeas _ _ => true | _ => false
/-- Classically-controlled feed-forward correction (single- or AND-of-two-bit). -/
def isFeedforward : QasmOp → Bool
  | .opIf _ _ => true | .opIf2 _ _ _ => true | _ => false
/-- A Clifford gate (H/S/X/Z/CX/CZ). -/
def isClifford : QasmOp → Bool
  | .opH _ => true | .opS _ => true | .opX _ => true | .opZ _ => true
  | .opCX _ _ => true | .opCZ _ _ => true | _ => false

/-- Highest qubit index a single op touches (feed-forward recurses into its body). -/
def maxQubitOf : QasmOp → Nat
  | .opH q | .opT q | .opS q | .opX q | .opZ q => q
  | .opCX a b | .opCZ a b => max a b
  | .opCCZ a b c => max a (max b c)
  | .opMeas q _ => q
  | .opIf _ op | .opIf2 _ _ op => maxQubitOf op

/-! ## §2. Program-level counts (additive over `++`). -/

def numTMagic      (ops : List QasmOp) : Nat := ops.countP isTMagic
def numCCZMagic    (ops : List QasmOp) : Nat := ops.countP isCCZMagic
def numMeas        (ops : List QasmOp) : Nat := ops.countP isMeas
def numFeedforward (ops : List QasmOp) : Nat := ops.countP isFeedforward
def numClifford    (ops : List QasmOp) : Nat := ops.countP isClifford
/-- Logical-qubit count = highest index used + 1. -/
def numQubits      (ops : List QasmOp) : Nat :=
  1 + ops.foldr (fun op acc => max (maxQubitOf op) acc) 0
/-- Sequential-length upper bound on circuit depth (each op one layer). -/
def seqDepth       (ops : List QasmOp) : Nat := ops.length

/-! ## §3. ADDITIVITY — the parametric composition law.  Each count (except the
    `max`-based `numQubits`) is additive over program concatenation. -/

theorem numTMagic_append (p q : List QasmOp) :
    numTMagic (p ++ q) = numTMagic p + numTMagic q := by
  simp [numTMagic, List.countP_append]
theorem numCCZMagic_append (p q : List QasmOp) :
    numCCZMagic (p ++ q) = numCCZMagic p + numCCZMagic q := by
  simp [numCCZMagic, List.countP_append]
theorem numMeas_append (p q : List QasmOp) :
    numMeas (p ++ q) = numMeas p + numMeas q := by
  simp [numMeas, List.countP_append]
theorem numFeedforward_append (p q : List QasmOp) :
    numFeedforward (p ++ q) = numFeedforward p + numFeedforward q := by
  simp [numFeedforward, List.countP_append]
theorem numClifford_append (p q : List QasmOp) :
    numClifford (p ++ q) = numClifford p + numClifford q := by
  simp [numClifford, List.countP_append]
theorem seqDepth_append (p q : List QasmOp) :
    seqDepth (p ++ q) = seqDepth p + seqDepth q := by
  simp [seqDepth]

/-! ## §4. The proved per-gadget resource vectors. -/

-- T gate-teleportation gadget (`PPMToQASM.tGadgetOps`).
theorem tGadget_qubits      : numQubits tGadgetOps = 2 := by decide
theorem tGadget_TMagic      : numTMagic tGadgetOps = 1 := by decide
theorem tGadget_CCZMagic    : numCCZMagic tGadgetOps = 0 := by decide
theorem tGadget_meas        : numMeas tGadgetOps = 1 := by decide
theorem tGadget_feedforward : numFeedforward tGadgetOps = 1 := by decide
-- 2 = H (in the |T⟩ prep) + CX; the S correction is inside the feed-forward op.
theorem tGadget_clifford    : numClifford tGadgetOps = 2 := by decide

-- CCZ state-teleportation gadget (`PPMToQASM.cczGadgetOps`).
theorem cczGadget_qubits      : numQubits cczGadgetOps = 6 := by decide
theorem cczGadget_TMagic      : numTMagic cczGadgetOps = 0 := by decide
theorem cczGadget_CCZMagic    : numCCZMagic cczGadgetOps = 1 := by decide
theorem cczGadget_meas        : numMeas cczGadgetOps = 3 := by decide
theorem cczGadget_feedforward : numFeedforward cczGadgetOps = 6 := by decide
theorem cczGadget_clifford    : numClifford cczGadgetOps = 6 := by decide

/-! ## §5. Additivity in action: the cost of a composed program is the sum. -/

example : numMeas (tGadgetOps ++ cczGadgetOps) = 4 := by
  rw [numMeas_append, tGadget_meas, cczGadget_meas]
example : numTMagic (tGadgetOps ++ cczGadgetOps) = 1 := by
  rw [numTMagic_append, tGadget_TMagic, cczGadget_TMagic]
example : numCCZMagic (tGadgetOps ++ cczGadgetOps) = 1 := by
  rw [numCCZMagic_append, tGadget_CCZMagic, cczGadget_CCZMagic]

-- Inspect the full resource vectors:
#eval (numQubits tGadgetOps, numTMagic tGadgetOps, numMeas tGadgetOps,
       numClifford tGadgetOps, numFeedforward tGadgetOps, seqDepth tGadgetOps)
#eval (numQubits cczGadgetOps, numCCZMagic cczGadgetOps, numMeas cczGadgetOps,
       numClifford cczGadgetOps, numFeedforward cczGadgetOps, seqDepth cczGadgetOps)

end FormalRV.PPM.Resource.PPMResourceCount
