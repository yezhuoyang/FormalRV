/-
  FormalRV.Resource.GateCount
  ───────────────────────────
  The canonical, INDEPENDENT resource counters for the reversible `Gate` IR.

  ## The separation discipline (why this folder exists)

  A resource counter is an HONEST recursive tree-walk over a syntactic object —
  nothing else.  This module imports ONLY the IR (`Core.Gate`); it knows nothing
  about how a circuit is *built* (the gadget constructors) or *proved correct*
  (the semantics).  Because the counters live in their own world, a resource
  theorem `countT (gadget n) = 14·n` CANNOT fudge the count — the number is
  forced by the syntax tree, and a skeptic can `#eval` the counter on a
  constructed circuit to check it WITHOUT reading any proof.

  Resource verification then has the shape John requires: a concrete syntactic
  object (or a generator that builds it), a proof it is semantically correct, and
  a proof that THESE counters applied to THAT object equal the closed form.

  `countT` agrees with the legacy `Gate.tcount` (bridge `countT_eq_tcount`), so
  existing resource theorems interoperate; new per-gate counters (`countCNOT`,
  `countToffoli`, `countX`) are added here.
-/
import FormalRV.Core.Gate

namespace FormalRV.Resource

open FormalRV.Framework

/-! ## §1. The Gate-IR counters (honest recursive tree-walks). -/

/-- **T-count.**  7 per Toffoli (textbook decomposition); Cliffords and identity
are T-free.  Sums over `seq`. -/
def countT : Gate → Nat
  | .I         => 0
  | .X _       => 0
  | .CX _ _    => 0
  | .CCX _ _ _ => 7
  | .seq a b   => countT a + countT b

/-- **CNOT count.** -/
def countCNOT : Gate → Nat
  | .CX _ _    => 1
  | .seq a b   => countCNOT a + countCNOT b
  | _          => 0

/-- **Toffoli (CCX) count.** -/
def countToffoli : Gate → Nat
  | .CCX _ _ _ => 1
  | .seq a b   => countToffoli a + countToffoli b
  | _          => 0

/-- **X (NOT) count.** -/
def countX : Gate → Nat
  | .X _       => 1
  | .seq a b   => countX a + countX b
  | _          => 0

/-- **Total gate count** (identity is free). -/
def gateCount : Gate → Nat
  | .I         => 0
  | .X _       => 1
  | .CX _ _    => 1
  | .CCX _ _ _ => 1
  | .seq a b   => gateCount a + gateCount b

/-- **Sequential depth** (a TIME resource). -/
def depth : Gate → Nat
  | .I         => 0
  | .X _       => 1
  | .CX _ _    => 1
  | .CCX _ _ _ => 1
  | .seq a b   => depth a + depth b

/-! ### Space resource: the qubit count.

The gate/depth counters above are TIME resources.  `width` is the SPACE
resource — the number of qubits the circuit needs. -/

/-- **Qubit count (register width).**  The largest qubit index the circuit
touches, plus one — the size of the register the machine must allocate.  (Gate-IR
gadgets use dense `0..w-1` indexing, so this is the qubit count.)  This is the
SPACE resource, dual to the gate counts (TIME). -/
def width : Gate → Nat
  | .I         => 0
  | .X q       => q + 1
  | .CX c t    => max (c + 1) (t + 1)
  | .CCX a b c => max (max (a + 1) (b + 1)) (c + 1)
  | .seq a b   => max (width a) (width b)

/-! ## §2. Compositional laws (the counters distribute over `seq`). -/

@[simp] theorem countT_seq (a b : Gate) : countT (.seq a b) = countT a + countT b := rfl
@[simp] theorem countCNOT_seq (a b : Gate) : countCNOT (.seq a b) = countCNOT a + countCNOT b := rfl
@[simp] theorem countToffoli_seq (a b : Gate) : countToffoli (.seq a b) = countToffoli a + countToffoli b := rfl
@[simp] theorem gateCount_seq (a b : Gate) : gateCount (.seq a b) = gateCount a + gateCount b := rfl

/-! ## §3. Bridges to the legacy `Core.Gate` counters (interoperability).

The arithmetic resource theorems are stated with `Gate.tcount` / `Gate.gcount`;
these bridges show the canonical `Resource` counters are the SAME functions, so
those theorems are already statements about `Resource.countT` / `gateCount`. -/

@[simp] theorem countT_eq_tcount (g : Gate) : countT g = Gate.tcount g := by
  induction g with
  | seq a b iha ihb => simp [countT, Gate.tcount, iha, ihb]
  | _ => rfl

@[simp] theorem gateCount_eq_gcount (g : Gate) : gateCount g = Gate.gcount g := by
  induction g with
  | seq a b iha ihb => simp [gateCount, Gate.gcount, iha, ihb]
  | _ => rfl

@[simp] theorem depth_eq_gateDepth (g : Gate) : depth g = Gate.depth g := by
  induction g with
  | seq a b iha ihb => simp [depth, Gate.depth, iha, ihb]
  | _ => rfl

/-! ## §4. Internal consistency: the T-count is exactly 7 per Toffoli.

This ties two INDEPENDENT counters together — proof that `countT` really is "7 ×
Toffolis", computed from the same tree. -/

theorem countT_eq_seven_countToffoli (g : Gate) :
    countT g = 7 * countToffoli g := by
  induction g with
  | seq a b iha ihb => simp only [countT, countToffoli, iha, ihb]; omega
  | _ => rfl

/-! ## §5. Smoke checks — a skeptic can `#eval` any counter on a built circuit. -/

example : countT (.CCX 0 1 2) = 7 := by decide
example : countCNOT (.seq (.CX 0 1) (.CX 1 2)) = 2 := by decide
example : countToffoli (.seq (.CCX 0 1 2) (.CCX 1 2 3)) = 2 := by decide
example : gateCount (.seq (.X 0) (.CCX 0 1 2)) = 2 := by decide
example : countT (.seq (.CCX 0 1 2) (.CCX 0 1 2)) = 7 * countToffoli (.seq (.CCX 0 1 2) (.CCX 0 1 2)) :=
  countT_eq_seven_countToffoli _
example : width (.CCX 0 1 2) = 3 := by decide          -- SPACE: 3 qubits
example : width (.seq (.X 0) (.CX 1 2)) = 3 := by decide

end FormalRV.Resource
