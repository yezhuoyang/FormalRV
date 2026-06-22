/-
  FormalRV.PauliRotation.Compiler.CircuitCompile
  ─────────────────────────────────────
  The TOP of the pipeline: logical Clifford+T/Toffoli circuits → naive
  gate-by-gate rotation sequence (the standard dictionary, `Compile.lean`)
  → VERIFIED ASAP parallelization (`Scheduler.lean`):

      compileScheduled gs  =  scheduleList (compileNaive gs)

  with the end-to-end theorem `compileScheduled_denote`: the parallelized
  layers denote EXACTLY the naive sequence (side condition: every emitted
  axis canonical and in width — DECIDABLE, so concrete circuits discharge it
  by `decide`).

  HONESTY: this verifies the OPTIMIZER leg (reorder/parallelize preserves
  semantics, counts preserved on the nose).  The DICTIONARY leg (the naive
  sequence denotes the gate matrices, up to global phase) is the known
  open item (`README.md` gap 2); until it lands, `seqDenote (compileNaive gs)`
  is the specification the schedule provably meets.
-/
import FormalRV.PauliRotation.Compiler.Scheduler

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Resource

/-! ## §1. The logical gate set and the naive compiler. -/

/-- A logical circuit gate (Clifford + T + Toffoli-class).  Multi-qubit
gates expect distinct operands; `CCZ`/`CCX` expect `a < b < c` (canonical
operand order). -/
inductive LGate where
  | X (q : Nat) | Y (q : Nat) | Z (q : Nat)
  | H (q : Nat) | S (q : Nat) | Sdg (q : Nat) | T (q : Nat) | Tdg (q : Nat)
  | CNOT (c t : Nat)
  | CCZ (a b c : Nat)
  | CCX (a b c : Nat)
  deriving Repr, DecidableEq

/-- Naive per-gate compilation: the standard dictionary, serialized. -/
def LGate.compile : LGate → List Rot
  | .X q        => (xGate q).flatten
  | .Y q        => (yGate q).flatten
  | .Z q        => (zGate q).flatten
  | .H q        => (hGate q).flatten
  | .S q        => (sGate q).flatten
  | .Sdg q      => (sDag q).flatten
  | .T q        => (tGate q).flatten
  | .Tdg q      => (tDag q).flatten
  | .CNOT c t   => (cnotGate c t).flatten
  | .CCZ a b c  => (cczGate a b c).flatten
  | .CCX a b c  => (hGate c).flatten ++ (cczGate a b c).flatten ++ (hGate c).flatten

/-- Naive circuit compilation: gate by gate, in sequence. -/
def compileNaive (gs : List LGate) : List Rot := gs.flatMap LGate.compile

/-- **The compiled-and-parallelized program.** -/
def compileScheduled (gs : List LGate) : RotProg :=
  scheduleList (compileNaive gs)

/-! ## §2. End-to-end theorems. -/

/-- **END-TO-END OPTIMIZER CORRECTNESS**: the parallel layers denote exactly
the naive gate-by-gate sequence.  The side condition (canonical axes, in
width) is decidable — concrete circuits discharge it by `decide`. -/
theorem compileScheduled_denote (n : Nat) (gs : List LGate)
    (h : ∀ r ∈ compileNaive gs,
          sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ n) :
    RotProg.denote n (compileScheduled gs) = seqDenote n (compileNaive gs) :=
  scheduleList_denote n (compileNaive gs) h

/-- The T-count of the schedule is the T-count of the naive sequence —
parallelization never creates or destroys non-Clifford content. -/
theorem compileScheduled_countPi8 (gs : List LGate) :
    countPi8 (compileScheduled gs)
      = (compileNaive gs).countP (fun r => r.angle == RAngle.piEighth) :=
  scheduleList_countPi8 (compileNaive gs)

/-- Depth never exceeds the sequential rotation count. -/
theorem compileScheduled_depth_le (gs : List LGate) :
    rotDepth (compileScheduled gs) ≤ (compileNaive gs).length :=
  scheduleList_depth_le (compileNaive gs)

/-! ## §3. A worked circuit, kernel-checked end to end.

`T(0); T(1); CNOT(0,1)` — five rotations naively (depth 5), scheduled into
TWO layers: the two T's and the CNOT's `Z₀`-rotation all commute into the
first layer; the `Z₀X₁` and `X₁` rotations follow in the second. -/

def demoCircuit : List LGate := [.T 0, .T 1, .CNOT 0 1]

-- the decidable side condition of the end-to-end theorem, at width 2:
example : ∀ r ∈ compileNaive demoCircuit,
    sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ 2 := by decide

example : (compileNaive demoCircuit).length = 5 := by decide   -- naive: depth 5
example : rotDepth (compileScheduled demoCircuit) = 2 := by decide -- scheduled: 2
example : countPi8 (compileScheduled demoCircuit) = 2 := by decide
example : RotProg.wf (compileScheduled demoCircuit) = true := by decide

/-! A Toffoli compiles to 13 rotations (3 + 7 + 3) and schedules to depth 5:
`[Z₂-with-Z-cluster] → [X₂] → [Z-cluster ∪ Z₂-cluster] → [X₂] → [Z₂]`. -/

example : (compileNaive [.CCX 0 1 2]).length = 13 := by decide
example : rotDepth (compileScheduled [.CCX 0 1 2]) = 5 := by decide
example : countPi8 (compileScheduled [.CCX 0 1 2]) = 7 := by decide

/-! Two disjoint Toffolis: same depth 5, not 10 — the scheduler interleaves
them into the SAME five layers. -/

example : rotDepth (compileScheduled [.CCX 0 1 2, .CCX 3 4 5]) = 5 := by decide
example : countPi8 (compileScheduled [.CCX 0 1 2, .CCX 3 4 5]) = 14 := by decide

end FormalRV.PauliRotation
