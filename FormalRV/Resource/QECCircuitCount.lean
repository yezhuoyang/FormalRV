/-
  FormalRV.Resource.QECCircuitCount — canonical independent counters for the
  QEC-layer physical-circuit IR (`FormalRV.QEC.Circuit.PhysCircuit`).

  ## Discipline (see FormalRV/Resource/README.md)

  Counters are honest tree-walks importing ONLY the circuit IR — never gadget
  constructors or correctness proofs — so `counter(object) = formula` theorems
  cannot be fudged and a skeptic can `#eval` the counter on the constructed
  object.  The per-gadget count theorems (e.g. that the compiled syndrome-
  extraction circuit of a surgery gadget has width `surgeryPhysQubits g`)
  live with the gadgets, in `FormalRV/QEC/Circuit/ExtractionCount.lean`.

  ## TIME vs SPACE

  * TIME : `cxCountC` (two-qubit gates), `measCountC`, `prepCountC`,
           `opCountC` (total ops = sequential-depth upper bound, one op per
           step — the IR is a flat sequential list; logical-cycle time is the
           `FormalRV/QEC/Time/LogicalCycle.lean` algebra, not a gate count).
  * SPACE: `widthC` — max touched virtual-qubit index + 1.  Because syndrome
           and surgery ancillas are explicit indices in the syntax tree, they
           are counted; this is the layer at which "hidden" QEC overhead
           becomes visible to a skeptic.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.Circuit.PhysCircuit
import FormalRV.Resource.Interface

namespace FormalRV.Resource

open FormalRV.QEC.Circuit

/-! ## TIME: operation counters -/

/-- Number of CNOTs. -/
def cxCountC (c : PhysCircuit) : Nat := c.countP (fun op => op.isCX)

/-- Number of measurements. -/
def measCountC (c : PhysCircuit) : Nat := c.countP (fun op => op.isMeas)

/-- Number of basis preparations (resets). -/
def prepCountC (c : PhysCircuit) : Nat := c.countP (fun op => op.isPrep)

/-- Total operation count (= sequential-step upper bound). -/
def opCountC (c : PhysCircuit) : Nat := c.length

@[simp] theorem cxCountC_nil : cxCountC [] = 0 := rfl
@[simp] theorem measCountC_nil : measCountC [] = 0 := rfl
@[simp] theorem prepCountC_nil : prepCountC [] = 0 := rfl

theorem cxCountC_append (c d : PhysCircuit) :
    cxCountC (c ++ d) = cxCountC c + cxCountC d := List.countP_append ..

theorem measCountC_append (c d : PhysCircuit) :
    measCountC (c ++ d) = measCountC c + measCountC d := List.countP_append ..

theorem prepCountC_append (c d : PhysCircuit) :
    prepCountC (c ++ d) = prepCountC c + prepCountC d := List.countP_append ..

theorem opCountC_append (c d : PhysCircuit) :
    opCountC (c ++ d) = opCountC c + opCountC d := List.length_append ..

/-- Counter reconciliation: every operation is exactly one of prep/CX/meas. -/
theorem opCountC_eq_parts (c : PhysCircuit) :
    opCountC c = prepCountC c + cxCountC c + measCountC c := by
  induction c with
  | nil => rfl
  | cons op rest ih =>
    cases op <;>
      simp [opCountC, prepCountC, cxCountC, measCountC,
            PhysOp.isPrep, PhysOp.isCX, PhysOp.isMeas,
            List.length_cons] at * <;>
      omega

/-! ## SPACE: register width -/

/-- Footprint of one operation: max touched index + 1. -/
def opWidth : PhysOp → Nat
  | .prep _ q => q + 1
  | .cx c t   => max c t + 1
  | .meas _ q => q + 1

/-- Register width: max touched virtual-qubit index + 1 (0 for the empty
    circuit).  Dense `0..w−1` indexing assumed, as for `Resource.width` on the
    `Gate` IR. -/
def widthC (c : PhysCircuit) : Nat :=
  c.foldr (fun op acc => max (opWidth op) acc) 0

@[simp] theorem widthC_nil : widthC [] = 0 := rfl

@[simp] theorem widthC_cons (op : PhysOp) (c : PhysCircuit) :
    widthC (op :: c) = max (opWidth op) (widthC c) := rfl

/-- Width of a concatenation is the max of the widths (space is shared, not
    added — virtual qubits are reused by index, never double-counted). -/
theorem widthC_append (c d : PhysCircuit) :
    widthC (c ++ d) = max (widthC c) (widthC d) := by
  induction c with
  | nil => simp
  | cons op rest ih =>
    simp [List.cons_append, widthC_cons, ih, Nat.max_assoc]

/-! ## Data vs. ancilla qubits (walked from the circuit).

  A qubit is an ANCILLA if the circuit ever PREPS (resets) or MEASURES it —
  the syndrome / surgery qubits, allocated and read out each round.  A qubit
  is DATA if it is only ever a CX endpoint and is NEVER prepped or measured —
  the persistent logical data of a code patch.  Both counters DEDUP-walk the
  actual circuit, so the totals are read off the syntactic object. -/

open FormalRV.QEC.Circuit in
/-- The qubit a prep/meas op acts on (ancilla activity); `none` for `cx`. -/
def ancillaOpQubit : PhysOp → Option Nat
  | .prep _ q => some q
  | .meas _ q => some q
  | .cx _ _   => none

open FormalRV.QEC.Circuit in
/-- The distinct ANCILLA qubits of a circuit: those prepped or measured. -/
def ancillaQubits (c : PhysCircuit) : List Nat :=
  (c.filterMap ancillaOpQubit).dedup

open FormalRV.QEC.Circuit in
/-- The distinct DATA qubits: CX endpoints that are never prepped/measured. -/
def dataQubits (c : PhysCircuit) : List Nat :=
  ((c.flatMap PhysOp.touches).filter (fun q => q ∉ ancillaQubits c)).dedup

open FormalRV.QEC.Circuit in
/-- **Number of ANCILLA qubits used** (independent walk of the circuit). -/
def numAncillaQubits (c : PhysCircuit) : Nat := (ancillaQubits c).length

open FormalRV.QEC.Circuit in
/-- **Number of DATA qubits used** (independent walk of the circuit). -/
def numDataQubits (c : PhysCircuit) : Nat := (dataQubits c).length

open FormalRV.QEC.Circuit in
/-- **Total distinct physical qubits used** = data + ancilla (no double
counting — data and ancilla qubit-sets are disjoint by definition: a data
qubit is never prepped/measured, an ancilla qubit always is). -/
def numPhysQubits (c : PhysCircuit) : Nat :=
  numDataQubits c + numAncillaQubits c

open FormalRV.QEC.Circuit in
/-- Data and ancilla qubit sets are DISJOINT (the split is well-defined). -/
theorem data_ancilla_disjoint (c : PhysCircuit) (q : Nat)
    (hd : q ∈ dataQubits c) : q ∉ ancillaQubits c := by
  unfold dataQubits at hd
  rw [List.mem_dedup, List.mem_filter] at hd
  exact (by simpa using hd.2)

/-! ## Interface instance -/

instance : HasResourceCount FormalRV.QEC.Circuit.PhysCircuit where
  cnot   := cxCountC
  gates  := opCountC
  qubits := widthC

end FormalRV.Resource
