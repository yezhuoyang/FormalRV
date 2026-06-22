/-
  FormalRV.QEC.Circuit.PhysCircuit — the LOW-LEVEL SYNTACTIC circuit IR of the
  QEC layer.

  ## Charter (John, 2026-06-10)

  The QEC layer creates and verifies the syntactic object needed for
  fault-tolerant Shor **assuming infinitely many qubits**: every qubit index
  here is a VIRTUAL qubit (a bare `Nat`), allocation is free, and there is no
  placement, routing, hardware mapping, or wallclock time.  Whether a finite
  machine can realise this demand in a given time is the `FormalRV.System`
  layer's question, not ours.

  ## What this file is

  The minimal physical-operation vocabulary needed so that syndrome-extraction
  circuits exist as LEAN OBJECTS rather than only as emitted Stim strings
  (`QEC/LatticeSurgery/StimEmit.lean`):

    * `PhysOp`     — basis preparation (reset), CNOT, basis measurement;
    * `PhysCircuit`— a sequential list of `PhysOp`s;
    * `CheckBlock` — the structured unit of syndrome extraction: one ancilla,
                     one CNOT fan over a stabilizer support, one measurement
                     (exactly the `RX/CX…/MX` and `R/CX…/M` blocks Stim sees);
    * `Round`      — a list of check blocks (one syndrome-extraction round);
    * Stim serialization `toStim`, so the legacy string emitter becomes a
      serializer OF this IR (bridge theorems in `SyndromeExtraction.lean`).

  Because syndrome ancillas, surgery ancillas, and (later) teleportation
  ancillas are explicit indices IN the syntax tree, the independent tree-walk
  counters in `FormalRV/Resource/QECCircuitCount.lean` can count exactly the
  overhead the top layer neglects.  Semantics (the circuit implements the
  intended Pauli-product measurement) lives in `CircuitSemantics.lean`.

  This file is a LEAF: it imports nothing, so the resource counters can import
  it without seeing any gadget constructor or proof (the `Resource/` charter).

  No Mathlib.  Pure Bool / Nat / List.  Decidable everywhere.
-/

namespace FormalRV.QEC.Circuit

/-! ## Bases, operations, circuits -/

/-- Preparation/measurement basis: computational (`z`, i.e. `|0⟩`/`M`) or
    Hadamard (`x`, i.e. `|+⟩`/`MX`). -/
inductive MeasBasis where
  | z
  | x
  deriving DecidableEq, Repr, BEq, Inhabited

/-- One physical operation over VIRTUAL qubits (unbounded `Nat` indices).

    * `prep b q`  — reset qubit `q` to the `+1` eigenstate of basis `b`
                    (`|0⟩` for `z`, `|+⟩` for `x`);
    * `cx c t`    — CNOT with control `c`, target `t`;
    * `meas b q`  — measure qubit `q` in basis `b`. -/
inductive PhysOp where
  | prep (b : MeasBasis) (q : Nat)
  | cx (c t : Nat)
  | meas (b : MeasBasis) (q : Nat)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A physical circuit: a sequential list of operations.  (Parallelism is a
    LOGICAL-CYCLE-level notion — see `FormalRV/QEC/Time/LogicalCycle.lean` —
    not a gate-moment notion; the demand layer never needs hardware moments.) -/
abbrev PhysCircuit := List PhysOp

namespace PhysOp

/-- The virtual qubits an operation touches. -/
def touches : PhysOp → List Nat
  | .prep _ q => [q]
  | .cx c t   => [c, t]
  | .meas _ q => [q]

def isCX : PhysOp → Bool
  | .cx _ _ => true
  | _       => false

def isMeas : PhysOp → Bool
  | .meas _ _ => true
  | _         => false

def isPrep : PhysOp → Bool
  | .prep _ _ => true
  | _         => false

end PhysOp

/-! ## Check-row supports

    A recursive (induction-friendly) definition of the support of a GF(2)
    check row.  `rowSupportFrom row i` lists the absolute indices of the
    `true` entries of `row`, where `row` starts at absolute index `i`. -/

/-- Indices of `true` entries, offset by the starting index `i`. -/
def rowSupportFrom : List Bool → Nat → List Nat
  | [],        _ => []
  | b :: rest, i =>
      if b then i :: rowSupportFrom rest (i + 1)
      else rowSupportFrom rest (i + 1)

/-- The support of a check row (indices of its `true` entries). -/
def rowSupport (row : List Bool) : List Nat := rowSupportFrom row 0

/-- Every support index of `rowSupportFrom row i` is `≥ i`. -/
theorem rowSupportFrom_ge (row : List Bool) :
    ∀ (i : Nat), ∀ j ∈ rowSupportFrom row i, i ≤ j := by
  induction row with
  | nil => intro i j hj; cases hj
  | cons b rest ih =>
    intro i j hj
    by_cases hb : b
    · simp only [rowSupportFrom, hb, if_true] at hj
      rcases List.mem_cons.mp hj with h | h
      · exact h ▸ Nat.le_refl i
      · exact Nat.le_of_succ_le (ih (i + 1) j h)
    · simp only [rowSupportFrom, hb] at hj
      exact Nat.le_of_succ_le (ih (i + 1) j hj)

/-- Every support index of `rowSupportFrom row i` is `< i + row.length`. -/
theorem rowSupportFrom_lt (row : List Bool) :
    ∀ (i : Nat), ∀ j ∈ rowSupportFrom row i, j < i + row.length := by
  induction row with
  | nil => intro i j hj; cases hj
  | cons b rest ih =>
    intro i j hj
    have hsucc : i + (b :: rest).length = (i + 1) + rest.length := by
      simp only [List.length_cons]; omega
    by_cases hb : b
    · simp only [rowSupportFrom, hb, if_true] at hj
      rcases List.mem_cons.mp hj with h | h
      · subst h; simp only [List.length_cons]; omega
      · rw [hsucc]; exact ih (i + 1) j h
    · simp only [rowSupportFrom, hb] at hj
      rw [hsucc]; exact ih (i + 1) j hj

/-- Support indices are distinct (the recursion emits strictly increasing
    indices). -/
theorem rowSupportFrom_nodup (row : List Bool) :
    ∀ (i : Nat), (rowSupportFrom row i).Nodup := by
  induction row with
  | nil => intro _; exact List.nodup_nil
  | cons b rest ih =>
    intro i
    by_cases hb : b
    · simp only [rowSupportFrom, hb, if_true]
      refine List.nodup_cons.mpr ⟨?_, ih (i + 1)⟩
      intro hmem
      have := rowSupportFrom_ge rest (i + 1) i hmem
      omega
    · simp only [rowSupportFrom, hb]
      exact ih (i + 1)

/-- The support of a row is bounded by its length. -/
theorem rowSupport_lt (row : List Bool) : ∀ j ∈ rowSupport row, j < row.length := by
  intro j hj
  have := rowSupportFrom_lt row 0 j hj
  omega

/-- The support of a row has no duplicates. -/
theorem rowSupport_nodup (row : List Bool) : (rowSupport row).Nodup :=
  rowSupportFrom_nodup row 0

/-- Membership characterization for the offset recursion. -/
theorem mem_rowSupportFrom (row : List Bool) :
    ∀ (i j : Nat), j ∈ rowSupportFrom row i ↔
      ∃ k, k < row.length ∧ j = i + k ∧ row.getD k false = true := by
  induction row with
  | nil =>
    intro i j
    constructor
    · intro h; cases h
    · rintro ⟨k, hk, _, _⟩; cases hk
  | cons b rest ih =>
    intro i j
    constructor
    · intro hj
      by_cases hb : b
      · simp only [rowSupportFrom, hb, if_true] at hj
        rcases List.mem_cons.mp hj with h | h
        · refine ⟨0, by simp only [List.length_cons]; omega, by omega, by simp [hb]⟩
        · obtain ⟨k, hk, hjk, hread⟩ := (ih (i + 1) j).mp h
          refine ⟨k + 1, by simp only [List.length_cons]; omega, by omega, by simpa using hread⟩
      · simp only [rowSupportFrom, hb] at hj
        obtain ⟨k, hk, hjk, hread⟩ := (ih (i + 1) j).mp hj
        refine ⟨k + 1, by simp only [List.length_cons]; omega, by omega, by simpa using hread⟩
    · rintro ⟨k, hk, hjk, hread⟩
      cases k with
      | zero =>
        have hb : b = true := by simpa using hread
        subst hb
        have hji : j = i := by omega
        subst hji
        simp only [rowSupportFrom, if_true]
        exact List.mem_cons_self ..
      | succ k' =>
        have hmem : j ∈ rowSupportFrom rest (i + 1) := by
          refine (ih (i + 1) j).mpr ⟨k', ?_, by omega, by simpa using hread⟩
          simp only [List.length_cons] at hk; omega
        by_cases hb : b
        · simp only [rowSupportFrom, hb, if_true]
          exact List.mem_cons_of_mem _ hmem
        · simpa only [rowSupportFrom, hb, if_false] using hmem

/-- Membership in `rowSupport`: exactly the indices reading `true`. -/
theorem mem_rowSupport (row : List Bool) (j : Nat) :
    j ∈ rowSupport row ↔ j < row.length ∧ row.getD j false = true := by
  rw [rowSupport, mem_rowSupportFrom row 0 j]
  constructor
  · rintro ⟨k, hk, hjk, hread⟩
    have hkj : j = k := by omega
    subst hkj
    exact ⟨hk, hread⟩
  · rintro ⟨hlt, hread⟩
    exact ⟨j, hlt, by omega, hread⟩

/-- The support size equals the row's Hamming weight (`filter`-count). -/
theorem rowSupportFrom_length (row : List Bool) :
    ∀ (i : Nat), (rowSupportFrom row i).length = (row.filter (fun b => b)).length := by
  induction row with
  | nil => intro _; rfl
  | cons b rest ih =>
    intro i
    by_cases hb : b
    · simp [rowSupportFrom, hb, ih (i + 1)]
    · simp [rowSupportFrom, hb, ih (i + 1)]

/-- `|rowSupport row|` = Hamming weight of the row. -/
theorem rowSupport_length (row : List Bool) :
    (rowSupport row).length = (row.filter (fun b => b)).length :=
  rowSupportFrom_length row 0

/-! ## Check blocks and syndrome-extraction rounds

    The structured unit: one ancilla qubit, one CNOT fan over the stabilizer
    support, one measurement.  CNOT orientation per CSS convention (and per
    `StimEmit` / `PPM.CliffordConj`):

      * X-check: ancilla in `|+⟩` is the CONTROL — `CX anc → s`;
      * Z-check: ancilla in `|0⟩` is the TARGET  — `CX s → anc`. -/

/-- One syndrome-extraction check block. -/
structure CheckBlock where
  basis : MeasBasis
  anc   : Nat
  supp  : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace CheckBlock

/-- The block's physical operations: prep ancilla, CNOT fan, measure ancilla. -/
def ops (b : CheckBlock) : PhysCircuit :=
  match b.basis with
  | .x => PhysOp.prep .x b.anc ::
            (b.supp.map (fun s => PhysOp.cx b.anc s) ++ [PhysOp.meas .x b.anc])
  | .z => PhysOp.prep .z b.anc ::
            (b.supp.map (fun s => PhysOp.cx s b.anc) ++ [PhysOp.meas .z b.anc])

/-- Number of operations: 1 prep + |supp| CNOTs + 1 measurement. -/
theorem ops_length (b : CheckBlock) : b.ops.length = b.supp.length + 2 := by
  cases hb : b.basis <;> simp [ops, hb]

end CheckBlock

/-- One syndrome-extraction round: a list of check blocks.  (Ancilla
    distinctness across blocks is a hypothesis where theorems need it, not
    baked into the type.) -/
abbrev Round := List CheckBlock

namespace Round

/-- Flatten a round to its sequential physical circuit. -/
def ops (r : Round) : PhysCircuit := r.flatMap CheckBlock.ops

@[simp] theorem ops_nil : Round.ops [] = [] := rfl

@[simp] theorem ops_cons (b : CheckBlock) (r : Round) :
    Round.ops (b :: r) = b.ops ++ Round.ops r := rfl

theorem ops_append (r s : Round) : Round.ops (r ++ s) = r.ops ++ s.ops := by
  simp [Round.ops]

end Round

/-! ## Stim serialization

    The IR serializes to exactly the Stim text the legacy emitter
    (`StimEmit.surgeryToStim`) produces — proven in `SyndromeExtraction.lean`.
    From this point on, emitted Stim is a VIEW of the verified syntactic
    object, not an independent artifact. -/

def MeasBasis.prepStim : MeasBasis → String
  | .z => "R"
  | .x => "RX"

def MeasBasis.measStim : MeasBasis → String
  | .z => "M"
  | .x => "MX"

/-- One Stim line per operation. -/
def PhysOp.toStim : PhysOp → String
  | .prep b q => b.prepStim ++ " " ++ toString q ++ "\n"
  | .cx c t   => "CX " ++ toString c ++ " " ++ toString t ++ "\n"
  | .meas b q => b.measStim ++ " " ++ toString q ++ "\n"

/-- Serialize a circuit to Stim text (one line per operation). -/
def toStim : PhysCircuit → String
  | []        => ""
  | op :: ops => op.toStim ++ toStim ops

@[simp] theorem toStim_nil : toStim [] = "" := rfl

@[simp] theorem toStim_cons (op : PhysOp) (ops : PhysCircuit) :
    toStim (op :: ops) = op.toStim ++ toStim ops := rfl

end FormalRV.QEC.Circuit
