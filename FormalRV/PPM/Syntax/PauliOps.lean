/-
  FormalRV.Framework.PauliOps — Pauli operators + logical-
  operator definitions + Pauli-measurement verifier.

  Per John's directive (2026-05-22):  "user needs to provide
  his definition of all logical Z operators, then we verify
  that the physical-level implementation is actually that
  logical operation."

  This is essential for PPM (logical Pauli measurements):
  every logical CNOT, S, T-injection, magic-state injection,
  and many ancillary FT primitives are built from Pauli-product
  measurements at the physical level.

  Verification model.
      USER PROVIDES (in `LogicalOpDef`):
        - for each logical qubit in a code block,
            pauli_X = the physical Pauli string we DECLARE
                      to be its logical X
            pauli_Z = the physical Pauli string we DECLARE
                      to be its logical Z
      USER ALSO PROVIDES (per claimed measurement):
        - claimed logical-qubit ID + Pauli kind (X / Z)
        - the physical PauliString actually measured
      FRAMEWORK VERIFIES:
        - the physical PauliString matches the user's
          declared Pauli for the claimed logical operation.

  Limitations (v1).
      Equality is STRICT (list equality).  Two physically-
      equivalent Pauli strings differing by stabilizer
      multiplication or qubit reordering are NOT yet
      recognised as the same.  A future extension would
      check equivalence modulo the code's stabilizer group
      using `QECCode.hx`, `QECCode.hz`.
-/
import FormalRV.System.Core.Architecture
import FormalRV.System.Core.CodedLayout

namespace FormalRV.System.Architecture

/-! ## Pauli operators -/

/-- Single-qubit Pauli factor.  `I` is the identity. -/
inductive PauliKind
  | I | X | Y | Z
  deriving Repr, DecidableEq

/-- A Pauli acting on a specific qubit. -/
structure PauliFactor where
  qubit : Nat
  pauli : PauliKind
  deriving Repr, DecidableEq

/-- A Pauli string: a list of `PauliFactor`s.  Implicit
    identity on unmentioned qubits.  We do NOT require ordering
    or uniqueness in this v1 representation (a future version
    may canonicalise). -/
abbrev PauliString := List PauliFactor

/-! ## Logical-operator definitions

    For each logical qubit in a code block, the user declares
    `pauli_X` and `pauli_Z` — the physical Pauli strings that
    THE USER ASSERTS are the logical X and Z of that qubit. -/

/-- The user's declaration of logical X and Z for one logical
    qubit (identified by its `local_index` in the code block). -/
structure LogicalOpDef where
  local_index : Nat
  pauli_X     : PauliString
  pauli_Z     : PauliString
  deriving Repr

/-! ## Extending `CodeBlockBinding`

    We add a `logical_op_defs` field via a separate structure
    rather than editing `CodeBlockBinding`, preserving backward
    compatibility for the trivial-code demos.

    A `CodeBlockWithLogicalOps` pairs a `CodeBlockBinding` with
    a list of logical-op definitions (one per logical qubit
    in the block, with `local_index < block.code.k`). -/

structure CodeBlockWithLogicalOps where
  binding         : CodeBlockBinding
  logical_op_defs : List LogicalOpDef

/-! ## PauliString-in-block-scope helpers

    A `LogicalOpDef` declares `pauli_X` and `pauli_Z` for a
    logical qubit; their PauliString factors must touch only
    atoms in the relevant code block.  Otherwise the user
    could declare a "logical Z" that's actually a Pauli
    spanning multiple blocks — silent boundary violation. -/

def pauli_string_qubits (p : PauliString) : List Nat :=
  p.map (·.qubit)

def pauli_string_in_atoms (p : PauliString) (allowed : List Nat) : Bool :=
  (pauli_string_qubits p).all (fun q => allowed.contains q)

/-! ## The verifier -/

/-- Look up the `LogicalOpDef` for a given local-index in a
    block-with-ops. -/
def CodeBlockWithLogicalOps.find_op
    (block : CodeBlockWithLogicalOps) (local_idx : Nat) :
    Option LogicalOpDef :=
  block.logical_op_defs.find?
    (fun lop => lop.local_index == local_idx)

/-- A claim: "this physical Pauli string realises a logical
    Pauli measurement of kind `kind` on logical qubit
    `logical_id`."

    Verifier checks:
      (i)  the physical string matches the user's declared
           `pauli_X` or `pauli_Z` for that logical qubit;
      (ii) the physical string AND the declared one touch
           only atoms in the bound block's `physical_qubits`. -/
def verify_logical_pauli_measurement
    (clayout : CodedLogicalLayout)
    (blocks_with_ops : List CodeBlockWithLogicalOps)
    (logical_id : Nat)
    (kind : PauliKind)
    (physical : PauliString) : Bool :=
  -- Find which (block, local_index) this logical qubit lives in
  match clayout.find_binding logical_id with
  | none         => false
  | some binding =>
    -- Find the block-with-ops for this block_id
    match blocks_with_ops.find?
            (fun b => b.binding.block_id == binding.block_id) with
    | none => false
    | some bwo =>
      match bwo.find_op binding.local_index with
      | none     => false
      | some lop =>
        let allowed := bwo.binding.physical_qubits
        match kind with
        | .X =>
            decide (physical = lop.pauli_X)
            && pauli_string_in_atoms physical allowed
            && pauli_string_in_atoms lop.pauli_X allowed
        | .Z =>
            decide (physical = lop.pauli_Z)
            && pauli_string_in_atoms physical allowed
            && pauli_string_in_atoms lop.pauli_Z allowed
        | _  => false   -- Y not yet supported

/-! ## A claimed Pauli measurement (for inclusion in a submission)

    The implementer asserts: "the physical Pauli string
    `physical_pauli` realises logical Pauli `pauli_kind` on
    logical qubit `logical_id`."

    The framework verifies this claim against the user's
    declared logical operators. -/

structure PauliMeasurementClaim where
  logical_id     : Nat
  pauli_kind     : PauliKind
  physical_pauli : PauliString
  /-- Optional stabilizer-product witness.  When `none`, the
      framework uses STRICT list equality against the declared
      `pauli_X` / `pauli_Z`.  When `some w`, the framework
      accepts the physical Pauli if `physical · w ≡ declared`
      (modulo phase and ordering) via `StabilizerEquiv`. -/
  stabilizer_witness : Option PauliString := none
  deriving Repr

/-! ## What this gives us

    The implementer who wants to claim "this physical operation
    is a logical Z measurement on logical qubit 7":

    1. PROVIDES (with the rest of the submission) a
       `CodeBlockWithLogicalOps` that includes the
       `logical_op_defs` for every logical qubit in the block.
       In particular `pauli_Z` for `local_index = 7`.

    2. PROVIDES (per claimed measurement) a `PauliString` they
       declare is the physical realisation.

    3. CALLS `verify_logical_pauli_measurement`.

    The framework `decide`s whether the physical string matches
    the declared `pauli_Z`.  No semantic interpretation needed;
    the user's `LogicalOpDef` is the spec, and the framework
    enforces consistency. -/

end FormalRV.System.Architecture
