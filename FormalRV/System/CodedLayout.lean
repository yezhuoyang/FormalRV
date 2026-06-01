/-
  FormalRV.Framework.CodedLayout — code-block-aware logical
  layout for QEC codes.

  Per John's directive (2026-05-22): the framework must support
  declaring that a computation uses a specific QEC code (e.g.
  `[[144, 18, 12]]`) and reference logical qubits by their
  local index within that code block.

  Compared to the existing `LogicalLayout` (which maps logical
  qubits 1-to-1 with physical atoms — the trivial code), this
  module supports:

      * A list of `CodeBlockBinding`s, each declaring an
        `[[n, k, d]]` instance and the `n` physical atoms it
        occupies.
      * `LogicalQubitBinding`s mapping a flat logical-qubit ID
        to a `(block_id, local_index)` pair, where
        `local_index < k`.
      * A consistency check that:
          - every block's physical-qubit list has length n
          - every binding references a valid block + valid
            local index
          - every gate target has a binding

  Designed for any qLDPC family: bivariate-bicycle, lifted-product,
  surface code (k=1), or any code described by a `QECCode`.

  Concrete example (the LPCodedAdderDemo): an adder using
  logical qubits 3, 15, 17 in an `[[144, 18, 12]]` code block.
-/
import FormalRV.System.Architecture
import FormalRV.Framework.L4_QECCode

namespace FormalRV.Framework.Architecture

open FormalRV.Framework

/-! ## Code-block binding -/

/-- A `CodeBlockBinding` declares that a specific set of
    physical qubits implements a particular QEC code instance.

    `physical_qubits` lists the `code.n` physical-atom IDs in
    the architecture that form this block. -/
structure CodeBlockBinding where
  block_id        : Nat
  code            : QECCode
  physical_qubits : List Nat

/-! ## Logical-qubit binding -/

/-- A `LogicalQubitBinding` maps a flat logical-qubit ID (the
    one used in `LogicalGateKind` targets) to a `(block_id,
    local_index)` pair, where `local_index < code.k`.

    Each logical qubit is BACKED BY many physical atoms (the
    whole code block); the explicit qubit-to-physical
    enumeration lives in `CodeBlockBinding.physical_qubits`. -/
structure LogicalQubitBinding where
  logical_id  : Nat
  block_id    : Nat
  local_index : Nat
  deriving Repr, DecidableEq

/-! ## Coded logical layout -/

/-- A code-block-aware logical layout: a list of code blocks,
    a list of logical-qubit bindings, and the ordered list of
    logical gates.  Generalises `LogicalLayout` to non-trivial
    codes. -/
structure CodedLogicalLayout where
  code_blocks    : List CodeBlockBinding
  qubit_bindings : List LogicalQubitBinding
  logical_gates  : List LogicalGate

namespace CodedLogicalLayout

/-- Find a code block by `block_id`. -/
def find_block (clayout : CodedLogicalLayout) (bid : Nat) :
    Option CodeBlockBinding :=
  clayout.code_blocks.find? (fun b => b.block_id == bid)

/-- Find the binding for a logical-qubit ID. -/
def find_binding (clayout : CodedLogicalLayout) (lid : Nat) :
    Option LogicalQubitBinding :=
  clayout.qubit_bindings.find? (fun b => b.logical_id == lid)

/-- Each code block's `physical_qubits` list has length equal
    to the code's `n`. -/
def blocks_have_correct_size (clayout : CodedLogicalLayout) : Bool :=
  clayout.code_blocks.all
    (fun cb => decide (cb.physical_qubits.length = cb.code.n))

/-- Every logical-qubit binding references a valid block and a
    `local_index` strictly less than that block's `k`. -/
def bindings_in_range (clayout : CodedLogicalLayout) : Bool :=
  clayout.qubit_bindings.all (fun qb =>
    match clayout.find_block qb.block_id with
    | none    => false
    | some cb => decide (qb.local_index < cb.code.k))

/-- Every logical qubit referenced by any gate has a binding. -/
def all_gate_targets_bound (clayout : CodedLogicalLayout) : Bool :=
  clayout.logical_gates.all (fun lg =>
    (LogicalLayout.LogicalGateKind.targets lg.kind).all
      (fun lid => (clayout.find_binding lid).isSome))

/-- **The coded-layout consistency predicate.**

    A `CodedLogicalLayout` is consistent iff:
      (i)   every block's physical-qubit list has the right size;
      (ii)  every binding's `local_index < k`;
      (iii) every gate target has a binding.

    Decidable on concrete layouts. -/
def consistent (clayout : CodedLogicalLayout) : Bool :=
  clayout.blocks_have_correct_size
  && clayout.bindings_in_range
  && clayout.all_gate_targets_bound

end CodedLogicalLayout

/-! ## Physical-syscall-in-block-scope verification

    Closes the "actual logical qubit" gap: every implementing
    physical SysCall must act ONLY on physical atoms belonging
    to the relevant logical qubits' code blocks.  Otherwise the
    implementer could claim a logical operation backed by
    physical operations on the WRONG atoms — a silent cheat. -/

/-- Extract the list of physical-qubit IDs a SysCall touches.
    Classical SysCalls (decoder, Pauli updates, magic / ancilla
    requests) return `[]`. -/
def syscall_acts_on (sc : SysCall) : List Nat :=
  match sc.kind with
  | .Gate1q q _          => [q]
  | .Gate2q q1 q2 _      => [q1, q2]
  | .Measure q _         => [q]
  | .TransitQubit q _    => [q]
  | .RequestFreshAncilla _ => []
  | .RequestMagicState  _ => []
  | .DecodeSyndrome     _ => []
  | .PauliFrameUpdate   _ => []

namespace CodedLogicalLayout

/-- The physical atoms allowed to be touched by a logical gate
    targeting the given list of logical qubits.  Equals the
    UNION of the `physical_qubits` lists of those qubits' blocks. -/
def allowed_atoms_for_logicals
    (clayout : CodedLogicalLayout) (logical_ids : List Nat) : List Nat :=
  (logical_ids.filterMap (fun lid =>
    (clayout.find_binding lid).bind (fun b => clayout.find_block b.block_id))
   ).flatMap (·.physical_qubits)

/-- Does the impl-syscall list of a logical gate act only on
    physical atoms allowed by the layout (i.e., atoms in the
    union of the gate's targets' code blocks)? -/
def gate_impl_in_scope (clayout : CodedLogicalLayout)
    (lg : LogicalGate) (psched : Schedule) : Bool :=
  let allowed :=
    clayout.allowed_atoms_for_logicals
      (LogicalLayout.LogicalGateKind.targets lg.kind)
  lg.implementing_syscalls.all (fun i =>
    match psched[i]? with
    | none    => false   -- index out of range (also caught elsewhere)
    | some sc => (syscall_acts_on sc).all (fun q => allowed.contains q))

/-- **`impls_in_scope` headline predicate.**  Every logical gate's
    implementing syscalls act ONLY on atoms in the gate's
    targets' code blocks.

    Closes the gap between "impl indices are in range" (which the
    bridge already checks) and "the impl syscalls act on the
    right physical qubits". -/
def impls_in_scope (clayout : CodedLogicalLayout) (psched : Schedule) : Bool :=
  clayout.logical_gates.all (fun lg => gate_impl_in_scope clayout lg psched)

/-- Every impl syscall of a logical gate fires within the gate's
    declared [begin_us, end_us] window.  Otherwise the implementer
    could claim a logical gate at time [100, 200] while the impl
    syscalls actually fire at time 500 — temporal scope cheat. -/
def gate_impl_in_time_window (lg : LogicalGate) (psched : Schedule) : Bool :=
  lg.implementing_syscalls.all (fun i =>
    match psched[i]? with
    | none    => false
    | some sc => decide (lg.begin_us ≤ sc.begin_us)
              && decide (sc.end_us ≤ lg.end_us))

/-- **`impls_time_consistent` headline predicate.**  Every logical
    gate's implementing syscalls fire within the gate's time
    window. -/
def impls_time_consistent (clayout : CodedLogicalLayout)
    (psched : Schedule) : Bool :=
  clayout.logical_gates.all (fun lg => gate_impl_in_time_window lg psched)

end CodedLogicalLayout

end FormalRV.Framework.Architecture
