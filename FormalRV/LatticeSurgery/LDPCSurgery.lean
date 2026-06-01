/-
  FormalRV.Framework.LDPCSurgery — LDPC lattice surgery gadget
  structure and structural verifier.

  Implements qianxu (Cain–Xu et al. 2026) Appendix C, especially
  Sec. C.1 ("Description").  A surgery gadget on a qLDPC code
  performs a single logical-Pauli-product measurement (PPM) by:

    (1) Initialising an ancilla system A in |0⟩.
    (2) Measuring τ_s cycles of merged-code stabilisers — the
        joint stabilisers of the data code Q and ancilla code A,
        coupled via connection matrices f_X' and f_Z.
    (3) Detaching A from Q by measuring A in the Z basis with
        adaptive Pauli corrections.

  The merged code's parity-check matrices are

       H̃_X = [ H_X   0   ]      H̃_Z = [ H_Z   f_Z  ]
             [ f_X'  H_X' ]            [  0    H_Z' ]

  Per the paper, the surgery gadget is fault-tolerant iff:

    (i)   The merged code has distance d̃ = Θ(d_data).
    (ii)  The merged code remains qLDPC.
    (iii) τ_s = Θ(d_data) (we use τ_s ≥ ⌈2 d_data / 3⌉).

  Plus the structural constraint that the target logical
  operator P̄ lies in the row span of H̃_X (X-type PPM) or H̃_Z
  (Z-type PPM):

       ⟨ℒ⟩ = f_X'ᵀ · ker(H_X'ᵀ)

  is restated here as a row-span identity on the merged matrix,
  which the implementer supplies a witness for.

  We accept (i) — the merged-code distance — as implementer-
  supplied (paper-cited from QDistRnd numerical computation).
  We verify (ii) and (iii) structurally; we verify the row-span
  identity (the kernel condition) decidably.

  ## Single-qubit vs multi-block PPMs

  This file handles the SINGLE-CODE-BLOCK case (one data code +
  one ancilla system).  For PPMs across two code blocks
  (e.g., Z̄_i ⊗ Z̄'_j with i on memory, j on processor), use
  the bridge construction in `LDPCSurgeryBridge.lean`.
-/

import FormalRV.System.Architecture
import FormalRV.Framework.L4_QECCode
import FormalRV.QEC.LDPCMatrix

namespace FormalRV.Framework.LDPC

open FormalRV.Framework

/-! ## Surgery gadget structure -/

/-- A single-code-block surgery gadget realising one logical
    Pauli measurement on a qLDPC data code.

    Per qianxu App. C.1, the implementer supplies:

    * `data_code` — the data code Q(Q, S_X, S_Z), with parity
      matrices H_X = `data_code.hx`, H_Z = `data_code.hz`.

    * `ancilla_n` — the number of ancilla qubits |Q'|.

    * `ancilla_hx` — H_X', the ancilla X-check matrix
      (|S_X'| × ancilla_n).
    * `ancilla_hz` — H_Z', the ancilla Z-check matrix
      (|S_Z'| × ancilla_n).

    * `conn_x` — f_X', the connection matrix joining each
      ancilla X-check to a subset of data qubits
      (|S_X'| × data_code.n).
    * `conn_z` — f_Z, the connection matrix joining each
      data Z-check to a subset of ancilla qubits
      (|S_Z|  × ancilla_n).

    * `tau_s` — number of merged-code measurement cycles
      (the surgery cycle count).

    * `target_pauli` — the logical Pauli operator P̄ being
      measured, as a Bool vector of length
      `data_code.n + ancilla_n`.  The vector's first
      `data_code.n` entries describe the action on Q; the
      remainder describes the action on Q'.

    * `span_witness` — a Bool vector selecting which rows of
      the merged X- or Z-check matrix sum (XOR) to give the
      `target_pauli`.  This is the row-span witness the
      framework uses to verify the kernel condition of
      qianxu Sec. C.1.

    * `merged_qldpc_bound` — the qLDPC degree bound (Δ) that
      the implementer claims for the merged code.  Verified
      structurally by `is_qldpc`. -/
structure SurgeryGadget where
  data_code         : QECCode
  ancilla_n         : Nat
  ancilla_hx        : BoolMat
  ancilla_hz        : BoolMat
  conn_x            : BoolMat
  conn_z            : BoolMat
  tau_s             : Nat
  target_pauli      : BoolVec
  span_witness      : BoolVec
  merged_qldpc_bound : Nat
  deriving Inhabited

namespace SurgeryGadget

/-! ## Merged-code parity matrices -/

/-- Total qubit count of the merged code = `data_code.n + ancilla_n`. -/
def merged_n (g : SurgeryGadget) : Nat := g.data_code.n + g.ancilla_n

/-- Merged X-check matrix:
      H̃_X = [ H_X   0   ]
            [ f_X'  H_X' ]
    The top block is the data X-checks extended by zeros on
    the ancilla qubits; the bottom block is the ancilla
    X-checks `H_X'` augmented by `f_X'` on the data qubits. -/
def merged_hx (g : SurgeryGadget) : BoolMat :=
  let zeros := zero_vec g.ancilla_n
  let top := g.data_code.hx.map (fun row => row ++ zeros)
  let bot := hcat g.conn_x g.ancilla_hx
  vcat top bot

/-- Merged Z-check matrix:
      H̃_Z = [ H_Z   f_Z  ]
            [  0    H_Z' ]  -/
def merged_hz (g : SurgeryGadget) : BoolMat :=
  let zeros := zero_vec g.data_code.n
  let top := hcat g.data_code.hz g.conn_z
  let bot := g.ancilla_hz.map (fun row => zeros ++ row)
  vcat top bot

/-! ## Structural well-formedness predicates -/

/-- All matrix dimensions and row lengths are mutually
    consistent.  Decidable. -/
def dimensions_consistent (g : SurgeryGadget) : Bool :=
  -- data_code.hx, hz : rows of length data_code.n
  matrix_has_n_cols g.data_code.hx g.data_code.n
  && matrix_has_n_cols g.data_code.hz g.data_code.n
  -- ancilla_hx, hz : rows of length ancilla_n
  && matrix_has_n_cols g.ancilla_hx g.ancilla_n
  && matrix_has_n_cols g.ancilla_hz g.ancilla_n
  -- conn_x : same row count as ancilla_hx, row length data_code.n
  && decide (g.conn_x.length = g.ancilla_hx.length)
  && matrix_has_n_cols g.conn_x g.data_code.n
  -- conn_z : same row count as data_code.hz, row length ancilla_n
  && decide (g.conn_z.length = g.data_code.hz.length)
  && matrix_has_n_cols g.conn_z g.ancilla_n
  -- target_pauli : length data_code.n + ancilla_n
  && decide (g.target_pauli.length = g.merged_n)
  -- span_witness : length = number of rows in merged H_X
  && decide (g.span_witness.length =
              g.data_code.hx.length + g.ancilla_hx.length)

/-! ## Row-span identity (the "kernel condition" of qianxu Sec. C.1) -/

/-- Structural correctness: the target logical Pauli operator
    equals the GF(2) sum of the rows of merged_hx selected by
    span_witness.  This is the qianxu kernel-condition
    `⟨ℒ⟩ = f_X'ᵀ · ker(H_X'ᵀ)` restated as a row-span identity
    over the MERGED matrix, decidable on concrete instances. -/
def targets_logical_correctly (g : SurgeryGadget) : Bool :=
  decide (row_combination g.span_witness g.merged_hx = g.target_pauli)

/-! ## Fault-tolerance criteria -/

/-- Criterion (iii): `τ_s = Θ(d_data)`.  We require
    `3 · τ_s ≥ 2 · d_data` (i.e., `τ_s ≥ ⌈2d/3⌉`), matching the
    paper's choice of `τ_s ≈ 2d/3` which balances space-like
    and time-like logical error rates. -/
def tau_s_sufficient (g : SurgeryGadget) : Bool :=
  decide (3 * g.tau_s ≥ 2 * g.data_code.d)

/-- Criterion (ii): the merged code remains qLDPC, i.e., row and
    column weights of `merged_hx` and `merged_hz` are bounded by
    the claimed `merged_qldpc_bound`. -/
def merged_is_qldpc (g : SurgeryGadget) : Bool :=
  is_qldpc g.merged_hx g.merged_n g.merged_qldpc_bound
  && is_qldpc g.merged_hz g.merged_n g.merged_qldpc_bound

/-! ## Headline verifier -/

/-- **The headline structural verifier** for a surgery gadget.

    Checks (decidably):
    * dimensions are mutually consistent
    * the merged code is qLDPC (criterion ii)
    * τ_s is sufficient (criterion iii)
    * the target logical lies in the row span of merged_hx
      (the kernel condition).

    Criterion (i) — merged-code distance d̃ = Θ(d_data) — is
    paper-cited from QDistRnd / Monte Carlo; we accept it as
    an implementer-supplied claim. -/
def verify_surgery_gadget (g : SurgeryGadget) : Bool :=
  g.dimensions_consistent
  && g.tau_s_sufficient
  && g.merged_is_qldpc
  && g.targets_logical_correctly

/-! ## Schedule-level verifier

    A real Cuccaro N-bit submission's PPM stream is a SEQUENCE
    of surgery gadgets.  The framework verifies each gadget
    independently.  Compositional fault tolerance follows from
    standard FT-circuit construction theorems (the implementer
    cites these, not the framework). -/

/-- Every gadget in a list passes the headline verifier. -/
def verify_surgery_schedule (gadgets : List SurgeryGadget) : Bool :=
  gadgets.all verify_surgery_gadget

end SurgeryGadget

end FormalRV.Framework.LDPC
