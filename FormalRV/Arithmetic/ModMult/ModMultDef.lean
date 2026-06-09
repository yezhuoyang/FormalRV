/-
  FormalRV.Arithmetic.ModMult.ModMultDef
  ──────────────────────────────────────────────
  THE definition of the SQIR-faithful in-place modular multiplier, as concrete
  `Gate`-IR data. **Definitions only — no proofs.**

  THE multiplier is `modmult_MCP_gate bits N a ainv`: it maps the data
  register `x ↦ (a · x) mod N` in place, on `modmult_total_dim bits` qubits, where
  `bits` is the bit-width of the integers (needs `2N ≤ 2^bits`).

  Construction (bottom-up):
    step → prefix → const_gate     -- shift-and-add of (a·2^j mod N) into the accumulator
    + modmult_swap_acc_mult                -- swap accumulator ↔ multiplier register
    = inplace_candidate            -- x ↦ (a·x) mod N  (compute · swap · uncompute)
    + Gate.shift + encode adapter  = modmult_MCP_gate  (MultiplyCircuitProperty layout)

  Correctness : `SQIRModMultCorrectness.lean`  (`modmult_correct`)
  Resource    : `SQIRModMultResource.lean`     (`modmult_tcount = 112·bits²`)
  Supporting  : `SQIRModMultDefinitions.lean`  (input encoding, classical specs,
                verified BaseUCom families, q_start-parametric infrastructure)
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag
import FormalRV.Arithmetic.ModularAdder
import FormalRV.Arithmetic.MCPBridge

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Layout: where the multiplier control bits live -/

/-- Multiplier bit `j` sits at this qubit, just above the Cuccaro mod-add block. -/
def mult_control_idx (bits j : Nat) : Nat := 2 + (2 * bits + 1) + j

/-! ## Shift-and-add: const-multiplier `acc ↦ acc + (a·x) mod N` -/

/-- One step: conditionally add `(a · 2^j) mod N` to the accumulator,
controlled by multiplier bit `j`. -/
def modmult_step_gate (bits N a j : Nat) : Gate :=
  sqir_style_controlledModAddConst_gate bits 2 N ((a * 2 ^ j) % N)
    (mult_control_idx bits j) 1

/-- Apply the step for `j = 0, …, k-1` in order. -/
def modmult_prefix_gate (bits N a : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => seq (modmult_prefix_gate bits N a k) (modmult_step_gate bits N a k)

/-- The const-multiplier gate: process all `bits` multiplier bits. -/
def modmult_const_gate (bits N a : Nat) : Gate :=
  modmult_prefix_gate bits N a bits

/-! ## Accumulator ↔ multiplier register swap -/

/-- Qubit of accumulator (target) bit `i` in the Cuccaro layout. -/
def modmult_target_idx (i : Nat) : Nat := 2 + 2 * i + 1

/-- Swap accumulator bits `[0,k)` with multiplier bits `[0,k)`. -/
def modmult_swap_acc_mult_aux (bits : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => Gate.seq (modmult_swap_acc_mult_aux bits k)
                      (qubit_swap (modmult_target_idx k) (mult_control_idx bits k))

/-- Full SWAP of the accumulator (target) register with the multiplier register. -/
def modmult_swap_acc_mult (bits : Nat) : Gate := modmult_swap_acc_mult_aux bits bits

/-! ## In-place multiplier: `x ↦ (a·x) mod N` -/

/-- In-place modular multiplier (requires `a · ainv ≡ 1 mod N`):
compute `(a·x) mod N` into the accumulator, swap it into the `x` register, then
uncompute the old `x` by accumulating `(N - ainv)·(a·x) ≡ -x (mod N)`. -/
def modmult_inplace_candidate (bits N a ainv : Nat) : Gate :=
  Gate.seq (modmult_const_gate bits N a)
    (Gate.seq (modmult_swap_acc_mult bits)
              (modmult_const_gate bits N ((N - ainv) % N)))

/-! ## MCP-layout wrapper (the `MultiplyCircuitProperty` interface) -/

/-- Total qubit budget: `bits` for the external data register + the SQIR
ancilla/workspace block `sqir_modmult_rev_anc bits`. -/
def modmult_total_dim (bits : Nat) : Nat := bits + sqir_modmult_rev_anc bits

/-- Shift every gate position up by `off` (embeds a gate into a larger register). -/
def Gate.shift (off : Nat) : Gate → Gate
  | Gate.I         => Gate.I
  | Gate.X q       => Gate.X (off + q)
  | Gate.CX a b    => Gate.CX (off + a) (off + b)
  | Gate.CCX a b c => Gate.CCX (off + a) (off + b) (off + c)
  | Gate.seq g h   => Gate.seq (Gate.shift off g) (Gate.shift off h)

/-- Adapter between the external `encodeDataZeroAnc` layout and the (shifted)
SQIR multiplier layout: swap the data register `[0,bits)` into the shifted
multiplier register (bit-order reversed). -/
def encode_to_mult_adapter (bits : Nat) : Gate :=
  reverse_register_swap bits 0 (bits + mult_control_idx bits 0)

/-- The in-place multiplier embedded at the shifted SQIR layout. -/
def modmult_inplace_shifted (bits N a ainv : Nat) : Gate :=
  Gate.shift bits (modmult_inplace_candidate bits N a ainv)

/-- **THE SQIR modular multiplier** (MCP layout): `encode adapter` →
`shifted in-place multiplier` → `decode adapter`. Maps `x ↦ (a·x) mod N`.

Correctness: `modmult_correct`.  Resource: `modmult_tcount = 112·bits²`. -/
def modmult_MCP_gate (bits N a ainv : Nat) : Gate :=
  Gate.seq (encode_to_mult_adapter bits)
    (Gate.seq (modmult_inplace_shifted bits N a ainv)
              (encode_to_mult_adapter bits))

end FormalRV.BQAlgo
