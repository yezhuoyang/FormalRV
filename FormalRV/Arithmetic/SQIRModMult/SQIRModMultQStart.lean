/-
  FormalRV.Arithmetic.SQIRModMult.SQIRModMultQStart
  ─────────────────────────────────────────────────
  q_start-PARAMETRIC infrastructure: ports of the gate chain
  (`SQIRModMultDef.lean`) and the input encoding to a free workspace offset
  `q_start`, plus the multiplier-bit install helpers. Consumed only by the
  prefix-invariant correctness proofs. No proofs.
-/
import FormalRV.Arithmetic.SQIRModMult.SQIRModMultDef

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-- q_start-parametric multiplier-bit position. -/
def sqir_mult_control_idx_qstart (bits q_start j : Nat) : Nat :=
  q_start + (2 * bits + 1) + j

/-- q_start-parametric input state. -/
def sqir_mult_input_F_qstart (bits q_start m acc : Nat) : Nat → Bool := fun q =>
  if q < q_start + 2 * bits + 1 then
    cuccaro_input_F q_start false 0 acc q
  else if q < q_start + 2 * bits + 1 + bits then
    m.testBit (q - (q_start + 2 * bits + 1))
  else false

/-- q_start-parametric one-step gate. -/
def sqir_modmult_step_gate_qstart (bits q_start N a j flagPos : Nat) : Gate :=
  sqir_style_controlledModAddConst_gate bits q_start N ((a * 2 ^ j) % N)
    (sqir_mult_control_idx_qstart bits q_start j) flagPos

/-- Install multiplier bits `0,…,num-1` from `m`, skipping bit `j`. -/
def install_mult_bits_skip_j (bits m j : Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0,     f => f
  | n + 1, f =>
    if n = j then install_mult_bits_skip_j bits m j n f
    else update (install_mult_bits_skip_j bits m j n f) (sqir_mult_control_idx bits n) (m.testBit n)

/-- q_start-parametric `install_mult_bits_skip_j`. -/
def install_mult_bits_skip_j_qstart (bits q_start m j : Nat) :
    Nat → (Nat → Bool) → (Nat → Bool)
  | 0,     f => f
  | n + 1, f =>
    if n = j then install_mult_bits_skip_j_qstart bits q_start m j n f
    else update (install_mult_bits_skip_j_qstart bits q_start m j n f)
                (sqir_mult_control_idx_qstart bits q_start n) (m.testBit n)

/-- q_start-parametric prefix gate. -/
def sqir_modmult_prefix_gate_qstart (bits q_start N a flagPos : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => seq (sqir_modmult_prefix_gate_qstart bits q_start N a flagPos k)
                 (sqir_modmult_step_gate_qstart bits q_start N a k flagPos)

/-- q_start-parametric full const-multiplier gate. -/
def sqir_modmult_const_gate_qstart (bits q_start N a flagPos : Nat) : Gate :=
  sqir_modmult_prefix_gate_qstart bits q_start N a flagPos bits

/-- q_start-parametric accumulator (target) bit index. -/
def sqir_target_idx_qstart (q_start i : Nat) : Nat := q_start + 2 * i + 1

/-- q_start-parametric accumulator↔multiplier swap (recursive). -/
def sqir_swap_acc_mult_aux_qstart (bits q_start : Nat) : Nat → Gate
  | 0     => Gate.I
  | k + 1 => Gate.seq (sqir_swap_acc_mult_aux_qstart bits q_start k)
                      (qubit_swap (sqir_target_idx_qstart q_start k)
                                  (sqir_mult_control_idx_qstart bits q_start k))

/-- q_start-parametric full accumulator↔multiplier swap. -/
def sqir_swap_acc_mult_qstart (bits q_start : Nat) : Gate :=
  sqir_swap_acc_mult_aux_qstart bits q_start bits

/-- q_start-parametric in-place modular multiplier (requires `a·ainv ≡ 1 mod N`). -/
def sqir_modmult_inplace_candidate_qstart (bits q_start N a ainv flagPos : Nat) : Gate :=
  Gate.seq (sqir_modmult_const_gate_qstart bits q_start N a flagPos)
    (Gate.seq (sqir_swap_acc_mult_qstart bits q_start)
              (sqir_modmult_const_gate_qstart bits q_start N ((N - ainv) % N) flagPos))

end FormalRV.BQAlgo
