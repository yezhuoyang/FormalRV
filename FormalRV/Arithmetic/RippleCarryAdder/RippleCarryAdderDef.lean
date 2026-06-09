/-
  FormalRV.Arithmetic.RippleCarryAdder.RippleCarryAdderDef
  ───────────────────────────────────────────────────────
  THE definition of the **Gidney** ripple-carry adder, as concrete `Gate`-IR
  data. **Just the circuit — no specs, no proofs, no post-states.**

  THE adder is `gidney_adder`: a forward faithful cascade, then a final-CX
  cascade (stamps the sum), then a reverse cascade, on `3*n + 2` qubits with
  the registers interleaved LSB-first:
    • read[i]   = 3*i      (the `a` register; preserved)
    • target[i] = 3*i + 1  (the `b` register; becomes bit i of (a+b))
    • carry[i]  = 3*i + 2  (carry chain; LEFT DIRTY by the base adder)

  `gidney_adder_full_faithful_no_measurement_patched` is the carry-clearing
  variant — same target/read action, but it also returns the carry register to
  0. That patched adder is the one the modular-adder layer builds on.

  Where everything else lives (one file per job):
    • Classical spec / encoding / decoders : `RippleCarryAdderSpec.lean`
    • Basis-state post-states + invariants  : `RippleCarryAdderPostStates.lean`
    • Cost-only skeleton (NOT this adder)   : `RippleCarryAdderCostSkeleton.lean`
    • Correctness theorems                  : `RippleCarryAdderCorrectness.lean`
    • Resource theorems (T / qubits / RSA)  : `RippleCarryAdderResource.lean`
    • Worked example + OpenQASM             : `RippleCarryAdderExample.lean`

  Refs: Gidney, arXiv:1709.06648; Qrisp `qq_gidney_adder.py`.
-/
import FormalRV.Core.Gate

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Register indexing (interleaved, LSB-first)

`read[i], target[i], carry[i]` interleave in groups of three:
`read[i] = 3*i`, `target[i] = 3*i + 1`, `carry[i] = 3*i + 2`. -/

/-- Qubit index for the i-th read bit. -/
def read_idx (i : Nat) : Nat := 3 * i

/-- Qubit index for the i-th target bit. -/
def target_idx (i : Nat) : Nat := 3 * i + 1

/-- Qubit index for the i-th carry bit. -/
def carry_idx (i : Nat) : Nat := 3 * i + 2

/-- Total qubits for an n-bit adder: `3n + 2`. -/
def adder_n_qubits (n : Nat) : Nat := 3 * n + 2

/-! ## Final-CX cascade — stamps the sum bit onto the target register -/

/-- Final-CX cascade — one `CX(read[i], target[i])` per bit. -/
def gidney_final_cx_cascade : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_final_cx_cascade n)
                        (Gate.CX (read_idx n) (target_idx n))

/-! ## Faithful per-bit steps (forward) and their gate-reverses

Per `qq_gidney_adder.py`: the first bit (no chain CX), interior bits (CCX +
chain CX + 2 propagation CXs), and the last bit (no propagation). The
propagation CXs pre-XOR `read[i+1]`/`target[i+1]` by `carry[i]`, which is what
makes the next bit compute Gidney's carry. -/

/-- Faithful interior bit-step `i ≥ 1` (not last): CCX + chain-CX + 2 propagation CXs. -/
def gidney_adder_bit_step_faithful_interior (i : Nat) : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.seq
        (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
        (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
      (Gate.CX (carry_idx i) (read_idx (i + 1))))
    (Gate.CX (carry_idx i) (target_idx (i + 1)))

/-- Gate-reverse of `gidney_adder_bit_step_faithful_interior i`. -/
def gidney_adder_bit_step_faithful_interior_reverse (i : Nat) : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.seq
        (Gate.CX (carry_idx i) (target_idx (i + 1)))
        (Gate.CX (carry_idx i) (read_idx (i + 1))))
      (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))

/-- Faithful first bit-step `i = 0`: CCX + 2 propagation CXs (no chain CX). -/
def gidney_adder_bit_step_faithful_first : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0))
      (Gate.CX (carry_idx 0) (read_idx 1)))
    (Gate.CX (carry_idx 0) (target_idx 1))

/-- Gate-reverse of `gidney_adder_bit_step_faithful_first`. -/
def gidney_adder_bit_step_faithful_first_reverse : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.CX (carry_idx 0) (target_idx 1))
      (Gate.CX (carry_idx 0) (read_idx 1)))
    (Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0))

/-- Faithful last bit-step `i ≥ 1`: CCX + chain CX (no propagation). -/
def gidney_adder_bit_step_faithful_last (i : Nat) : Gate :=
  Gate.seq
    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
    (Gate.CX (carry_idx (i - 1)) (carry_idx i))

/-- Gate-reverse of `gidney_adder_bit_step_faithful_last i`. -/
def gidney_adder_bit_step_faithful_last_reverse (i : Nat) : Gate :=
  Gate.seq
    (Gate.CX (carry_idx (i - 1)) (carry_idx i))
    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))

/-! ## Forward cascades -/

/-- All-interior cascade: `gidney_adder_bit_step_faithful_interior (k+1)` for
`k = 0..n-1` (structural core; same `7n` T-count as the cost skeleton). -/
def gidney_adder_forward_faithful_interior : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq
                 (gidney_adder_forward_faithful_interior n)
                 (gidney_adder_bit_step_faithful_interior (n + 1))

/-- Cascade of bits `0..n-1`, each WITH propagation (first ; interior ; …). -/
def gidney_adder_forward_with_propagation : Nat → Gate
  | 0       => Gate.I
  | 1       => gidney_adder_bit_step_faithful_first
  | n + 2   => Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_interior (n + 1))

/-- **Faithful full forward cascade** for an n-bit adder: bits `0..n-2` with
propagation, then the last bit (no propagation). `Gate.I` for `n ≤ 1`. -/
def gidney_adder_forward_faithful_full : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   => Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_last (n + 1))

/-- Reverse of `gidney_adder_forward_with_propagation`. -/
def gidney_adder_forward_with_propagation_reverse : Nat → Gate
  | 0       => Gate.I
  | 1       => gidney_adder_bit_step_faithful_first_reverse
  | n + 2   => Gate.seq (gidney_adder_bit_step_faithful_interior_reverse (n + 1))
                        (gidney_adder_forward_with_propagation_reverse (n + 1))

/-- Reverse of `gidney_adder_forward_faithful_full`. -/
def gidney_adder_forward_faithful_full_reverse : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   => Gate.seq (gidney_adder_bit_step_faithful_last_reverse (n + 1))
                        (gidney_adder_forward_with_propagation_reverse (n + 1))

/-! ## THE adder -/

/-- **Full no-measurement faithful Gidney adder** (`n+2` bits): forward faithful
cascade ; final-CX cascade ; faithful reverse cascade. Total T-count `14·(n+2)`.
Edge cases `n ≤ 1` return `Gate.I`. -/
def gidney_adder_full_faithful_no_measurement : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   => Gate.seq
                (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                          (gidney_final_cx_cascade (n + 2)))
                (gidney_adder_forward_faithful_full_reverse (n + 2))

/-- **THE canonical, semantically-correct Gidney ripple-carry adder.** Alias for
`gidney_adder_full_faithful_no_measurement`. This is the adder the Shor cost
model binds to (`adderToff_eq`) and the canonical name downstream code uses. -/
def gidney_adder (n : Nat) : Gate := gidney_adder_full_faithful_no_measurement n

/-! ## Patched (carry-clearing) variant

Each reverse step gets a trailing `CX(read[i], carry[i])` that clears the carry
register (the base adder leaves it dirty). This patched adder is what the
modular-adder layer builds on. -/

/-- Patched first-bit reverse step (clears `carry[0]`). -/
def gidney_adder_bit_step_faithful_first_reverse_patched : Gate :=
  Gate.seq gidney_adder_bit_step_faithful_first_reverse
           (Gate.CX (read_idx 0) (carry_idx 0))

/-- Patched interior-bit reverse step (clears `carry[i]`). -/
def gidney_adder_bit_step_faithful_interior_reverse_patched (i : Nat) : Gate :=
  Gate.seq (gidney_adder_bit_step_faithful_interior_reverse i)
           (Gate.CX (read_idx i) (carry_idx i))

/-- Patched last-bit reverse step (clears `carry[i]`). -/
def gidney_adder_bit_step_faithful_last_reverse_patched (i : Nat) : Gate :=
  Gate.seq (gidney_adder_bit_step_faithful_last_reverse i)
           (Gate.CX (read_idx i) (carry_idx i))

/-- Patched propagation reverse cascade. -/
def gidney_adder_forward_with_propagation_reverse_patched : Nat → Gate
  | 0       => Gate.I
  | 1       => gidney_adder_bit_step_faithful_first_reverse_patched
  | n + 2   =>
      Gate.seq (gidney_adder_bit_step_faithful_interior_reverse_patched (n + 1))
               (gidney_adder_forward_with_propagation_reverse_patched (n + 1))

/-- Patched full reverse cascade. -/
def gidney_adder_forward_faithful_full_reverse_patched : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   =>
      Gate.seq (gidney_adder_bit_step_faithful_last_reverse_patched (n + 1))
               (gidney_adder_forward_with_propagation_reverse_patched (n + 1))

/-- **Patched full faithful no-measurement Gidney adder**: forward ; final-CX ;
**patched** reverse (which additionally clears the carry register). -/
def gidney_adder_full_faithful_no_measurement_patched : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   =>
      Gate.seq
        (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                  (gidney_final_cx_cascade (n + 2)))
        (gidney_adder_forward_faithful_full_reverse_patched (n + 2))

end FormalRV.BQAlgo
