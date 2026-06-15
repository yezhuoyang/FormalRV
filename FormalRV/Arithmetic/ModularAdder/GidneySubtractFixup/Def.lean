/-
  FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup.Def
  ─────────────────────────────────────────────────────────
  THE definition of the FAITHFUL Gidney-2025 (arXiv:2505.15917, main.tex L972–975)
  `2.5n`-Toffoli modular adder — the **subtract-with-underflow + lookup-fixup**
  construction the paper actually uses for `X += c (mod p)`.

  ## The paper's construction (main.tex L972–975, verbatim)

  To do `X += c (mod p)` with `x < p`, `c < p` (X held in `bits = len(p)` value bits
  plus ONE extra top qubit `Q`, total width `W = bits + 1`):

    1. Flip the addition into a SUBTRACTION of `T2 = p − c`: compute `X -= T2`.
       The extra qubit `Q` (target bit `bits`) catches the underflow — `Q = 1`
       iff `x − T2 < 0`, i.e. iff `x < p − c`, i.e. iff `x + c < p`.
    2. Complete the modular addition with `X += [0, p][Q]` — a conditional add of
       the constant `p` controlled by `Q` (add `p` iff `Q = 1`).
    3. Uncompute `Q` by measurement-based uncomputation (Toffoli-free).

  Correctness: `X -= (p−c)` gives `x + c − p` (2's complement). If `x+c ≥ p` there
  is no underflow (`Q=0`) and the result is `x+c−p = (x+c) mod p`; if `x+c < p`
  there is underflow (`Q=1`) and `+= p` gives `x+c−p+p = x+c = (x+c) mod p`. Either
  way the low `bits` register holds `(x+c) mod p`, and the conditional add-back
  clears `Q` back to `0` automatically (both `x+c−p` and `x+c` are `< 2^bits`).

  ## How it is built here (composition, maximal reuse)

  The two additions are the MEASURED Gidney ripple-carry adder
  `FormalRV.Arithmetic.MeasuredAdder.gidneyAdderMeasured` (`n` Toffoli per add, the
  carry ancillas released by Gidney's measurement-based AND-uncompute). The
  conditional `+p` is realised WITHOUT any CCCX by the masked-constant-read idiom:
  a CX cascade copies `Q ∧ p.testBit i` into the adder's read register, the ordinary
  measured adder runs, and the cascade is un-applied (CX is involutive). The `Q`
  uncompute is FREE: after the fixup, `Q` is already `0`.

  Where to look next:
    • Correctness : `GidneySubtractFixup/Correctness.lean`  (value = `(x+c) % p`)
    • Resource    : `GidneySubtractFixup/Resource.lean`      (Toffoli count + paper link)

  Refs: Gidney 2025 arXiv:2505.15917 main.tex L972–975 (construction), L977 (`2.5n`
  vs Berry `3.5n`); the controlled additions of dlogs feeding this adder are bridged
  to the verified residue by `FormalRV.CFS.dlog_reduction_eq_residueAccumulate`.
-/
import FormalRV.Arithmetic.MeasuredAdder

namespace FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Arithmetic.MeasuredAdder

/-! ## §1. Boolean-level specification -/

/-- Spec for modular addition by a constant `c` under modulus `p`. -/
def gidneyModAddFixupSpec (p c x : Nat) : Nat := (x + c) % p

/-! ## §2. Loading a classical constant into the read register.

The measured adder adds the read register to the target. To add a CONSTANT `d`
we load `d` into the (clean) read register with an X-gate cascade (one X per set
bit of `d`), run the adder, then unload (X is involutive). This is the standard
"add constant" idiom, here over the MEASURED adder. -/

/-- Load `d` into the read register: `X (read_idx k)` for each `k < W` with
`d.testBit k`. Applied to a clean (`read = 0`) register it writes the bits of `d`;
applied again it clears them (X involutive). -/
def loadConst : Nat → Nat → Gate
  | 0,     _ => Gate.I
  | k + 1, d => Gate.seq (loadConst k d)
                  (if d.testBit k then Gate.X (read_idx k) else Gate.I)

/-- Add the constant `d` (mod `2^W`) to the target via the measured Gidney adder:
load `d` into the read register, run the measured adder, unload. Computes
`target := (target + d) % 2^W` with the read register restored to `0` and the carry
register released. -/
def addConstMeasured (W d : Nat) : EGate :=
  EGate.seq
    (EGate.seq (EGate.base (loadConst W d)) (gidneyAdderMeasured W 0))
    (EGate.base (loadConst W d))

/-! ## §3. The masked-constant conditional add of `p` controlled by the flag.

After the subtraction, the underflow is held in the in-band top target bit
`Q = target_idx bits`. The adder of the fixup stage REWRITES that top bit, so `Q`
cannot itself be used as the persistent control. Following the paper, we copy `Q`
into a FRESH out-of-band ancilla `flag` (one CX), and condition the fixup add on
`flag` — which the adder never touches, so the un-prepare cancels cleanly.

To add `p` iff `flag = 1` without any controlled-CCX we PREPARE the read register
with the masked constant `flag ∧ p.testBit i` (one CX per set bit of `p`, from
`flag` into `read_idx i`), run the ordinary measured adder, then UN-PREPARE (CX
involutive). The read register is clean before and after. -/

/-- Prepare the read register by XORing each `read_idx k` (for `k < W`) with
`flag ∧ p.testBit k`, where the control `flag` lives at qubit index `flagIdx`. A CX
cascade conditioned on the bit pattern of `p`. -/
def prepareMaskedP (flagIdx : Nat) : Nat → Nat → Gate
  | 0,     _ => Gate.I
  | k + 1, p =>
      Gate.seq (prepareMaskedP flagIdx k p)
               (if p.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)

/-- Conditional add of the constant `p` controlled by the qubit at `flagIdx`:
prepare the read register with the masked constant `flag ∧ p`, run the measured
Gidney adder at width `W`, un-prepare. Computes `target := (target + (if flag then p
else 0)) % 2^W` with the read register restored to `0` and carries released. -/
def conditionalAddP (W flagIdx p : Nat) : EGate :=
  EGate.seq
    (EGate.seq (EGate.base (prepareMaskedP flagIdx W p))
               (gidneyAdderMeasured W 0))
    (EGate.base (prepareMaskedP flagIdx W p))

/-! ## §4. THE faithful Gidney-2025 subtract-fixup modular adder.

Width `W = bits + 1` (the `bits` value bits of `X` plus the extra top qubit `Q`
at `target_idx bits`). The clean input is `adder_input_F W 0 x` (read register `0`,
target = `x`, carries `0`); the fixup flag ancilla lives out-of-band at
`flagIdx = adder_n_qubits W = 3·W + 2` and starts at `false`.

Stage 1 — SUBTRACT `T2 = p − c`: `addConstMeasured W (2^W - (p-c))` computes
`target := (x + (2^W - (p-c))) % 2^W = x + c − p` (mod `2^W`). The top bit
`Q = target_idx bits` is the underflow flag (`Q = 1` iff `x + c < p`).

Stage 2 — COPY Q → flag: `CX (target_idx bits) flagIdx` lands the underflow into the
out-of-band ancilla, which the fixup adder will leave untouched.

Stage 3 — CONDITIONAL `+p`: `conditionalAddP W flagIdx p` adds `p` to the target iff
`flag = 1`, completing the modular reduction AND clearing the in-band `Q` to `0`
(both `x+c−p` and `x+c` are `< 2^bits`).

Stage 4 — UNCOMPUTE flag: `EGate.mz flagIdx` releases the ancilla by
measurement-based uncomputation (Toffoli-free), per the paper's step 3. -/
def gidneyModAddFixup (bits p c : Nat) : EGate :=
  EGate.seq
    (EGate.seq
      (EGate.seq
        (addConstMeasured (bits + 1) (2 ^ (bits + 1) - (p - c)))
        (EGate.base (Gate.CX (target_idx bits) (adder_n_qubits (bits + 1)))))
      (conditionalAddP (bits + 1) (adder_n_qubits (bits + 1)) p))
    (EGate.mz (adder_n_qubits (bits + 1)))

end FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
