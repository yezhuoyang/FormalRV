import FormalRV.Arithmetic.RippleCarryAdder
import Mathlib.Data.Nat.Bitwise

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate




/-! ## Boolean-level specifications -/

/-- Spec for modular addition by a constant under arbitrary modulus `N`. -/
def modAddConstSpec (N c x : Nat) : Nat := (x + c) % N

/-- Spec specialized to `N = 2^bits` (the case the patched Gidney
adder implements natively without any extra circuitry). -/
def addConstPow2Spec (bits c x : Nat) : Nat := (x + c) % 2^bits

/-! ## Modular reduction by arbitrary N — missing pieces

To implement `(x + c) mod N` for general `N` (the actual modular
adder needed by modular multiplication), the standard construction
requires:

1. **Constant addition over `n+1` bits** (room for carry-out).  Use
   `gidney_adder_full_faithful_no_measurement_patched (bits + 1)` to
   compute `t := x + c` with a "free" overflow bit in the target.

2. **Constant subtraction**: a gate `sub_const_gate N` that computes
   `t := t - N` in two's complement, leaving an overflow/underflow
   flag in a dedicated ancilla bit.  Missing.

3. **Comparator / sign-bit extraction**: detect whether `t ≥ N` by
   checking the borrow-out of step 2.  Missing.

4. **Controlled add-back of `N`**: a CCX-controlled version of step 1
   that re-adds `N` when the sign bit indicates underflow.  Missing.

5. **Uncompute the comparison flag** by re-comparing `t` against `N`
   (or by some other reversible-flag-clearing scheme).  Missing.

None of these primitives currently exist in `BQAlgo/*`.  Building
each one is itself a multi-step task analogous to the patched-Gidney-
adder work just completed.  Estimated scope: ~3-5 ticks of
infrastructure work (one tick each per missing primitive plus one
tick to compose them).

The next concrete sub-target is `sub_const_gate` — the reversible
constant-subtraction gate.  The simplest construction reuses the
patched Gidney adder via `x - N = x + (2^bits - N)`, treating the
subtraction as addition of the two's-complement representation of
`-N` (mod `2^bits`).  That reduces the problem to:

  given the patched adder for `(x + c') mod 2^bits` (where `c' = 2^bits - N`),
  prove that the result satisfies the borrow-flag interpretation that
  comparator + conditional add-back will need.

This is a clean follow-up tick.

The `patched_adder_add_const_pow2_bundled` primitive above is the
key building block — every subsequent step reuses it. -/

/-! ## Wraparound subtract-constant primitive

The simplest reversible subtraction: compute `x + (2^bits - N) mod 2^bits`
by feeding the constant `2^bits - N` into the read register of the
patched Gidney adder.  This is reversible (just the adder), takes
no extra ancillas, and lays the foundation for the comparator
(`x < N` iff this subtraction underflows).

**Semantic caveat**: Lean's `Nat` subtraction saturates at zero, so
the canonical spec is stated as `(x + (2^bits - N)) % 2^bits`, NOT
`(x - N) % 2^bits` (which would silently truncate the underflow
case `x < N` to zero rather than wrapping).  Split-case lemmas
below recover the two natural arithmetic specializations under the
appropriate side conditions. -/

/-- Wraparound spec for subtraction by `N` modulo `2^bits`. -/
def subConstPow2Spec (bits N x : Nat) : Nat := (x + (2^bits - N)) % 2^bits

/-! ## Underflow/borrow flag — missing infrastructure

The natural way to detect underflow (i.e., whether `x < N` at the
input) is to expose a "borrow flag" bit in the output.  In a
standard reversible subtractor this is the carry-out of the
high bit, which would naturally live at position `carry_idx bits`
(= `3*bits + 2`) — but `gidney_adder_full_faithful_no_measurement_patched bits`
operates on `adder_n_qubits bits = 3*bits + 2` qubits, indexed
`0..3*bits + 1`, and **does not include** position `carry_idx bits`.
Additionally, the patch's carry-clearing zeroes all carries that
ARE in range, removing the candidate flag from the in-range carries
as well.

To extract the borrow flag we need ONE of:

1. **Widen the adder** to `bits + 1` bits.  The high bit of the
   wider target register would directly encode the borrow (and the
   spec becomes `(x + (2^bits - N))` without the mod — the high bit
   is the wraparound indicator).  Requires re-instantiating the
   patched-adder primitive at width `bits + 1`, with the "extra"
   read bit forced to zero.  Two of the existing free qubit slots
   (positions `3*bits, 3*bits + 1`) already provide r[bits] and
   t[bits], so this only requires extending the adder definition,
   not allocating more qubits.

2. **Add a separate comparison circuit**: after the subtraction,
   compare `target` to `x` (or equivalently check the high bit of
   `target` under a specific encoding).  This introduces a new gate
   primitive — at minimum a controlled-CX cascade that XORs an
   ancilla flag based on the comparison result.  Then the flag
   needs to be reversibly uncomputed before reuse.

3. **Hand-craft a borrow-flag-aware variant** of the Gidney adder
   itself, where one of the existing ancillas is repurposed as the
   borrow output rather than being cleared by the patch.  Departs
   from the proved patched-adder primitive.

The cleanest path (lowest risk, maximum reuse) is **option 1**: a
`(bits+1)`-bit version of the patched-adder primitive applied to a
zero-padded input.  The borrow is then literally `target_val
(bits+1) (...) ≥ 2^bits`, or equivalently the function
`gidney_target_val_high_bit (bits+1) (...)`.

This is the next concrete sub-target for the modular-addition layer.
For this iteration, the wraparound subtraction primitive
(`patched_adder_sub_const_pow2` + split-case lemmas) is complete
under the existing infrastructure. -/

/-! ## Widened subtraction with borrow flag extraction

The "underflow flag" / "comparison flag" / "borrow bit" is the
canonical missing piece between wraparound subtraction and the full
modular adder.  Following the path noted above, we instantiate the
patched Gidney adder at width `bits + 1` and prove that the high
target bit (bit at position `bits`) is exactly the comparison flag
`decide (x < N)`. -/

/-- Wraparound-subtraction spec at widened bit-count `bits + 1`. -/
def subConstPow2WideSpec (bits N x : Nat) : Nat :=
  (x + (2^(bits + 1) - N)) % 2^(bits + 1)

/-! ## Conditional add-back primitive (masked-register preparation)

Following from the underflow/comparison flag (`patched_adder_sub_const_underflow_flag`),
the next step in the standard modular-addition pipeline is a
conditional add-back of `N` whenever the comparison flag indicates
underflow.

Naive controlled-adder approaches require controlled-CCX gates not
present in the Gate IR (which has only `X / CX / CCX / seq`).  We
avoid this by using **masked-register preparation**: prepare the
adder's read register with the bits `flag ∧ N.testBit i` (computed
in-place via a single CX per nonzero N-bit), then run the ordinary
patched Gidney adder, then un-prepare (the cascade is its own
inverse since CX is involutive).

The flag qubit lives at index `flagIdx`, required to be disjoint
from the adder's working register (`adder_n_qubits bits ≤ flagIdx`).
This places the flag above the natural adder range and avoids
collisions with read / target / carry positions.

### Deliverable A — `prepareMaskedConstRead`

Cascade of CXs from `flagIdx` into each `read_idx k` (for `k < bits`)
guarded by whether `N.testBit k` is set. -/

/-- Prepare the read register by XORing each `read_idx k` (for `k < bits`)
with `flag ∧ N.testBit k`, where the flag bit lives at `flagIdx`.
Implemented as a CX cascade conditioned on the bit pattern of `N`. -/
def prepareMaskedConstRead : Nat → Nat → Nat → Gate
  | 0,     _, _       => Gate.I
  | k + 1, N, flagIdx =>
      Gate.seq (prepareMaskedConstRead k N flagIdx)
               (if N.testBit k then Gate.CX flagIdx (read_idx k) else Gate.I)

/-! ### Deliverable C — `conditionalAddConstGate` -/

/-- Conditional add-back gate: prepare the read register with the
masked constant `flag ∧ N`, run the patched Gidney adder, un-prepare
the read register.  The result computes
`target := (x + (if flag then N else 0)) mod 2^bits` without using
any controlled-CCX (CCCX) gate. -/
def conditionalAddConstGate (bits N flagIdx : Nat) : Gate :=
  Gate.seq (prepareMaskedConstRead bits N flagIdx)
    (Gate.seq (gidney_adder_full_faithful_no_measurement_patched bits)
      (prepareMaskedConstRead bits N flagIdx))

/-! ## Composable constant-add / constant-sub primitives

The conditional add-back gate above is parameterised by an external
`flag` bit.  For full modular-addition composition we also need an
*unconditional* constant-add gate that takes its input as a clean
`adder_input_F bits 0 x` (zero read register, target = `x`) and
produces clean output (target = `(x + c) mod 2^bits`, read register
restored to zero, carries cleared).

These primitives are simpler than the conditional variant — no flag
ancilla, no `WellTyped` enlargement — so they live entirely inside
the natural `adder_n_qubits bits` dimension.

The same prep/unprep idiom is used, but with an X-gate cascade (rather
than CX) since the constant is classically known. -/

/-! ### `prepareConstRead` — unconditional read-register preparation -/

/-- Unconditionally prepare `read_idx k := c.testBit k` for `k < bits`
by applying `X (read_idx k)` whenever `c.testBit k = true`.  When
applied to a zero read register, sets it to the bits of `c`; applied
again (involutive), it clears the read register back to zero. -/
def prepareConstRead : Nat → Nat → Gate
  | 0,     _ => Gate.I
  | k + 1, c => Gate.seq (prepareConstRead k c)
                  (if c.testBit k then Gate.X (read_idx k) else Gate.I)

/-! ### Self-contained `addConstGate` and `subConstGate` -/

/-- Composable constant-add gate: prepare read with `c`, run the
patched Gidney adder, unprepare read.  Takes a clean
`adder_input_F bits 0 x` and produces target = `(x + c) mod 2^bits`,
with read register restored to zero and carries cleared. -/
def addConstGate (bits c : Nat) : Gate :=
  Gate.seq (prepareConstRead bits c)
    (Gate.seq (gidney_adder_full_faithful_no_measurement_patched bits)
      (prepareConstRead bits c))

/-- Composable constant-sub gate, expressed as wraparound addition of
`2^bits - N`.  This implements `(x + (2^bits - N)) mod 2^bits`, which
equals `(x - N) mod 2^bits` over the two's-complement view. -/
def subConstGate (bits N : Nat) : Gate :=
  addConstGate bits (2^bits - N)

/-! ### Deliverable B — arithmetic pipeline spec and correctness -/

/-- Arithmetic-level spec for the widened modular-addition pipeline at
width `bits + 1`.  Composes: subtract-`N` after add-`c`, conditionally
add back `N` when the comparison flag indicates underflow. -/
def modAddConstArithmeticSpec (bits N c x : Nat) : Nat :=
  (subConstPow2WideSpec bits N (x + c)
    + (if decide ((x + c) < N) then N else 0)) % 2^(bits + 1)

/-! ### Deliverable D — flag-copy gate

The single `CX (target_idx bits) flagIdx` that moves the comparison
flag from in-band `target_idx bits` to out-of-band `flagIdx`, suitable
as a control for the conditional add-back. -/

/-- Flag-copy gate: a single CX from `target_idx bits` into `flagIdx`. -/
def copyTargetHighBitToFlag (bits flagIdx : Nat) : Gate :=
  Gate.CX (target_idx bits) flagIdx

/-- The full DIRTY-FLAG modular add-constant gate.  Pipeline:
`addConstGate (bits+1) c  ;  subConstGate (bits+1) N  ;
copyTargetHighBitToFlag bits flagIdx  ;
conditionalAddConstGate (bits+1) N flagIdx`.

The result has the low `bits` target bits encoding `(x + c) mod N`,
but the flag bit at `flagIdx` is LEFT DIRTY at `decide ((x + c) < N)`.
Flag uncomputation is handled in a later tick. -/
def modAddConstGate_dirtyFlag (bits N c flagIdx : Nat) : Gate :=
  Gate.seq (addConstGate (bits + 1) c)
    (Gate.seq (subConstGate (bits + 1) N)
      (Gate.seq (copyTargetHighBitToFlag bits flagIdx)
        (conditionalAddConstGate (bits + 1) N flagIdx)))

/-! ### Flag-uncompute gate -/

/-- Reversible flag-uncompute gate: `subConstGate c ; CX (target_idx bits) flagIdx ;
X flagIdx ; addConstGate c`.  Restores `flagIdx` to false while leaving the
target, read, and carry registers unchanged. -/
def flagUncomputeGate (bits c flagIdx : Nat) : Gate :=
  Gate.seq (subConstGate (bits + 1) c)
    (Gate.seq (Gate.CX (target_idx bits) flagIdx)
      (Gate.seq (Gate.X flagIdx)
        (addConstGate (bits + 1) c)))

/-- **Clean modular add-constant gate**.  Composition of the dirty-flag
pipeline with the flag-uncompute step.  The internal flag bit lives at
`adder_n_qubits (bits + 1)`. -/
def modAddConstGate (bits N c : Nat) : Gate :=
  Gate.seq (modAddConstGate_dirtyFlag bits N c (adder_n_qubits (bits + 1)))
    (flagUncomputeGate bits c (adder_n_qubits (bits + 1)))

/-! ## Tick 6 — Controlled modular add-constant (skeleton + WellTyped)

For modular multiplication we need a *controlled* version of
`modAddConstGate`: `if control then add c mod N else identity`.

**Design.**  Replace each `addConstGate` / `subConstGate` step in the
`modAddConstGate` pipeline by `conditionalAddConstGate` controlled by
the external `controlIdx`.  Replace the internal `CX (target_idx bits)
flagIdx` flag-copy by `CCX (controlIdx, target_idx bits, flagIdx)`,
and `X flagIdx` by `CX (controlIdx, flagIdx)`.

This uses only Gate IR primitives X / CX / CCX — no controlled-CCX
(CCCX) needed.  The "step 4" (`conditionalAddConstGate N flagIdx`) is
*unchanged*: when `control = false`, the controlled flag-copy at step 3
never fires, so `flagIdx = 0`, and the conditional add-back is itself
identity in that branch.

The correctness theorem follows by case-splitting on the value of
`controlIdx`: for `false`, each step is identity on the working
register; for `true`, each step matches the corresponding step in
`modAddConstGate`.  Proof is deferred to the next sub-tick.

This commit delivers: gate definition + WellTyped (the rest of the
proof requires a per-step "identity-when-control-false" lemma and a
"matches-modAddConstGate-when-control-true" lemma). -/

/-- Controlled modular add-constant gate.  Eight-step pipeline:
controlled add `c` ; controlled sub `N` ; controlled flag-copy ;
flag-controlled add-back `N` ; controlled sub `c` ; controlled
flag-copy ; controlled X flag ; controlled add `c`. -/
def controlledModAddConstGate (bits N c controlIdx flagIdx : Nat) : Gate :=
  Gate.seq (conditionalAddConstGate (bits + 1) c controlIdx)
    (Gate.seq (conditionalAddConstGate (bits + 1) (2^(bits + 1) - N) controlIdx)
      (Gate.seq (Gate.CCX controlIdx (target_idx bits) flagIdx)
        (Gate.seq (conditionalAddConstGate (bits + 1) N flagIdx)
          (Gate.seq (conditionalAddConstGate (bits + 1) (2^(bits + 1) - c) controlIdx)
            (Gate.seq (Gate.CCX controlIdx (target_idx bits) flagIdx)
              (Gate.seq (Gate.CX controlIdx flagIdx)
                (conditionalAddConstGate (bits + 1) c controlIdx)))))))

/-! ### Tick 7 — Modular multiplier by repeated controlled additions

The modular multiplier circuit applies, for each bit `i` of a
multiplier register `m`, a `controlledModAddConstGate` with constant
`(a * 2^i) % N` controlled by the `i`-th multiplier qubit.  The
cumulative effect is to send the adder's target register from `x` to
`(x + a * m) % N`, where `m = ∑_{i : bit_i = 1} 2^i`.

**Register layout**: positions `0 .. adder_n_qubits (bits+1) - 1` form
the adder block (read/target/carry).  Positions
`adder_n_qubits (bits+1) + 0 .. adder_n_qubits (bits+1) + multBits - 1`
are the multiplier qubits, and position
`adder_n_qubits (bits+1) + multBits` is the shared flag qubit (clean
before and after each iteration). -/

/-- Auxiliary recursive gate for the modular multiplier: applies
controlled modular-add of `(a * 2^i) % N` for bits `i = 0, 1, ..., k-1`.
The parameter `multBits` is the TOTAL multiplier width (used to
position the shared flag qubit); `k` is the recursion index running
from 0 up to `multBits`. -/
def modMultConstGateAux (bits N a multBits : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 =>
    Gate.seq
      (modMultConstGateAux bits N a multBits k)
      (controlledModAddConstGate bits N ((a * 2^k) % N)
        (adder_n_qubits (bits + 1) + k)
        (adder_n_qubits (bits + 1) + multBits))

/-- Modular multiplier gate: applies `controlledModAddConstGate` for
each bit of the multiplier register, accumulating `(a * m) % N` into
the adder's target register, where `m` is the natural-number value of
the multiplier register. -/
def modMultConstGate (bits N a multBits : Nat) : Gate :=
  modMultConstGateAux bits N a multBits multBits

/-! #### Tick 7c — multiplier-encoded input. -/

/-- Auxiliary recursive helper for the multiplier-encoded input: starting
from `f`, applies an `update _ (adder_n_qubits (bits+1) + j) (Nat.testBit
m j)` for each `j = 0, 1, ..., i-1`, in order.  The last update written
is at `j = i - 1`. -/
def mult_input_F_aux (bits multBits m : Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, f => f
  | i+1, f =>
    update (mult_input_F_aux bits multBits m i f)
           (adder_n_qubits (bits + 1) + i) (Nat.testBit m i)

/-- **Multiplier-encoded input.**  Starts from `adder_input_F (bits+1) 0
x` (which puts value `x` in the adder's target register and 0 elsewhere
within the adder block; `false` outside), then fills the multiplier
qubits at positions `adder_n_qubits (bits+1) + j` (for `j = 0, ...,
multBits - 1`) with the bits of `m`. -/
def mult_input_F (bits multBits x m : Nat) : Nat → Bool :=
  mult_input_F_aux bits multBits m multBits (adder_input_F (bits + 1) 0 x)

/-! ### Tick 8 — Initial-state form for Shor's modular multiplier.

The Shor oracle expects modular multiplication acting on an input state
where the multiplier register holds `x` and the adder register is
zeroed.  The gate then advances the adder's target from `0` to
`a * x mod N` (out-of-place form).

**Register-layout note.**  Our `mult_input_F bits multBits x m` places
the adder block at LOW positions (0 to `adder_n_qubits (bits+1) - 1`),
the multiplier register at positions `adder_n_qubits (bits+1) ..
adder_n_qubits (bits+1) + multBits - 1` (LITTLE-endian by
`Nat.testBit`), and the flag at the TOP.  The Shor encoding
`encodeDataZeroAnc n anc x` (in `MCPBridge.lean`) places data at LOW
positions 0..n-1 in BIG-endian order, and zero ancillas at n..n+anc-1.
These layouts are NOT identical — bridging fully to
`encodeDataZeroAnc` requires register permutation (swap-style)
and/or coordinate flipping, deferred to a future tick.

What we land here: the **initial-state correctness** theorem and the
WellTyped corollary at the Shor-compatible total dimension. -/

/-- Initial state for the multiplier: the multiplier register holds
`x`, the adder block and flag are zeroed. -/
def mult_state_init (bits multBits x : Nat) : Nat → Bool :=
  mult_input_F bits multBits 0 x

/-! ### Tick 9 — Modular exponentiation step gate family.

The `i`-th step of QPE's controlled-multiplication cascade requires
multiplication by `a^(2^i) mod N`.  We define
`f_modmult_step_gate bits N a multBits i := modMultConstGate bits N
(a^(2^i) % N) multBits` and lift the multiplier's initial-state
correctness to the squared constant. -/

/-- The `i`-th step of the QPE multiplication cascade: multiplication
by the constant `a^(2^i) mod N` applied to the multiplier-encoded
state. -/
def f_modmult_step_gate (bits N a multBits i : Nat) : Gate :=
  modMultConstGate bits N (a^(2^i) % N) multBits

/-! ### Tick 10 — Out-of-place gate family + WellTyped over all iterates.

`f_modmult_gate_family bits N a multBits : Nat → Gate` provides the
full Shor-style multiplication cascade: at iterate `i`, multiplication
by `a^(2^i) mod N`.  WellTyped for all `i` follows by lifting the
single-step WellTyped theorem under the family. -/

/-- Modular multiplication gate family indexed by QPE iterate. -/
def f_modmult_gate_family (bits N a multBits : Nat) : Nat → Gate :=
  f_modmult_step_gate bits N a multBits

/-! ### Tick 13 — Two-qubit SWAP primitive (path A foundation).

A SWAP between two qubits, expressed as the standard three-CNOT
decomposition `CX a b ; CX b a ; CX a b`.  This is the smallest
building block for the in-place modular multiplier wrapper
(`OOPmul(a) ; SWAP ; OOPmul^(-1)(a⁻¹)`) — see QUESTIONS.md
2026-05-28 03:24 path (A). -/

/-- Two-qubit SWAP: exchanges the values at qubits `a` and `b` via the
standard three-CNOT decomposition. -/
def qubit_swap (a b : Nat) : Gate :=
  Gate.seq (Gate.CX a b) (Gate.seq (Gate.CX b a) (Gate.CX a b))

/-! ### Tick 14 — Register SWAP primitive (multi-qubit SWAP). -/

/-- Auxiliary recursive register-swap helper.  At iteration count `n`,
applies pairwise `qubit_swap (offsetA + k) (offsetB + k)` for
`k = 0, 1, ..., n - 1`. -/
def register_swap_aux (offsetA offsetB : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 => Gate.seq (register_swap_aux offsetA offsetB k)
                    (qubit_swap (offsetA + k) (offsetB + k))

/-- Register-level SWAP: exchanges two `multBits`-wide registers at
positions `[offsetA, offsetA + multBits)` and
`[offsetB, offsetB + multBits)`. -/
def register_swap (multBits offsetA offsetB : Nat) : Gate :=
  register_swap_aux offsetA offsetB multBits

/-! ### Tick 16 — In-place modular multiplier definition + WellTyped.

Compose the three stages of the Markov–Saeedi / Beauregard in-place
modular multiplier:

  modMultConstGate(a) ; mult_target_swap ; modMultConstGate(N - ainv)

The middle SWAP exchanges each multiplier-register qubit at position
`adder_n_qubits (bits+1) + k` with the corresponding adder-target
qubit at position `target_idx k = 3*k + 1`.  Because the target
register is interleaved with the adder's read/carry positions, this
SWAP is a sequence of `qubit_swap`s at NON-contiguous positions and
cannot be re-used from `register_swap`. -/

/-- Auxiliary recursive multiplier-target SWAP at iteration count `n`:
swaps `(adder_n_qubits (bits+1) + k, target_idx k)` for
`k = 0, ..., n - 1`. -/
def mult_target_swap_aux (bits : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 => Gate.seq (mult_target_swap_aux bits k)
                    (qubit_swap (adder_n_qubits (bits + 1) + k) (target_idx k))

/-- Multiplier-target SWAP: pairwise exchanges multiplier-register
qubits at `adder_n_qubits (bits+1) + k` with adder-target qubits at
`target_idx k`, for `k = 0, ..., multBits - 1`. -/
def mult_target_swap (bits multBits : Nat) : Gate :=
  mult_target_swap_aux bits multBits

/-- **In-place modular multiplier gate.**  Three-stage composition:
1. `modMultConstGate bits N a multBits` — OOPmul(a): `|x⟩|0⟩ → |x⟩|a*x mod N⟩`.
2. `mult_target_swap bits multBits` — exchanges multiplier and target
   registers: `|x⟩|a*x mod N⟩ → |a*x mod N⟩|x⟩`.
3. `modMultConstGate bits N ((N - ainv) % N) multBits` — adds
   `(N - ainv) * (a*x mod N)` to the target, yielding 0 by
   `mod_inv_cancel_identity`.  Net effect: `|a*x mod N⟩|0⟩`.

The multiplier register holds the input `x` initially; after the
gate, it holds `(a * x) mod N`, with adder and flag clean.  This is
exactly the in-place semantics of `MultiplyCircuitProperty`. -/
def modMultInPlace (bits N a ainv multBits : Nat) : Gate :=
  Gate.seq (modMultConstGate bits N a multBits)
           (Gate.seq (mult_target_swap bits multBits)
                     (modMultConstGate bits N ((N - ainv) % N) multBits))

/-! ### Tick 20 — Reverse-pairing register SWAP (layout-conversion primitive).

The layout conversion from `encodeDataZeroAnc n anc x` (data at LOW
positions 0..n-1, BIG-endian) to `mult_state_init bits multBits x`
(data at HIGH positions adder_n_qubits..+multBits-1, LITTLE-endian)
is a REVERSED pairing: position `i ∈ [0, n)` swaps with position
`adder_n_qubits + (n - 1 - i) ∈ [adder_n_qubits, adder_n_qubits + n)`.

This tick defines `reverse_register_swap` and proves its position-level
correctness.  The next tick composes it with `modMultInPlace` to obtain
a layout-converting in-place modular multiplier acting on
`encodeDataZeroAnc`. -/

/-- Auxiliary recursive reverse-pairing register SWAP at iteration
count `k`: at step k, swaps `(offsetA + k, offsetB + (n - 1 - k))`. -/
def reverse_register_swap_aux (n offsetA offsetB : Nat) : Nat → Gate
  | 0 => Gate.I
  | k+1 => Gate.seq (reverse_register_swap_aux n offsetA offsetB k)
                    (qubit_swap (offsetA + k) (offsetB + (n - 1 - k)))

/-- Reverse-pairing register SWAP: exchanges positions
`[offsetA, offsetA + n)` and `[offsetB, offsetB + n)` with index
reversal (position `offsetA + i` swaps with `offsetB + (n - 1 - i)`). -/
def reverse_register_swap (n offsetA offsetB : Nat) : Gate :=
  reverse_register_swap_aux n offsetA offsetB n

end FormalRV.BQAlgo
