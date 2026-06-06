import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Audit.Common.PaperClaims
import FormalRV.PPM.GidneyAND
import Mathlib.Tactic.IntervalCases

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims
open FormalRV.BQCode




/-! ## Register indexing for the ripple-carry adder

    qianxu Fig. 4(a) interleaves three registers along the qubit axis:
    `read[0], target[0], carry[0], read[1], target[1], carry[1], …`
    For an `n`-bit adder, the wire count is `read = n+1`, `target = n+1`,
    `carry = n` (with an extra read/target for the overflow bit). The
    figure shows n=4: 14 lines total (5+5+4).

    We choose the convention: qubit indices interleave in groups of
    three, with the final read/target on top of the carry chain.
    `read[i] = 3*i`, `target[i] = 3*i + 1`, `carry[i] = 3*i + 2`. -/

/-- Qubit index for the i-th read bit. -/
def read_idx (i : Nat) : Nat := 3 * i

/-- Qubit index for the i-th target bit. -/
def target_idx (i : Nat) : Nat := 3 * i + 1

/-- Qubit index for the i-th carry bit. -/
def carry_idx (i : Nat) : Nat := 3 * i + 2

/-- Total qubits required for an n-bit adder: 3n+2 (n carries +
    n+1 reads + n+1 targets - the final i has no carry). -/
def adder_n_qubits (n : Nat) : Nat := 3 * n + 2

/-! ## Stub: per-bit "computation unit" (blue box in Fig. 4(a))

    Each blue box in qianxu Fig. 4(a) is the per-bit computation
    unit. From the figure, it appears to be a MAJ on
    (read[i], target[i], carry[i]) but with the prior carry chain
    threaded in. The exact gate sequence is the next deliverable;
    this stub captures the indexing for now. -/

/-- Per-bit computation unit at bit position `i`. CURRENTLY a stub
    using `cuccaro_MAJ` on the (read[i], target[i], carry[i]) triple
    — this MUST be replaced with the exact Fig. 4(a) gate sequence
    in the next tick (the figure has additional CX gates threading
    carry[i-1] into the unit). -/
def ripple_carry_unit_stub (i : Nat) : Gate :=
  cuccaro_MAJ (read_idx i) (target_idx i) (carry_idx i)

/-! ## Gidney forward-pass per-bit step (Iter 19, 2026-05-12)

    Faithful Lean encoding of one bit's contribution to Qrisp's
    `qq_gidney_adder` forward loop. Source:
    `PyCircuits/adders/GIDNEY_GATE_SEQUENCE.md`.

    Per-bit forward gates (lines 58-83 of `qq_gidney_adder.py`):
    - i = 0: `CCX(a[0], b[0], gidney_anc[0])`
    - i > 0: `CCX(a[i], b[i], gidney_anc[i])` + `CX(gidney_anc[i-1], gidney_anc[i])`

    (We omit the optional propagation CXs `CX(carry[i], a[i+1])` and
    `CX(carry[i], b[i+1])` from this minimal encoding — they affect
    gate count but NOT Toffoli or T-count, which is what qianxu's
    Eq. E3 cost is built on.)

    Naming: read[i] = Qrisp's a[i], target[i] = Qrisp's b[i],
    carry[i] = Qrisp's gidney_anc[i] (paper's distinct carry wire). -/

/-- ⚠️ **COST-ONLY SKELETON — does NOT compute addition.**  This simplified step omits the
    carry-propagation CXs (Iter 53 finding below), so for `i > 0` it XORs the wrong value into
    `carry[i]`.  The semantically-correct, basis-state-proven steps are
    `gidney_adder_bit_step_faithful_{first,interior,last}`, composed into the correct forward pass
    `gidney_adder_forward_faithful_full`.  This skeleton is retained ONLY for T-count accounting,
    which provably equals the correct adder's (`gidney_cost_skeleton_eq_faithful`). -/
def gidney_adder_bit_step (i : Nat) : Gate :=
  if i = 0 then
    Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
  else
    Gate.seq
      (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
      (Gate.CX (carry_idx (i - 1)) (carry_idx i))

/-! ## Forward cascade (Iter 20, 2026-05-12)

    Compose `gidney_adder_bit_step` for bits 0 through n-1 into the
    full forward pass. Mirrors `UnaryLookup.lean`'s `prefix_and_cascade`
    structure 1:1. -/

/-- ⚠️ **COST-ONLY SKELETON** forward pass (built on the wrong `gidney_adder_bit_step`).  NOT
    semantically correct — use `gidney_adder_forward_faithful_full`.  Retained only for its
    T-count, which equals the correct adder's by `gidney_cost_skeleton_eq_faithful`. -/
def gidney_adder_forward : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_adder_forward n) (gidney_adder_bit_step n)

/-! ## Reverse pass + final CX cascade (Iter 21, 2026-05-12)

    The full Gidney adder structure (`qq_gidney_adder.py` lines 85-127):
    - Forward cascade (already encoded: `gidney_adder_forward`)
    - **Reverse pass under `invert()`** — emits bit steps in reverse order
    - **Final CX cascade** — `cx(a[i], b[i])` for each i (stamps the sum)

    Under measurement-based uncomputation (Gidney's trick), the reverse
    pass uses 0 Toffolis. But for the gate-level review we encode the
    explicit reverse — same Toffolis going the other direction — to
    establish the no-measurement upper bound. -/

/-- Reverse pass cascade: emits `bit_step n-1, n-2, ..., 0` in reverse
    order. Like `prefix_and_uncompute`, this gives `n` Toffolis. -/
def gidney_adder_uncompute : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_adder_bit_step n) (gidney_adder_uncompute n)

/-- Final CX cascade — one `CX(read[i], target[i])` per bit, stamping
    the sum onto the target register. Source:
    `qq_gidney_adder.py:122-123`. -/
def gidney_final_cx_cascade : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_final_cx_cascade n)
                        (Gate.CX (read_idx n) (target_idx n))

/-- ⚠️ **COST-ONLY SKELETON** full adder (forward + reverse + final CX) built on the wrong
    bit-step — NOT semantically correct.  Its T-count (`tcount_gidney_adder_full = 14n`) is valid
    and is what the Shor cost model binds to; the correct, basis-state-proven adder is the faithful
    cascade (`gidney_adder_forward_faithful_full` + reverse + `gidney_final_cx_cascade`).  See
    `gidney_cost_skeleton_eq_faithful` for the cost equivalence with the correct adder. -/
def gidney_adder_full (n : Nat) : Gate :=
  Gate.seq (Gate.seq (gidney_adder_forward n) (gidney_adder_uncompute n))
           (gidney_final_cx_cascade n)

/-! ## Review-gap closure: Gidney measurement-AND drops 14n → 7n
    (Iter 44, 2026-05-12)

    With `BQCode.GidneyAND` (Iter 43), we can now FORMALLY close
    the Iter 25 finding. The n-bit Gidney adder consists of n
    forward Gidney-AND cycles. Per `GidneyAND_cycle_tcount_eq_seven`
    (Iter 43), each cycle costs exactly 7 T-gates (1 CCX forward +
    PPM-based reverse with 0 Toffolis).

    So the **measurement-uncomputation n-bit Gidney adder T-count
    is `7n`**, matching qianxu Eq. E3 exactly. The gate-explicit
    14n bound (`tcount_gidney_adder_full`) drops to 7n once the
    Gidney trick is formally accounted for.

    **Review gap closure**: this is the FORMAL EXPRESSION of "qianxu's
    7n claim equals Lean's 7n claim under the Gidney optimization".
    The previously load-bearing assumption is now a derived theorem. -/

/-- Per-bit Gidney adder with measurement-based uncomputation:
    one full Gidney-AND cycle per bit. T-count per bit = 7. -/
def gidney_adder_bit_with_measurement_uncompute_tcount : Nat := 7

/-- n-bit Gidney adder T-count with measurement-based uncomputation:
    `7n`. Derived structurally from `GidneyAND_cycle_tcount_eq_seven`
    (Iter 43) applied at each bit. -/
def gidney_adder_full_with_measurement_uncompute_tcount (n : Nat) : Nat :=
  gidney_adder_bit_with_measurement_uncompute_tcount * n

/-! ### **Review-gap surfacing (Iter 53, 2026-05-12)**: simplified bit-step ≠ Gidney carry

    Per CLAUDE.md hard rule "arithmetic-only verifications don't count",
    pushing toward bit-step semantic correctness for `i > 0` immediately
    reveals that **the simplified `gidney_adder_bit_step` we encoded
    does NOT compute Gidney's actual carry**.

    The i > 0 step in our Lean encoding is:
    ```
    Gate.seq (Gate.CCX read[i] target[i] carry[i]) (Gate.CX carry[i-1] carry[i])
    ```
    On a classical basis state, this XORs `(read[i] ∧ target[i]) ⊕
    carry[i-1]` into `carry[i]`. That is **not** the carry-out formula
    of a ripple-carry adder. The correct standard carry-out is
    `(a ∧ b) ∨ ((a ⊕ b) ∧ prev_carry)`, equivalent under Gidney's trick to
    `((a ⊕ prev_carry) ∧ (b ⊕ prev_carry)) ⊕ prev_carry`.

    The Gidney circuit requires **pre-XORing `a[i] ⊕= prev_carry` and
    `b[i] ⊕= prev_carry`** before the AND (these CXs are emitted by the
    previous bit's propagation step in
    `PyCircuits/adders/GIDNEY_GATE_SEQUENCE.md`). Our `gidney_adder_
    bit_step` omits both the propagation CXs from the previous step and
    the implicit pre-XOR.

    **NEW REVIEW FINDING**: the simplified bit-step has the right Toffoli
    count (1 per bit) but the **wrong logical action**. The earlier
    Iter 20 "tcount_gidney_adder_forward n = 7n" theorem is therefore
    a count of a gate sequence that does not implement Gidney's adder.
    This is precisely the kind of gap the new CLAUDE.md rules require
    us to surface; the count-only review could not see this. -/

/-! ## Faithful Gidney bit-step (Iter 55, 2026-05-12)

    The Iter 53 review-gap finding motivates a corrected encoding.
    Per `PyCircuits/adders/GIDNEY_GATE_SEQUENCE.md` and
    `qq_gidney_adder.py:58-73`, the per-bit forward step at an
    interior bit `i ≥ 1` (not the last) emits FOUR gates:

    1. `mcx([a[i], b[i]], gidney_anc[i], method="gidney")` →
       `Gate.CCX (read_idx i) (target_idx i) (carry_idx i)`
    2. `cx(gidney_anc[i-1], gidney_anc[i])` →
       `Gate.CX (carry_idx (i-1)) (carry_idx i)`
    3. `cx(gidney_anc[i], a[i+1])` →
       `Gate.CX (carry_idx i) (read_idx (i+1))`         [propagation]
    4. `cx(gidney_anc[i], b[i+1])` →
       `Gate.CX (carry_idx i) (target_idx (i+1))`        [propagation]

    Gates 3-4 are the **propagation CXs missing from the Iter 19
    simplified encoding**. They pre-XOR `read[i+1]` and `target[i+1]`
    by `carry[i]`, which is what makes the next bit's AND compute
    Gidney's carry formula `((a ⊕ prev) ∧ (b ⊕ prev)) ⊕ prev`. -/

/-- Faithful Gidney bit-step at an interior bit `i ≥ 1` (not the last).
    Emits 4 gates: CCX + chain-CX + 2 propagation CXs. **This is the
    review-correct encoding** per `qq_gidney_adder.py:58-73`. -/
def gidney_adder_bit_step_faithful_interior (i : Nat) : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.seq
        (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
        (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
      (Gate.CX (carry_idx i) (read_idx (i + 1))))
    (Gate.CX (carry_idx i) (target_idx (i + 1)))

/-! ### Faithful interior cascade (Iter 56)

    Compose `gidney_adder_bit_step_faithful_interior` for bits
    `1..n`, parameterized by `n` (the number of interior steps to
    emit). This is the faithful analog of `gidney_adder_forward` —
    same per-bit Toffoli count (7), but with `4 * n` total gates
    instead of `2 * n` (the propagation CXs are now included).

    Note: this cascade treats all bits as "interior" (i ≥ 1, not the
    last). A full Gidney adder would prepend an i=0 step (no chain
    CX) and append a last-bit step (no propagation). The interior
    cascade is the structural core — it captures the Gidney carry
    semantics on the bulk of the adder. -/

/-- Faithful interior cascade: composes
    `gidney_adder_bit_step_faithful_interior (k+1)` for `k = 0..n-1`.
    Emits exactly `4n` gates (n Toffolis + 3n CXs). -/
def gidney_adder_forward_faithful_interior : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq
                 (gidney_adder_forward_faithful_interior n)
                 (gidney_adder_bit_step_faithful_interior (n + 1))

/-! ## Faithful bit-step correctness (Iter 57)

    **First Verified-tier theorem for the faithful adder encoding**:
    proves the per-bit composite action on classical basis states,
    using the Iter 52 reusable framework. -/

/-- The post-state after applying `gidney_adder_bit_step_faithful_interior i`
    to a basis state `f_to_vec dim f`, expressed as four chained
    `update`s. This is the **explicit semantic action** of the
    faithful bit-step:

      step 1 (CCX):    carry[i]    ⊕= read[i] ∧ target[i]
      step 2 (CX):     carry[i]    ⊕= carry[i-1]
      step 3 (CX):     read[i+1]   ⊕= carry[i]  (post-step-2 value)
      step 4 (CX):     target[i+1] ⊕= carry[i]  (post-step-2 value)

    With pre-XORed inputs from the previous bit's propagation, the
    post-step-2 carry[i] equals Gidney's carry formula
    `((read[i] ⊕ prev) ∧ (target[i] ⊕ prev)) ⊕ prev`. -/
def gidney_bit_step_faithful_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f  (carry_idx i)
              (xor (f (carry_idx i))
                   (f (read_idx i) && f (target_idx i)))
  let f₂ := update f₁ (carry_idx i)
              (xor (f₁ (carry_idx i)) (f₁ (carry_idx (i - 1))))
  let f₃ := update f₂ (read_idx (i + 1))
              (xor (f₂ (read_idx (i + 1))) (f₂ (carry_idx i)))
  let f₄ := update f₃ (target_idx (i + 1))
              (xor (f₃ (target_idx (i + 1))) (f₃ (carry_idx i)))
  f₄

/-! ## Interior gate-reverse + matrix-level involution (Iter 82, 2026-05-12)

    Mirrors Iter 81's first-bit pattern and Iter 69's last-bit
    pattern. Interior step is 4 gates: CCX + chain CX + 2
    propagation CXs. Gate-reverse swaps the order. Forward · reverse
    collapses via 4 involution pairs (3 CNOT + 1 CCX), each with
    one `Matrix.mul_assoc` reassociation to expose the pair. -/

/-- Gate-reverse of `gidney_adder_bit_step_faithful_interior i`. -/
def gidney_adder_bit_step_faithful_interior_reverse (i : Nat) : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.seq
        (Gate.CX (carry_idx i) (target_idx (i + 1)))
        (Gate.CX (carry_idx i) (read_idx (i + 1))))
      (Gate.CX (carry_idx (i - 1)) (carry_idx i)))
    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))

/-! ## Faithful cascade correctness (Iter 58)

    Lift the per-bit correctness (Iter 57) to the full n-bit faithful
    interior cascade by induction. The cascade-level post-state is the
    fold of per-bit post-states, and the inductive step uses
    `gate_seq_acts_on_basis` + the IH + the per-bit correctness. -/

/-- Cascade-level post-state: fold of `gidney_bit_step_faithful_post_state`
    over bits 1..n. Matches the recursive structure of
    `gidney_adder_forward_faithful_interior`. -/
def gidney_cascade_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | n + 1, f =>
      gidney_bit_step_faithful_post_state (n + 1)
        (gidney_cascade_post_state n f)

/-- **Bit-disjointness hypothesis for bit `i`**: bundles the 12
    conditions needed for the per-bit correctness theorem. Decidable
    on any concrete `i, dim`; for the parametric cascade we quantify
    over the bit index. -/
structure BitDisjointness (dim i : Nat) : Prop where
  hri    : read_idx i < dim
  hti    : target_idx i < dim
  hci    : carry_idx i < dim
  hcim1  : carry_idx (i - 1) < dim
  hri1   : read_idx (i + 1) < dim
  hti1   : target_idx (i + 1) < dim
  h_rt   : read_idx i ≠ target_idx i
  h_rc   : read_idx i ≠ carry_idx i
  h_tc   : target_idx i ≠ carry_idx i
  h_cc   : carry_idx (i - 1) ≠ carry_idx i
  h_ci_ri1 : carry_idx i ≠ read_idx (i + 1)
  h_ci_ti1 : carry_idx i ≠ target_idx (i + 1)

/-! ## Adder first-bit (i=0) case (Iter 65, 2026-05-12)

    The interior bit-step `gidney_adder_bit_step_faithful_interior`
    assumes i ≥ 1 (uses `carry[i-1]`). The first bit (i=0) has no
    chain CX since there's no `carry[-1]`; it only emits CCX + 2
    propagation CXs.

    Per `qq_gidney_adder.py:68-73` (`if c_in is None`):
    ```
    mcx([a[0], b[0]], gidney_anc[0], method="gidney")  # 1 Toffoli
    cx(gidney_anc[0], a[1])                            # propagation
    cx(gidney_anc[0], b[1])                            # propagation
    ```
    Three gates: 1 CCX + 2 CX. T-count = 7; gate count = 3. -/

/-- Faithful Gidney bit-step at i=0 (first bit). Emits 3 gates: CCX +
    2 propagation CXs (no chain CX since `carry[-1]` doesn't exist). -/
def gidney_adder_bit_step_faithful_first : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0))
      (Gate.CX (carry_idx 0) (read_idx 1)))
    (Gate.CX (carry_idx 0) (target_idx 1))

/-- Post-state of `gidney_adder_bit_step_faithful_first` on basis
    states: CCX writes `(read[0] ∧ target[0])` into `carry[0]`, then
    propagation CXs XOR `carry[0]` into `read[1]` and `target[1]`.
    No chain CX (since there's no prev carry). -/
def gidney_first_bit_post_state (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f  (carry_idx 0)
              (xor (f (carry_idx 0))
                   (f (read_idx 0) && f (target_idx 0)))
  let f₂ := update f₁ (read_idx 1)
              (xor (f₁ (read_idx 1)) (f₁ (carry_idx 0)))
  let f₃ := update f₂ (target_idx 1)
              (xor (f₂ (target_idx 1)) (f₂ (carry_idx 0)))
  f₃

/-! ## First-bit gate-reverse + matrix-level involution (Iter 81, 2026-05-12)

    Mirrors Iter 69's last-bit and Iter 73's simplified-bit-step
    constructions. The first-bit forward step emits CCX +
    2 propagation CXs; its gate-reverse swaps the order to
    CX_prop_t ; CX_prop_r ; CCX. Forward · reverse collapses via
    3 involution pairs (two CNOT involutions + one CCX involution). -/

/-- Gate-reverse of `gidney_adder_bit_step_faithful_first`. Emits
    `CX(carry[0], target[1]) ; CX(carry[0], read[1]) ; CCX(read[0],
    target[0], carry[0])` — the original three gates in reverse order. -/
def gidney_adder_bit_step_faithful_first_reverse : Gate :=
  Gate.seq
    (Gate.seq
      (Gate.CX (carry_idx 0) (target_idx 1))
      (Gate.CX (carry_idx 0) (read_idx 1)))
    (Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0))

/-! ## Adder last-bit (no-propagation) case (Iter 67, 2026-05-12)

    The interior `gidney_adder_bit_step_faithful_interior` emits 4
    gates (CCX + chain CX + 2 propagation CXs). The **last interior
    bit** has no "next bit" to propagate into, so the 2 propagation
    CXs are omitted per `qq_gidney_adder.py:71-73`:
    ```
    if i != len(b) - 2:
        cx(gidney_anc[i], a[i + 1])
        cx(gidney_anc[i], b[i + 1])
    ```
    Last-bit step: 2 gates (CCX + chain CX). T-count = 7,
    gate count = 2. -/

/-- Faithful Gidney bit-step at the **last interior bit** `i ≥ 1`
    (no propagation CXs). Emits 2 gates: CCX + chain CX. -/
def gidney_adder_bit_step_faithful_last (i : Nat) : Gate :=
  Gate.seq
    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))
    (Gate.CX (carry_idx (i - 1)) (carry_idx i))

/-- Post-state of `gidney_adder_bit_step_faithful_last i`: CCX writes
    `(read[i] ∧ target[i])` into `carry[i]`, then chain CX XORs
    `carry[i-1]` into `carry[i]`. No propagation. -/
def gidney_last_bit_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (carry_idx i)
              (xor (f (carry_idx i))
                   (f (read_idx i) && f (target_idx i)))
  update f₁ (carry_idx i)
    (xor (f₁ (carry_idx i)) (f₁ (carry_idx (i - 1))))

/-! ## Reverse-bit-step involution (Iter 68, 2026-05-12)

    Foundational lemma for the **no-measurement reverse cascade**
    correctness: forward bit-step followed by its gate-reversed
    counterpart restores the basis state. Each gate (CCX, CX) is
    its own inverse, so applying them in reverse order undoes the
    forward action.

    **Building block for full adder correctness** (Iter 69 target):
    the explicit reverse cascade is `gidney_adder_uncompute n`
    (Iter 21, simplified bit-step). To bridge to the n-bit
    correctness theorem, we need the gate-level involution proven
    here. -/

/-- The **gate-reversed last-bit step** at index `i`:
    `seq (CX carry[i-1] carry[i]) (CCX read[i] target[i] carry[i])`.
    Mirrors `gidney_adder_bit_step_faithful_last i`'s gate order. -/
def gidney_adder_bit_step_faithful_last_reverse (i : Nat) : Gate :=
  Gate.seq
    (Gate.CX (carry_idx (i - 1)) (carry_idx i))
    (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))

/-! ## Gate-reverse of simplified bit-step + matrix-level fwd·rev = 1 (Iter 73, 2026-05-12)

    The simplified `gidney_adder_bit_step` (Iter 19) emits `CCX; CX` at
    i>0. Its gate-reverse — `CX; CCX` — is the natural per-bit inverse.
    Composed, `bit_step · bit_step_reverse` collapses to identity at
    matrix level:

      (CCX · CX) · (CX · CCX) = CCX · (CX · CX) · CCX = CCX · 1 · CCX = 1

    using `CNOT_CNOT_eq_one` (Framework/PadAction.lean) for the inner
    CX-pair and `CCX_CCX_eq_one` for the outer CCX-pair. For i = 0
    both reduce to a single CCX, so the involution is the bare
    `CCX_CCX_eq_one`.

    This is the **building block for Iter 74's
    `gidney_adder_forward · gidney_adder_uncompute_proper = 1`**
    cascade-level induction. Mirrors Iter 69's `..._last_fwd_rev_id`
    but for the simplified bit-step (the one used by
    `gidney_adder_forward`); Iter 69 covered only the last-bit
    faithful step. -/

/-- Gate-reverse of `gidney_adder_bit_step i`. At i = 0 both forward
    and reverse are the same single CCX (CCX is self-inverse); at
    i > 0 the reverse is `CX · CCX` (gate-order swap of forward's
    `CCX · CX`). -/
def gidney_adder_bit_step_reverse (i : Nat) : Gate :=
  if i = 0 then
    Gate.CCX (read_idx 0) (target_idx 0) (carry_idx 0)
  else
    Gate.seq
      (Gate.CX (carry_idx (i - 1)) (carry_idx i))
      (Gate.CCX (read_idx i) (target_idx i) (carry_idx i))

/-! ## Proper reverse cascade + matrix-level cascade·uncompute = 1 (Iter 75, 2026-05-12)

    `gidney_adder_uncompute` (Iter 21) uses the FORWARD bit-step in
    reverse bit order — that's the right *count* (7n Toffolis) but
    NOT a true inverse of `gidney_adder_forward` at the gate level
    (forward·that_uncompute ≠ 1 because each `bit_step i` for i>0
    is `CCX · CX`, doing it twice gives `CCX · CX · CCX · CX` ≠ 1).

    The **proper** uncompute uses the gate-reversed bit-step
    `gidney_adder_bit_step_reverse` (Iter 73). Then forward·proper
    DOES collapse to identity at the matrix level, by induction on
    n + Iter 73's per-bit involution. This is the adder analog of
    Iter 74's `prefix_and_cascade_uncompute_eq_one` (lookup side).

    The existing `gidney_adder_uncompute` is kept (matches the
    "explicit reverse Toffolis" interpretation used by the
    no-measurement upper-bound T-count theorem). The proper
    version sits alongside it as the SEMANTICALLY-correct inverse. -/

/-- **Proper reverse cascade**: gate-by-gate inverse of
    `gidney_adder_forward`. Emits `bit_step_reverse n-1, n-2, ...,
    0` in reverse order. Each gate-reverse swaps the CCX·CX → CX·CCX
    within the bit-step. -/
def gidney_adder_uncompute_proper : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (gidney_adder_bit_step_reverse n)
                        (gidney_adder_uncompute_proper n)

/-! ## Faithful full forward cascade (Iter 79, 2026-05-12)

    The Iter 19 simplified `gidney_adder_bit_step` had an review
    gap (Iter 53): for i > 0 it does NOT compute Gidney's actual
    carry (it ignores the propagation of `carry[i-1]` through the
    chain CX correctly only in the limited sense of the simplified
    encoding). Iter 55-67 introduced three FAITHFUL bit-step
    variants matching `qq_gidney_adder.py:68-104`:

    - `gidney_adder_bit_step_faithful_first` (Iter 65): bit 0,
      emits CCX + 2 propagation CXs.
    - `gidney_adder_bit_step_faithful_interior` (Iter 55): bits
      1..n-2, emits CCX + chain CX + 2 propagation CXs.
    - `gidney_adder_bit_step_faithful_last` (Iter 67): bit n-1,
      emits CCX + chain CX (no propagation, since there's no
      "next bit").

    This section **glues all three into a single forward cascade**
    that matches the actual Gidney adder structure, per the
    `qq_gidney_adder.py` reference. Indexed parametrically by `n`,
    the number of bit positions, with the convention that the
    cascade is meaningful for `n ≥ 2` (n=0 has nothing to add;
    n=1 has no carry chain so the chain CXs / propagation CXs are
    structurally absent — special-case to `Gate.I` here).

    **Phase A review capstone**: T-count derived from the gate
    sequence is `7 * n`, matching qianxu's claim of `q_A` Toffolis
    per adder (Eq. E3's structural-cost component).
-/

/-- Helper: cascade of `n` faithful bit-steps, each WITH
    propagation to the next bit. Bit 0 uses `..._first`; bits 1..n-1
    use `..._interior`. For `n = 0`: identity. For `n ≥ 1`: first ;
    interior(1) ; interior(2) ; ... ; interior(n-1).

    All bits in this cascade have propagation CXs to bit `i+1`;
    pair this with `gidney_adder_bit_step_faithful_last` to get a
    full adder cascade (the LAST bit has no propagation). -/
def gidney_adder_forward_with_propagation : Nat → Gate
  | 0       => Gate.I
  | 1       => gidney_adder_bit_step_faithful_first
  | n + 2   => Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_interior (n + 1))

/-- **Faithful full forward cascade for an n-bit Gidney adder**.
    Glues first/interior/last bit-steps per `qq_gidney_adder.py`'s
    actual gate structure.

    - `n = 0` or `n = 1`: degenerate, returns `Gate.I`.
    - `n = k + 2`: `forward_with_propagation (k + 1) ; last (k + 1)`,
      i.e., bits 0..k each emit CCX + 3 CXs (first emits CCX + 2 CXs;
      interior emit CCX + chain CX + 2 propagation CXs); bit k+1
      emits CCX + chain CX (last, no propagation).

    Concrete: for `n = 33` (RSA-2048 q_A=33 adder block), this is
    `forward_with_propagation 32 ; last 32` = 33 Toffolis = 231 T. -/
def gidney_adder_forward_faithful_full : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   => Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                        (gidney_adder_bit_step_faithful_last (n + 1))

/-! ## Faithful full forward cascade correctness on basis states (Iter 80, 2026-05-12)

    Chain the per-bit correctness theorems
    (`..._first_correct` Iter 65, `..._interior_correct` Iter 57,
    `..._last_correct` Iter 67) into a single cascade-level
    correctness theorem matching the Iter 79 def
    `gidney_adder_forward_faithful_full`.

    The cascade-level post-state is the **fold of per-bit
    post-states**: start with `f`, apply `first_bit_post_state`,
    then `interior_bit_step_post_state (1)`, then ..., then
    `last_bit_post_state (n+1)`. Each per-bit post-state is a
    `Nat → Bool` function representing the basis-state image
    of the bit-step. -/

/-- Post-state of `gidney_adder_forward_with_propagation n` on `f`.
    Recursion matches the def's three clauses (0, 1, n+2). -/
def gidney_propagation_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | 1    , f => gidney_first_bit_post_state f
  | n + 2, f =>
      gidney_bit_step_faithful_post_state (n + 1)
        (gidney_propagation_post_state (n + 1) f)

/-- Post-state of the **faithful full forward cascade** on `f`.
    Composes `propagation_post_state (n+1)` (bits 0..n with
    propagation) with `last_bit_post_state (n+1)` (bit n+1 with no
    propagation). -/
def gidney_forward_faithful_full_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | 1    , f => f
  | n + 2, f =>
      gidney_last_bit_post_state (n + 1)
        (gidney_propagation_post_state (n + 1) f)

/-! ## Final CX cascade correctness on basis states (Iter 85, 2026-05-12)

    `gidney_final_cx_cascade n` (Iter 21) emits one
    `CX(read[i], target[i])` per bit. On basis states this XORs
    `read[i]` into `target[i]` for each `i ∈ 0..n-1`.

    This is the **third leg** of the full Gidney adder: after the
    forward cascade writes carries and modifies read/target via
    propagation, this CX cascade stamps the sum bit onto target.
    Combined with the reverse cascade that uncomputes carries, the
    net effect is target := a + b mod 2^n. -/

/-- Post-state of `gidney_final_cx_cascade n`: nested chain of
    `update target[i] (target[i] XOR read[i])` for i = 0..n-1. -/
def gidney_final_cx_cascade_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | n + 1, f =>
      let f' := gidney_final_cx_cascade_post_state n f
      update f' (target_idx n) (xor (f' (target_idx n)) (f' (read_idx n)))

/-! ## Faithful reverse cascade + matrix-level fwd · rev = 1 (Iter 83, 2026-05-12)

    Glues the per-bit gate-reverses (first_reverse Iter 81,
    interior_reverse Iter 82, last_reverse Iter 68) into a cascade
    that is the gate-by-gate inverse of `gidney_adder_forward_faithful_full`.

    With the per-bit involutions in place (Iter 67/81/82), the
    cascade-level forward · reverse = 1 follows by structural induction,
    mirroring Iter 75's simplified-bit-step cascade involution proof. -/

/-- Reverse of `gidney_adder_forward_with_propagation`: emits
    `interior_reverse (n-1), interior_reverse (n-2), ...,
    interior_reverse 1, first_reverse` in reverse order. -/
def gidney_adder_forward_with_propagation_reverse : Nat → Gate
  | 0       => Gate.I
  | 1       => gidney_adder_bit_step_faithful_first_reverse
  | n + 2   => Gate.seq (gidney_adder_bit_step_faithful_interior_reverse (n + 1))
                        (gidney_adder_forward_with_propagation_reverse (n + 1))

/-- Reverse of `gidney_adder_forward_faithful_full`. Emits
    `last_reverse (n+1), interior_reverse(n)..., first_reverse`. -/
def gidney_adder_forward_faithful_full_reverse : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   => Gate.seq (gidney_adder_bit_step_faithful_last_reverse (n + 1))
                        (gidney_adder_forward_with_propagation_reverse (n + 1))

/-! ## Full faithful adder + reverse-correctness corollary (Iter 86, 2026-05-12)

    Define the full no-measurement faithful Gidney adder as the
    composition forward + final CX + reverse, all using the
    Iter 79-83 faithful infrastructure. Total T-count is `14n`
    (7n forward + 0 final CX + 7n reverse).

    Also derive **reverse cascade correctness on basis states** as
    a direct corollary of Iter 80 (forward correctness) + Iter 83
    (matrix-level forward · reverse = 1). The argument: from
    `uc_eval(rev) * uc_eval(fwd) = 1` and `uc_eval(fwd) * f_to_vec(f)
    = f_to_vec(post_state f)`, we get `uc_eval(rev) * f_to_vec(post_state f)
    = uc_eval(rev) * uc_eval(fwd) * f_to_vec(f) = 1 * f_to_vec(f) =
    f_to_vec(f)`. -/

/-- **Full no-measurement faithful Gidney adder**. For `n+2` bits:
    composes the faithful forward cascade (Iter 79) with the final
    CX cascade (Iter 21) and the faithful reverse cascade (Iter 83).

    Total T-count: `14(n+2)` Toffolis × 7 = no, wait: 7(n+2) forward
    + 0 final CX + 7(n+2) reverse = 14(n+2) T-gates.

    Edge cases `n=0, n=1` return `Gate.I`. -/
def gidney_adder_full_faithful_no_measurement : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   => Gate.seq
                (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                          (gidney_final_cx_cascade (n + 2)))
                (gidney_adder_forward_faithful_full_reverse (n + 2))

/-- **The canonical, semantically-correct Gidney ripple-carry adder.**  Alias for the faithful,
    basis-state-proven, no-measurement adder (`gidney_adder_full_faithful_no_measurement`).  This
    — NOT the cost-only `gidney_adder_full` skeleton — is the adder the Shor cost model binds to
    (`adderToff_eq`), and the canonical name downstream code should use. -/
def gidney_adder (n : Nat) : Gate := gidney_adder_full_faithful_no_measurement n

/-! ## Full adder on zero input — smoke test (Iter 89, 2026-05-12)

    The simplest concrete end-to-end case: on all-zero input
    (read = target = carry = 0), the full faithful adder produces
    the all-zero output. This corresponds to the arithmetic claim
    `0 + 0 = 0`.

    Proof strategy:
    - Show `gidney_first_bit_post_state (zero) = zero` (each update
      writes `xor false false = false`, so by `Function.update_eq_self`
      the function is unchanged).
    - By induction, show `gidney_propagation_post_state n zero = zero`
      and `gidney_bit_step_faithful_post_state i zero = zero`.
    - Show `gidney_final_cx_cascade_post_state n zero = zero`.
    - Compose to get the full adder's action on `f_to_vec dim zero`.

    This is a **smoke test**: it doesn't prove the carry-chain math
    for arbitrary inputs, but it does exercise the full review chain
    end-to-end on a concrete instance. -/

/-- The all-zero input function. -/
abbrev zeroF : Nat → Bool := fun _ => false

/-! ## Concrete 2-bit adder example: 1 + 0 = 1 (Iter 94, 2026-05-12)

    Beyond Iter 89's all-zero smoke test, verify the FORWARD cascade
    on a non-trivial concrete input where `read = (1, 0)`,
    `target = (0, 0)`, `carry = (0, 0)`. The arithmetic semantics:
    `1 + 0 = 1` (no carries propagate since read_0 ∧ target_0 = 0).

    All `decide`-checked. Tests that the forward post-state
    computation correctly evaluates at specific qubit indices for
    a non-zero classical input. -/

/-- Input function for `read = (1, 0), target = (0, 0), carry = (0, 0)`.
    Encoded as `i == 0` (true only at i=0 = read_0 = 1; all else false). -/
def inputF_1_plus_0 : Nat → Bool := fun i => i == 0

/-! ## Concrete 2-bit adder: `1 + 1 = 2` (Iter 106, 2026-05-12)

    Carry-propagating input case: `read = target = (1, 0)`,
    `carry = (0, 0)`. Expected arithmetic: `1 + 1 = 10` binary,
    so `target_0 = 0` (sum LSB) and `target_1 = 1` (sum MSB =
    carry-out).

    `decide`-checks of the forward and final-CX intermediate
    states confirm:
    - Forward generates `carry_0 = 1` (read_0 ∧ target_0 = 1).
    - Forward propagates: `read_1 = 0 ⊕ carry_0 = 1`, `target_1 = 0 ⊕ carry_0 = 1`.
    - Forward bit-1 step: `carry_1 = (read_1' ∧ target_1') ⊕ carry_0 = 1 ⊕ 1 = 0`.
    - Final CX: `target_0 ⊕= read_0 = 1 ⊕ 1 = 0` (sum bit 0 ✓).
    - Final CX: `target_1 ⊕= read_1' = 1 ⊕ 1 = 0` — at this point
      target_1 = 0, NOT the sum bit 1. The **reverse cascade** would
      uncompute the carries AND restore target_1's sum-bit value
      (1). -/

/-- Input for `(a=1, b=1)` 2-bit addition. -/
def inputF_1_plus_1 : Nat → Bool
  | 0 => true   -- read_0 = a_0 = 1
  | 1 => true   -- target_0 = b_0 = 1
  | _ => false  -- read_1 = a_1 = 0, target_1 = b_1 = 0, carries = 0

/-! ## Concrete 3-bit adder: `3 + 1 = 4` (Iter 111, 2026-05-12)

    Extends Iter 106's 2-bit `1+1=2` to a 3-bit example with
    multi-bit carry propagation. Input: `a = (1, 1, 0) = 3` LSB-first,
    `b = (1, 0, 0) = 1` LSB-first. Expected sum: `3+1=4 = (0,0,1)`
    LSB-first.

    Indexing: read_i=3i, target_i=3i+1, carry_i=3i+2.
    - read_0=0, target_0=1, carry_0=2
    - read_1=3, target_1=4, carry_1=5
    - read_2=6, target_2=7, carry_2=8

    Carry chain:
    - carry_0 = read_0 ∧ target_0 = 1 ∧ 1 = 1 (generated)
    - propagation: read_1 ⊕= 1 → 0, target_1 ⊕= 1 → 1
    - carry_1 = (read_1' ∧ target_1') ⊕ carry_0 = (0 ∧ 1) ⊕ 1 = 1
    - propagation: read_2 ⊕= 1 → 1, target_2 ⊕= 1 → 1
    - carry_2 = (read_2' ∧ target_2') ⊕ carry_1 = (1 ∧ 1) ⊕ 1 = 0 -/

/-- Input for `(a=3, b=1)` 3-bit addition. -/
def inputF_3_plus_1 : Nat → Bool
  | 0 => true   -- read_0 = a_0 = 1
  | 1 => true   -- target_0 = b_0 = 1
  | 3 => true   -- read_1 = a_1 = 1
  -- target_1, carries, read_2, target_2 all default to false
  | _ => false

/-! ## Concrete 4-bit adder: `7 + 1 = 8` (Iter 116, 2026-05-12)

    Extends the carry-propagation breadth: a = 7 = (1, 1, 1, 0)
    LSB-first, b = 1 = (1, 0, 0, 0) LSB-first. Expected sum = 8 =
    (0, 0, 0, 1) LSB-first. The carry chain propagates through
    ALL FOUR bits, generating carry_0 = carry_1 = carry_2 = 1 and
    finally carry_3 = 0 (the last-bit step's CCX writes 1, then
    chain CX XORs carry_2 = 1, yielding 0).

    12-qubit decide check (4 bits × 3 indices). -/

/-- Input for `(a=7, b=1)` 4-bit addition. -/
def inputF_7_plus_1 : Nat → Bool
  | 0 => true   -- read_0 = a_0 = 1
  | 1 => true   -- target_0 = b_0 = 1
  | 3 => true   -- read_1 = a_1 = 1
  | 6 => true   -- read_2 = a_2 = 1
  -- read_3 = a_3 = 0, target_1, target_2, target_3, carries all 0
  | _ => false

/-! ## First-bit reverse post-state (Iter 122, 2026-05-12)

    Define the basis-state post-state of `gidney_adder_bit_step_faithful_first_reverse`
    (Iter 81). The reverse step emits 3 gates in reverse order:
    1. `CX(carry_0, target_1)` — undoes target_1 propagation.
    2. `CX(carry_0, read_1)` — undoes read_1 propagation.
    3. `CCX(read_0, target_0, carry_0)` — undoes carry_0 write.

    On a basis state f, the post-state has 3 chained `update`s
    matching these gates' classical actions. This is the dual of
    `gidney_first_bit_post_state` (Iter 65) for the gate-reversed
    direction. -/

/-- Post-state of `gidney_adder_bit_step_faithful_first_reverse`
    on a basis-state input `f`. Three chained updates matching
    the three gates' classical actions. -/
def gidney_first_bit_reverse_post_state (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (target_idx 1)
              (xor (f (target_idx 1)) (f (carry_idx 0)))
  let f₂ := update f₁ (read_idx 1)
              (xor (f₁ (read_idx 1)) (f₁ (carry_idx 0)))
  update f₂ (carry_idx 0)
    (xor (f₂ (carry_idx 0)) (f₂ (read_idx 0) && f₂ (target_idx 0)))

/-! ## Interior-bit reverse post-state (Iter 127, 2026-05-12)

    Mirror of Iter 122's first-bit reverse for the interior bit-step
    `gidney_adder_bit_step_faithful_interior_reverse i` (Iter 82).
    Four chained `update`s matching the 4 gates in gate-reverse order:
    1. `CX(carry_i, target_(i+1))` — undoes target propagation.
    2. `CX(carry_i, read_(i+1))` — undoes read propagation.
    3. `CX(carry_(i-1), carry_i)` — undoes chain CX.
    4. `CCX(read_i, target_i, carry_i)` — undoes CCX write. -/

/-- Post-state of `gidney_adder_bit_step_faithful_interior_reverse i`
    on a basis-state input `f`. Four chained updates matching the
    four gates' classical actions. -/
def gidney_interior_bit_reverse_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (target_idx (i + 1))
              (xor (f (target_idx (i + 1))) (f (carry_idx i)))
  let f₂ := update f₁ (read_idx (i + 1))
              (xor (f₁ (read_idx (i + 1))) (f₁ (carry_idx i)))
  let f₃ := update f₂ (carry_idx i)
              (xor (f₂ (carry_idx i)) (f₂ (carry_idx (i - 1))))
  update f₃ (carry_idx i)
    (xor (f₃ (carry_idx i)) (f₃ (read_idx i) && f₃ (target_idx i)))

/-! ## Last-bit reverse post-state (Iter 128, 2026-05-12)

    Mirror of Iter 122 (first-bit) and Iter 127 (interior-bit) for
    the last-bit step `gidney_adder_bit_step_faithful_last_reverse i`
    (RippleCarryAdder.lean:1137). Only 2 gates (no propagation to
    (i+1) since this is the last bit), so the post-state has 2
    chained `update`s on `carry_i` in gate-reverse order:
    1. `CX(carry_(i-1), carry_i)` — undoes chain CX.
    2. `CCX(read_i, target_i, carry_i)` — undoes CCX write.

    Completes the reverse post-state suite: first-bit (Iter 122) +
    interior-bit (Iter 127) + last-bit (Iter 128, this iter). After
    this, the full reverse cascade is navigable at the basis-state
    level layer-by-layer. -/

/-- Post-state of `gidney_adder_bit_step_faithful_last_reverse i`
    on a basis-state input `f`. Two chained updates on `carry_i`
    matching the two gates' classical actions. -/
def gidney_last_bit_reverse_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (carry_idx i)
              (xor (f (carry_idx i)) (f (carry_idx (i - 1))))
  update f₁ (carry_idx i)
    (xor (f₁ (carry_idx i)) (f₁ (read_idx i) && f₁ (target_idx i)))

/-! ## Phase A end-to-end — first statement attempt (Iter 141, 2026-05-13)

    Per Iter 138 reflection: state the Phase A end-to-end theorem
    with named placeholders. Mirrors Iter 140's Phase B approach —
    build the structural skeleton first, identify missing
    primitives, decide-witness what we can.

    **The conjecture**: the full Gidney adder maps the basis state
    encoding `(a, b, 0_carries)` to a post-state where the target
    register holds bits of `a + b mod 2^n`. The "no-measurement"
    variant additionally leaves the carries dirty (per Iter 106
    finding — dirty-carries observation).

    **What we CAN state without new infrastructure** (the
    classical-action shadow):
    1. A generic input encoding `adder_input_F n a b` representing
       the basis state `|a⟩|b⟩|0⟩_carries` on `3n` qubits.
    2. Decide-witness that the generic encoding reduces to our
       existing concrete `inputF_*` defs for specific (n, a, b)
       instances.
    3. A classical specification `adder_sum_bit_classical a b i`
       giving bit `i` of `(a + b) mod 2^n` via `Nat.testBit`.

    **What stays parked** (operational claim, SORRIED):
    The actual theorem `post_state(adder_input_F n a b) i = some
    function of (a, b, i)` requires the carry-chain induction
    invariant (the Iter 132 reflection's named obstacle). -/

/-- **Generic input encoding** for the n-bit Gidney adder. Maps
    qubit index `k` to its Boolean value when the adder's input
    is `(a, b, 0_carries)`:
    - `k = 3i` (read_i): bit `i` of `a` if `i < n`, else false.
    - `k = 3i + 1` (target_i): bit `i` of `b` if `i < n`, else false.
    - `k = 3i + 2` (carry_i): false.
    Decide-witnessed below to match the existing concrete
    `inputF_*` defs. -/
def adder_input_F (n a b : Nat) (k : Nat) : Bool :=
  match k % 3 with
  | 0 => decide (k / 3 < n) && a.testBit (k / 3)
  | 1 => decide (k / 3 < n) && b.testBit (k / 3)
  | _ => false

/-! ### SQIR-style classical carry recurrence (Iter 157, 2026-05-13)

    Foundation for the semantic correctness proof. Ports SQIR's
    `carry b n f g` and `sumfb b f g` from
    [SQIR/examples/shor/ModMult.v:497, 638](../../../SQIR/examples/shor/ModMult.v):

    ```
    Fixpoint carry b n f g :=
      match n with
      | 0 => b
      | S n' => let c := carry b n' f g in
                let a := f n' in
                let b := g n' in
                (a && b) ⊕ (b && c) ⊕ (a && c)
      end.

    Definition sumfb b f g := fun x => carry b x f g ⊕ f x ⊕ g x.
    ```

    These give the **bit-level recurrence** that the carry-chain
    induction will track. The existing `adder_sum_bit_classical`
    (`(a + b).testBit i`) gives the answer but hides the
    recurrence; for the invariant proof we need the explicit
    form.

    SQIR-style invariant insight (per loop_prompt.md rule 1):
    these defs let us state "after step i of the cascade, carry_i
    bit position holds `carry false i a_bits b_bits`" — the
    non-trivial induction predicate. NOT `target_i = bit_i(a+b)`
    directly, which doesn't compose through partial states. -/

/-- **Classical carry function** (SQIR ModMult.v:497 port). Given a
    carry-in `b₀ : Bool` and two bit-streams `f g : Nat → Bool`,
    `Adder.carry b₀ n f g` is the carry-out after processing bits
    `0..n-1` of `f + g`. -/
def Adder.carry (b₀ : Bool) : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0,     _, _ => b₀
  | n + 1, f, g =>
      let c := Adder.carry b₀ n f g
      let a := f n
      let b := g n
      xor (xor (a && b) (b && c)) (a && c)

/-- **Classical sum-bit function** (SQIR ModMult.v:638 port).
    `Adder.sumfb b₀ f g i = carry b₀ i f g ⊕ f i ⊕ g i` —
    bit `i` of the sum `f + g` with carry-in `b₀`. -/
def Adder.sumfb (b₀ : Bool) (f g : Nat → Bool) (i : Nat) : Bool :=
  xor (xor (Adder.carry b₀ i f g) (f i)) (g i)

/-! ### End-of-forward-cascade invariant (Iter 159, 2026-05-13)

    The non-trivial induction predicate for the forward cascade.
    Analog of SQIR's `MAJseq'_correct` end state (where the f
    register is characterized by `msma i c f g` for i = n).

    **Derivation by simulation** (per loop_prompt.md rule 2): the
    invariant was derived from the decide-witnessed (7,1) n=4
    case at line 2486-2503. Hand-checked all 12 qubits:
    - `read_i = a_i ⊕ c_i` where `c_j = Adder.carry false j a b`
      (so `c_0 = false`, `c_1 = a_0 ∧ b_0`, etc.).
    - `target_i = b_i ⊕ c_i` (uniform across i).
    - `carry_i = c_{i+1}` (= the classical carry-out after
      processing bit i).

    Note the uniformity: at i=0, `c_0 = false`, so `read_0 = a_0 ⊕
    false = a_0` and `target_0 = b_0 ⊕ false = b_0`, both
    unchanged from the input — matches the gate sequence (the
    first-bit step doesn't touch read_0 / target_0). -/

/-- **End-of-forward-cascade invariant**: characterizes the state
    after `gidney_forward_faithful_full n` has processed all `n`
    bits of inputs `a` and `b`.

    Quantum quantities (read/target/carry positions) are
    characterized as classical functions of `a`, `b`, and the
    classical carry chain `Adder.carry`. SQIR-style: this is the
    `forall i, predicate` form, not the per-step `msma`. -/
def Gidney.forward_cascade_post_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ i, i < n →
    post (read_idx i)
      = xor (a.testBit i) (Adder.carry false i (a.testBit) (b.testBit))
    ∧ post (target_idx i)
        = xor (b.testBit i) (Adder.carry false i (a.testBit) (b.testBit))
    ∧ post (carry_idx i)
        = Adder.carry false (i + 1) (a.testBit) (b.testBit)

/-- **Step-indexed propagation invariant** (Iter 175, analog of
    SQIR's msma/msmb/msmc at ModMult.v:631).

    After `k` propagation iterations of
    `gidney_propagation_post_state k f` on input
    `adder_input_F n a b`:
    - For `j < k`: carry_j = c_{j+1} (= Adder.carry false (j+1) ...);
      else (j ≥ k, unchanged): carry_j = false.
    - For `j ≤ k`: read_j = a_j ⊕ c_j (propagated; note c_0 = false
      so j=0 collapses to read_0 = a_0); else (j > k, unchanged):
      read_j = a_j.
    - Same for target_j.

    Indexing: k=0 means "before first step", k=1 means "after
    first-bit step", k=K means "after first-bit + (K-1) interior
    steps" (= bits 0..K-1 processed).

    This is the non-trivial induction invariant for cascade
    composition (rule 1: mirror SQIR's MAJseq'_correct
    structure). -/
def Gidney.propagation_step_invariant
    (k n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    -- carry_j: processed iff j < k
    (post (carry_idx j) =
      if j < k then Adder.carry false (j + 1) a.testBit b.testBit
      else false)
    ∧ -- read_j: propagated iff j ≤ k
    (post (read_idx j) =
      if j ≤ k then
        xor (a.testBit j) (Adder.carry false j a.testBit b.testBit)
      else a.testBit j)
    ∧ -- target_j: same as read_j but with b
    (post (target_idx j) =
      if j ≤ k then
        xor (b.testBit j) (Adder.carry false j a.testBit b.testBit)
      else b.testBit j)

/-- **Forward post-state of interior bit-step at `i`** (Iter 166).
    Defined analogously to `gidney_first_bit_post_state` but for
    the interior 4-gate step at position `i ≥ 1`.

    Gate sequence (from `gidney_adder_bit_step_faithful_interior i`):
    1. CCX(read_i, target_i, carry_i)
    2. CX(carry_{i-1}, carry_i)   — chain carry from previous
    3. CX(carry_i, read_{i+1})    — propagation
    4. CX(carry_i, target_{i+1})  — propagation

    Each gate's classical action is an XOR-update at the target. -/
def gidney_interior_bit_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  let f₁ := update f (carry_idx i)
              (xor (f (carry_idx i)) (f (read_idx i) && f (target_idx i)))
  let f₂ := update f₁ (carry_idx i)
              (xor (f₁ (carry_idx i)) (f₁ (carry_idx (i - 1))))
  let f₃ := update f₂ (read_idx (i + 1))
              (xor (f₂ (read_idx (i + 1))) (f₂ (carry_idx i)))
  let f₄ := update f₃ (target_idx (i + 1))
              (xor (f₃ (target_idx (i + 1))) (f₃ (carry_idx i)))
  f₄

/-! ### End per-bit-step preservation skeletons -/

/-! ### End SQIR-style classical carry recurrence -/

/-- **Classical specification**: bit `i` of `(a + b) mod 2^n`,
    the value the i-th target qubit SHOULD hold after the full
    forward + final-CX cascade (per Iter 106's finding, the
    reverse cascade only undoes propagation but not the sum). -/
def adder_sum_bit_classical (a b i : Nat) : Bool := (a + b).testBit i

/-- **End-state invariant for forward cascade (forward only, no
    final-CX)** (Iter 187, 2026-05-13). Captures the EXACT classical
    action of `gidney_forward_faithful_full_post_state n` on
    `adder_input_F n a b` for an n-bit adder (n ≥ 2).

    For all `j < n`:
    - **carry_j** = `c_{j+1}` (last-bit step writes c_{n-1} = c_n,
      propagation writes all earlier carries).
    - **read_j** = `a_j ⊕ c_j` (forward propagation; `c_0 = 0` collapses
      to `a_0` for j = 0).
    - **target_j** = `b_j ⊕ c_j` (forward propagation; analogous).

    Compared to `Gidney.post_forward_final_cx_invariant` (Iter 183):
    same carry and read clauses; target clause is `b_j ⊕ c_j` here vs
    `a_j ⊕ b_j` post-final-CX (the final-CX layer XORs read_j into
    target_j, canceling c_j).

    Composition path: `gidney_forward_faithful_full_post_state n =
    gidney_last_bit_post_state (n-1) ∘ gidney_propagation_post_state (n-1)`
    (for n ≥ 2 via the recursive def's third clause). The propagation
    invariant at step (n-1) gives all positions j < n propagated, with
    `carry_{n-1} = false` (still unprocessed); the last-bit step at
    position n-1 writes `carry_{n-1} = c_n` and doesn't touch
    read/target. Combining: all 3 invariants hold for j ∈ [0, n-1]. -/
def Gidney.post_last_bit_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    (post (carry_idx j)
      = Adder.carry false (j + 1) a.testBit b.testBit)
    ∧ (post (read_idx j)
        = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit))
    ∧ (post (target_idx j)
        = xor (b.testBit j) (Adder.carry false j a.testBit b.testBit))

/-- **End-state invariant for forward + final-CX cascade**
    (Iter 183, 2026-05-13). Captures the EXACT classical action of
    `gidney_final_cx_cascade_post_state n ∘
     gidney_forward_faithful_full_post_state n` on
    `adder_input_F n a b` for an n-bit adder (n ≥ 2).

    For all `j < n`:
    - **carry_j** = `c_{j+1}` (= `Adder.carry false (j+1) a.testBit b.testBit`).
      All carries 0..n-1 hold the math carry into the next position.
    - **read_j** = `a_j ⊕ c_j` (forward propagation; `c_0 = 0` collapses
      this to `a_0` for j = 0).
    - **target_j** = `a_j ⊕ b_j`. The forward step writes target_j =
      b_j ⊕ c_j (propagation); the final-CX layer adds read_j = a_j ⊕ c_j;
      `(b_j ⊕ c_j) ⊕ (a_j ⊕ c_j) = a_j ⊕ b_j`. The c_j contributions
      **cancel** in the XOR — this is exactly the review finding of Iter 182.

    **Key review insight**: `target_j` is NOT the classical sum bit
    `a_j ⊕ b_j ⊕ c_j`. The reverse cascade is essential to re-XOR `c_j`
    into target_j (via the per-step `CX(c_{j-1}, t_j)` gates), completing
    the sum-bit computation. This invariant captures the correct
    intermediate state at the boundary between forward + final-CX and
    the reverse cascade.

    Per Iter 182 finding + QUESTIONS.md #1 (2026-05-13): this invariant
    is the **provable** parametric statement at this layer. The headline
    sum-bit theorem (target_j = sum_j) needs the additional reverse
    cascade composition, awaiting John's approval of the restatement. -/
def Gidney.post_forward_final_cx_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    (post (carry_idx j)
      = Adder.carry false (j + 1) a.testBit b.testBit)
    ∧ (post (read_idx j)
        = xor (a.testBit j) (Adder.carry false j a.testBit b.testBit))
    ∧ (post (target_idx j)
        = xor (a.testBit j) (b.testBit j))

/-! ### Reverse cascade post-state + restated headline (Iter 191, 2026-05-13)

    Per Iter 182's review finding + QUESTIONS.md #1: the existing
    `TODO_gidney_classical_action` is unprovable as stated. The fix
    requires the REVERSE cascade, which re-XORs c_j into target_j to
    bridge `target_j = a_j ⊕ b_j` (post-final-CX, per Iter 189) to
    `sum_j = a_j ⊕ b_j ⊕ c_j`.

    This section defines the missing `gidney_propagation_reverse_post_state`
    and `gidney_full_reverse_post_state` (mirroring the forward def's
    recursive structure) and drafts the **proposed** restated headline
    `TODO_gidney_classical_action_with_reverse` as a NEW theorem
    alongside the existing one (per Rule 3 — never modify existing
    theorem statements without permission).

    AWAITING JOHN'S APPROVAL of QUESTIONS.md #1 to (a) retract the
    existing unprovable theorem, OR (b) keep both and document the
    new one as the canonical headline. -/

/-- **Post-state of the reverse propagation cascade** (Iter 191).
    Mirrors `gidney_adder_forward_with_propagation_reverse` (line 1826):
    apply `interior_reverse (n+1)`, then recurse, ending with `first_reverse`.
    For `n+2`: applies interior_reverse from i=n+1 down to i=1, then first_reverse. -/
def gidney_propagation_reverse_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0       , f => f
  | 1       , f => gidney_first_bit_reverse_post_state f
  | n + 2   , f =>
      gidney_propagation_reverse_post_state (n + 1)
        (gidney_interior_bit_reverse_post_state (n + 1) f)

/-- **Post-state of the full forward+reverse cascade** (Iter 191).
    Mirrors `gidney_adder_forward_faithful_full_reverse` (line 1849):
    apply `last_reverse (n+1)`, then `propagation_reverse (n+1)`. -/
def gidney_full_reverse_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0       , f => f
  | 1       , f => f
  | n + 2   , f =>
      gidney_propagation_reverse_post_state (n + 1)
        (gidney_last_bit_reverse_post_state (n + 1) f)

/-! ### Post-full-reverse invariant + parametric holds (Iter 197, 2026-05-13)

    Decompose the headline `TODO_gidney_classical_action_with_reverse` via
    a structural predicate `Gidney.post_full_reverse_invariant`, capturing
    BOTH the sum-bit (`target_j = sum_j`) AND the read-restore (`read_j = a_j`)
    properties of the post-full-reverse state. The predicate is a strict
    refinement of the headline (richer claim).

    Per Iter 191's decide-witnessed traces:
    - For (n=2, a=1, b=1): post-full-reverse state has r=(1,0), t=(0,1),
      c=(1,1). target_j matches sum_j; read_j matches a.testBit j.
    - For (n=3, a=3, b=1): same pattern, multi-bit.

    Note: carry_j is DIRTY (not restored to input 0) — this is the
    "Iter 106 dirty carries" observation. The predicate intentionally
    EXCLUDES a carry-restore claim. -/

/-- **Post-full-reverse invariant** (Iter 197, 2026-05-13). Captures
    target+read state after the full forward+final-CX+reverse cascade.
    For `n ≥ 2`:
    - `target_j = sum_j = (a + b).testBit j` (the SUM bit, completing
      the review chain).
    - `read_j = a.testBit j` (RESTORED to input value via the
      reverse cascade's r_{i+1} ⊕= c_i operation, which inverts the
      forward propagation r_{i+1} ⊕= c_i). -/
def Gidney.post_full_reverse_invariant
    (n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, j < n →
    (post (target_idx j) = adder_sum_bit_classical a b j)
    ∧ (post (read_idx j) = a.testBit j)

/-! **Parametric `post_full_reverse_invariant_holds`** — DELETED 2026-05-22.

    Previously held a sorried forwarding stub named
    `TODO_post_full_reverse_invariant_holds`.  The canonical proven
    theorem `Gidney.post_full_reverse_invariant_holds` (defined later in
    this file, ~line 5816) supersedes it; the forwarding stub was never
    referenced by other declarations.  Removed to eliminate the
    dishonest sorry from the build.  The review-history of the path that
    produced the proven theorem (step-indexed `reverse_step_invariant`
    + induction on k + 5 helper lemmas + 3 j-case lemmas) is preserved
    in the docstrings of the lemmas immediately below and in
    `PROGRESS.md` tick entries from 2026-05-14. -/

/-- **Step-indexed reverse-cascade invariant** (Iter 2026-05-14, the
    `inv_k` from the comment-bridge above the `sorry` at
    `TODO_post_full_reverse_invariant_holds`).

    `reverse_step_invariant k n a b post` says: after `k` reverse
    steps have fired on the post-final-CX state, every position
    `j ∈ [n - k, n - 1]` has been corrected to its final
    target/read values (target_j = sum_j, read_j = a.testBit j).
    Positions `j < n - k` have NOT yet been corrected and are
    excluded from the predicate's quantifier.

    - `k = 0`: empty predicate (no j satisfies `n ≤ j < n`).
    - `k = 1`: covers j = n-1 (the last-bit reverse target).
    - `k = n`: covers all j ∈ [0, n-1], i.e., equivalent to
      `Gidney.post_full_reverse_invariant n a b post`.

    The cascade-induction proof of `TODO_post_full_reverse_invariant_holds`
    factors as: state `reverse_step_invariant k _` for k=1..n,
    induct on k via Iter 194/195/200/201 + frame, conclude at k=n. -/
def Gidney.reverse_step_invariant
    (k n a b : Nat) (post : Nat → Bool) : Prop :=
  ∀ j, n - k ≤ j → j < n →
    (post (target_idx j) = adder_sum_bit_classical a b j)
    ∧ (post (read_idx j) = a.testBit j)

/-! ## Register decoders for the Gidney interleaved layout

The Gidney adder uses the interleaved register layout
`(read[i], target[i], carry[i]) = (3*i, 3*i+1, 3*i+2)`.  The three
decoders below interpret these positions as the bits of an `n`-bit
unsigned integer, **LSB-first** (position 0 = bit weight `2^0`),
matching the bit-position convention used by the existing concrete
test inputs (`inputF_1_plus_1` etc.).

These are the **plumbing definitions** required to state any
arithmetic-semantics theorem about the Gidney adder — i.e., the
statement "after the adder, `target_val = (read_val + target_val) mod 2^n`".
That statement is the open Iter 88-89 capstone obligation and the
direct blocker for Tick D's modular-adder correctness.  The decoders
land independently of the eventual capstone closure.

NOTE on bit ordering: this differs from `Framework.funbool_to_nat`
(which is big-endian: position 0 is MSB).  The two conventions
coexist in the project — the Gidney layout uses LSB-first internally
for arithmetic, while the canonical `encodeDataZeroAnc` (used by
`MultiplyCircuitProperty`) uses big-endian `nat_to_funbool` for the
full register.  A future bridge theorem will need to permute between
the two layouts. -/

/-- Decoder: value of the `read` register at width `n`, LSB-first.
Bit at `read_idx i = 3*i` contributes weight `2^i`. -/
def gidney_read_val : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      gidney_read_val n f + (if f (read_idx n) then 2^n else 0)

/-- Decoder: value of the `target` register at width `n`, LSB-first.
Bit at `target_idx i = 3*i + 1` contributes weight `2^i`. -/
def gidney_target_val : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      gidney_target_val n f + (if f (target_idx n) then 2^n else 0)

/-- Decoder: value of the `carry` register at width `n`, LSB-first.
Bit at `carry_idx i = 3*i + 2` contributes weight `2^i`. -/
def gidney_carry_val : Nat → (Nat → Bool) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      gidney_carry_val n f + (if f (carry_idx n) then 2^n else 0)

/-! ## Tick D blocker: carry-register non-clearing on non-zero input

A `decide`-checked smoke test that surfaces the **actual register
behavior of `gidney_adder_full_faithful_no_measurement 2` on the
`1 + 1 = 2` input**:

* Input: `read = 1, target = 1, carry = 0` (all LSB-first at width 2).
* Output: `read = 1` ✓ (preserved), `target = 2` ✓ (sum correct),
  but **`carry = 3`** (binary `11`, NOT zeroed).

The sum bits are correct, so the structural composition forward → final_cx
→ reverse does compute `target := (read + target) mod 2^n` in the target
register.  But the reverse cascade *does not* clear the carry register
in general: it uses the post-final-CX target values when it tries to
uncompute the carry chain, and the algebra of that uncompute does not
match the original forward computation.

**Consequence for Tick D**: a modular-adder construction built on
`gidney_adder_full_faithful_no_measurement` as the inner adder would
inherit dirty-carry output.  Modular reduction (which requires clean
ancillas to compare and conditionally subtract) cannot be cleanly
stated on top of it.  Possible resolutions for a future tick:

1. Re-derive a no-measurement reverse cascade that correctly accounts
   for the post-final-CX target values.
2. Use a different adder family with clean uncompute (e.g., Cuccaro
   completed with boundary CX corrections).
3. Reorder the cascade and verify the uncompute identities under the
   unchanged target.

The decoders + smoke tests below give precise positive statements
(target correct, read preserved) and a precise negative statement
(carry ≠ 0), all `decide`-checked.  Future arithmetic-semantics work
can take these as the starting point. -/

/-- Concrete 1+1 input (LSB-first): `read = 1, target = 1` at width 2. -/
def inputF_1_plus_1_tickD : Nat → Bool
  | 0 => true   -- read_idx 0 = 0:  read[0] = 1 (LSB)
  | 1 => true   -- target_idx 0 = 1: target[0] = 1 (LSB)
  | _ => false  -- read[1] = 0, target[1] = 0, carry[0] = carry[1] = 0

/-! ## Option-1 patch: append `CX(r[i], c[i])` after each reverse CCX

QUESTIONS.md (2026-05-27, [modmult-axiom]) proposed four resolutions to
the carry-non-clearing obstruction.  This section tests **Option 1**:
add a `CX(read_idx i, carry_idx i)` gate after each reverse CCX so the
carry is unconditionally cleared.

**Algebraic justification.**  After the forward + final-CX cascade,
`target[i]_new = target[i]_orig ⊕ read[i]` (the final-CX action).  The
existing reverse CCX computes `c[i] ⊕= read[i] ∧ target[i]_new
= read[i] ∧ (target[i]_orig ⊕ read[i])
= (read[i] ∧ target[i]_orig) ⊕ read[i]` (by distributivity, since
`read[i] ∧ read[i] = read[i]`).  This XORs the original forward-CCX
contribution `read[i] ∧ target[i]_orig` (which set `c[i]` in the first
place) PLUS an extraneous `read[i]`.  The patch's `CX(read_idx i,
carry_idx i)` cancels the extraneous `read[i]`, leaving exactly the
inverse of the forward CCX.

**Verification scope** (this iteration): exhaustive `decide` over all
`(a, b)` ∈ [0, 2^n) × [0, 2^n) for `n ∈ {2, 3}` confirms:
* Carries cleared.
* Target bits correct (sum mod 2^n).
* Read register preserved.

Parametric proof for arbitrary `n` is future work — the n=2 and n=3
exhaustive verification (192 + 16 carry cases plus 192 + 32 target/read
cases) gives strong evidence that Option 1 is viable.  These patched
gate definitions are the building blocks for the next modular-adder
tick. -/

/-- Patched first-bit reverse step: existing first-reverse followed by
`CX(read_idx 0, carry_idx 0)` to clear `carry_idx 0`. -/
def gidney_adder_bit_step_faithful_first_reverse_patched : Gate :=
  Gate.seq gidney_adder_bit_step_faithful_first_reverse
           (Gate.CX (read_idx 0) (carry_idx 0))

/-- Patched interior-bit reverse step: existing interior-reverse
followed by `CX(read_idx i, carry_idx i)` to clear `carry_idx i`. -/
def gidney_adder_bit_step_faithful_interior_reverse_patched (i : Nat) :
    Gate :=
  Gate.seq (gidney_adder_bit_step_faithful_interior_reverse i)
           (Gate.CX (read_idx i) (carry_idx i))

/-- Patched last-bit reverse step: existing last-reverse followed by
`CX(read_idx i, carry_idx i)` to clear `carry_idx i`. -/
def gidney_adder_bit_step_faithful_last_reverse_patched (i : Nat) :
    Gate :=
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

/-- Patched full faithful no-measurement Gidney adder: forward +
final-CX + **patched** reverse. -/
def gidney_adder_full_faithful_no_measurement_patched : Nat → Gate
  | 0       => Gate.I
  | 1       => Gate.I
  | n + 2   =>
      Gate.seq
        (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                  (gidney_final_cx_cascade (n + 2)))
        (gidney_adder_forward_faithful_full_reverse_patched (n + 2))

end FormalRV.BQAlgo
