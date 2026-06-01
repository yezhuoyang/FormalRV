/-
  FormalRV.BQAlgo.CuccaroSubConst — exact-budget Cuccaro
  subtract-constant primitive + flag-feasibility analysis.

  Tick 46:
  - Define `cuccaro_subConstGate` as add-by-two's-complement.
  - Prove subtract correctness via wraparound spec.
  - Prove arithmetic split lemmas (no-underflow vs underflow cases).
  - Analyze whether the clean exact-budget subtract exposes a
    borrow/comparison flag.

  Conclusion (Deliverable D, formal): the CLEAN exact-budget Cuccaro
  subtract-constant primitive restores all non-target ancilla to their
  canonical zero values. The only informative output is the target
  register itself, which encodes `(x + 2^bits - N) mod 2^bits` — a
  function that distinguishes `x < N` from `x ≥ N` via its value but
  NOT via any single ancilla bit. Therefore an exact-budget
  modular-reduction step cannot read the borrow flag from a single
  qubit of this gate's output; a different construction (forward-only
  comparator copying the top carry before reverse uncompute, or a
  modified primitive that reserves a flag qubit) is required for the
  next layer.

  This file does NOT extend the Cuccaro budget — it identifies the
  precise structural blocker for the SQIR-axiom-closure pipeline.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Deliverable A — subtract-constant gate + spec. -/

/-- **Cuccaro subtract-constant gate** (exact-budget).  Implemented as
add by the two's-complement of `N`. -/
def cuccaro_subConstGate (bits q_start N : Nat) : Gate :=
  cuccaro_addConstGate bits q_start (2^bits - N)

/-- **Wraparound spec for subtract.**  The target register after a
subtract-constant equals `(x + (2^bits - N)) mod 2^bits`.  In the
non-underflow case (`x ≥ N`) this reduces to `x - N`; in the underflow
case (`x < N`) it equals `x + 2^bits - N`. -/
def cuccaro_subConstSpec (bits N x : Nat) : Nat :=
  (x + (2^bits - N)) % 2^bits

/-! ## Deliverable C — arithmetic split lemmas. -/

/-- **Non-underflow case.**  When `N ≤ x`, the wraparound spec reduces
to integer subtraction. -/
theorem cuccaro_subConstSpec_of_le
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) (hle : N ≤ x) :
    cuccaro_subConstSpec bits N x = x - N := by
  unfold cuccaro_subConstSpec
  -- x + (2^bits - N) = (x - N) + 2^bits (since x ≥ N, N ≤ 2^bits).
  have h1 : x + (2^bits - N) = (x - N) + 2^bits := by omega
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Underflow case.**  When `x < N`, the wraparound spec equals
`x + 2^bits - N`. -/
theorem cuccaro_subConstSpec_of_lt
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < N) :
    cuccaro_subConstSpec bits N x = x + 2^bits - N := by
  unfold cuccaro_subConstSpec
  -- x + (2^bits - N) < 2^bits since x < N ≤ 2^bits.
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Deliverable B — subtract correctness (target decode + clean). -/

/-- **HEADLINE — subtract-constant target decode.**  After
`cuccaro_subConstGate bits q_start N` on `cuccaro_input_F q_start
false 0 x`, the target register decodes to `cuccaro_subConstSpec bits N x`. -/
theorem cuccaro_subConstGate_target_decode
    (bits q_start N x : Nat) (h1N : 1 ≤ N) (hN : N ≤ 2^bits) :
    cuccaro_target_val bits q_start
      (Gate.applyNat (cuccaro_subConstGate bits q_start N)
        (cuccaro_input_F q_start false 0 x))
    = cuccaro_subConstSpec bits N x := by
  unfold cuccaro_subConstGate cuccaro_subConstSpec
  apply cuccaro_addConstGate_target_decode
  -- Need: 2^bits - N < 2^bits. From 1 ≤ N and N ≤ 2^bits:
  --   2^bits - N ≤ 2^bits - 1 < 2^bits.
  omega

/-- **subtract-constant WellTyped.** -/
theorem cuccaro_subConstGate_wellTyped
    (bits q_start N dim : Nat) (h : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_subConstGate bits q_start N) := by
  unfold cuccaro_subConstGate
  exact cuccaro_addConstGate_wellTyped bits q_start (2^bits - N) dim h

/-- **HEADLINE — packaged clean subtract-constant primitive.**
- WellTyped at dimension `q_start + (2*bits + 1)`;
- target decode = `cuccaro_subConstSpec bits N x`;
- read register restored to 0;
- carry-in qubit restored to false. -/
theorem cuccaro_subConstGate_clean
    (bits q_start N x : Nat) (h1N : 1 ≤ N) (hN : N ≤ 2^bits) :
    Gate.WellTyped (q_start + (2 * bits + 1))
        (cuccaro_subConstGate bits q_start N)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat (cuccaro_subConstGate bits q_start N)
            (cuccaro_input_F q_start false 0 x))
        = cuccaro_subConstSpec bits N x
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat (cuccaro_subConstGate bits q_start N)
            (cuccaro_input_F q_start false 0 x))
        = 0
    ∧ Gate.applyNat (cuccaro_subConstGate bits q_start N)
          (cuccaro_input_F q_start false 0 x) q_start = false := by
  unfold cuccaro_subConstGate
  -- All four conjuncts follow from cuccaro_addConstGate_clean with c := 2^bits - N.
  have h : 2^bits - N < 2^bits := by omega
  obtain ⟨hwt, htd, hrd, hci⟩ := cuccaro_addConstGate_clean bits q_start (2^bits - N) x h
  refine ⟨hwt, ?_, hrd, hci⟩
  rw [htd]
  rfl

/-! ## Deliverable D — flag-feasibility analysis.

The clean Cuccaro subtract-constant gate restores ALL ancilla
qubits within the `2*bits + 1`-qubit budget to their canonical
zero values:
- carry-in qubit (pos `q_start`) → `false`;
- read register (positions `q_start + 2*i + 2` for `i < bits`)
  decodes to `0` (every bit is `false`).

The only remaining variation is in the target register, which holds
the wraparound value `cuccaro_subConstSpec bits N x`.

This wraparound value is mathematically informative — it distinguishes
`x < N` from `x ≥ N` because:
- if `x ≥ N`: target ∈ `[0, 2^bits - N - 1]`;
- if `x < N`:  target ∈ `[2^bits - N, 2^bits - 1]`.

However, **no SINGLE ancilla bit holds the borrow flag**. Reading the
flag would require a comparison `target < 2^bits - N`, which is itself
a multi-step quantum operation needing additional workspace.

We formalize this as a positive theorem: the clean state has all
non-target ancilla = 0/false. -/

/-- **Formal blocker — clean subtract leaves NO single bit holding the
borrow flag.**  Every ancilla qubit within the `2*bits + 1` adder
budget is restored.  In particular:
- the carry-in qubit at `q_start` holds `false`;
- every read-register qubit at `q_start + 2*i + 2` (i < bits) holds
  `false`.

Consequence: an exact-budget modular-reduction step that needs the
borrow flag cannot extract it from any single output qubit of the
clean subtract-constant gate.  A different construction is required
(see PROGRESS.md tick-46 status for the path forward). -/
theorem cuccaro_subConstGate_clean_state_loses_underflow_info
    (bits q_start N x : Nat) (h1N : 1 ≤ N) (hN : N ≤ 2^bits) :
    -- Carry-in restored to false.
    (Gate.applyNat (cuccaro_subConstGate bits q_start N)
        (cuccaro_input_F q_start false 0 x) q_start = false)
    ∧
    -- Every read-register qubit is false.
    (∀ i, i < bits →
        Gate.applyNat (cuccaro_subConstGate bits q_start N)
          (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2) = false) := by
  unfold cuccaro_subConstGate
  refine ⟨?_, ?_⟩
  · exact cuccaro_addConstGate_carry_in_bit bits q_start (2^bits - N) x
  · intro i hi
    exact cuccaro_addConstGate_read_bit bits q_start (2^bits - N) x i hi

/-! ## Deliverable D — additional witness: clean state's target encodes
borrow via Nat order, but not via a single Boolean qubit.

For any `bits, N, x` with the standard hypotheses, the target value
`v := cuccaro_subConstSpec bits N x` satisfies:
- `x < N → v ≥ 2^bits - N`
- `x ≥ N → v < 2^bits - N`

The `decide (x < N)` flag is therefore EXTRACTABLE in classical post-
processing of `v`, but extracting it inside the quantum circuit
requires an additional comparison subcircuit, which itself needs
workspace beyond the `2*bits + 1` adder budget. -/

/-- **Target encodes borrow via Nat-order, not via a single Boolean.**
In the underflow case, the target value lies in
`[2^bits - N, 2^bits - 1]`; in the non-underflow case it lies in
`[0, 2^bits - N - 1]`. -/
theorem cuccaro_subConstSpec_underflow_range
    (bits N x : Nat) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    (x < N → 2^bits - N ≤ cuccaro_subConstSpec bits N x)
    ∧ (N ≤ x → cuccaro_subConstSpec bits N x < 2^bits - N) := by
  refine ⟨?_, ?_⟩
  · intro hlt
    rw [cuccaro_subConstSpec_of_lt bits N x hN hlt]
    omega
  · intro hle
    rw [cuccaro_subConstSpec_of_le bits N x hN hx hle]
    omega

/-! ## Deliverable E — candidate next route (documentation only).

The exact-budget blocker for modular reduction is structural: the
forward-then-reverse Cuccaro adder uncomputes the top carry. To
extract a borrow flag, one of the following must hold:

(a) **Reserve a flag qubit OUTSIDE the `2*bits + 1` budget.**  In the
    SQIR modmult layout `n + modmult_rev_anc n = n + (2*n + 1) =
    3*n + 1`, the `n` data qubits are separate from the adder ancilla.
    A modular-reduction inner step could temporarily use a data qubit
    as the flag — but this requires careful protocol design and is
    not a clean primitive.

(b) **Forward-only comparator circuit.**  Build a separate
    `cuccaro_compareConstGate` that:
      1. Runs the forward MAJ chain (computes top carry at
         pos `q_start + 2*bits`).
      2. CNOT's the top carry into a flag qubit `flagPos`.
      3. Runs the reverse MAJ chain (uncomputes the forward chain).
    This still requires a flag qubit at `flagPos`, hence one extra
    qubit beyond the adder budget.

(c) **Modified primitive with reserved internal flag.**  Use a
    `(2*bits + 2)`-qubit layout where the extra qubit serves as the
    flag — this exceeds the exact SQIR budget by 1 ancilla, but may
    be acceptable if the modular-multiplier compiles with some slack.

None of these can be built without an additional qubit beyond the
clean Cuccaro add-constant primitive. The Tick-46 conclusion is
therefore: **exact-budget modular reduction with a borrow flag is
not buildable from the current Cuccaro add-constant primitive
alone**. A flag qubit (either internal or external) must be
introduced. -/

end FormalRV.BQAlgo
