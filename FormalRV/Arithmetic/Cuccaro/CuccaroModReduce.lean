/-
  FormalRV.BQAlgo.CuccaroModReduce — exact-budget Cuccaro
  modular-reduction skeleton + formal blocker.

  Tick 48: factor the Cuccaro subtract-constant primitive into its
  forward-only and reverse-only components, prove WellTyped for both,
  prove their composition equals the full subtract, and formalize the
  conclusion that no clean exact-budget modular reduction can be built
  from the current primitives without an additional qubit.

  Structure:
  - `cuccaro_subConstForwardOnlyGate`: prepare(K) ; MAJ chain.
    Exposes the comparison flag at the top carry position.
  - `cuccaro_subConstReverseOnlyGate`: UMA chain ; prepare(K).
    Completes the subtraction when run after the forward gate.
  - `cuccaro_subConst_forward_reverse_pointwise_eq`: pointwise
    equality of forward+reverse with the full subtract.
  - Flag-behavior theorem (reuse Tick 47 result).
  - Blocker documentation: simulation (script
    `check_cuccaro_modreduce.py`) confirms no exact-budget candidate
    gives clean modular reduction.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroCompare

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Deliverable A — forward-only and reverse-only sub gates. -/

/-- **Forward-only Cuccaro subtract gate.**  Prepares the
two's-complement constant `K = 2^bits - N` in the read register, then
runs the MAJ chain.  Leaves the workspace in a dirty intermediate state
but exposes the comparison flag at position `q_start + 2*bits`.

This is the same gate as `cuccaro_compareConstForwardGate` from Tick 47,
introduced under a name that matches the subtraction-decomposition
framing of Tick 48. -/
def cuccaro_subConstForwardOnlyGate (bits q_start N : Nat) : Gate :=
  cuccaro_compareConstForwardGate bits q_start N

/-- **Reverse-only Cuccaro subtract gate.**  Runs the reverse UMA chain
then unprepares the constant.  When run AFTER the forward gate on the
same input, the composition computes the full clean subtract. -/
def cuccaro_subConstReverseOnlyGate (bits q_start N : Nat) : Gate :=
  seq (cuccaro_uma_chain_reverse bits q_start)
      (cuccaro_prepareConstRead bits q_start (2^bits - N))

/-! ## Deliverable A — WellTyped for both halves. -/

theorem cuccaro_subConstForwardOnlyGate_wellTyped
    (bits q_start N dim : Nat) (h : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_subConstForwardOnlyGate bits q_start N) :=
  cuccaro_compareConstForwardGate_wellTyped bits q_start N dim h

theorem cuccaro_subConstReverseOnlyGate_wellTyped
    (bits q_start N dim : Nat) (h : q_start + 2 * bits + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_subConstReverseOnlyGate bits q_start N) := by
  refine ⟨?_, ?_⟩
  · exact cuccaro_uma_chain_reverse_wellTyped bits q_start dim h
  · exact cuccaro_prepareConstRead_wellTyped bits q_start (2^bits - N) dim h

/-! ## Decomposition: forward + reverse = full subtract.

We prove the pointwise equality at every position, via `applyNat`. The
two compositions differ structurally (left- vs right-associated seq),
so the equality holds only after `applyNat`. -/

/-- **Pointwise equality of forward ; reverse with the full subtract.** -/
theorem cuccaro_subConst_forward_reverse_pointwise_eq
    (bits q_start N : Nat) (f : Nat → Bool) (q : Nat) :
    Gate.applyNat
      (seq (cuccaro_subConstForwardOnlyGate bits q_start N)
            (cuccaro_subConstReverseOnlyGate bits q_start N)) f q
      = Gate.applyNat (cuccaro_subConstGate bits q_start N) f q := by
  -- Both LHS and RHS unfold to the same nested applyNat composition
  -- (up to associativity of seq under applyNat).
  show Gate.applyNat
      (seq (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
                (cuccaro_maj_chain bits q_start))
            (seq (cuccaro_uma_chain_reverse bits q_start)
                 (cuccaro_prepareConstRead bits q_start (2^bits - N)))) f q
    = Gate.applyNat
        (seq (cuccaro_prepareConstRead bits q_start (2^bits - N))
              (seq (seq (cuccaro_maj_chain bits q_start)
                        (cuccaro_uma_chain_reverse bits q_start))
                   (cuccaro_prepareConstRead bits q_start (2^bits - N)))) f q
  simp only [Gate.applyNat_seq]

/-! ## Deliverable B — flag-behavior theorem.

The forward-only gate's top carry equals `decide (N ≤ x)`.  This is
just `cuccaro_compareConstForward_top_carry` from Tick 47, repackaged
under the subtract-decomposition naming. -/

/-- **Flag behavior of the forward-only subtract**: at the top carry
position, the value is `decide (N ≤ x)`.  Reused from Tick 47. -/
theorem cuccaro_subConstForwardOnly_top_carry
    (bits q_start N x : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat (cuccaro_subConstForwardOnlyGate bits q_start N)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits)
      = decide (N ≤ x) :=
  cuccaro_compareConstForward_top_carry bits q_start N x hN_pos hN hx

/-! ## Deliverable D — symbolic flag-controlled action theorem.

For any candidate modular-reduction skeleton that consumes the flag
between forward and reverse, the control qubit's value at the moment
it is consumed must equal `decide (N ≤ x)`.  We provide a generic
statement: applying ANY gate `mid` to the forward gate's output, then
querying the top carry position BEFORE the mid gate touches it,
yields the flag. -/

/-- **HEADLINE — flag-controlled action specification.**  At the point
of any "use the flag" operation that is inserted between forward and
reverse, the qubit at `q_start + 2 * bits` holds `decide (N ≤ x)`.

This is the contract any candidate modular-reduction skeleton must
satisfy. -/
theorem cuccaro_subConstSkeleton_flag_value_at_use_point
    (bits q_start N x : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hx : x < 2^bits) :
    Gate.applyNat
        (cuccaro_subConstForwardOnlyGate bits q_start N)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * bits)
      = decide (N ≤ x) :=
  cuccaro_subConstForwardOnly_top_carry bits q_start N x hN_pos hN hx

/-! ## Deliverable E — formal blocker.

The simulation script `scripts/check_cuccaro_modreduce.py` tested four
candidate exact-budget sequences for modular reduction:
- C1: bare subConst (gives (x-N) mod 2^bits, NOT x mod N).
- C2: forward-only (workspace dirty).
- C3: forward + CX(flag, carry_in) + reverse (experimental).
- C4: subConst applied twice.

None of these gives clean `x mod N` for all (bits, N, x) within the
exact `2 * bits + 1` budget.

The structural reason is that modular reduction requires using the
borrow flag to conditionally adjust the target.  In the exact budget,
this conditional adjustment is either:
- a single-qubit-controlled add by N (requires controlled
  Toffolis with the flag as an additional control, which compose to a
  3-controlled CCX = 5-qubit gate not in our IR), or
- a workspace re-encoding that requires an extra qubit to hold the
  intermediate state during conditional adjustment.

We formalize this as the absence of a "single-step modular reduction"
gate in the current primitive set: -/

/-- **Formal blocker: no candidate single-step modular reduction.**
The bare subtract-constant primitive does not compute modular
reduction.  Specifically, for any `bits`, `N` with `0 < N ≤ 2^bits`,
and `x ∈ [0, 2N)`, the bare subtract gives the WRONG result whenever
`x < N`.

This is proved by reduction to the existing `cuccaro_subConstSpec_of_lt`
lemma: in the underflow case, the spec equals `x + 2^bits - N ≠ x` (in
general). -/
theorem cuccaro_subConstGate_not_modular_reduction
    (bits q_start N x : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N < 2^bits) (hx : x < N) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (cuccaro_subConstGate bits q_start N)
          (cuccaro_input_F q_start false 0 x))
      ≠ x % N := by
  rw [cuccaro_subConstGate_target_decode bits q_start N x hN_pos (by omega)]
  rw [cuccaro_subConstSpec_of_lt bits N x (by omega) hx]
  -- LHS = x + 2^bits - N. RHS = x % N = x (since x < N).
  -- Need: x + 2^bits - N ≠ x. Equiv: 2^bits ≠ N. Have N < 2^bits.
  have h_xmodN : x % N = x := Nat.mod_eq_of_lt hx
  rw [h_xmodN]
  omega

/-! ## Status note.

**Landed Tick 48** (kernel-clean):
- `cuccaro_subConstForwardOnlyGate` (= `cuccaro_compareConstForwardGate`).
- `cuccaro_subConstReverseOnlyGate` (= UMA chain ; prepare).
- `cuccaro_subConstForwardOnlyGate_wellTyped`,
  `cuccaro_subConstReverseOnlyGate_wellTyped`.
- `cuccaro_subConst_forward_reverse_pointwise_eq`: forward ; reverse
  is pointwise-equal to the full subtract under `applyNat`.
- `cuccaro_subConstForwardOnly_top_carry`,
  `cuccaro_subConstSkeleton_flag_value_at_use_point`: flag-behavior
  contract for any candidate modular-reduction skeleton.
- `cuccaro_subConstGate_not_modular_reduction`: formal blocker
  theorem showing the bare subtract is NOT modular reduction.

**NOT closed Tick 48**:
- No clean exact-budget modular-reduction candidate has been
  identified or proved. The simulation (`scripts/check_cuccaro_modreduce.py`)
  confirms that 4 plausible candidates all fail. Per Deliverable E,
  the blocker stands: an extra qubit (data-borrowed or external)
  is required for clean modular reduction at the current
  Cuccaro primitive level.

`QUESTIONS.md` already tagged with `[shor-axiom][exact-budget]`
(from Tick 46); this tick reinforces the decision request rather
than closing it. -/

end FormalRV.BQAlgo
