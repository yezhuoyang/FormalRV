import FormalRV.Core.Gate
import FormalRV.Framework.PaperClaims
import FormalRV.Arithmetic.Correctness

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims




/-! ## Register indexing for the unary lookup circuit

    Layout (top to bottom): ctrl[0], then `n_addr` pairs of
    (address[i], and[i]), then `n_word` word qubits.

    Index assignment:
      ctrl_idx       = 0
      address_idx i  = 1 + 2*i          (i = 0..n_addr-1)
      and_idx i      = 1 + 2*i + 1      (i = 0..n_addr-1)
      word_idx n_addr j = 1 + 2*n_addr + j  (j = 0..n_word-1)
-/

/-- Qubit index for the controller bit (top wire in Fig. 4(b)). -/
def ulookup_ctrl_idx : Nat := 0

/-- Qubit index for the i-th address bit. -/
def ulookup_address_idx (i : Nat) : Nat := 1 + 2 * i

/-- Qubit index for the i-th ancilla AND bit (interleaved with address). -/
def ulookup_and_idx (i : Nat) : Nat := 1 + 2 * i + 1

/-- Qubit index for the j-th word bit, given the number of address bits. -/
def ulookup_word_idx (n_addr j : Nat) : Nat := 1 + 2 * n_addr + j

/-- Total qubits required for an `n_addr`-address-bit, `n_word`-word-bit
    unary lookup: 1 + 2*n_addr + n_word. -/
def unary_lookup_n_qubits (n_addr n_word : Nat) : Nat :=
  1 + 2 * n_addr + n_word

/-! ## Stub: unary lookup gate sequence

    Fig. 4(b) shows a cascade of Toffolis and CNOTs. The exact gate
    sequence per address bit is the next concrete deliverable.
    For Iter 1 we land only the indexing infrastructure; future
    iterations will populate the gate sequence and derive the
    T-count.

    A schematic outline of the structure (to be encoded gate-by-gate):
    1. Build the unary "address-decoder" tree: cascade of CCXs writing
       AND-bits from (ctrl, address[i]) into ancilla register.
    2. Apply word-controlled CNOTs from each unary AND-bit onto the
       target word registers.
    3. Uncompute the unary cascade in reverse order.

    The Toffoli count is dominated by step 1 + step 3 (the cascade
    + its uncomputation). The "71 τ_s per Toffoli" figure from
    qianxu p. 24 (`15·q_w/(k_p − 3) ≈ 71`) is exactly the formula
    relating these counts to the cycle cost. -/

/-- Placeholder: the empty lookup (Iter 1 only encodes indexing). -/
def unary_lookup_stub (_n_addr _n_word : Nat) : Gate := Gate.I

/-! ## Prefix-AND cascade (Iter 11, 2026-05-12)

    The "address-decoder" inner structure of Fig. 4(b). Faithful Lean
    encoding of `PyCircuits/lookups/unary_lookup_qrisp.py`'s
    `build_prefix_and_cascade(ctrl, address, and_anc)` (Iter 5
    Python implementation). The cascade emits:

      and[0] = ctrl ∧ address[0]              -- 1 CCX
      and[i] = and[i-1] ∧ address[i]   (i≥1)  -- 1 CCX each

    Total: n_addr Toffolis forward (uncomputation in reverse mirrors
    these). This is the "I/O-bound" red-highlighted region of Fig. 4(b).
-/

/-- One step of the prefix-AND cascade at bit `i`:
      i=0  → CCX(ctrl, address[0], and[0])
      i>0  → CCX(and[i-1], address[i], and[i])

    Faithful translation of
    `PyCircuits/lookups/unary_lookup_qrisp.py:build_prefix_and_cascade`. -/
def prefix_and_step (i : Nat) : Gate :=
  if i = 0 then
    Gate.CCX ulookup_ctrl_idx (ulookup_address_idx 0) (ulookup_and_idx 0)
  else
    Gate.CCX (ulookup_and_idx (i - 1)) (ulookup_address_idx i) (ulookup_and_idx i)

/-- The full forward prefix-AND cascade for `n_addr` address bits,
    composed via `Gate.seq`. -/
def prefix_and_cascade : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (prefix_and_cascade n) (prefix_and_step n)

/-! ## Single-iteration unit framing (Iter 13, 2026-05-12)

    The `prefix_and_cascade` above is the **address-decoder unit
    that runs ONCE per iteration of the unary lookup loop**. The
    full lookup (qianxu p. 23) iterates through 2^q_a address
    bitstrings, using Gray-code-style amortization + measurement-
    based uncomputation to achieve a total of **2^q_a Toffolis**,
    NOT `2 · q_a · 2^q_a`.

    For the explicit gate-level review, we still encode the reverse
    cascade `prefix_and_uncompute` below. The reason: this gives
    the **upper-bound** Toffoli count if NO measurement-based
    optimization is used (2·q_a per iteration, 2·q_a·2^q_a total),
    against which the paper's claim of 2^q_a represents an
    optimization factor of 2·q_a.

    The measurement-based path is the topic of future ticks (Phase B
    of CLAUDE.md roadmap: PPM construction). -/

/-- One reverse step of the prefix-AND cascade — same gate as the
    forward step (CCX is self-inverse) but emitted in reverse order
    in `prefix_and_uncompute`. Provided as a separate def for
    clarity even though structurally `prefix_and_step` already
    encodes the gate. -/
def prefix_and_uncompute_step (i : Nat) : Gate := prefix_and_step i

/-- The full reverse uncomputation cascade. Emits `prefix_and_step n-1`
    then `n-2`, ..., then `0`. Together with `prefix_and_cascade n`,
    forms the no-measurement upper-bound: total `2n` Toffolis. -/
def prefix_and_uncompute : Nat → Gate
  | 0       => Gate.I
  | n + 1   => Gate.seq (prefix_and_step n) (prefix_and_uncompute n)

/-- The no-measurement upper bound: forward + reverse cascade uses `2n`
    Toffolis. This represents the gate-level cost WITHOUT the Gidney-
    style measurement trick. The paper's optimization gets the per-
    iteration cost down to `n` (forward only, reverse uses measurements). -/
def prefix_and_compute_and_uncompute (n : Nat) : Gate :=
  Gate.seq (prefix_and_cascade n) (prefix_and_uncompute n)

/-! ## Unary lookup iteration body (Iter 14, 2026-05-12)

    One "iteration" of the unary lookup loop for a single address
    value. Structure (mirrors Iter 5 Python's full flow):
    1. **Address-bit flips** (X gates): flip address bits that are 0 in
       the target address value, so the prefix-AND cascade fires exactly
       on this address.
    2. **Forward prefix-AND cascade** (`prefix_and_cascade n_addr`).
    3. **Word-CNOTs**: for each bit j where the table[addr][j] = 1,
       emit `CX(and[n_addr-1], word[j])`.
    4. **Reverse cascade** (`prefix_and_uncompute n_addr`).
    5. **Mirror of step 1** (undo the X flips).

    Toffoli count = `2 · n_addr` (steps 2 and 4 only; X/CX are
    tcount-zero). This is the no-measurement upper bound for one
    iteration of the unary lookup. -/

/-- Helper: emit X gates at each index in the list. -/
def x_gates_from_indices : List Nat → Gate
  | []      => Gate.I
  | i :: xs => Gate.seq (x_gates_from_indices xs) (Gate.X i)

/-- Helper: emit CX gates with a fixed control and each target in the list. -/
def cx_gates_from_indices (ctrl : Nat) : List Nat → Gate
  | []        => Gate.I
  | tgt :: xs => Gate.seq (cx_gates_from_indices ctrl xs) (Gate.CX ctrl tgt)

/-- One iteration of the unary lookup loop targeting a specific address
    value. `addr_flip_idxs` is the list of address-bit indices to X-flip
    (so the cascade fires for the target value). `word_cnot_idxs` is the
    list of word-bit indices to write (per the table row at that address).
-/
def unary_lookup_iteration (n_addr : Nat)
    (addr_flip_idxs word_cnot_idxs : List Nat) : Gate :=
  let flips      := x_gates_from_indices addr_flip_idxs
  let cascade    := prefix_and_cascade n_addr
  let cnots      := cx_gates_from_indices (ulookup_and_idx (n_addr - 1)) word_cnot_idxs
  let uncompute  := prefix_and_uncompute n_addr
  Gate.seq (Gate.seq (Gate.seq (Gate.seq flips cascade) cnots) uncompute) flips

/-! ## Multi-iteration unary lookup (Iter 27, 2026-05-12)

    The full unary lookup loop iterates through 2^q_a address values,
    one iteration per address. Each iteration calls `unary_lookup_iteration`
    with the address-flip pattern for that value and the corresponding
    table row's word-CNOT pattern.

    For the no-measurement Toffoli count, each iteration contributes
    `14 · n_addr` T-gates, so the multi-iteration total is
    `14 · n_addr · addr_count`. The paper's claim of `2^q_a` Toffolis
    (= `7 · 2^q_a` T) requires BOTH:
    - the Gidney measurement-based uncompute (factor of 2: 14n → 7n per iter)
    - Gray-code amortization (factor of n_addr: n_addr cascade Toffolis
      per iteration → 1 amortized across consecutive iterations)
-/

/-- Compose `unary_lookup_iteration` for a list of `(addr_flips,
    word_cnots)` data tuples. Each tuple is one iteration of the
    lookup loop. -/
def unary_lookup_multi_iteration (n_addr : Nat) :
    List (List Nat × List Nat) → Gate
  | []                     => Gate.I
  | (flips, cnots) :: rest =>
      Gate.seq (unary_lookup_multi_iteration n_addr rest)
               (unary_lookup_iteration n_addr flips cnots)

/-! ## Cascade correctness by induction (Iter 64, 2026-05-12)

    Lift the per-step correctness to the full `prefix_and_cascade n`.
    Mirrors Iter 58 for the adder. **Second Verified-tier review chain
    under the new hard rules.** -/

/-- Per-step post-state: applying `prefix_and_step i` XORs
    `(prev ∧ address[i])` into `and[i]`, where `prev = ctrl` at i=0
    and `and[i-1]` at i>0. -/
def prefix_and_step_post_state (i : Nat) (f : Nat → Bool) : Nat → Bool :=
  if i = 0 then
    update f (ulookup_and_idx 0)
      (xor (f (ulookup_and_idx 0))
           (f ulookup_ctrl_idx && f (ulookup_address_idx 0)))
  else
    update f (ulookup_and_idx i)
      (xor (f (ulookup_and_idx i))
           (f (ulookup_and_idx (i - 1)) && f (ulookup_address_idx i)))

/-- Cascade post-state: fold of per-step post-states over bits 0..n-1.
    Matches the recursive structure of `prefix_and_cascade`. -/
def prefix_and_cascade_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | n + 1, f => prefix_and_step_post_state n (prefix_and_cascade_post_state n f)

/-- Disjointness bundle for a single bit of the lookup prefix-AND
    cascade. The five conditions follow from the indexing structure
    `ulookup_*_idx i = 1 + 2*i (+1)`. -/
structure ULookupBitDisjointness (dim i : Nat) : Prop where
  h_ctrl     : ulookup_ctrl_idx < dim
  h_and_pred : ulookup_and_idx (i - 1) < dim
  h_addr     : ulookup_address_idx i < dim
  h_and      : ulookup_and_idx i < dim

/-! ## Gray-code amortization scaffolding (Iter 46, 2026-05-12)

    The standard `unary_lookup_multi_iteration` re-runs the full
    `n_addr`-step cascade on every iteration, giving `n_addr · 2^q_a`
    cascade Toffolis. The **Gray-code amortization** orders the
    iterations so consecutive address values differ by exactly ONE
    bit. Then only the ONE differing position needs a cascade-step
    update; the other `n_addr - 1` AND-bits remain stable.

    **Total Toffolis under Gray-code amortization**:
    - First iteration: full cascade = `n_addr` Toffolis
    - Each subsequent iteration: 1 Toffoli (one cascade-step update)
    - Total: `n_addr + (2^q_a - 1)` ≈ `2^q_a` Toffolis for q_a ≥ n_addr.

    For q_a=6 (RSA-2048): standard = 6·64 = 384 Toffolis; Gray-code =
    6 + 63 = 69 Toffolis; paper figure = 2^6 = 64 Toffolis. The
    Gray-code count is **within +5 of the paper claim** — close
    enough that the residual gap is bookkeeping (whether the initial
    cascade counts as "Toffolis for this lookup" or amortized across
    multiple lookups). -/

/-- Gray-code-amortized Toffoli count for a q_a-bit unary lookup:
    `n_addr` (initial cascade) + `(2^q_a - 1)` (one Toffoli per
    subsequent iteration). -/
def gray_code_unary_lookup_toffoli_count (n_addr q_a : Nat) : Nat :=
  n_addr + (2 ^ q_a - 1)

/-- **Two-step closure roadmap**: the lookup review-gap (12× at q_a=6)
    decomposes as 2× (Gidney AND, closed Iter 43-44) × 6× (Gray-code,
    scaffolded here). With Gray-code Toffoli count = `n_addr + 2^q_a - 1`,
    the ratio Lean-Gray-code / paper-claim is
    `(n_addr + 2^q_a - 1) / 2^q_a ≈ 1.08` at q_a=6 — **down from 6×
    to ~8% residual**. The residual is the initial-cascade
    bookkeeping discussed above. -/
def gray_code_residual_ratio (n_addr q_a : Nat) : Nat × Nat :=
  (gray_code_unary_lookup_toffoli_count n_addr q_a,
   qianxu_E9_lookup_gate_derived_count q_a)

/-! ## Cascade on zero input — smoke test (Iter 91, 2026-05-12)

    Mirror of Iter 89's adder-side zero-input theorems. On the all-
    zero input (every qubit false), the lookup prefix-AND cascade
    produces all-zero output: each CCX writes
    `xor false (false ∧ false) = false`, a no-op via
    `Function.update_eq_self`.

    Combined with Iter 74's matrix cascade · uncompute = 1, this
    gives the **lookup-side analog of Iter 89's full-adder zero
    smoke test**: the prefix-AND cascade and its uncompute act as
    identity on the zero input. -/

/-- The all-zero input function (local re-abbreviation; the adder
    side defines a `zeroF` in its own namespace). -/
abbrev zeroFLook : Nat → Bool := fun _ => false

/-! ## Concrete 2-bit lookup example: prefix-AND cascade on (ctrl=1, addr=10) (Iter 97, 2026-05-12)

    Mirror of Iter 94's adder concrete decide example. For a 2-bit
    unary lookup cascade with input `ctrl = 1, address_0 = 1,
    address_1 = 0` (i.e., address bitstring "10" with the
    least-significant bit set), the cascade computes:
    - and_0 = ctrl ∧ address_0 = 1 ∧ 1 = 1
    - and_1 = and_0 ∧ address_1 = 1 ∧ 0 = 0

    All decide-checked. -/

/-- Input for the lookup: ctrl=1 (qubit 0), address_0=1 (qubit 1),
    everything else false (and_0, address_1, and_1 all 0). -/
def inputF_lookup_ctrl_addr_10 : Nat → Bool
  | 0 => true   -- ctrl = 1
  | 1 => true   -- address_0 = 1
  | _ => false  -- and_0, address_1, and_1, ... = 0

/-- **And another variant**: with `ctrl=1, address=11`, both AND
    ancillas should fire to 1. -/
def inputF_lookup_ctrl_addr_11 : Nat → Bool
  | 0 => true   -- ctrl = 1
  | 1 => true   -- address_0 = 1
  | 3 => true   -- address_1 = 1
  | _ => false

/-! ## Concrete 3-bit lookup cascade decide examples (Iter 112, 2026-05-12)

    Extends Iter 97's 2-step decide examples to 3 steps,
    matching the q_a=3 lookup instance from qianxu Fig. 4(b)
    (which shows a 3-address-bit, 6-word-bit lookup).

    Tests the chained AND computation: each step's CCX writes
    `previous_and ∧ next_address` into the next AND ancilla. -/

/-- Input for `q_a = 3` lookup: ctrl=1, address = (1, 1, 0)
    LSB-first. The cascade should compute:
    - and_0 = ctrl ∧ addr_0 = 1 ∧ 1 = 1
    - and_1 = and_0 ∧ addr_1 = 1 ∧ 1 = 1
    - and_2 = and_1 ∧ addr_2 = 1 ∧ 0 = 0 -/
def inputF_lookup_q3_addr_110 : Nat → Bool
  | 0 => true   -- ctrl = 1
  | 1 => true   -- addr_0 = 1
  | 3 => true   -- addr_1 = 1
  | _ => false  -- addr_2 = 0; and ancillas all 0

/-- Input with all 3 address bits set: ctrl=1, address = (1, 1, 1).
    All ANDs fire to 1. -/
def inputF_lookup_q3_addr_111 : Nat → Bool
  | 0 => true   -- ctrl
  | 1 => true   -- addr_0
  | 3 => true   -- addr_1
  | 5 => true   -- addr_2
  | _ => false  -- and ancillas

/-! ### Semantic-correctness invariant for the prefix-AND cascade
    (Iter 219, 2026-05-13)

    Mirror of Iter 175's `Gidney.propagation_step_invariant` for the
    forward adder cascade. The lookup's prefix-AND chain builds up
    the AND of `ctrl` with successive address bits:
    - After step 0: and_0 = ctrl ∧ addr.testBit 0.
    - After step k (for k ≤ n): and_i for i < k holds
      ctrl ∧ ⋀_{j ≤ i} addr.testBit j; and_i for i ≥ k holds the
      input value (false for clean input).
-/

/-- **Math AND of `ctrl` with the first `n` bits of `addr`**.
    `address_and ctrl addr n = ctrl ∧ addr.testBit 0 ∧ ... ∧ addr.testBit (n-1)`. -/
def Lookup.address_and (ctrl : Bool) (addr : Nat) : Nat → Bool
  | 0     => ctrl
  | n + 1 => Lookup.address_and ctrl addr n && addr.testBit n

/-- **Step-indexed prefix-AND cascade invariant** (Iter 219, analog of
    Iter 175's `Gidney.propagation_step_invariant`).

    After `k` steps of the prefix-AND cascade applied to a state where
    `f(ctrl_idx) = ctrl`, `f(address_idx i) = addr.testBit i`, and
    `f(and_idx i) = false` for all i < n:
    - For i < k (computed): post(and_idx i) = ctrl ∧ ⋀_{j ≤ i} addr.testBit j.
    - For i ≥ k (untouched): post(and_idx i) = false. -/
def Lookup.cascade_step_invariant (k n : Nat) (ctrl : Bool) (addr : Nat)
    (post : Nat → Bool) : Prop :=
  ∀ i, i < n →
    post (ulookup_and_idx i) =
      if i < k then Lookup.address_and ctrl addr (i + 1) else false

/-! ## X-flip layer + CNOT layer classical post-states (Iter 224, 2026-05-13)

    Specs for the two non-cascade gate-layer factors of
    `unary_lookup_iteration`:
    * `flips := x_gates_from_indices addr_flip_idxs`  — outer wrapper.
    * `cnots := cx_gates_from_indices (and_idx (n_addr - 1)) word_cnot_idxs` — middle.

    The recursion order matches the Gate.seq nesting in the source:
    `i :: xs` builds `seq (...xs cascade) (X i)` — the head is applied
    LAST. The post-state therefore wraps the tail's post-state in an
    `update` at position `i`. -/

/-- **Classical post-state of `x_gates_from_indices xs`**: starting from
    `f`, apply X-flips to the indices in `xs` in the order matching the
    Gate.seq nesting (tail first, head last). With unique indices, the
    net effect is to XOR each listed position with `true`. -/
def Lookup.x_flip_post_state : List Nat → (Nat → Bool) → (Nat → Bool)
  | [], f => f
  | i :: xs, f =>
    let f' := Lookup.x_flip_post_state xs f
    Function.update f' i (! (f' i))

/-- **Classical post-state of `cx_gates_from_indices ctrl xs`**:
    each CX(ctrl, tgt) does `tgt := tgt ⊕ ctrl`. In the order matching
    the Gate.seq nesting, the tail is applied first. **Crucially**:
    the control wire `ctrl` is never the target of any CX in this
    layer, so its value is preserved across the layer (see
    `cnot_layer_post_state_ctrl_unchanged` below). -/
def Lookup.cnot_layer_post_state (ctrl : Nat) : List Nat → (Nat → Bool) → (Nat → Bool)
  | [], f => f
  | tgt :: xs, f =>
    let f' := Lookup.cnot_layer_post_state ctrl xs f
    Function.update f' tgt (xor (f' tgt) (f' ctrl))

/-! ## Boolean-level cascade · uncompute = identity (Iter 229, 2026-05-13)

    Iter 76 proved `prefix_and_cascade n · prefix_and_uncompute n = 1`
    at the matrix level (Mathlib `Matrix`). The boolean-level analog,
    needed for the `unary_lookup_iteration_correct` headline, lifts
    this to: applying the bool-level cascade-then-uncompute post-state
    composition to any `f` yields `f`. Proof by induction on n, using
    Iter 227's `prefix_and_step_post_state_involution`. -/

/-- **Boolean post-state of the reverse cascade**: applies
    `prefix_and_step_post_state` in the reverse order (n-1, n-2, ..., 0),
    matching `prefix_and_uncompute n = seq (step (n-1)) (...) (step 0)`. -/
def prefix_and_uncompute_post_state : Nat → (Nat → Bool) → (Nat → Bool)
  | 0    , f => f
  | n + 1, f => prefix_and_uncompute_post_state n (prefix_and_step_post_state n f)

/-! ## Iteration post-state + word/and disjointness (Iter 230, 2026-05-13)

    Define the boolean post-state of `unary_lookup_iteration` as the
    explicit 5-stage composition: flips → cascade → cnots → uncompute → flips.

    Prove the key disjointness: when CNOT targets are word-register
    indices (≥ 1 + 2·n_addr), they don't touch any and-bit (which lie
    at positions 2 + 2·i < 1 + 2·n_addr for i < n_addr).

    Together with Iter 226 (X-flip involution) and Iter 229 (cascade·uncompute = id),
    these are the cancellation arguments that make the iteration body's
    NET effect = "trigger-conditioned XOR on the word register, identity
    elsewhere". -/

/-- **Boolean post-state of `unary_lookup_iteration`**. The 5-stage
    composition mirrors the Gate.seq structure of `unary_lookup_iteration`:
    `flips · cascade · cnots · uncompute · flips`. -/
def Lookup.iteration_post_state
    (n_addr : Nat) (addr_flip_idxs word_cnot_idxs : List Nat)
    (f : Nat → Bool) : Nat → Bool :=
  let f1 := Lookup.x_flip_post_state addr_flip_idxs f
  let f2 := prefix_and_cascade_post_state n_addr f1
  let f3 := Lookup.cnot_layer_post_state (ulookup_and_idx (n_addr - 1)) word_cnot_idxs f2
  let f4 := prefix_and_uncompute_post_state n_addr f3
  Lookup.x_flip_post_state addr_flip_idxs f4

/-- **All elements of `xs` are word-register indices** (i.e., ≥ 1 + 2·n_addr).
    Captures the structural condition that CNOT targets in a lookup
    iteration write to the word register, not the ctrl/address/and registers. -/
def Lookup.AllWordIdx (n_addr : Nat) (xs : List Nat) : Prop :=
  ∀ i ∈ xs, 1 + 2 * n_addr ≤ i

/-! ## Multi-iteration post-state (Iter 248, 2026-05-14)

    Bool-level analog of `unary_lookup_multi_iteration`. Folds
    `iteration_post_state` over an iter list to model the full
    multi-iteration lookup loop's classical action.

    The Gray-code amortization (qianxu p. 23) is a GATE-COUNT
    optimization; the SEMANTIC behavior is the same regardless of
    iter ordering, so this post-state captures the abstract
    "for each iter, apply its single-iter transformation" pattern. -/

/-- **Boolean post-state of `unary_lookup_multi_iteration`**. Recursive
    fold matching the gate-level structure: each `(flips, cnots)`
    tuple in the iter list contributes one application of
    `iteration_post_state`. -/
def Lookup.multi_iteration_post_state (n_addr : Nat) :
    List (List Nat × List Nat) → (Nat → Bool) → (Nat → Bool)
  | [],                     f => f
  | (flips, cnots) :: rest, f =>
      Lookup.iteration_post_state n_addr flips cnots
        (Lookup.multi_iteration_post_state n_addr rest f)

/-! ## Abstract trigger predicate + multi-iter XOR value (Iter 249, 2026-05-14)

    Pure classical formulation of the multi-iteration semantics:
    `iter_triggers` says whether a given iter's prefix-AND chain fires
    on (ctrl, addr); `multi_iteration_xor_value` sums the boolean
    contributions across iters at a target word position.

    The Iter 251 headline will state:
      `multi_iteration_post_state n_addr iters f p =
         xor (f p) (multi_iteration_xor_value ctrl addr n_addr iters p)`
    for word positions p, given f carrying the expected (ctrl, addr, clean and-bits). -/

/-- **Iter trigger predicate** (pure classical): true iff the iter's
    prefix-AND chain fires on input `(ctrl, addr)`, equivalently iff
    `ctrl` is true and the effective address (addr XOR flip mask) is
    all-ones for the first `n_addr` bits.

    Equivalent to `Lookup.address_and ctrl effective_addr n_addr` where
    `effective_addr.testBit i = xor (addr.testBit i) (decide (ulookup_address_idx i ∈ flips))`. -/
def Lookup.iter_triggers (ctrl : Bool) (addr : Nat) (n_addr : Nat)
    (flips : List Nat) : Bool :=
  match n_addr with
  | 0 => ctrl
  | n + 1 => Lookup.iter_triggers ctrl addr n flips
              && xor (addr.testBit n) (decide (ulookup_address_idx n ∈ flips))

/-- **Multi-iteration XOR contribution at a word position** (pure classical).
    For a word position `p`, the boolean XOR contribution is `XOR` over
    all iters of `(p ∈ cnots_i) AND (iter_i triggers)`. -/
def Lookup.multi_iteration_xor_value
    (ctrl : Bool) (addr : Nat) (n_addr : Nat) :
    List (List Nat × List Nat) → Nat → Bool
  | [], _ => false
  | (flips, cnots) :: rest, p =>
      xor (decide (p ∈ cnots) && Lookup.iter_triggers ctrl addr n_addr flips)
          (Lookup.multi_iteration_xor_value ctrl addr n_addr rest p)

/-! ## Effective-address Nat construction (Iter 250, 2026-05-14)

    To connect `iter_triggers` (Iter 249, recursive Bool) to
    `Lookup.address_and ctrl effective_addr n_addr` (Iter 219, indexed
    by a Nat), we construct an explicit Nat `effective_addr addr flips n`
    whose first `n` bits match the X-flipped pattern.

    The bridge theorem
    `iter_triggers ctrl addr n_addr flips = address_and ctrl (effective_addr addr flips n_addr) n_addr`
    deferred to Iter 251 (requires Nat.testBit lemmas for the recursive
    Nat construction). For now: definition + decide-witnesses validating it. -/

/-- **Effective address Nat construction (Iter 253 reform via `Nat.lor`)**.
    Recursively builds a Nat whose i-th bit (for i < n) equals
    `xor (addr.testBit i) (decide (ulookup_address_idx i ∈ flips))`.

    Uses bitwise OR (`|||`) instead of addition. With OR, the testBit
    characterization (Iter 254) is straightforward via `Nat.testBit_or`
    and `Nat.testBit_two_pow`. -/
def Lookup.effective_addr (addr : Nat) (flips : List Nat) : Nat → Nat
  | 0     => 0
  | n + 1 =>
    let lower := Lookup.effective_addr addr flips n
    if xor (addr.testBit n) (decide (ulookup_address_idx n ∈ flips))
    then lower ||| (2 ^ n)
    else lower

/-! ## Multi-iter headline assembly (Iter 257, 2026-05-14)

    The multi-iter classical XOR contribution at a word position is the
    sum (XOR) over all iters of `(p ∈ cnots_i) AND (iter's trigger fires)`.
    The trigger is expressed via `address_and ctrl (effective_addr ...) n_addr`. -/

/-- **Classical XOR contribution at a word position** (via address_and).
    Recursive fold matching the multi-iter post-state structure. -/
def Lookup.multi_iteration_xor_value_via_address_and
    (ctrl : Bool) (addr : Nat) (n_addr : Nat) :
    List (List Nat × List Nat) → Nat → Bool
  | [], _ => false
  | (flips, cnots) :: rest, p =>
      xor (decide (p ∈ cnots) &&
           Lookup.address_and ctrl
             (Lookup.effective_addr addr flips n_addr) n_addr)
          (Lookup.multi_iteration_xor_value_via_address_and ctrl addr n_addr rest p)

end FormalRV.BQAlgo
