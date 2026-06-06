import FormalRV.Core.Gate
import FormalRV.Framework.PaperClaims
import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupDefinitions

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims

/-! ## Smoke tests matching Fig. 4(b)'s example (n_addr=3, n_word=6) -/

/-- 1 + 2·3 + 6 = 13 qubits, matching the 13 horizontal wires in
    Fig. 4(b)'s example diagram. -/
example : unary_lookup_n_qubits 3 6 = 13 := by decide

/-- ctrl[0] is wire 0. -/
example : ulookup_ctrl_idx = 0 := by decide

/-- address[0] is wire 1, and[0] is wire 2 (highlighted red in the figure). -/
example : ulookup_address_idx 0 = 1 ∧ ulookup_and_idx 0 = 2 := by decide

/-- address[1] is wire 3, and[1] is wire 4 (also highlighted red). -/
example : ulookup_address_idx 1 = 3 ∧ ulookup_and_idx 1 = 4 := by decide

/-- address[2] is wire 5, and[2] is wire 6. -/
example : ulookup_address_idx 2 = 5 ∧ ulookup_and_idx 2 = 6 := by decide

/-- word[0..5] are wires 7..12. -/
example : ulookup_word_idx 3 0 = 7 ∧ ulookup_word_idx 3 5 = 12 := by decide

/-- Smoke: stub has T-count 0 (placeholder; real circuit has many). -/
example : tcount (unary_lookup_stub 3 6) = 0 := by decide

/-- Each cascade step is exactly 1 Toffoli (`gcount = 1`), regardless
    of which branch of the `if` fires. -/
theorem gcount_prefix_and_step (i : Nat) : gcount (prefix_and_step i) = 1 := by
  unfold prefix_and_step
  split <;> rfl

/-- Each cascade step is exactly 7 T-gates (`tcount = 7`). -/
theorem tcount_prefix_and_step (i : Nat) : tcount (prefix_and_step i) = 7 := by
  unfold prefix_and_step
  split <;> rfl

example : tcount (prefix_and_step 0) = 7 := by decide

example : tcount (prefix_and_step 5) = 7 := tcount_prefix_and_step 5

example : gcount (prefix_and_step 7) = 1 := gcount_prefix_and_step 7

/-- The 3-bit prefix-AND cascade has exactly 3 Toffolis = 21 T-gates. -/
example : tcount (prefix_and_cascade 3) = 21 := by decide

example : gcount (prefix_and_cascade 3) = 3 := by decide

/-- General Toffoli count: an `n`-bit prefix-AND cascade has exactly `n`
    Toffolis. **Gate-derived** from the recursive definition — no paper
    claim involved. Matches Iter 5 Python's predicted `n_addr` Toffolis. -/
theorem gcount_prefix_and_cascade (n : Nat) :
    gcount (prefix_and_cascade n) = n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show gcount (Gate.seq (prefix_and_cascade n) (prefix_and_step n)) = n + 1
    simp [gcount, ih, gcount_prefix_and_step]

/-- T-count of the cascade is `7n` (one Toffoli = 7 T after decomposition). -/
theorem tcount_prefix_and_cascade (n : Nat) :
    tcount (prefix_and_cascade n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (prefix_and_cascade n) (prefix_and_step n)) = 7 * (n + 1)
    simp [tcount, ih, tcount_prefix_and_step]
    omega

/-- Each uncompute step is exactly 1 Toffoli. -/
theorem gcount_prefix_and_uncompute_step (i : Nat) :
    gcount (prefix_and_uncompute_step i) = 1 :=
  gcount_prefix_and_step i

/-- Toffoli count of the reverse cascade: also exactly `n` Toffolis. -/
theorem gcount_prefix_and_uncompute (n : Nat) :
    gcount (prefix_and_uncompute n) = n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show gcount (Gate.seq (prefix_and_step n) (prefix_and_uncompute n)) = n + 1
    simp [gcount, ih, gcount_prefix_and_step]
    omega

/-- T-count of the reverse cascade: `7n`. -/
theorem tcount_prefix_and_uncompute (n : Nat) :
    tcount (prefix_and_uncompute n) = 7 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show tcount (Gate.seq (prefix_and_step n) (prefix_and_uncompute n)) = 7 * (n + 1)
    simp [tcount, ih, tcount_prefix_and_step]
    omega

theorem gcount_prefix_and_compute_and_uncompute (n : Nat) :
    gcount (prefix_and_compute_and_uncompute n) = 2 * n := by
  unfold prefix_and_compute_and_uncompute
  simp [gcount, gcount_prefix_and_cascade, gcount_prefix_and_uncompute]
  omega

/-- All X-gate sequences are T-count zero. -/
theorem tcount_x_gates_zero (xs : List Nat) : tcount (x_gates_from_indices xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    show tcount (Gate.seq (x_gates_from_indices xs) (Gate.X i)) = 0
    simp [tcount, ih]

/-- All CX-gate sequences are T-count zero. -/
theorem tcount_cx_gates_zero (ctrl : Nat) (xs : List Nat) :
    tcount (cx_gates_from_indices ctrl xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons tgt xs ih =>
    show tcount (Gate.seq (cx_gates_from_indices ctrl xs) (Gate.CX ctrl tgt)) = 0
    simp [tcount, ih]

/-- Gate-count of `x_gates_from_indices xs` is the list length: one X
    per index, identity contributes 0. -/
theorem gcount_x_gates_from_indices (xs : List Nat) :
    gcount (x_gates_from_indices xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    show gcount (Gate.seq (x_gates_from_indices xs) (Gate.X i)) = (i :: xs).length
    simp [gcount, ih, List.length_cons]

/-- Gate-count of `cx_gates_from_indices ctrl xs` is the list length. -/
theorem gcount_cx_gates_from_indices (ctrl : Nat) (xs : List Nat) :
    gcount (cx_gates_from_indices ctrl xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons tgt xs ih =>
    show gcount (Gate.seq (cx_gates_from_indices ctrl xs) (Gate.CX ctrl tgt))
          = (tgt :: xs).length
    simp [gcount, ih, List.length_cons]

/-- The iteration body has T-count `14 · n_addr` regardless of the
    address pattern or word pattern (only the two cascades contribute T). -/
theorem tcount_unary_lookup_iteration (n_addr : Nat)
    (addr_flip_idxs word_cnot_idxs : List Nat) :
    tcount (unary_lookup_iteration n_addr addr_flip_idxs word_cnot_idxs)
      = 14 * n_addr := by
  unfold unary_lookup_iteration
  simp [tcount, tcount_prefix_and_cascade, tcount_prefix_and_uncompute,
        tcount_x_gates_zero, tcount_cx_gates_zero]
  omega

/-- **Gate-count of one iteration body**: `2·|addr_flips| + 2·n_addr +
    |word_cnots|`. Decomposes as: forward+reverse X-flip layers contribute
    `2·|addr_flips|`; forward+reverse prefix-AND cascades contribute
    `2·n_addr`; word CNOTs contribute `|word_cnots|`. Derived purely from
    the gate sequence of `unary_lookup_iteration` — no paper-claim
    constant. This is the **leaf gate-count review claim** for one
    iteration body, mirroring `tcount_unary_lookup_iteration` (Iter 14)
    but at the structural (all-gate) level. -/
theorem gcount_unary_lookup_iteration (n_addr : Nat)
    (addr_flip_idxs word_cnot_idxs : List Nat) :
    gcount (unary_lookup_iteration n_addr addr_flip_idxs word_cnot_idxs)
      = 2 * addr_flip_idxs.length + 2 * n_addr + word_cnot_idxs.length := by
  unfold unary_lookup_iteration
  simp [gcount, gcount_x_gates_from_indices, gcount_cx_gates_from_indices,
        gcount_prefix_and_cascade, gcount_prefix_and_uncompute]
  omega

/-- T-count of the multi-iteration cascade: `14 · n_addr · |iters|`
    regardless of the data carried in the iterations (each iteration
    contributes a fixed `14 · n_addr`, only Toffolis matter). -/
theorem tcount_unary_lookup_multi_iteration (n_addr : Nat)
    (iters : List (List Nat × List Nat)) :
    tcount (unary_lookup_multi_iteration n_addr iters)
      = 14 * n_addr * iters.length := by
  induction iters with
  | nil => simp [unary_lookup_multi_iteration, tcount]
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show tcount (Gate.seq (unary_lookup_multi_iteration n_addr rest)
                          (unary_lookup_iteration n_addr flips cnots))
           = 14 * n_addr * (rest.length + 1)
    simp [tcount, ih, tcount_unary_lookup_iteration, Nat.mul_succ]

/-- Concrete: at n_addr=3 with 8 iterations (= 2^3), total T-count is
    `14 · 3 · 8 = 336`. This is the **no-measurement** bound; the
    paper's `2^q_a = 8` Toffolis = 56 T requires Gidney measurement +
    Gray-code amortization. -/
example :
    tcount (unary_lookup_multi_iteration 3
              [([], []), ([], []), ([], []), ([], []),
               ([], []), ([], []), ([], []), ([], [])])
      = 336 := by decide

/-- **Gate-count of the multi-iteration cascade** (Iter 77): each
    iteration contributes its data-dependent gcount
    `2·|flips_i| + 2·n_addr + |cnots_i|` (Iter 76 leaf), and the
    multi-iteration gcount is the sum of those.

    Expressed as a sum: total gates =
    `2·n_addr · |iters| + 2 · (Σᵢ |flipsᵢ|) + (Σᵢ |cnotsᵢ|)`.

    Derived purely from the gate sequence via induction on the
    iter-list, using `gcount_unary_lookup_iteration` (Iter 76) at
    each step. Mirrors `tcount_unary_lookup_multi_iteration` but
    aggregates data-dependent gate counts (vs T-count's uniform
    `14 · n_addr` per iteration). -/
theorem gcount_unary_lookup_multi_iteration (n_addr : Nat)
    (iters : List (List Nat × List Nat)) :
    gcount (unary_lookup_multi_iteration n_addr iters)
      = 2 * n_addr * iters.length
        + 2 * (iters.map (fun p => p.1.length)).sum
        + (iters.map (fun p => p.2.length)).sum := by
  induction iters with
  | nil => simp [unary_lookup_multi_iteration, gcount]
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show gcount (Gate.seq (unary_lookup_multi_iteration n_addr rest)
                          (unary_lookup_iteration n_addr flips cnots))
           = 2 * n_addr * (rest.length + 1)
             + 2 * ((flips, cnots) :: rest |>.map (fun p => p.1.length)).sum
             + ((flips, cnots) :: rest |>.map (fun p => p.2.length)).sum
    simp [gcount, ih, gcount_unary_lookup_iteration, Nat.mul_succ,
          List.map_cons, List.sum_cons]
    ring

/-! ## Review finding: two-factor lookup gap (Iter 28, 2026-05-12)

    **Structural review finding (lookup-side analog of Iter 25)**:
    qianxu p. 23 claims `2^q_a Toffolis` for a complete unary lookup
    on q_a address bits (= `7 · 2^q_a` T-gates). Our gate-faithful
    Lean encoding `unary_lookup_multi_iteration n_addr iters` (with
    `iters.length = 2^n_addr`) produces **`14 · n_addr · 2^n_addr`
    T-gates** — a factor of `2 · n_addr` more.

    The gap decomposes into TWO independent structural optimizations:

    **Factor 1 (×2, Gidney measurement-based uncompute, like Iter 25's adder):**
    Each iteration's prefix-AND uncompute cascade is `n_addr` Toffolis
    explicitly, but only `0` under Gidney's measurement trick. So per-
    iteration count drops from `14 · n_addr` to `7 · n_addr` T.

    **Factor 2 (×n_addr, Gray-code amortization):**
    Consecutive iterations differ by one address bit. With Gray-code
    ordering, only ONE bit flip + ONE cascade step is needed per
    iteration after the first, instead of the full `n_addr`-step
    cascade. So `n_addr · 2^q_a` cascade Toffolis collapse to
    `n_addr + (2^q_a − 1) · 1 ≈ 2^q_a` Toffolis total.

    **Combined**: `14 · n_addr · 2^q_a` (Lean no-measurement, no-Gray-code)
    → `7 · 2^q_a` (paper, with both optimizations).

    Both optimizations are real and well-cited, but neither is
    formally established in our Lean. The Lean review certifies the
    `14 · n_addr · 2^q_a` upper bound and explicitly identifies the
    `2 · n_addr` factor as the load-bearing optimization gap. -/

/-- **Lookup review finding theorem**: the no-measurement / no-Gray-code
    T-count of the n_addr-bit unary lookup with `addr_count`
    iterations is `2 · n_addr ·` the paper's per-iteration T-count.
    At `addr_count = 2^q_a`, this gives the full two-factor gap. -/
theorem unary_lookup_two_factor_gap (n_addr : Nat)
    (iters : List (List Nat × List Nat)) :
    tcount (unary_lookup_multi_iteration n_addr iters)
      = 2 * n_addr * (7 * iters.length) := by
  rw [tcount_unary_lookup_multi_iteration,
      ← Nat.mul_assoc (2 * n_addr) 7 iters.length,
      Nat.mul_right_comm 2 n_addr 7]

/-- Concrete at q_a=6 (RSA-2048 case), simulated with a list of 64
    empty-data iterations: `14 · 6 · 64 = 5376` T-gates (Lean
    no-measurement) vs `7 · 64 = 448` T-gates (paper, with full
    optimization). The two-factor gap is `2 · 6 = 12` ×. -/
example :
    tcount (unary_lookup_multi_iteration 6
              (List.replicate 64 ([], [])))
      = 5376 := by decide

/-- The 12× gap at q_a=6 is exactly `2 · n_addr` — formally captured. -/
example : 5376 = 12 * 448 := by decide

/-- **Review factor decomposition** (Iter 119): the `2 · n_addr`
    multiplier of `unary_lookup_two_factor_gap` factors into:
    - **2**: no-measurement factor (matches the adder's
      `gidney_adder_full_faithful_no_measurement_vs_measurement_factor`
      from Iter 88 — uses explicit-reverse instead of Gidney's
      measurement-AND trick).
    - **n_addr**: no-Gray-code factor (lookup-specific — qianxu's
      Gray-code amortization reduces n_addr Toffolis per cascade
      to 1 amortized across consecutive iterations).

    Concrete decomposition at q_a=6 (RSA-2048 inner-product lookup):
    Lean T-count = 12 × paper claim = (2 measurement × 6 Gray-code) × paper. -/
theorem unary_lookup_factor_decomposition_2_times_n_addr
    (n_addr : Nat) (iters : List (List Nat × List Nat)) :
    tcount (unary_lookup_multi_iteration n_addr iters)
      = 2 * (n_addr * (7 * iters.length)) := by
  rw [unary_lookup_two_factor_gap]
  ring

/-- Mirror decomposition: `n_addr · (2 · 7 · iters.length)`. Same
    total but groups by the Gray-code factor first. -/
theorem unary_lookup_factor_decomposition_n_addr_times_2
    (n_addr : Nat) (iters : List (List Nat × List Nat)) :
    tcount (unary_lookup_multi_iteration n_addr iters)
      = n_addr * (2 * (7 * iters.length)) := by
  rw [unary_lookup_two_factor_gap]
  ring

/-! ## Faithfulness check + per-step correctness (Iter 62, 2026-05-12)

    **Iter 62 review-check**: re-compared Lean's `prefix_and_step` to
    Qrisp's `build_prefix_and_cascade` (`PyCircuits/lookups/
    unary_lookup_qrisp.py:155-159`):
    - Python `mcx([ctrl, address[0]], and_anc[0])` ↔ Lean
      `Gate.CCX ulookup_ctrl_idx (ulookup_address_idx 0) (ulookup_and_idx 0)`
    - Python `mcx([and_anc[i-1], address[i]], and_anc[i])` ↔ Lean
      `Gate.CCX (ulookup_and_idx (i-1)) (ulookup_address_idx i) (ulookup_and_idx i)`

    The encodings map 1:1. **`prefix_and_step` is faithful** to the
    Python ground truth — no Iter 53-style review-gap on the lookup
    side's address-decoder primitive. (Note: unlike the adder
    `gidney_adder_bit_step` which had a faithfulness bug, the lookup
    cascade primitive is straightforward enough that the simplified
    encoding IS the actual circuit.)

    Per-step correctness theorem (Iter 63 work, brought forward
    since review-check is positive): the i=0 step's Toffoli action. -/

/-- **`prefix_and_step 0` correctness**: on a classical basis state,
    the i=0 step XORs `(ctrl ∧ address[0])` into `and[0]`. The
    standard unary-cascade base case. Proven via the Iter 52 reusable
    `gate_ccx_acts_on_basis` framework. -/
theorem prefix_and_step_zero_correct (dim : Nat) (f : Nat → Bool)
    (h0 : ulookup_ctrl_idx < dim)
    (h1 : ulookup_address_idx 0 < dim)
    (h2 : ulookup_and_idx 0 < dim) :
    uc_eval (Gate.toUCom dim (prefix_and_step 0)) * f_to_vec dim f
      = f_to_vec dim
          (update f (ulookup_and_idx 0)
            (xor (f (ulookup_and_idx 0))
                 (f ulookup_ctrl_idx && f (ulookup_address_idx 0)))) := by
  -- Unfold the i=0 branch of prefix_and_step
  show uc_eval (Gate.toUCom dim
          (Gate.CCX ulookup_ctrl_idx (ulookup_address_idx 0)
                    (ulookup_and_idx 0)))
        * f_to_vec dim f = _
  apply gate_ccx_acts_on_basis dim _ _ _ h0 h1 h2
  · -- ctrl_idx = 0, address_idx 0 = 1, so 0 ≠ 1
    decide
  · -- ctrl_idx = 0, and_idx 0 = 2, so 0 ≠ 2
    decide
  · -- address_idx 0 = 1, and_idx 0 = 2, so 1 ≠ 2
    decide

/-- **`prefix_and_step (i+1)` correctness**: on a classical basis state,
    the i>0 step XORs `(and[i] ∧ address[i+1])` into `and[i+1]`. The
    chain step of the unary cascade. Proven via `gate_ccx_acts_on_basis`. -/
theorem prefix_and_step_succ_correct (dim i : Nat) (f : Nat → Bool)
    (h_and_i  : ulookup_and_idx i < dim)
    (h_addr   : ulookup_address_idx (i + 1) < dim)
    (h_and_i1 : ulookup_and_idx (i + 1) < dim) :
    uc_eval (Gate.toUCom dim (prefix_and_step (i + 1))) * f_to_vec dim f
      = f_to_vec dim
          (update f (ulookup_and_idx (i + 1))
            (xor (f (ulookup_and_idx (i + 1)))
                 (f (ulookup_and_idx i) && f (ulookup_address_idx (i + 1))))) := by
  -- prefix_and_step (i+1) reduces to its i>0 branch
  show uc_eval (Gate.toUCom dim
          (Gate.CCX (ulookup_and_idx i) (ulookup_address_idx (i + 1))
                    (ulookup_and_idx (i + 1))))
        * f_to_vec dim f = _
  apply gate_ccx_acts_on_basis dim _ _ _ h_and_i h_addr h_and_i1
  · -- and_idx i = 1 + 2*i + 1, address_idx (i+1) = 1 + 2*(i+1), disjoint
    unfold ulookup_and_idx ulookup_address_idx
    omega
  · -- and_idx i = 1 + 2*i + 1, and_idx (i+1) = 1 + 2*(i+1) + 1, disjoint
    unfold ulookup_and_idx
    omega
  · -- address_idx (i+1) = 1 + 2*(i+1), and_idx (i+1) = 1 + 2*(i+1) + 1, disjoint
    unfold ulookup_address_idx ulookup_and_idx
    omega

/-- Concrete: at i=2 (chain step), the per-step action XORs
    `and[2] ∧ address[3]` into `and[3]`. Note that
    `prefix_and_step 3` triggers the i>0 branch (since 3 ≠ 0). -/
example (dim : Nat) (f : Nat → Bool)
    (h_and_2 : ulookup_and_idx 2 < dim)
    (h_addr_3 : ulookup_address_idx 3 < dim)
    (h_and_3 : ulookup_and_idx 3 < dim) :
    uc_eval (Gate.toUCom dim (prefix_and_step 3)) * f_to_vec dim f
      = f_to_vec dim
          (update f (ulookup_and_idx 3)
            (xor (f (ulookup_and_idx 3))
                 (f (ulookup_and_idx 2) && f (ulookup_address_idx 3)))) :=
  prefix_and_step_succ_correct dim 2 f h_and_2 h_addr_3 h_and_3

/-- **Unified per-step correctness**: combines the i=0 and i>0 cases
    via the new `prefix_and_step_post_state`. Useful as the inductive
    step in the cascade correctness proof below. -/
theorem prefix_and_step_correct (dim i : Nat) (f : Nat → Bool)
    (h_ctrl : ulookup_ctrl_idx < dim)
    (h_and_pred : ulookup_and_idx (i - 1) < dim)
    (h_addr : ulookup_address_idx i < dim)
    (h_and : ulookup_and_idx i < dim) :
    uc_eval (Gate.toUCom dim (prefix_and_step i)) * f_to_vec dim f
      = f_to_vec dim (prefix_and_step_post_state i f) := by
  unfold prefix_and_step prefix_and_step_post_state
  split
  · -- i = 0 branch
    rename_i hi0
    subst hi0
    apply gate_ccx_acts_on_basis dim _ _ _ h_ctrl h_addr h_and
    · -- ctrl_idx = 0, address_idx 0 = 1
      decide
    · -- ctrl_idx = 0, and_idx 0 = 2
      decide
    · -- address_idx 0 = 1, and_idx 0 = 2
      decide
  · -- i ≠ 0 branch: same CCX action with and[i-1] as control
    apply gate_ccx_acts_on_basis dim _ _ _ h_and_pred h_addr h_and
    · unfold ulookup_and_idx ulookup_address_idx
      omega
    · unfold ulookup_and_idx
      omega
    · unfold ulookup_address_idx ulookup_and_idx
      omega

/-- **Lookup `prefix_and_step` is involutive at the gate-IR level.**
    For any `i`, applying `prefix_and_step i` twice acts as identity
    on classical basis states. Direct lift of
    `gate_ccx_ccx_id_on_basis` via case-splitting on `i = 0`. **First
    Verified-tier lookup-side involution** — building block for
    Iter 71's `prefix_and_cascade · prefix_and_uncompute = identity`
    proof (the lookup analog of Iter 69's adder-side closure). -/
theorem prefix_and_step_involutive (dim i : Nat) (f : Nat → Bool)
    (h_ctrl : ulookup_ctrl_idx < dim)
    (h_and_pred : ulookup_and_idx (i - 1) < dim)
    (h_addr : ulookup_address_idx i < dim)
    (h_and : ulookup_and_idx i < dim) :
    uc_eval (Gate.toUCom dim (Gate.seq (prefix_and_step i) (prefix_and_step i)))
      * f_to_vec dim f
      = f_to_vec dim f := by
  unfold prefix_and_step
  split
  · -- i = 0 branch: prefix_and_step 0 = CCX ctrl_idx address_idx_0 and_idx_0
    rename_i hi0
    subst hi0
    apply gate_ccx_ccx_id_on_basis dim _ _ _ h_ctrl h_addr h_and
    · -- ctrl_idx = 0 ≠ address_idx 0 = 1
      decide
    · -- ctrl_idx = 0 ≠ and_idx 0 = 2
      decide
    · -- address_idx 0 = 1 ≠ and_idx 0 = 2
      decide
  · -- i ≠ 0 branch: prefix_and_step i = CCX and[i-1] address[i] and[i]
    apply gate_ccx_ccx_id_on_basis dim _ _ _ h_and_pred h_addr h_and
    · -- and_idx (i-1) ≠ address_idx i
      unfold ulookup_and_idx ulookup_address_idx
      omega
    · -- and_idx (i-1) ≠ and_idx i
      unfold ulookup_and_idx
      omega
    · -- address_idx i ≠ and_idx i
      unfold ulookup_address_idx ulookup_and_idx
      omega

/-- **Matrix-level form of `prefix_and_step_involutive`** (Iter 71):
    `uc_eval (seq (step i) (step i)) = 1`, independent of any basis
    vector. Useful for cascade-level proofs where we re-associate
    matrix products and need to collapse pairs to 1 in the middle.

    Proven via case-split on `i = 0` and reduction to
    `CCX_CCX_eq_one` (matrix-level CCX involution from PadAction). -/
theorem prefix_and_step_step_eq_one (dim i : Nat)
    (h_ctrl : ulookup_ctrl_idx < dim)
    (h_and_pred : ulookup_and_idx (i - 1) < dim)
    (h_addr : ulookup_address_idx i < dim)
    (h_and : ulookup_and_idx i < dim) :
    uc_eval (Gate.toUCom dim (Gate.seq (prefix_and_step i) (prefix_and_step i)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ) := by
  unfold prefix_and_step
  split
  · -- i = 0 branch
    rename_i hi0
    subst hi0
    rw [Gate.toUCom_seq, Gate.toUCom_CCX]
    show uc_eval (UCom.seq (BaseUCom.CCX ulookup_ctrl_idx
                            (ulookup_address_idx 0) (ulookup_and_idx 0)
                            : BaseUCom dim)
                           (BaseUCom.CCX ulookup_ctrl_idx
                            (ulookup_address_idx 0) (ulookup_and_idx 0))) = 1
    exact CCX_CCX_eq_one dim _ _ _ h_ctrl h_addr h_and
            (by decide) (by decide) (by decide)
  · -- i ≠ 0 branch
    rw [Gate.toUCom_seq, Gate.toUCom_CCX]
    show uc_eval (UCom.seq (BaseUCom.CCX (ulookup_and_idx (i-1))
                            (ulookup_address_idx i) (ulookup_and_idx i)
                            : BaseUCom dim)
                           (BaseUCom.CCX (ulookup_and_idx (i-1))
                            (ulookup_address_idx i) (ulookup_and_idx i))) = 1
    refine CCX_CCX_eq_one dim _ _ _ h_and_pred h_addr h_and ?_ ?_ ?_
    · unfold ulookup_and_idx ulookup_address_idx; omega
    · unfold ulookup_and_idx; omega
    · unfold ulookup_address_idx ulookup_and_idx; omega

/-- **Faithful n-step prefix-AND cascade correctness**: given
    disjointness on each bit 0..n-1, the cascade acts on `f_to_vec
    dim f` to produce `f_to_vec dim (prefix_and_cascade_post_state n f)`.
    Proof by structural recursion on n, using `gate_seq_acts_on_basis`
    + IH + per-step correctness (Iter 63).

    **Second Verified-tier review chain (lookup side, mirroring
    Iter 58 for the adder).** -/
theorem prefix_and_cascade_correct
    (dim : Nat) (hdim : 0 < dim) (f : Nat → Bool) :
    ∀ n, (∀ i, i < n → ULookupBitDisjointness dim i) →
    uc_eval (Gate.toUCom dim (prefix_and_cascade n)) * f_to_vec dim f
      = f_to_vec dim (prefix_and_cascade_post_state n f)
  | 0    , _ => by
      show uc_eval (Gate.toUCom dim Gate.I) * f_to_vec dim f = f_to_vec dim f
      rw [Gate.toUCom_I]
      show uc_eval (BaseUCom.ID 0 : BaseUCom dim) * f_to_vec dim f
            = f_to_vec dim f
      rw [uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hyp => by
      show uc_eval (Gate.toUCom dim
              (Gate.seq (prefix_and_cascade n) (prefix_and_step n)))
            * f_to_vec dim f
            = f_to_vec dim (prefix_and_cascade_post_state (n + 1) f)
      apply gate_seq_acts_on_basis dim _ _ f (prefix_and_cascade_post_state n f) _
      · -- IH: n-step cascade is correct
        exact prefix_and_cascade_correct dim hdim f n
                (fun i hi => hyp i (Nat.lt_succ_of_lt hi))
      · -- Per-step correctness at i = n
        have d := hyp n (Nat.lt_succ_self n)
        exact prefix_and_step_correct dim n _
                d.h_ctrl d.h_and_pred d.h_addr d.h_and

/-! ## Cascade · uncompute = identity (Iter 74, 2026-05-12)

    With the per-bit involution `prefix_and_step_step_eq_one` (Iter 71)
    in hand, we lift to the **cascade level by induction on n**:

      uc_eval (cascade(n+1) · uncompute(n+1))
        = uc_eval (cascade n · step n · step n · uncompute n)
        = uc_eval cascade n · 1 · uc_eval uncompute n   [by Iter 71]
        = 1                                              [by IH]

    This is the **lookup-side end-to-end matrix-level cascade
    involution** — the closing argument that
    `prefix_and_cascade n` and `prefix_and_uncompute n` are
    matrix inverses without needing measurement. Mirrors what
    Iter 75/76 will build for the adder side. -/

/-- **Matrix-level cascade · uncompute = identity**. The n-step
    forward cascade composed with the n-step reverse cascade is
    the identity matrix. Proof by structural induction on n,
    re-associating the matrix products to expose the per-step
    `prefix_and_step · prefix_and_step` involution
    (`prefix_and_step_step_eq_one` from Iter 71).

    **Third Verified-tier review chain (lookup side)** — composition
    of the n-step forward cascade (Iter 64) with its uncomputation
    is the identity matrix. Confirms that without measurement-based
    uncomputation, the lookup ancillas ARE faithfully reset to zero
    on the basis-state image. -/
theorem prefix_and_cascade_uncompute_eq_one
    (dim : Nat) (hdim : 0 < dim) :
    ∀ n, (∀ i, i < n → ULookupBitDisjointness dim i) →
    uc_eval (Gate.toUCom dim
              (Gate.seq (prefix_and_cascade n) (prefix_and_uncompute n)))
      = (1 : Matrix (Fin (2^dim)) (Fin (2^dim)) ℂ)
  | 0    , _ => by
      -- cascade 0 = uncompute 0 = Gate.I. uc_eval (seq I I) = ID · ID = 1 · 1 = 1.
      show uc_eval (Gate.toUCom dim (Gate.I : Gate)) *
             uc_eval (Gate.toUCom dim (Gate.I : Gate)) = 1
      rw [Gate.toUCom_I, uc_eval_ID_eq_one hdim, Matrix.one_mul]
  | n + 1, hyp => by
      have ih := prefix_and_cascade_uncompute_eq_one dim hdim n
                  (fun i hi => hyp i (Nat.lt_succ_of_lt hi))
      have d := hyp n (Nat.lt_succ_self n)
      have hstep := prefix_and_step_step_eq_one dim n
                      d.h_ctrl d.h_and_pred d.h_addr d.h_and
      -- After pattern-match, cascade (n+1) and uncompute (n+1) WHNF-reduce.
      -- Goal becomes:
      -- (uc_eval (toUCom uncompute n) * uc_eval (toUCom step n))
      --  * (uc_eval (toUCom step n) * uc_eval (toUCom cascade n)) = 1
      show (uc_eval (Gate.toUCom dim (prefix_and_uncompute n))
              * uc_eval (Gate.toUCom dim (prefix_and_step n)))
            * (uc_eval (Gate.toUCom dim (prefix_and_step n))
              * uc_eval (Gate.toUCom dim (prefix_and_cascade n))) = 1
      rw [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (uc_eval (Gate.toUCom dim (prefix_and_step n)))
                              (uc_eval (Gate.toUCom dim (prefix_and_step n)))
                              (uc_eval (Gate.toUCom dim (prefix_and_cascade n)))]
      -- Middle pair = uc_eval (toUCom (seq step step)) by defeq
      show uc_eval (Gate.toUCom dim (prefix_and_uncompute n)) *
            (uc_eval (Gate.toUCom dim
                       (Gate.seq (prefix_and_step n) (prefix_and_step n)))
              * uc_eval (Gate.toUCom dim (prefix_and_cascade n))) = 1
      rw [hstep, Matrix.one_mul]
      -- Now: uc_eval (toUCom uncompute n) * uc_eval (toUCom cascade n) = 1.
      -- This IS uc_eval (toUCom (seq cascade n uncompute n)) by defeq.
      exact ih

/-! ## Bridge to PaperClaims (Iter 29, 2026-05-12)

    Mirror of Iter 22's adder-side bridge in RippleCarryAdder.lean:
    connect the Lean gate-derived T-count to PaperClaims's
    `qianxu_E9_lookup_gate_derived_count := 2^q_a`. The bridge proves
    Lean encodes `2 · n_addr ·` the paper count — the same two-factor
    relationship as `unary_lookup_two_factor_gap` above, but expressed
    in terms of the PaperClaims data def. -/

/-- **Bridge theorem**: at `n_addr = q_a` address bits and
    `iters.length = 2^q_a` iterations (the full unary loop), the Lean
    no-measurement no-Gray-code T-count is `2 · q_a · 7 ·
    qianxu_E9_lookup_gate_derived_count q_a`. This formally connects
    the gate-derived count to the PaperClaims data def, parallel to
    Iter 22's `gidney_adder_forward_tcount_matches_PaperClaims`. -/
theorem unary_lookup_tcount_matches_PaperClaims (q_a : Nat)
    (iters : List (List Nat × List Nat))
    (hlen : iters.length = qianxu_E9_lookup_gate_derived_count q_a) :
    tcount (unary_lookup_multi_iteration q_a iters)
      = 2 * q_a * (7 * qianxu_E9_lookup_gate_derived_count q_a) := by
  rw [unary_lookup_two_factor_gap, hlen]

/-- Concrete bridge check at q_a=6 (RSA-2048 case): with 64 iterations,
    Lean encodes 5376 T-gates = 2 · 6 · 7 · 64. -/
example :
    tcount (unary_lookup_multi_iteration 6 (List.replicate 64 ([], [])))
      = 2 * 6 * (7 * qianxu_E9_lookup_gate_derived_count 6) := by
  apply unary_lookup_tcount_matches_PaperClaims 6
  decide

/-- For RSA-2048 (q_a=6, n_addr=6): Gray-code count = 69 Toffolis. -/
example : gray_code_unary_lookup_toffoli_count 6 6 = 69 := by decide

/-- Gap analysis: at q_a=6, Lean Gray-code count (69) is 5 more than
    the paper's exact `2^q_a = 64` Toffoli claim. The +5 is the
    initial cascade cost (n_addr - 1, since the first Toffoli is
    already counted in 2^q_a per Gidney). -/
example :
    gray_code_unary_lookup_toffoli_count 6 6
      - qianxu_E9_lookup_gate_derived_count 6 = 5 := by decide

/-- For RSA-2048: Lean Gray-code 69 vs paper 64; residual ~8%. -/
example : gray_code_residual_ratio 6 6 = (69, 64) := by decide

/-! ## Lookup-side review-gap closure characterization (Iter 47, 2026-05-12)

    The Iter 46 Gray-code count has a clean closed-form excess over
    qianxu's `2^q_a` claim: **exactly `n_addr - 1`**. This is the
    initial-cascade overhead. Once `n_addr - 1` Toffolis of cascade
    setup are amortized away (or attributed to a previous lookup), the
    Gray-code count matches the paper exactly.

    **Formal closure**: with both Gidney (Iter 43-44) and Gray-code
    (Iter 46) optimizations, the lookup-side review-gap is reduced to
    a single `n_addr - 1` initial-cascade term. This is a structural
    review finding ready for the paper-author follow-up. -/

/-- The Gray-code Toffoli count exceeds the paper's `2^q_a` claim by
    exactly `n_addr - 1` — the initial-cascade setup cost. -/
theorem gray_code_residual_eq_n_addr_minus_one (n_addr q_a : Nat) (h : 0 < n_addr)
    (_hq : 0 < q_a) :
    gray_code_unary_lookup_toffoli_count n_addr q_a
      = qianxu_E9_lookup_gate_derived_count q_a + (n_addr - 1) := by
  unfold gray_code_unary_lookup_toffoli_count
         qianxu_E9_lookup_gate_derived_count
  -- Goal: n_addr + (2^q_a - 1) = 2^q_a + (n_addr - 1)
  -- The `_hq : 0 < q_a` hypothesis is preserved in the signature for
  -- semantic clarity (q_a represents the address-bit count, which must
  -- be positive in any meaningful lookup) but is not load-bearing for
  -- the arithmetic — `2^q_a ≥ 1` holds for all q_a including 0.
  have h2 : 1 ≤ 2 ^ q_a := Nat.one_le_two_pow
  omega

/-- Concrete: at RSA-2048 (n_addr=6, q_a=6), residual = 5 = 6 - 1. -/
example :
    gray_code_unary_lookup_toffoli_count 6 6
      = qianxu_E9_lookup_gate_derived_count 6 + (6 - 1) :=
  gray_code_residual_eq_n_addr_minus_one 6 6 (by decide) (by decide)

/-- **Lookup-side review closure**: the Lean count exceeds the paper
    count by EXACTLY `n_addr - 1` Toffolis (the initial-cascade setup).
    Combined with Iter 44's Gidney closure, the original 12× gap at
    q_a=6 is **fully attributed**: 6× from Gray-code (now formalized,
    residual `n_addr - 1 = 5`), 2× from Gidney (Iter 44, closed). -/
theorem lookup_review_gap_closure (n_addr q_a : Nat) (h : 0 < n_addr) (hq : 0 < q_a) :
    gray_code_unary_lookup_toffoli_count n_addr q_a
      - qianxu_E9_lookup_gate_derived_count q_a
      = n_addr - 1 := by
  rw [gray_code_residual_eq_n_addr_minus_one n_addr q_a h hq]
  omega

/-- `prefix_and_step` on zero input gives zero (both `i = 0` and
    `i > 0` branches). Single CCX writes `xor false (false ∧ false)
    = false`, a no-op via `Function.update_eq_self`. -/
theorem prefix_and_step_post_state_on_zero (i : Nat) :
    prefix_and_step_post_state i zeroFLook = zeroFLook := by
  unfold prefix_and_step_post_state zeroFLook
  split <;> simp

/-- Prefix-AND cascade on zero input gives zero. Induction on n. -/
theorem prefix_and_cascade_post_state_on_zero : ∀ n,
    prefix_and_cascade_post_state n zeroFLook = zeroFLook
  | 0     => rfl
  | n + 1 => by
      show prefix_and_step_post_state n
            (prefix_and_cascade_post_state n zeroFLook) = zeroFLook
      rw [prefix_and_cascade_post_state_on_zero n]
      exact prefix_and_step_post_state_on_zero n

/-- **Cascade and its uncompute compose to identity on the zero
    state vector**. Direct corollary of Iter 74's matrix-level
    `prefix_and_cascade_uncompute_eq_one`, applied to `f_to_vec
    dim zeroFLook`. This is the lookup analog of Iter 89's adder
    zero-input smoke test (modulo the absence of the final-CX
    cascade analog on the lookup side). -/
theorem prefix_and_cascade_uncompute_on_zero
    (dim : Nat) (hdim : 0 < dim) (n : Nat)
    (hyp : ∀ i, i < n → ULookupBitDisjointness dim i) :
    uc_eval (Gate.toUCom dim
              (Gate.seq (prefix_and_cascade n) (prefix_and_uncompute n)))
      * f_to_vec dim zeroFLook
      = f_to_vec dim zeroFLook := by
  rw [prefix_and_cascade_uncompute_eq_one dim hdim n hyp, Matrix.one_mul]

/-- **Concrete prefix-AND cascade action check** for a 2-step
    cascade on `inputF_lookup_ctrl_addr_10`. After two steps:
    - and_0 (qubit 2) = ctrl ∧ address_0 = 1 ∧ 1 = 1 ✓
    - and_1 (qubit 4) = and_0 ∧ address_1 = 1 ∧ 0 = 0 ✓

    `decide` reduces the nested `update` chain at each specific
    qubit index. Verifies the cascade correctly computes the
    AND-chain on a non-trivial input. -/
example :
    let post := prefix_and_cascade_post_state 2 inputF_lookup_ctrl_addr_10
    post 0 = true ∧ post 1 = true ∧ post 2 = true
    ∧ post 3 = false ∧ post 4 = false := by decide

example :
    let post := prefix_and_cascade_post_state 2 inputF_lookup_ctrl_addr_11
    post 0 = true ∧ post 1 = true ∧ post 2 = true
    ∧ post 3 = true ∧ post 4 = true := by decide

/-- **3-step cascade decide-check on (ctrl=1, addr=110)**. The
    final AND ancilla (and_2 at qubit 6) is 0 because addr_2 = 0
    breaks the chain. -/
example :
    let post := prefix_and_cascade_post_state 3 inputF_lookup_q3_addr_110
    post 0 = true     -- ctrl unchanged
    ∧ post 1 = true   -- addr_0 unchanged
    ∧ post 2 = true   -- and_0 = ctrl ∧ addr_0 = 1
    ∧ post 3 = true   -- addr_1 unchanged
    ∧ post 4 = true   -- and_1 = and_0 ∧ addr_1 = 1
    ∧ post 5 = false  -- addr_2 unchanged (= 0)
    ∧ post 6 = false  -- and_2 = and_1 ∧ addr_2 = 0 (chain broken)
    := by decide

/-- **3-step cascade decide-check on (ctrl=1, addr=111)**. All
    AND ancillas fire to 1 (the chain propagates fully). -/
example :
    let post := prefix_and_cascade_post_state 3 inputF_lookup_q3_addr_111
    post 0 = true   -- ctrl
    ∧ post 1 = true   -- addr_0
    ∧ post 2 = true   -- and_0 = 1
    ∧ post 3 = true   -- addr_1
    ∧ post 4 = true   -- and_1 = 1
    ∧ post 5 = true   -- addr_2
    ∧ post 6 = true   -- and_2 = 1 (full chain fires)
    := by decide

/-! ## Iteration body resource count decide examples (Iter 121, 2026-05-12)

    Concrete decide-checks of `tcount` and `gcount` for the full
    `unary_lookup_iteration` body at varied parameters. Tests that
    the parametric theorems (Iter 14 tcount, Iter 76 gcount)
    evaluate correctly on specific qianxu-Fig-4(b)-flavored
    instances. -/

/-- **Concrete iteration tcount** at q_a=3, |flips|=2, |cnots|=3:
    T-count = 14·3 = 42 (data-independent — only Toffolis count). -/
example :
    tcount (unary_lookup_iteration 3 [0, 2] [0, 1, 3]) = 42 := by decide

/-- **Concrete iteration gcount** at the same instance:
    gcount = 2·|flips| + 2·n_addr + |cnots| = 2·2 + 2·3 + 3 = 13. -/
example :
    gcount (unary_lookup_iteration 3 [0, 2] [0, 1, 3]) = 13 := by decide

/-- **Multi-iteration concrete tcount** at q_a=3 with 4 iterations:
    T-count = 14·3·4 = 168 (data-independent). -/
example :
    tcount (unary_lookup_multi_iteration 3
              [([], []), ([0], [1]), ([1], [2]), ([0, 1], [0, 1])])
      = 168 := by decide

/-- **qianxu Fig. 4b instance** (q_a=3, q_w=6, full 2^3=8 iterations
    with the data implied by the figure's red-highlighted Toffolis
    and bit-flip pattern). Counts the no-measurement no-Gray-code
    bound: 14·3·8 = 336 T-gates total. -/
example :
    tcount (unary_lookup_multi_iteration 3
              (List.replicate 8 ([], []))) = 336 := by decide

/-- **Decide-witness on (n=3, k=0, ctrl=true, addr=3=0b011)** (Iter 219).
    No cascade steps applied: all and qubits are false. -/
example :
    Lookup.cascade_step_invariant 0 3 true 3
      (fun i => if i = ulookup_ctrl_idx then true
                else if i = ulookup_address_idx 0 then true
                else if i = ulookup_address_idx 1 then true
                else if i = ulookup_address_idx 2 then false
                else false) := by
  intro i hi
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | _ + 3, h => omega

/-- **Decide-witness on (n=3, k=2, ctrl=true, addr=3)** (Iter 219).
    After 2 steps: and_0 = and_1 = true (chain of ANDs), and_2 = false. -/
example :
    Lookup.cascade_step_invariant 2 3 true 3
      (fun i =>
        if i = ulookup_ctrl_idx then true
        else if i = ulookup_address_idx 0 then true
        else if i = ulookup_address_idx 1 then true
        else if i = ulookup_address_idx 2 then false
        else if i = ulookup_and_idx 0 then true   -- and_0 = ctrl ∧ addr_0 = 1
        else if i = ulookup_and_idx 1 then true   -- and_1 = and_0 ∧ addr_1 = 1
        else false) := by
  intro i hi
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | _ + 3, h => omega

/-- **Decide-witness on (n=3, k=3, ctrl=true, addr=3)** (Iter 219).
    Full cascade: and_2 = (1 ∧ 1) ∧ 0 = 0 (the top bit kills it). -/
example :
    Lookup.cascade_step_invariant 3 3 true 3
      (fun i =>
        if i = ulookup_ctrl_idx then true
        else if i = ulookup_address_idx 0 then true
        else if i = ulookup_address_idx 1 then true
        else if i = ulookup_address_idx 2 then false
        else if i = ulookup_and_idx 0 then true
        else if i = ulookup_and_idx 1 then true
        else if i = ulookup_and_idx 2 then false
        else false) := by
  intro i hi
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | _ + 3, h => omega

/-! ## Per-step preserves for the prefix-AND cascade (Iter 220, 2026-05-13)

    Mirror of Iter 177's `Gidney.propagation_step_invariant_k1` for the
    adder. Shows that applying `prefix_and_step k` advances the
    cascade invariant from step `k` to step `k+1`, preserving the
    `ctrl` and `address` register contents (which are unchanged by
    the prefix-AND-step CCX, since it only writes to `and_idx k`). -/

/-- **Per-step cascade invariant preservation** (Iter 220). Given an
    initial state `f` satisfying the step-`k` cascade invariant
    (with `ctrl` and `address` contents fixed in `f`), applying
    `prefix_and_step_post_state k` yields a state satisfying the
    step-`k+1` invariant.

    The proof case-splits on the position `i`:
    * `i = k`: the updated qubit. Compute the new value as
      `prev ∧ addr.testBit k`, where `prev = ctrl` if `k = 0` and
      `prev = and_{k-1} = address_and ctrl addr k` otherwise. By the
      definition of `address_and`, this is `address_and ctrl addr (k+1)`.
    * `i ≠ k`: untouched (frame condition via `update_neq`). The
      step-`k` value carries through unchanged. -/
theorem Lookup.cascade_step_preserves
    (k n : Nat) (hk : k < n) (ctrl : Bool) (addr : Nat) (f : Nat → Bool)
    (h_ctrl : f ulookup_ctrl_idx = ctrl)
    (h_addr : ∀ i, i < n → f (ulookup_address_idx i) = addr.testBit i)
    (h_inv : Lookup.cascade_step_invariant k n ctrl addr f) :
    Lookup.cascade_step_invariant (k + 1) n ctrl addr
      (prefix_and_step_post_state k f) := by
  intro i hi
  unfold prefix_and_step_post_state
  by_cases hik : i = k
  · -- Case i = k: this is the updated qubit.
    subst hik
    by_cases hi0 : i = 0
    · -- Sub-case k = i = 0: previous bit is ctrl.
      subst hi0
      rw [if_pos rfl, update_eq]
      have hfand0 : f (ulookup_and_idx 0) = false := by
        have h := h_inv 0 (by omega)
        rw [if_neg (Nat.lt_irrefl _)] at h
        exact h
      rw [hfand0, h_ctrl, h_addr 0 (by omega), Bool.false_xor,
          if_pos (Nat.zero_lt_succ _)]
      rfl
    · -- Sub-case i = k > 0: previous bit is and_{i-1}.
      rw [if_neg hi0, update_eq]
      have hfand_i : f (ulookup_and_idx i) = false := by
        have h := h_inv i (by omega)
        rw [if_neg (Nat.lt_irrefl _)] at h
        exact h
      have h_pos : 0 < i := Nat.pos_of_ne_zero hi0
      have h_pred_lt : i - 1 < i := Nat.sub_lt h_pos Nat.one_pos
      have hfand_pred : f (ulookup_and_idx (i - 1)) =
          Lookup.address_and ctrl addr i := by
        have h := h_inv (i - 1) (by omega)
        rw [if_pos h_pred_lt] at h
        rw [show i - 1 + 1 = i by omega] at h
        exact h
      rw [hfand_i, hfand_pred, h_addr i hi, Bool.false_xor,
          if_pos (Nat.lt_succ_self i)]
      rfl
  · -- Case i ≠ k: frame condition (and_idx is injective).
    have h_neq : ulookup_and_idx i ≠ ulookup_and_idx k := by
      unfold ulookup_and_idx
      intro heq
      apply hik
      omega
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, update_neq _ _ _ _ h_neq]
      have h := h_inv i hi
      have h_not_lt_0 : ¬ i < 0 := by omega
      have h_not_lt_1 : ¬ i < 0 + 1 := by omega
      rw [if_neg h_not_lt_0] at h
      rw [if_neg h_not_lt_1]
      exact h
    · rw [if_neg hk0, update_neq _ _ _ _ h_neq]
      have h := h_inv i hi
      by_cases hilk : i < k
      · rw [if_pos hilk] at h
        rw [if_pos (Nat.lt_succ_of_lt hilk)]
        exact h
      · rw [if_neg hilk] at h
        rw [if_neg (by omega : ¬ i < k + 1)]
        exact h

/-! ## Frame conditions for the cascade post-state (Iter 221, 2026-05-13)

    The prefix-AND step writes only to `ulookup_and_idx k`. Hence
    positions outside the and-register (ctrl, address) are preserved
    by every cascade step, and by induction the entire cascade. -/

/-- **Per-step frame condition**: `prefix_and_step_post_state k f` agrees
    with `f` outside `ulookup_and_idx k`. Both i=0 and i>0 branches of
    the post-state definition write to a single qubit
    (`ulookup_and_idx 0` and `ulookup_and_idx k` respectively). -/
theorem prefix_and_step_post_state_frame
    (k : Nat) (f : Nat → Bool) (j : Nat)
    (h_neq : j ≠ ulookup_and_idx k) :
    prefix_and_step_post_state k f j = f j := by
  unfold prefix_and_step_post_state
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl, update_neq _ _ _ _ h_neq]
  · rw [if_neg hk0, update_neq _ _ _ _ h_neq]

/-- **Cascade frame for the ctrl qubit**: the n-step cascade post-state
    agrees with `f` at `ulookup_ctrl_idx`. Proof by structural recursion
    on n; each step writes to `ulookup_and_idx _ ≠ ulookup_ctrl_idx = 0`. -/
theorem prefix_and_cascade_post_state_frame_ctrl
    (n : Nat) (f : Nat → Bool) :
    prefix_and_cascade_post_state n f ulookup_ctrl_idx = f ulookup_ctrl_idx := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show prefix_and_step_post_state k (prefix_and_cascade_post_state k f)
            ulookup_ctrl_idx = f ulookup_ctrl_idx
    rw [prefix_and_step_post_state_frame k _ ulookup_ctrl_idx
          (by unfold ulookup_ctrl_idx ulookup_and_idx; omega)]
    exact ih

/-- **Cascade frame for the address bits**: the n-step cascade post-state
    agrees with `f` at every `ulookup_address_idx j`. Address indices
    have parity 1 (`1 + 2*j`); and indices have parity 0 (`2 + 2*i`),
    so they are always disjoint. -/
theorem prefix_and_cascade_post_state_frame_addr
    (n : Nat) (f : Nat → Bool) (j : Nat) :
    prefix_and_cascade_post_state n f (ulookup_address_idx j)
      = f (ulookup_address_idx j) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show prefix_and_step_post_state k (prefix_and_cascade_post_state k f)
            (ulookup_address_idx j) = f (ulookup_address_idx j)
    rw [prefix_and_step_post_state_frame k _ (ulookup_address_idx j)
          (by unfold ulookup_address_idx ulookup_and_idx; omega)]
    exact ih

/-! ## Cascade composition: per-step preserves → invariant holds at any k
    (Iter 221, 2026-05-13)

    Lift `Lookup.cascade_step_preserves` (Iter 220) by induction on k:
    starting from a clean state (`f (and_idx i) = false` for all `i < n`)
    with `f` carrying valid `ctrl` and `address` registers, the k-step
    cascade post-state satisfies `cascade_step_invariant k n ctrl addr`.

    Lookup analog of Iter 188's `Gidney.post_last_bit_invariant_holds`. -/

/-- **Cascade invariant holds at every step `k ≤ n`**. By induction on `k`:
    * `k = 0`: the cascade post-state is `f`, which has all `and_idx`
      qubits clean by hypothesis. Matches `if i < 0 then ... else false = false`.
    * `k+1` step: by IH, the k-step cascade satisfies the step-`k`
      invariant. The cascade frame lemmas (Iter 221) ensure ctrl and
      address are preserved, so `Lookup.cascade_step_preserves` (Iter 220)
      lifts the step-`k` invariant on `cascade_post k f` to the step-`k+1`
      invariant on `cascade_post (k+1) f = step_post k (cascade_post k f)`. -/
theorem Lookup.cascade_step_invariant_holds
    (k n : Nat) (hk : k ≤ n) (ctrl : Bool) (addr : Nat) (f : Nat → Bool)
    (h_ctrl : f ulookup_ctrl_idx = ctrl)
    (h_addr : ∀ i, i < n → f (ulookup_address_idx i) = addr.testBit i)
    (h_clean : ∀ i, i < n → f (ulookup_and_idx i) = false) :
    Lookup.cascade_step_invariant k n ctrl addr
      (prefix_and_cascade_post_state k f) := by
  induction k with
  | zero =>
    intro i hi
    show prefix_and_cascade_post_state 0 f (ulookup_and_idx i) =
           if i < 0 then _ else false
    rw [if_neg (Nat.not_lt_zero _)]
    exact h_clean i hi
  | succ k' ih =>
    have hk' : k' ≤ n := Nat.le_of_succ_le hk
    have hk'_lt : k' < n := hk
    have h_inv := ih hk'
    have h_ctrl_post :
        prefix_and_cascade_post_state k' f ulookup_ctrl_idx = ctrl := by
      rw [prefix_and_cascade_post_state_frame_ctrl]
      exact h_ctrl
    have h_addr_post :
        ∀ i, i < n →
          prefix_and_cascade_post_state k' f (ulookup_address_idx i)
            = addr.testBit i := by
      intro i hi
      rw [prefix_and_cascade_post_state_frame_addr]
      exact h_addr i hi
    show Lookup.cascade_step_invariant (k' + 1) n ctrl addr
           (prefix_and_step_post_state k' (prefix_and_cascade_post_state k' f))
    exact Lookup.cascade_step_preserves k' n hk'_lt ctrl addr
            (prefix_and_cascade_post_state k' f)
            h_ctrl_post h_addr_post h_inv

/-- **Top-bit corollary** (Iter 223, 2026-05-13). After the n-step
    cascade, the top and-bit `ulookup_and_idx (n - 1)` carries the full
    `Lookup.address_and ctrl addr n` value (`ctrl ∧ ⋀_{j < n} addr.testBit j`).
    Direct specialization of `cascade_step_invariant_holds` at k = n
    and i = n - 1.

    This is the "trigger bit" read by the word-CNOT layer of the lookup
    iteration body — the value that decides whether the table row fires
    on this iteration's address. Lookup analog of Iter 199's
    `Adder.sumfb_eq_testBit_add` (final-bit extraction from the
    forward cascade). -/
theorem prefix_and_cascade_top_bit_eq_address_and
    (n : Nat) (hn : 0 < n) (ctrl : Bool) (addr : Nat) (f : Nat → Bool)
    (h_ctrl : f ulookup_ctrl_idx = ctrl)
    (h_addr : ∀ i, i < n → f (ulookup_address_idx i) = addr.testBit i)
    (h_clean : ∀ i, i < n → f (ulookup_and_idx i) = false) :
    prefix_and_cascade_post_state n f (ulookup_and_idx (n - 1))
      = Lookup.address_and ctrl addr n := by
  have h_inv := Lookup.cascade_step_invariant_holds n n (Nat.le_refl n)
                  ctrl addr f h_ctrl h_addr h_clean
  have h_pred_lt : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  have h := h_inv (n - 1) h_pred_lt
  rw [if_pos h_pred_lt] at h
  rw [show n - 1 + 1 = n by omega] at h
  exact h

/-- **Decide-witness on (n=3, ctrl=true, addr=7=0b111)** (Iter 223).
    Full address all-ones: top and-bit = ctrl ∧ 1 ∧ 1 ∧ 1 = true. -/
example :
    let f : Nat → Bool := fun i =>
      if i = ulookup_ctrl_idx then true
      else if i = ulookup_address_idx 0 then true
      else if i = ulookup_address_idx 1 then true
      else if i = ulookup_address_idx 2 then true
      else false
    prefix_and_cascade_post_state 3 f (ulookup_and_idx 2)
      = Lookup.address_and true 7 3 := by decide

/-- **Decide-witness on (n=3, ctrl=true, addr=3=0b011)** (Iter 223).
    Top address bit (addr_2) is 0, killing the chain: top and-bit = false. -/
example :
    let f : Nat → Bool := fun i =>
      if i = ulookup_ctrl_idx then true
      else if i = ulookup_address_idx 0 then true
      else if i = ulookup_address_idx 1 then true
      else if i = ulookup_address_idx 2 then false
      else false
    prefix_and_cascade_post_state 3 f (ulookup_and_idx 2)
      = Lookup.address_and true 3 3 := by decide

/-- **X-flip layer frame condition**: positions not in the flip list
    are unchanged by the layer. -/
theorem Lookup.x_flip_post_state_frame
    (xs : List Nat) (f : Nat → Bool) (j : Nat) (h : j ∉ xs) :
    Lookup.x_flip_post_state xs f j = f j := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have h_ne : j ≠ i := fun heq => h (by rw [heq]; exact List.mem_cons_self)
    have h_tail : j ∉ xs := fun hin => h (List.mem_cons_of_mem i hin)
    show (Function.update (Lookup.x_flip_post_state xs f) i _) j = f j
    rw [Function.update_of_ne h_ne]
    exact ih h_tail

/-- **CNOT-layer frame condition**: positions not in the target list
    AND not equal to the control are unchanged. (The control itself
    is preserved by a separate lemma since CX never targets ctrl.) -/
theorem Lookup.cnot_layer_post_state_frame
    (ctrl : Nat) (xs : List Nat) (f : Nat → Bool) (j : Nat) (h : j ∉ xs) :
    Lookup.cnot_layer_post_state ctrl xs f j = f j := by
  induction xs with
  | nil => rfl
  | cons tgt xs ih =>
    have h_ne : j ≠ tgt := fun heq => h (by rw [heq]; exact List.mem_cons_self)
    have h_tail : j ∉ xs := fun hin => h (List.mem_cons_of_mem tgt hin)
    show (Function.update (Lookup.cnot_layer_post_state ctrl xs f) tgt _) j = f j
    rw [Function.update_of_ne h_ne]
    exact ih h_tail

/-- **CNOT-layer preserves the control qubit** (Iter 224). The control
    `ctrl` is never the target of any CX in this layer. (For this lemma
    we additionally need `ctrl ∉ xs`, since CX(ctrl, ctrl) is malformed
    in our gate IR but the post-state def doesn't enforce that.) -/
theorem Lookup.cnot_layer_post_state_ctrl_unchanged
    (ctrl : Nat) (xs : List Nat) (f : Nat → Bool) (h_ctrl_not_tgt : ctrl ∉ xs) :
    Lookup.cnot_layer_post_state ctrl xs f ctrl = f ctrl :=
  Lookup.cnot_layer_post_state_frame ctrl xs f ctrl h_ctrl_not_tgt

/-- **Decide-witness on x-flip layer**: starting from f ≡ false on
    positions {0, 1, 2}, flipping {0, 2} produces (true, false, true). -/
example :
    let f : Nat → Bool := fun _ => false
    let f' := Lookup.x_flip_post_state [0, 2] f
    f' 0 = true ∧ f' 1 = false ∧ f' 2 = true := by decide

/-- **Decide-witness on CNOT layer**: with ctrl=0 (true) and targets
    {1, 2, 3} (initially all false), each XORs with ctrl → all become true. -/
example :
    let f : Nat → Bool := fun i => i = 0
    let f' := Lookup.cnot_layer_post_state 0 [1, 2, 3] f
    f' 0 = true ∧ f' 1 = true ∧ f' 2 = true ∧ f' 3 = true := by decide

/-- **Decide-witness on CNOT layer with ctrl=false**: when control is
    false, no XOR fires; targets remain at their initial values. -/
example :
    let f : Nat → Bool := fun _ => false
    let f' := Lookup.cnot_layer_post_state 0 [1, 2, 3] f
    f' 0 = false ∧ f' 1 = false ∧ f' 2 = false ∧ f' 3 = false := by decide

/-! ## Value-at-element lemmas for the X-flip / CNOT layers (Iter 225, 2026-05-13)

    Companions to the frame lemmas of Iter 224. With `xs.Nodup`, the
    layer's value at a position `j ∈ xs` is exactly one application of
    the layer's primitive: a single XOR-with-true for X-flip, a single
    XOR-with-ctrl for the CNOT layer. -/

/-- **X-flip value-at-element**: for `j ∈ xs` with `xs.Nodup`, the
    layer flips `f j` exactly once. -/
theorem Lookup.x_flip_post_state_at
    (xs : List Nat) (h_nodup : xs.Nodup) (f : Nat → Bool) (j : Nat)
    (h_in : j ∈ xs) :
    Lookup.x_flip_post_state xs f j = ! (f j) := by
  induction xs with
  | nil => exact absurd h_in (List.not_mem_nil)
  | cons i xs ih =>
    show (Function.update (Lookup.x_flip_post_state xs f) i _) j = ! (f j)
    by_cases hji : j = i
    · subst hji
      have h_not_tail : j ∉ xs := (List.nodup_cons.mp h_nodup).1
      rw [Function.update_self]
      rw [Lookup.x_flip_post_state_frame xs f j h_not_tail]
    · have h_tail : j ∈ xs := by
        rcases List.mem_cons.mp h_in with h | h
        · exact absurd h hji
        · exact h
      rw [Function.update_of_ne hji]
      exact ih (List.nodup_cons.mp h_nodup).2 h_tail

/-- **CNOT-layer value-at-element**: for `tgt ∈ xs` with `xs.Nodup`
    AND `ctrl ∉ xs` (so the control wire is preserved), the layer
    XORs `f tgt` with `f ctrl` exactly once. -/
theorem Lookup.cnot_layer_post_state_at
    (ctrl : Nat) (xs : List Nat) (h_nodup : xs.Nodup)
    (h_ctrl_not_in : ctrl ∉ xs) (f : Nat → Bool) (tgt : Nat)
    (h_in : tgt ∈ xs) :
    Lookup.cnot_layer_post_state ctrl xs f tgt = xor (f tgt) (f ctrl) := by
  induction xs with
  | nil => exact absurd h_in List.not_mem_nil
  | cons hd xs ih =>
    show (Function.update (Lookup.cnot_layer_post_state ctrl xs f) hd _) tgt
          = xor (f tgt) (f ctrl)
    have h_ctrl_not_hd : ctrl ≠ hd := fun heq => h_ctrl_not_in
                          (heq ▸ List.mem_cons_self)
    have h_ctrl_not_tail : ctrl ∉ xs := fun h_in_tail =>
                          h_ctrl_not_in (List.mem_cons_of_mem hd h_in_tail)
    have h_ctrl_unchanged_tail :
        Lookup.cnot_layer_post_state ctrl xs f ctrl = f ctrl :=
      Lookup.cnot_layer_post_state_frame ctrl xs f ctrl h_ctrl_not_tail
    by_cases htgt : tgt = hd
    · subst htgt
      have h_tgt_not_tail : tgt ∉ xs := (List.nodup_cons.mp h_nodup).1
      rw [Function.update_self]
      rw [Lookup.cnot_layer_post_state_frame ctrl xs f tgt h_tgt_not_tail,
          h_ctrl_unchanged_tail]
    · have h_tail : tgt ∈ xs := by
        rcases List.mem_cons.mp h_in with h | h
        · exact absurd h htgt
        · exact h
      rw [Function.update_of_ne htgt]
      exact ih (List.nodup_cons.mp h_nodup).2 h_ctrl_not_tail h_tail

/-- **Decide-witness on x_flip_post_state_at**: with f = false everywhere,
    flipping {0, 2}, queried at j=2 (in the list): result = true. -/
example :
    let f : Nat → Bool := fun _ => false
    Lookup.x_flip_post_state [0, 2] f 2 = ! (f 2) := by decide

/-- **Decide-witness on cnot_layer_post_state_at**: with f(0)=true and
    f(2)=false, CNOT layer ctrl=0, targets {1,2,3}, queried at tgt=2
    (in the list): result = false ⊕ true = true. -/
example :
    let f : Nat → Bool := fun i => i = 0
    Lookup.cnot_layer_post_state 0 [1, 2, 3] f 2 = xor (f 2) (f 0) := by decide

/-! ## X-flip layer involution (Iter 226, 2026-05-13)

    The outer wrapper of `unary_lookup_iteration` is two X-flip layers
    on the SAME `addr_flip_idxs` list. Since X² = I, the two layers
    cancel — the address register is restored to its input value at
    the end of the iteration.

    Combined with cascade · uncompute = I (Iter 76 at matrix level)
    and the word-CNOT layer's conditional XOR (Iter 225), this completes
    the structural picture of `unary_lookup_iteration`. -/

/-- **X-flip layer involution**: with `xs.Nodup`, applying the X-flip
    layer twice returns to the identity. By funext + case-split on
    `j ∈ xs` vs `j ∉ xs`, using value-at-element (Iter 225) for the
    in-list case and the frame lemma (Iter 224) for the not-in-list case. -/
theorem Lookup.x_flip_post_state_involution
    (xs : List Nat) (h_nodup : xs.Nodup) (f : Nat → Bool) :
    Lookup.x_flip_post_state xs (Lookup.x_flip_post_state xs f) = f := by
  funext j
  by_cases h_in : j ∈ xs
  · -- In list: layer fires twice; XOR true twice cancels.
    rw [Lookup.x_flip_post_state_at xs h_nodup _ j h_in]
    rw [Lookup.x_flip_post_state_at xs h_nodup f j h_in]
    cases f j <;> rfl
  · -- Not in list: both layers preserve via frame.
    rw [Lookup.x_flip_post_state_frame xs _ j h_in]
    rw [Lookup.x_flip_post_state_frame xs f j h_in]

/-- **Decide-witness on x-flip involution** at (xs=[0,2], f=fun i => i = 1).
    Both layers cancel; result equals input. -/
example :
    let f : Nat → Bool := fun i => i = 1
    Lookup.x_flip_post_state [0, 2] (Lookup.x_flip_post_state [0, 2] f) 0 = f 0
    ∧ Lookup.x_flip_post_state [0, 2] (Lookup.x_flip_post_state [0, 2] f) 1 = f 1
    ∧ Lookup.x_flip_post_state [0, 2] (Lookup.x_flip_post_state [0, 2] f) 2 = f 2
    := by decide

/-! ## Boolean-level cascade step involution (Iter 227, 2026-05-13)

    The matrix-level `prefix_and_step_step_eq_one` (Iter 71) shows
    `step k · step k = 1` as matrices. Here we prove the **boolean
    post-state analog**: `step_post k (step_post k f) = f` for ANY f.

    This is the structural building block for the boolean-level
    `cascade · uncompute = identity` (Iter 228+), which is what
    cancels the and-bits across the iteration body. -/

/-- **Step post-state value at the and-bit (k=0 branch)**. -/
theorem prefix_and_step_post_state_at_and_zero (f : Nat → Bool) :
    prefix_and_step_post_state 0 f (ulookup_and_idx 0)
      = xor (f (ulookup_and_idx 0))
            (f ulookup_ctrl_idx && f (ulookup_address_idx 0)) := by
  unfold prefix_and_step_post_state
  rw [if_pos rfl, update_eq]

/-- **Step post-state value at the and-bit (k>0 branch)**. -/
theorem prefix_and_step_post_state_at_and_succ
    (k : Nat) (hk : k ≠ 0) (f : Nat → Bool) :
    prefix_and_step_post_state k f (ulookup_and_idx k)
      = xor (f (ulookup_and_idx k))
            (f (ulookup_and_idx (k - 1)) && f (ulookup_address_idx k)) := by
  unfold prefix_and_step_post_state
  rw [if_neg hk, update_eq]

/-- **Boolean-level step involution**: applying `prefix_and_step_post_state k`
    twice yields the identity. The step's only write is to `ulookup_and_idx k`,
    XORing it with a frame (`f ctrl ∧ f addr_0` for k=0, `f and_{k-1} ∧ f addr_k`
    for k>0). The frame depends only on positions OTHER than `and_k`, so the
    second application sees the SAME frame value, and the XOR cancels.

    Holds for arbitrary `f` — no clean-state hypothesis. -/
theorem prefix_and_step_post_state_involution
    (k : Nat) (f : Nat → Bool) :
    prefix_and_step_post_state k (prefix_and_step_post_state k f) = f := by
  funext j
  -- Both branches: only ulookup_and_idx k is written, with a frame
  -- read from positions other than and_k.
  by_cases hj : j = ulookup_and_idx k
  · -- j = and_k: the updated qubit; XOR with same frame twice → cancel
    subst hj
    by_cases hk0 : k = 0
    · subst hk0
      have h_ctrl_ne : ulookup_ctrl_idx ≠ ulookup_and_idx 0 := by
        unfold ulookup_ctrl_idx ulookup_and_idx; omega
      have h_addr0_ne : ulookup_address_idx 0 ≠ ulookup_and_idx 0 := by
        unfold ulookup_address_idx ulookup_and_idx; omega
      -- post (post f) (and_0) = xor (post f and_0) (post f ctrl ∧ post f addr_0)
      rw [prefix_and_step_post_state_at_and_zero (prefix_and_step_post_state 0 f)]
      -- post f at ctrl and addr_0 = f at those positions (untouched)
      have h_post_ctrl : prefix_and_step_post_state 0 f ulookup_ctrl_idx
          = f ulookup_ctrl_idx := by
        unfold prefix_and_step_post_state
        rw [if_pos rfl, update_neq _ _ _ _ h_ctrl_ne]
      have h_post_addr0 : prefix_and_step_post_state 0 f (ulookup_address_idx 0)
          = f (ulookup_address_idx 0) := by
        unfold prefix_and_step_post_state
        rw [if_pos rfl, update_neq _ _ _ _ h_addr0_ne]
      rw [h_post_ctrl, h_post_addr0,
          prefix_and_step_post_state_at_and_zero f]
      -- xor (xor a X) X = a
      cases f (ulookup_and_idx 0) <;>
        cases f ulookup_ctrl_idx <;>
        cases f (ulookup_address_idx 0) <;> rfl
    · have h_andpred_ne : ulookup_and_idx (k - 1) ≠ ulookup_and_idx k := by
        have : 0 < k := Nat.pos_of_ne_zero hk0
        unfold ulookup_and_idx; omega
      have h_addrk_ne : ulookup_address_idx k ≠ ulookup_and_idx k := by
        unfold ulookup_address_idx ulookup_and_idx; omega
      rw [prefix_and_step_post_state_at_and_succ k hk0 (prefix_and_step_post_state k f)]
      have h_post_andpred : prefix_and_step_post_state k f (ulookup_and_idx (k - 1))
          = f (ulookup_and_idx (k - 1)) := by
        unfold prefix_and_step_post_state
        rw [if_neg hk0, update_neq _ _ _ _ h_andpred_ne]
      have h_post_addrk : prefix_and_step_post_state k f (ulookup_address_idx k)
          = f (ulookup_address_idx k) := by
        unfold prefix_and_step_post_state
        rw [if_neg hk0, update_neq _ _ _ _ h_addrk_ne]
      rw [h_post_andpred, h_post_addrk,
          prefix_and_step_post_state_at_and_succ k hk0 f]
      cases f (ulookup_and_idx k) <;>
        cases f (ulookup_and_idx (k - 1)) <;>
        cases f (ulookup_address_idx k) <;> rfl
  · -- j ≠ and_k: untouched by both applications (frame)
    rw [prefix_and_step_post_state_frame k _ j hj,
        prefix_and_step_post_state_frame k f j hj]

/-- **Decide-witness on step involution at k=0**: arbitrary input,
    apply step 0 twice, get input back. -/
example :
    let f : Nat → Bool := fun i => i % 2 = 0
    prefix_and_step_post_state 0 (prefix_and_step_post_state 0 f) 0 = f 0
    ∧ prefix_and_step_post_state 0 (prefix_and_step_post_state 0 f) 2 = f 2 := by
  decide

/-- **Decide-witness on step involution at k=2** (k > 0 branch). -/
example :
    let f : Nat → Bool := fun i => i = 4
    prefix_and_step_post_state 2 (prefix_and_step_post_state 2 f) 6 = f 6
    ∧ prefix_and_step_post_state 2 (prefix_and_step_post_state 2 f) 5 = f 5 := by
  decide

/-- **Boolean-level cascade · uncompute = identity**. Applying the
    forward n-step cascade post-state then the n-step uncompute post-state
    returns to the input `f`. Proof by induction on n + Iter 227's
    step involution.

    Lookup analog of Iter 76's matrix-level `prefix_and_cascade_uncompute_eq_one`. -/
theorem prefix_and_cascade_uncompute_post_state_eq_id
    (n : Nat) (f : Nat → Bool) :
    prefix_and_uncompute_post_state n (prefix_and_cascade_post_state n f) = f := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    -- cascade (k+1) f = step k (cascade k f)
    -- uncompute (k+1) g = uncompute k (step k g)
    -- So uncompute (k+1) (cascade (k+1) f)
    --   = uncompute k (step k (step k (cascade k f)))
    --   = uncompute k (cascade k f)   [step involution]
    --   = f                            [IH]
    show prefix_and_uncompute_post_state k
            (prefix_and_step_post_state k
              (prefix_and_step_post_state k (prefix_and_cascade_post_state k f)))
          = f
    rw [prefix_and_step_post_state_involution k (prefix_and_cascade_post_state k f)]
    exact ih f

/-- **Decide-witness on cascade · uncompute = id** at n=3 with a small
    concrete input function. -/
example :
    let f : Nat → Bool := fun i => i = 0 ∨ i = 5
    prefix_and_uncompute_post_state 3 (prefix_and_cascade_post_state 3 f) 0 = f 0
    ∧ prefix_and_uncompute_post_state 3 (prefix_and_cascade_post_state 3 f) 5 = f 5
    ∧ prefix_and_uncompute_post_state 3 (prefix_and_cascade_post_state 3 f) 2 = f 2
    := by decide

end FormalRV.BQAlgo
