/-
  FormalRV.BQAlgo.CuccaroFull — the BOUNDARY-CORRECTED Cuccaro adder.

  Tick 42: per the third-party Python sanity check
  (`scripts/check_cuccaro_adder.py`), the existing
  `cuccaro_n_bit_adder_skeleton` (forward MAJ-chain + forward UMA-chain)
  is NOT a correct in-place adder for n ≥ 2 — it fails 606 of 680 test
  cases. The fix is to **REVERSE the UMA chain order**: apply
  `UMA_{n-1}, UMA_{n-2}, ..., UMA_1, UMA_0` (descending) rather than
  `UMA_0, ..., UMA_{n-1}` (ascending). With that single structural fix,
  the simulator passes all 680 cases (n = 1..4, c_in ∈ {F, T}, all
  a, b < 2^n).

  This module defines the corrected `cuccaro_n_bit_adder_full` and
  proves WellTyped. Semantic correctness on the chain level is left as
  the next-tick deliverable.

  Layout (matches `cuccaro_input_F` in `BQAlgo/CuccaroCorrectness.lean`):
  - pos q_start + 0: c_in (carry-in).
  - pos q_start + 2i + 1: bit i of b (target register; becomes (a+b+c_in) mod 2^n).
  - pos q_start + 2i + 2: bit i of a (read register; preserved).
  - Total: 2*n + 1 qubits.

  This matches SQIR's `modmult_rev_anc n = 2*n + 1` budget EXACTLY,
  making this the natural exact-budget primitive for closing the
  original SQIR placeholders.
-/
import FormalRV.Core.Gate
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Cuccaro.CuccaroCorrectness

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Reverse UMA chain.

The recursion: `cuccaro_uma_chain_reverse (n+1) q_start` first applies
the reverse chain of length `n` on the suffix starting at `q_start + 2`
(which by induction covers UMA_n, ..., UMA_1 in descending order), then
applies `UMA_0` at `q_start`. Unrolling: UMA_{n-1}, ..., UMA_1, UMA_0
in descending order. -/

/-- Reverse UMA chain: `UMA_{n-1}, UMA_{n-2}, ..., UMA_0`, applied in
descending order on consecutive triples starting at `q_start`. -/
def cuccaro_uma_chain_reverse : Nat → Nat → Gate
  | 0,     _       => I
  | n + 1, q_start =>
      seq (cuccaro_uma_chain_reverse n (q_start + 2))
          (cuccaro_UMA q_start (q_start + 1) (q_start + 2))

/-! ## The full Cuccaro adder. -/

/-- **Boundary-corrected n-bit Cuccaro adder.**  Forward MAJ chain
followed by **reverse** UMA chain.  Validated by exhaustive Boolean
simulation for n = 1..4 (see `scripts/check_cuccaro_adder.py`).

Layout: `2 * n + 1` qubits starting at `q_start`; matches
`cuccaro_input_F`. -/
def cuccaro_n_bit_adder_full (n q_start : Nat) : Gate :=
  seq (cuccaro_maj_chain n q_start) (cuccaro_uma_chain_reverse n q_start)

/-! ## T-count: same 14n as the skeleton (CXs are T-free; reordering
doesn't change T-count). -/

/-- T-count of the reverse UMA chain is `7 * n`. -/
theorem tcount_cuccaro_uma_chain_reverse (n q_start : Nat) :
    tcount (cuccaro_uma_chain_reverse n q_start) = 7 * n := by
  induction n generalizing q_start with
  | zero => rfl
  | succ k ih =>
    show tcount (seq (cuccaro_uma_chain_reverse k (q_start + 2))
                      (cuccaro_UMA q_start (q_start + 1) (q_start + 2)))
         = 7 * (k + 1)
    simp [tcount, ih (q_start + 2),
          UMA_meets_paper_claim, paper_claim_UMA_tcount]
    omega

/-- T-count of the full adder: `14 * n`. Same as the (incorrect)
skeleton — reordering doesn't change cost. -/
theorem tcount_cuccaro_n_bit_adder_full (n q_start : Nat) :
    tcount (cuccaro_n_bit_adder_full n q_start) = 14 * n := by
  show tcount (seq (cuccaro_maj_chain n q_start)
                    (cuccaro_uma_chain_reverse n q_start)) = 14 * n
  simp [tcount, tcount_cuccaro_maj_chain, tcount_cuccaro_uma_chain_reverse]
  omega

/-- Smoke: 4-bit full adder has 56 T-gates. -/
example : tcount (cuccaro_n_bit_adder_full 4 0) = 56 := by decide

/-! ## WellTyped: structural induction on the chain recursion. -/

/-- The MAJ chain of `n` steps starting at `q_start` is well-typed in
any dimension `dim` containing the touched range `[q_start, q_start + 2n]`. -/
theorem cuccaro_maj_chain_wellTyped
    (n q_start dim : Nat) (h : q_start + 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_maj_chain n q_start) := by
  induction n generalizing q_start with
  | zero =>
    show Gate.WellTyped dim Gate.I
    show 0 < dim
    omega
  | succ k ih =>
    show Gate.WellTyped dim
        (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
              (cuccaro_maj_chain k (q_start + 2)))
    refine ⟨?_, ?_⟩
    · -- MAJ at (q_start, q_start+1, q_start+2): bounds + distinctness.
      apply cuccaro_MAJ_wellTyped
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · -- Recursive: chain at q_start+2 with k steps.
      apply ih
      omega

/-- The reverse UMA chain is well-typed in any dimension containing
`[q_start, q_start + 2n]`. -/
theorem cuccaro_uma_chain_reverse_wellTyped
    (n q_start dim : Nat) (h : q_start + 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_uma_chain_reverse n q_start) := by
  induction n generalizing q_start with
  | zero =>
    show Gate.WellTyped dim Gate.I
    show 0 < dim
    omega
  | succ k ih =>
    show Gate.WellTyped dim
        (seq (cuccaro_uma_chain_reverse k (q_start + 2))
              (cuccaro_UMA q_start (q_start + 1) (q_start + 2)))
    refine ⟨?_, ?_⟩
    · -- Recursive: reverse chain at q_start+2 with k steps.
      apply ih
      omega
    · -- UMA at (q_start, q_start+1, q_start+2): bounds + distinctness.
      apply cuccaro_UMA_wellTyped
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega

/-- **HEADLINE: Full Cuccaro adder is well-typed.**  In any dimension
`dim ≥ q_start + 2n + 1` (covers all touched qubits, the highest being
`q_start + 2n` for n ≥ 1), the corrected full adder is structurally
well-typed.  Proved by structural composition of MAJ-chain WellTyped
with reverse-UMA-chain WellTyped. -/
theorem cuccaro_n_bit_adder_full_wellTyped
    (n q_start dim : Nat) (h : q_start + 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (cuccaro_n_bit_adder_full n q_start) := by
  refine ⟨?_, ?_⟩
  · exact cuccaro_maj_chain_wellTyped n q_start dim h
  · exact cuccaro_uma_chain_reverse_wellTyped n q_start dim h

/-! ## Smoke: n=2, q_start=0, dim=5. -/

example : Gate.WellTyped 5 (cuccaro_n_bit_adder_full 2 0) :=
  cuccaro_n_bit_adder_full_wellTyped 2 0 5 (by decide)

/-! ## Start of chain semantics — single MAJ-step in a chain context.

The corrected full adder's semantic correctness reduces to a chain
invariant on the MAJ phase plus an unzip invariant on the reverse UMA
phase.  This tick lands the SINGLE-STEP relation for the MAJ chain, in
purely symbolic form (no specific n), as a foundation for the next
tick's induction.

The key fact: applying `cuccaro_MAJ q_start (q_start+1) (q_start+2)` to
an arbitrary state `f` changes only the three positions in
`{q_start, q_start+1, q_start+2}`, with the EXACT symbolic formulas
proved in Tick 41 (`cuccaro_MAJ_at_a/b/c/other`).  Composition with
`cuccaro_maj_chain k (q_start+2)` then leaves the first three positions
of THAT step untouched (since the recursive chain only touches
`[q_start+2, q_start+2k+2]`).

This gives a clean "step lemma" usable in the chain induction. -/

/-- **Frame lemma for the MAJ chain: positions strictly below
`q_start` are unchanged.**  The chain touches only qubits
`[q_start, q_start + 2n]`, so anything below is preserved.  Proved by
induction on `n` using `cuccaro_MAJ_at_other`. -/
theorem cuccaro_maj_chain_frame_below
    (n q_start : Nat) (f : Nat → Bool) (q : Nat) (h : q < q_start) :
    Gate.applyNat (cuccaro_maj_chain n q_start) f q = f q := by
  induction n generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
              (cuccaro_maj_chain k (q_start + 2))) f q = _
    simp only [Gate.applyNat_seq]
    -- After the first MAJ, position q (which is below q_start) is unchanged.
    have h1 : Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f q
                = f q := by
      apply cuccaro_MAJ_at_other
      · omega
      · omega
      · omega
    -- After the recursive chain (starting at q_start + 2), position q is also
    -- unchanged (q < q_start ≤ q_start + 2 still holds).
    have h2 := ih (q_start + 2) (Gate.applyNat
                  (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
                  (by omega)
    rw [h2, h1]

/-- **Frame lemma for the reverse UMA chain: positions strictly below
`q_start` are unchanged.** Analogous to the MAJ-chain frame. -/
theorem cuccaro_uma_chain_reverse_frame_below
    (n q_start : Nat) (f : Nat → Bool) (q : Nat) (h : q < q_start) :
    Gate.applyNat (cuccaro_uma_chain_reverse n q_start) f q = f q := by
  induction n generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_uma_chain_reverse k (q_start + 2))
              (cuccaro_UMA q_start (q_start + 1) (q_start + 2))) f q = _
    simp only [Gate.applyNat_seq]
    -- Push the outer UMA at_other (q ≠ q_start, q_start+1, q_start+2).
    rw [cuccaro_UMA_at_other q_start (q_start + 1) (q_start + 2) q
        (by omega) (by omega) (by omega)]
    -- Recursive ih: inner chain preserves q.
    exact ih (q_start + 2) f (by omega)

/-- **Frame lemma for the full adder: positions strictly below `q_start`
are unchanged.**  Composition of the MAJ-chain and reverse-UMA-chain
frame lemmas. -/
theorem cuccaro_n_bit_adder_full_frame_below
    (n q_start : Nat) (f : Nat → Bool) (q : Nat) (h : q < q_start) :
    Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f q = f q := by
  show Gate.applyNat
      (seq (cuccaro_maj_chain n q_start) (cuccaro_uma_chain_reverse n q_start))
      f q = _
  simp only [Gate.applyNat_seq]
  rw [cuccaro_uma_chain_reverse_frame_below n q_start _ q h]
  rw [cuccaro_maj_chain_frame_below n q_start f q h]

/-! ## Frame above the chain support — positions ≥ `q_start + 2n + 1` are
unchanged.

These are the "right boundary" frame lemmas: the chain never touches
qubits above the topmost MAJ/UMA wire. Together with the below-frame
lemmas, they pin down exactly which positions can be affected. -/

/-- The MAJ chain doesn't touch positions `≥ q_start + 2n + 1`. -/
theorem cuccaro_maj_chain_frame_above
    (n q_start : Nat) (f : Nat → Bool) (q : Nat)
    (h : q_start + 2 * n + 1 ≤ q) :
    Gate.applyNat (cuccaro_maj_chain n q_start) f q = f q := by
  induction n generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
              (cuccaro_maj_chain k (q_start + 2))) f q = _
    simp only [Gate.applyNat_seq]
    have h1 : Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f q
                = f q := by
      apply cuccaro_MAJ_at_other <;> omega
    have h2 := ih (q_start + 2) (Gate.applyNat
                  (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
                  (by omega)
    rw [h2, h1]

/-- The reverse UMA chain doesn't touch positions `≥ q_start + 2n + 1`. -/
theorem cuccaro_uma_chain_reverse_frame_above
    (n q_start : Nat) (f : Nat → Bool) (q : Nat)
    (h : q_start + 2 * n + 1 ≤ q) :
    Gate.applyNat (cuccaro_uma_chain_reverse n q_start) f q = f q := by
  induction n generalizing q_start f with
  | zero => rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_uma_chain_reverse k (q_start + 2))
              (cuccaro_UMA q_start (q_start + 1) (q_start + 2))) f q = _
    simp only [Gate.applyNat_seq]
    -- Push the outer UMA at_other (q ≥ q_start + 2(k+1) + 1 > q_start + 2).
    rw [cuccaro_UMA_at_other q_start (q_start + 1) (q_start + 2) q
        (by omega) (by omega) (by omega)]
    -- Recursive ih: inner chain at q_start + 2 with k steps preserves q
    -- (since q ≥ q_start + 2(k+1) + 1 = (q_start + 2) + 2k + 1).
    exact ih (q_start + 2) f (by omega)

/-- **Full adder doesn't touch positions outside `[q_start, q_start + 2n]`.** -/
theorem cuccaro_n_bit_adder_full_frame_above
    (n q_start : Nat) (f : Nat → Bool) (q : Nat)
    (h : q_start + 2 * n + 1 ≤ q) :
    Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f q = f q := by
  show Gate.applyNat
      (seq (cuccaro_maj_chain n q_start) (cuccaro_uma_chain_reverse n q_start))
      f q = _
  simp only [Gate.applyNat_seq]
  rw [cuccaro_uma_chain_reverse_frame_above n q_start _ q h]
  rw [cuccaro_maj_chain_frame_above n q_start f q h]

/-! ## First MAJ-chain step lemma (symbolic, parametric).

After applying `cuccaro_maj_chain (n+1) q_start` to `f`:
- Position `q_start` holds the result of the FIRST MAJ on its `a` wire,
  with the recursive chain leaving it untouched (since the recursive
  chain starts at `q_start + 2`).
  → equals `xor (f q_start) (f (q_start + 2))`, NOT just `f q_start`.

The key step lemma: the first three positions of a non-empty MAJ chain
are determined by the FIRST `cuccaro_MAJ` alone, since the recursive
sub-chain starts at `q_start + 2` and frames everything below.

We expose `q_start` (first MAJ's `a` wire) and `q_start + 1` (first
MAJ's `b` wire) — the `q_start + 2` position is touched by both the
first MAJ and the subsequent chain, so it requires more care. -/

/-- **First MAJ-chain step at position `q_start` (the first MAJ's `a` wire).**
After `cuccaro_maj_chain (n+1) q_start`, position `q_start` holds
`xor (f q_start) (f (q_start + 2))` — the result of MAJ_0's `a`-wire
action, since the recursive sub-chain (starting at `q_start + 2`)
doesn't touch positions below `q_start + 2`. -/
theorem cuccaro_maj_chain_at_first_a
    (n q_start : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_maj_chain (n + 1) q_start) f q_start
      = xor (f q_start) (f (q_start + 2)) := by
  show Gate.applyNat
      (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
            (cuccaro_maj_chain n (q_start + 2))) f q_start = _
  simp only [Gate.applyNat_seq]
  -- The recursive chain at q_start + 2 doesn't touch q_start (below).
  rw [cuccaro_maj_chain_frame_below n (q_start + 2) _ q_start (by omega)]
  -- Now reduces to the local MAJ semantics from Tick 41.
  apply cuccaro_MAJ_at_a <;> omega

/-- **First MAJ-chain step at position `q_start + 1` (the first MAJ's `b` wire).**
After `cuccaro_maj_chain (n+1) q_start`, position `q_start + 1` holds
`xor (f (q_start + 1)) (f (q_start + 2))`. -/
theorem cuccaro_maj_chain_at_first_b
    (n q_start : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_maj_chain (n + 1) q_start) f (q_start + 1)
      = xor (f (q_start + 1)) (f (q_start + 2)) := by
  show Gate.applyNat
      (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
            (cuccaro_maj_chain n (q_start + 2))) f (q_start + 1) = _
  simp only [Gate.applyNat_seq]
  rw [cuccaro_maj_chain_frame_below n (q_start + 2) _ (q_start + 1) (by omega)]
  apply cuccaro_MAJ_at_b <;> omega

/-! ## Tick 43 — Full MAJ-chain symbolic semantics.

We pin down what every position of the MAJ-chain's output state is, as a
purely symbolic function of the input state `f` and `q_start`.  The
chain stores running carries via the recursive `cuccaro_carry`. -/

/-- **Classical Cuccaro carry function.**  Given a state `f` and a
register origin `q_start`, `cuccaro_carry f q_start k` is the carry
into bit-position k of the addition encoded by `f` (per the layout
`pos q_start = c_in; pos q_start + 2i + 1 = b_i; pos q_start + 2i + 2 = a_i`).

Defined recursively via the majority function (which is the classical
full-adder carry-out). -/
def cuccaro_carry (f : Nat → Bool) (q_start : Nat) : Nat → Bool
  | 0     => f q_start
  | k + 1 => Boolean.majority
               (cuccaro_carry f q_start k)
               (f (q_start + 2 * k + 1))
               (f (q_start + 2 * k + 2))

/-- **Shift lemma.**  Applying `MAJ_0` (the first chain step) and then
the carry function starting from the shifted position `q_start + 2`
equals the original carry function at the next index.  This is the
algebraic glue for the chain-invariant induction. -/
theorem cuccaro_carry_after_MAJ0_shift
    (q_start : Nat) (f : Nat → Bool) (k : Nat) :
    cuccaro_carry (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
                  (q_start + 2) k
      = cuccaro_carry f q_start (k + 1) := by
  induction k with
  | zero =>
    -- LHS: cuccaro_carry ... 0 = post-MAJ_0 state at q_start + 2 = majority.
    -- RHS: cuccaro_carry f q_start 1 = majority (c_0) (b_0) (a_0) = majority.
    show Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f (q_start + 2)
      = Boolean.majority (f q_start) (f (q_start + 2 * 0 + 1)) (f (q_start + 2 * 0 + 2))
    rw [cuccaro_MAJ_at_c q_start (q_start + 1) (q_start + 2) (by omega) (by omega) (by omega)]
  | succ j ih =>
    -- Unfold both sides as majority of carry_j and the relevant b/a bits.
    show Boolean.majority
            (cuccaro_carry
              (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
              (q_start + 2) j)
            (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f
              (q_start + 2 + 2 * j + 1))
            (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f
              (q_start + 2 + 2 * j + 2))
          = Boolean.majority
              (cuccaro_carry f q_start (j + 1))
              (f (q_start + 2 * (j + 1) + 1))
              (f (q_start + 2 * (j + 1) + 2))
    rw [ih]
    rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
        (q_start + 2 + 2 * j + 1) (by omega) (by omega) (by omega)]
    rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
        (q_start + 2 + 2 * j + 2) (by omega) (by omega) (by omega)]
    have h1 : q_start + 2 + 2 * j + 1 = q_start + 2 * (j + 1) + 1 := by ring
    have h2 : q_start + 2 + 2 * j + 2 = q_start + 2 * (j + 1) + 2 := by ring
    rw [h1, h2]

/-! ### The three MAJ-chain invariants.

After applying `cuccaro_maj_chain n q_start` to `f`:
- For 0 ≤ i < n at pos `q_start + 2 * i`: holds `cuccaro_carry f q_start i ⊕ a_i`.
- For 0 ≤ i < n at pos `q_start + 2 * i + 1`: holds `b_i ⊕ a_i`.
- At pos `q_start + 2 * n` (the top): holds `cuccaro_carry f q_start n`.
-/

/-- **MAJ-chain invariant at the carry positions `q_start + 2*i` (i < n).** -/
theorem cuccaro_maj_chain_at_carry_a
    (n q_start : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    Gate.applyNat (cuccaro_maj_chain n q_start) f (q_start + 2 * i)
      = xor (cuccaro_carry f q_start i) (f (q_start + 2 * i + 2)) := by
  induction n generalizing q_start f i with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
              (cuccaro_maj_chain k (q_start + 2))) f (q_start + 2 * i) = _
    simp only [Gate.applyNat_seq]
    -- Case-split on i: i = 0 vs i ≥ 1.
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- i = 0: position q_start, sub-chain doesn't touch (frame_below).
      subst hi0
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ q_start (by omega)]
      rw [cuccaro_MAJ_at_a q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      -- cuccaro_carry f q_start 0 = f q_start.
      rfl
    · -- i ≥ 1: write i = j + 1 with j < k.
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < k := by omega
      -- Sub-position: q_start + 2*(j+1) = (q_start + 2) + 2*j.
      have hpos : q_start + 2 * (j + 1) = (q_start + 2) + 2 * j := by ring
      rw [hpos]
      -- Apply ih with sub-chain at q_start + 2, sub-state = MAJ_0 output, sub-i = j.
      rw [ih (q_start + 2)
          (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f) j hj]
      -- Goal: xor (cuccaro_carry (MAJ_0 output) (q_start + 2) j) (MAJ_0_output ((q_start+2) + 2*j + 2))
      --       = xor (cuccaro_carry f q_start (j+1)) (f (q_start + 2*(j+1) + 2)).
      -- (q_start + 2) + 2*j + 2 = q_start + 2*(j+1) + 2.
      have hpos2 : (q_start + 2) + 2 * j + 2 = q_start + 2 * (j + 1) + 2 := by ring
      rw [hpos2]
      -- MAJ_0 doesn't touch q_start + 2*(j+1) + 2 (it's ≥ q_start + 4 > q_start + 2).
      rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 2) (by omega) (by omega) (by omega)]
      -- Apply shift lemma.
      rw [cuccaro_carry_after_MAJ0_shift q_start f j]

/-- **MAJ-chain invariant at the `b`-bit positions `q_start + 2*i + 1` (i < n).** -/
theorem cuccaro_maj_chain_at_b_xor
    (n q_start : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    Gate.applyNat (cuccaro_maj_chain n q_start) f (q_start + 2 * i + 1)
      = xor (f (q_start + 2 * i + 1)) (f (q_start + 2 * i + 2)) := by
  induction n generalizing q_start f i with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
              (cuccaro_maj_chain k (q_start + 2))) f (q_start + 2 * i + 1) = _
    simp only [Gate.applyNat_seq]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- i = 0: position q_start + 1, sub-chain doesn't touch.
      subst hi0
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
      apply cuccaro_MAJ_at_b q_start (q_start + 1) (q_start + 2) <;> omega
    · -- i ≥ 1: shift to sub-chain.
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < k := by omega
      have hpos : q_start + 2 * (j + 1) + 1 = (q_start + 2) + 2 * j + 1 := by ring
      rw [hpos]
      rw [ih (q_start + 2)
          (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f) j hj]
      have hpos1 : (q_start + 2) + 2 * j + 1 = q_start + 2 * (j + 1) + 1 := by ring
      have hpos2 : (q_start + 2) + 2 * j + 2 = q_start + 2 * (j + 1) + 2 := by ring
      rw [hpos1, hpos2]
      rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 1) (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 2) (by omega) (by omega) (by omega)]

/-- **MAJ-chain invariant at the top position `q_start + 2*n`: holds the
final carry `c_n`.** -/
theorem cuccaro_maj_chain_at_top_carry
    (n q_start : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_maj_chain n q_start) f (q_start + 2 * n)
      = cuccaro_carry f q_start n := by
  induction n generalizing q_start f with
  | zero =>
    -- Chain is I; position q_start + 0 = q_start; cuccaro_carry f q_start 0 = f q_start.
    simp only [Nat.mul_zero, Nat.add_zero]
    rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
              (cuccaro_maj_chain k (q_start + 2))) f (q_start + 2 * (k + 1)) = _
    simp only [Gate.applyNat_seq]
    have hpos : q_start + 2 * (k + 1) = (q_start + 2) + 2 * k := by ring
    rw [hpos]
    rw [ih (q_start + 2)
        (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)]
    -- Goal: cuccaro_carry (MAJ_0_output) (q_start + 2) k = cuccaro_carry f q_start (k+1).
    exact cuccaro_carry_after_MAJ0_shift q_start f k

/-! ## Tick 43 — Reverse-UMA chain semantics: first single-step lemma.

Now begin the unzip side.  The reverse UMA chain processes UMA_{n-1}
first, then UMA_{n-2}, ..., then UMA_0.  Each UMA_i acts on the
positions `(q_start + 2*i, q_start + 2*i + 1, q_start + 2*i + 2)`,
where (after the MAJ chain + previous reverse UMAs) the state is:
- pos `q_start + 2*i`:   `c_i ⊕ a_i`        (the carry encoding).
- pos `q_start + 2*i + 1`: `b_i ⊕ a_i`      (the b encoding).
- pos `q_start + 2*i + 2`: `c_{i+1}` if i = n-1, or `a_{i+1}` after the
  later reverse UMAs have restored it (subtle — we'll prove this
  carefully).

For the FIRST reverse UMA step (which is UMA_{n-1} acting on the
post-MAJ state), the c-wire (pos `q_start + 2n`) holds `c_n`. The
UMA's action restores the original `a_{n-1}` there and writes the sum
bit `c_{n-1} ⊕ b_{n-1} ⊕ a_{n-1}` to position `q_start + 2n - 1`.

This direction is captured by the algebraic identity
`UMA_after_MAJ_writes_sum`, which says applying UMA to a post-MAJ
state restores a, writes the sum to b, and restores c.  We prove the
generic 3-position version here. -/

/-- **Algebraic UMA-after-MAJ identity (a-wire).**  Applying UMA to the
state after a MAJ on the same triple restores the original `a` value at
the a-wire.  This is the symbolic version of `MAJ_then_UMA_restores_a`. -/
theorem cuccaro_UMA_undo_MAJ_a
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c)
        (Gate.applyNat (cuccaro_MAJ a b c) f) a
      = f a := by
  -- Compute the composed action symbolically.
  rw [cuccaro_UMA_at_a a b c h_ab h_ac h_bc]
  rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc f]
  rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc f]
  rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc f]
  -- Goal: a-wire XOR c-wire XOR (a-wire AND b-wire) = f a.
  -- With a-wire = f a ⊕ f c, c-wire = majority, b-wire = f b ⊕ f c.
  unfold Boolean.majority
  cases f a <;> cases f b <;> cases f c <;> rfl

/-- **Algebraic UMA-after-MAJ identity (c-wire).**  Restores the original
`c` value at the c-wire. -/
theorem cuccaro_UMA_undo_MAJ_c
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c)
        (Gate.applyNat (cuccaro_MAJ a b c) f) c
      = f c := by
  rw [cuccaro_UMA_at_c a b c h_ab h_ac h_bc]
  rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc f]
  rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc f]
  rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc f]
  unfold Boolean.majority
  cases f a <;> cases f b <;> cases f c <;> rfl

/-- **Algebraic UMA-after-MAJ identity (b-wire).**  Writes the sum bit
`f a XOR f b XOR f c` at the b-wire. -/
theorem cuccaro_UMA_undo_MAJ_b
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c)
        (Gate.applyNat (cuccaro_MAJ a b c) f) b
      = xor (xor (f a) (f b)) (f c) := by
  rw [cuccaro_UMA_at_b a b c h_ab h_ac h_bc]
  rw [cuccaro_MAJ_at_a a b c h_ab h_ac h_bc f]
  rw [cuccaro_MAJ_at_c a b c h_ab h_ac h_bc f]
  rw [cuccaro_MAJ_at_b a b c h_ab h_ac h_bc f]
  unfold Boolean.majority
  cases f a <;> cases f b <;> cases f c <;> rfl

/-! ## Tick 43 — Full adder correctness (carry-in restoration).

We now prove that the full Cuccaro adder restores its carry-in
qubit `q_start` to its original value. This is one of the three
positional invariants for full correctness; the next-tick deliverable
will extend to sum bits and a-restoration.

Proof structure: induction on `n`. For `n + 1`, the adder
reassociates as `MAJ_0 ; sub_full_adder_n ; UMA_0`, where
`sub_full_adder_n` is the full adder of length `n` at `q_start + 2`.
The IH gives that `sub_full_adder_n` restores its own carry-in (at
`q_start + 2`), and the frame_below lemmas plus
`cuccaro_UMA_undo_MAJ_a` close the chain. -/

/-- **Carry-in restoration: position `q_start` is unchanged by the
full Cuccaro adder.** -/
theorem cuccaro_n_bit_adder_full_carry_in_restored
    (n q_start : Nat) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f q_start = f q_start := by
  induction n generalizing q_start f with
  | zero =>
    -- The 0-bit adder is `seq I I`; applied to f, position q_start = f q_start.
    rfl
  | succ k ih =>
    show Gate.applyNat
        (seq (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                  (cuccaro_maj_chain k (q_start + 2)))
              (seq (cuccaro_uma_chain_reverse k (q_start + 2))
                   (cuccaro_UMA q_start (q_start + 1) (q_start + 2))))
        f q_start = _
    simp only [Gate.applyNat_seq]
    -- Goal now: applyNat UMA_0 (... lots of nesting ...) q_start = f q_start.
    -- Apply UMA's a-wire formula.
    rw [cuccaro_UMA_at_a q_start (q_start + 1) (q_start + 2)
        (by omega) (by omega) (by omega)]
    -- The "inner state" g (after MAJ_0, sub_MAJ_k, sub_UMA_reverse_k) at:
    -- - q_start: not touched by sub-chains (frame_below); = MAJ_0(f)(q_start).
    -- - q_start+1: same; = MAJ_0(f)(q_start+1).
    -- - q_start+2: restored to MAJ_0(f)(q_start+2) by IH on sub-adder.
    have hg_qs : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                    (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                       (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                    q_start
                  = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                  f q_start := by
      rw [cuccaro_uma_chain_reverse_frame_below k (q_start + 2) _ q_start (by omega)]
      rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ q_start (by omega)]
    have hg_qs1 : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                    (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                       (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                    (q_start + 1)
                  = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                  f (q_start + 1) := by
      rw [cuccaro_uma_chain_reverse_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
      rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
    have hg_qs2 : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                    (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                       (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                    (q_start + 2)
                  = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                  f (q_start + 2) := by
      -- This is IH for sub-adder at q_start+2, applied to input MAJ_0(f).
      have hih := ih (q_start + 2)
        (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
      simp only [cuccaro_n_bit_adder_full, Gate.applyNat_seq] at hih
      exact hih
    rw [hg_qs, hg_qs1, hg_qs2]
    -- Now reduce the MAJ outputs.
    rw [cuccaro_MAJ_at_a q_start (q_start + 1) (q_start + 2)
        (by omega) (by omega) (by omega)]
    rw [cuccaro_MAJ_at_b q_start (q_start + 1) (q_start + 2)
        (by omega) (by omega) (by omega)]
    rw [cuccaro_MAJ_at_c q_start (q_start + 1) (q_start + 2)
        (by omega) (by omega) (by omega)]
    -- Goal is now a pure Boolean identity in `f q_start`, `f (q_start+1)`,
    -- `f (q_start+2)`. Reduce by case analysis.
    unfold Boolean.majority
    cases f q_start <;> cases f (q_start + 1) <;> cases f (q_start + 2) <;> rfl

/-- **Read register restoration: position `q_start + 2*i + 2` is unchanged
by the full Cuccaro adder for any `i < n`.**

This is the second of the three positional invariants — the `a` register
(stored at the read-positions) is preserved by the full adder.

Same induction pattern as `_carry_in_restored`: split on `i = 0` vs
`i ≥ 1`. For `i = 0`, the local `cuccaro_UMA_undo_MAJ_c` identity
applies after using IH on the sub-carry-in restoration. For `i ≥ 1`,
the sub-adder's a-restoration IH directly handles it, with the outer
UMA_0 and MAJ_0 leaving the position untouched. -/
theorem cuccaro_n_bit_adder_full_a_restored
    (n q_start : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f (q_start + 2 * i + 2)
      = f (q_start + 2 * i + 2) := by
  induction n generalizing q_start f i with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (seq (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                  (cuccaro_maj_chain k (q_start + 2)))
              (seq (cuccaro_uma_chain_reverse k (q_start + 2))
                   (cuccaro_UMA q_start (q_start + 1) (q_start + 2))))
        f (q_start + 2 * i + 2) = _
    simp only [Gate.applyNat_seq]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- i = 0: position q_start + 2. UMA_0's c-wire action.
      subst hi0
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [cuccaro_UMA_at_c q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      -- Inner state at q_start, q_start+1, q_start+2.
      have hg_qs : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                      (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                         (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                      q_start
                    = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                    f q_start := by
        rw [cuccaro_uma_chain_reverse_frame_below k (q_start + 2) _ q_start (by omega)]
        rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ q_start (by omega)]
      have hg_qs1 : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                      (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                         (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                      (q_start + 1)
                    = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                    f (q_start + 1) := by
        rw [cuccaro_uma_chain_reverse_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
        rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
      have hg_qs2 : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                      (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                         (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                      (q_start + 2)
                    = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                    f (q_start + 2) := by
        have hih := cuccaro_n_bit_adder_full_carry_in_restored k (q_start + 2)
          (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
        simp only [cuccaro_n_bit_adder_full, Gate.applyNat_seq] at hih
        exact hih
      rw [hg_qs, hg_qs1, hg_qs2]
      rw [cuccaro_MAJ_at_a q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_at_b q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_at_c q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      unfold Boolean.majority
      cases f q_start <;> cases f (q_start + 1) <;> cases f (q_start + 2) <;> rfl
    · -- i ≥ 1: position q_start + 2i + 2 > q_start + 2, untouched by MAJ_0/UMA_0.
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < k := by omega
      -- UMA_0 at q_start + 2(j+1) + 2: doesn't touch (it's > q_start + 2).
      rw [cuccaro_UMA_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 2) (by omega) (by omega) (by omega)]
      -- IH for sub-adder at q_start+2 with input MAJ_0(f) at sub-index j.
      have hih := ih (q_start + 2)
        (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f) j hj
      simp only [cuccaro_n_bit_adder_full, Gate.applyNat_seq] at hih
      have hpos : q_start + 2 + 2 * j + 2 = q_start + 2 * (j + 1) + 2 := by ring
      rw [hpos] at hih
      rw [hih]
      -- MAJ_0 doesn't touch q_start + 2(j+1) + 2 either.
      rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 2) (by omega) (by omega) (by omega)]

/-- **Sum-bit invariant: at position `q_start + 2*i + 1` (for `i < n`),
the full Cuccaro adder produces the sum bit `c_i ⊕ b_i ⊕ a_i`.**

This is the third and final positional invariant for the full adder.
With the carry-in and a-restoration theorems above, this completes the
symbolic specification of `cuccaro_n_bit_adder_full`.

Proof structure: induction on n, splitting i into `i = 0` (UMA_0's
b-wire action + cuccaro_UMA_undo_MAJ_b at the local level) and
`i ≥ 1` (sub-adder's IH + carry-shift bridging). -/
theorem cuccaro_n_bit_adder_full_sum_bit
    (n q_start : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f (q_start + 2 * i + 1)
      = xor (xor (cuccaro_carry f q_start i) (f (q_start + 2 * i + 1)))
            (f (q_start + 2 * i + 2)) := by
  induction n generalizing q_start f i with
  | zero => omega
  | succ k ih =>
    show Gate.applyNat
        (seq (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                  (cuccaro_maj_chain k (q_start + 2)))
              (seq (cuccaro_uma_chain_reverse k (q_start + 2))
                   (cuccaro_UMA q_start (q_start + 1) (q_start + 2))))
        f (q_start + 2 * i + 1) = _
    simp only [Gate.applyNat_seq]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- i = 0: position q_start + 1. UMA_0's b-wire action.
      subst hi0
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [cuccaro_UMA_at_b q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      have hg_qs : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                      (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                         (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                      q_start
                    = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                    f q_start := by
        rw [cuccaro_uma_chain_reverse_frame_below k (q_start + 2) _ q_start (by omega)]
        rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ q_start (by omega)]
      have hg_qs1 : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                      (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                         (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                      (q_start + 1)
                    = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                    f (q_start + 1) := by
        rw [cuccaro_uma_chain_reverse_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
        rw [cuccaro_maj_chain_frame_below k (q_start + 2) _ (q_start + 1) (by omega)]
      have hg_qs2 : Gate.applyNat (cuccaro_uma_chain_reverse k (q_start + 2))
                      (Gate.applyNat (cuccaro_maj_chain k (q_start + 2))
                         (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f))
                      (q_start + 2)
                    = Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                                    f (q_start + 2) := by
        have hih := cuccaro_n_bit_adder_full_carry_in_restored k (q_start + 2)
          (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f)
        simp only [cuccaro_n_bit_adder_full, Gate.applyNat_seq] at hih
        exact hih
      rw [hg_qs, hg_qs1, hg_qs2]
      rw [cuccaro_MAJ_at_a q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_at_b q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_at_c q_start (q_start + 1) (q_start + 2)
          (by omega) (by omega) (by omega)]
      -- cuccaro_carry f q_start 0 = f q_start (by definition).
      unfold cuccaro_carry
      unfold Boolean.majority
      cases f q_start <;> cases f (q_start + 1) <;> cases f (q_start + 2) <;> rfl
    · -- i ≥ 1: position q_start + 2(j+1) + 1, untouched by MAJ_0/UMA_0.
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < k := by omega
      rw [cuccaro_UMA_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 1) (by omega) (by omega) (by omega)]
      have hih := ih (q_start + 2)
        (Gate.applyNat (cuccaro_MAJ q_start (q_start + 1) (q_start + 2)) f) j hj
      simp only [cuccaro_n_bit_adder_full, Gate.applyNat_seq] at hih
      have hpos1 : q_start + 2 + 2 * j + 1 = q_start + 2 * (j + 1) + 1 := by ring
      have hpos2 : q_start + 2 + 2 * j + 2 = q_start + 2 * (j + 1) + 2 := by ring
      rw [hpos1, hpos2] at hih
      rw [hih]
      -- IH gives the sum-bit formula in terms of cuccaro_carry (MAJ_0 f) (q_start+2) j and MAJ_0(f) at sub-positions.
      -- Convert via shift lemma + MAJ_0 frame.
      rw [cuccaro_carry_after_MAJ0_shift q_start f j]
      rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 1) (by omega) (by omega) (by omega)]
      rw [cuccaro_MAJ_at_other q_start (q_start + 1) (q_start + 2)
          (q_start + 2 * (j + 1) + 2) (by omega) (by omega) (by omega)]

/-! ## Final correctness: combined symbolic specification of the full adder.

The three positional invariants together pin down the full state at
every position of the adder's support, modulo the "above support"
frame already proved.  This is the symbolic semantic correctness of
`cuccaro_n_bit_adder_full`, validating the Python simulation
externally. -/

/-- **HEADLINE — symbolic correctness of the full Cuccaro adder.**
For any input state `f`, the full Cuccaro adder of length `n`
starting at `q_start`:
- restores the carry-in at position `q_start`;
- produces sum bit `c_i ⊕ b_i ⊕ a_i` at position `q_start + 2*i + 1`
  for each `i < n` (where c_i is the cumulative classical carry);
- restores the read register `a_i` at position `q_start + 2*i + 2`. -/
theorem cuccaro_n_bit_adder_full_correct
    (n q_start : Nat) (f : Nat → Bool) :
    (Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f q_start = f q_start) ∧
    (∀ i, i < n →
        Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f (q_start + 2 * i + 1)
          = xor (xor (cuccaro_carry f q_start i) (f (q_start + 2 * i + 1)))
                (f (q_start + 2 * i + 2))) ∧
    (∀ i, i < n →
        Gate.applyNat (cuccaro_n_bit_adder_full n q_start) f (q_start + 2 * i + 2)
          = f (q_start + 2 * i + 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact cuccaro_n_bit_adder_full_carry_in_restored n q_start f
  · exact fun i hi => cuccaro_n_bit_adder_full_sum_bit n q_start f i hi
  · exact fun i hi => cuccaro_n_bit_adder_full_a_restored n q_start f i hi

/-! ## Status note (Tick 43).

**ALL THREE POSITIONAL INVARIANTS LANDED, KERNEL-CLEAN.**

Theorems landed this tick:
- `cuccaro_carry` definition.
- `cuccaro_carry_after_MAJ0_shift` (the algebraic shift lemma).
- **MAJ-chain forward invariant** (3 positional theorems):
  `cuccaro_maj_chain_at_carry_a`, `cuccaro_maj_chain_at_b_xor`,
  `cuccaro_maj_chain_at_top_carry`.
- **UMA-undoes-MAJ algebraic identities** at the 3-position local
  level: `cuccaro_UMA_undo_MAJ_a/b/c`.
- **Full-adder correctness — all three positional invariants**:
  `cuccaro_n_bit_adder_full_carry_in_restored`,
  `cuccaro_n_bit_adder_full_sum_bit`,
  `cuccaro_n_bit_adder_full_a_restored`, and their conjunction
  `cuccaro_n_bit_adder_full_correct`.

All headlines: `[propext, Quot.sound]` only (kernel-clean).

The symbolic Cuccaro adder spec is now fully verified.  Next-tick
deliverable: bridge `cuccaro_carry`/sum-bit formulas to integer
arithmetic (`cuccaroAdderSpec = (a + b) % 2^bits`) and to the framework
`Adder.carry`/`Adder.sumfb` so that decoded outputs match the natural
arithmetic spec. After that, build controlled modular add-constant
toward the SQIR-axiom-closure pipeline.

The original SQIR placeholder axioms remain NOT closed; this tick
delivers the COMPLETE symbolic semantic correctness of the
exact-budget primitive adder. -/

end FormalRV.BQAlgo
