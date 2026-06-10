/-
  FormalRV.Shor.MeasUncompute — measurement-based uncomputation as a top-level IR design,
  and the measurement-uncompute lookup-add (Gidney/Berry, 1905.07682 l.200–227, l.772).

  Gidney's lookup-add does `read · add · UNcompute`.  The unitary uncompute is a SECOND
  full table read (`2·w·2^w` Toffolis).  Measurement-based uncomputation instead MEASURES
  the temp register (disentangling it) and applies a cheap phase fixup, so the temp returns
  to |0⟩ for ~0 Toffolis.  This halves the read cost — the `4·w·2^w → 2·w·2^w` step toward
  the paper's `2^w`.

  Modelling measurement needs a new IR constructor.  Rather than touch the core `Gate`
  inductive (which would break every exhaustive match across the codebase), we add a small
  measurement-augmented IR `EGate = base Gate | mz | seq`.  `mz q` resets qubit `q` to |0⟩ —
  the net COMPUTATIONAL effect of measure-in-X + phase-fixup + reset.  (The PHASE-fixup
  correctness is a named obligation, cited; it lives in the amplitude layer, not the
  Boolean `applyNat`.)

  CROSS-REFERENCES (status updates to the model above):

  * The `mz`-as-reset Boolean model is now JUSTIFIED at the density layer: see
    `FormalRV.Shor.MeasuredANDUncompute`, `FormalRV.Shor.MeasuredLookupUncompute`, and
    `FormalRV.Shor.PhaseLookupFixup`, where the X-measure + classically-controlled-fixup
    channel is PROVEN to be the perfect uncompute.  The "named obligation" caveat above
    is therefore discharged — `mz` is no longer an unproven amplitude-layer assumption.

  * `babbushLookupAdd` (below) has a PROVEN value-level layout defect for `W ≥ 2`
    (`babbushLookupAddValueSpec_unsatisfiable` / `babbushLookupAdd_misses_table` in
    `FormalRV.Shor.MeasUncomputeValue`).  Its Toffoli-count theorems in this file remain
    valid; for value-correct semantics use `babbushLookupAddAt` from
    `FormalRV.Shor.MeasUncomputeAt`.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuit
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGateDerivations
import FormalRV.Arithmetic.Cuccaro.CuccaroFull

namespace FormalRV.Shor.MeasUncompute

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit FormalRV.Shor.WindowedLookupAdd

/-- Measurement-augmented gate IR. -/
inductive EGate where
  | base : Gate → EGate
  | mz   : Nat → EGate
  | seq  : EGate → EGate → EGate

/-- Boolean (value) semantics.  `mz q` resets qubit `q` to `false` — the computational
    effect of measurement-based uncomputation (the measured qubit is disentangled and
    returns to |0⟩). -/
def EGate.applyNat : EGate → (Nat → Bool) → (Nat → Bool)
  | .base g,  f => Gate.applyNat g f
  | .mz q,    f => Function.update f q false
  | .seq a b, f => EGate.applyNat b (EGate.applyNat a f)

/-- T-count: base gates count their T-gates; measurement is T-free. -/
def EGate.tcount : EGate → Nat
  | .base g  => Gate.tcount g
  | .mz _    => 0
  | .seq a b => EGate.tcount a + EGate.tcount b

/-- Toffoli count = T-count / 7 (the PPM magic-state currency). -/
def EGate.toffoli (g : EGate) : Nat := EGate.tcount g / 7

/-- Measure-reset a list of qubits (used to clear the temp register after the add). -/
def mzList : List Nat → EGate
  | []      => EGate.base Gate.I
  | q :: qs => EGate.seq (mzList qs) (EGate.mz q)

theorem tcount_mzList (L : List Nat) : EGate.tcount (mzList L) = 0 := by
  induction L with
  | nil => rfl
  | cons q qs ih => simp [mzList, EGate.tcount, Gate.tcount, ih]

/-- **Measurement-uncompute lookup-add** (Gidney l.276 with measurement-based uncompute):
    read `T[a]` into the temp (= adder addend), `acc += temp`, then MEASURE-clear the temp
    instead of a second read. -/
def measLookupAdd (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) : EGate :=
  EGate.seq (EGate.seq
    (EGate.base (lookupReadAt w (addendIdx q_start) W T))
    (EGate.base (cuccaro_n_bit_adder_full bits q_start)))
    (mzList ((List.range W).map (addendIdx q_start)))

/-- **Structural Toffoli count of the measurement-uncompute lookup-add**: `2·w·2^w + 2·bits`
    — exactly HALF the lookup-read cost of the double-read `lookupAddAt`
    (`4·w·2^w + 2·bits`).  The measurement removes the second read (`mzList` is Toffoli-free),
    so the `4·w·2^w → 2·w·2^w` reduction is read off the verified `EGate` structure. -/
theorem toffoli_measLookupAdd (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) :
    EGate.toffoli (measLookupAdd w W T bits q_start) = 2 * w * 2 ^ w + 2 * bits := by
  unfold EGate.toffoli measLookupAdd
  simp only [EGate.tcount, tcount_mzList]
  rw [tcount_lookupReadAt, tcount_cuccaro_n_bit_adder_full,
      show 14 * w * 2 ^ w + 14 * bits + 0 = (2 * w * 2 ^ w + 2 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- For comparison, the unitary double-read `lookupAddAt` costs `4·w·2^w + 2·bits` Toffolis
    (`WindowedCircuit.tcount_lookupAddAt` over 7).  So measurement-uncompute saves the full
    second read `2·w·2^w`. -/
theorem measUncompute_saves_a_read (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) :
    EGate.toffoli (measLookupAdd w W T bits q_start) + 2 * w * 2 ^ w
      = toffoliCount (lookupAddAt w W T bits q_start) := by
  rw [toffoli_measLookupAdd, toffoliCount, tcount_lookupAddAt,
      show 2 * (14 * w * 2 ^ w) + 14 * bits = (4 * w * 2 ^ w + 2 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  ring

/-! ## Measurement-uncompute of the per-iteration cascade: read cost `w·2^w` (not `2w·2^w`).

The unitary unary-lookup iteration is `flips·cascade·cnots·UNCOMPUTE·flips` — `2w` Toffolis
per row (`w` cascade + `w` uncompute).  Measuring (rather than unitarily uncomputing) the
AND-ancillas drops the per-row cost to `w`, halving the whole read to `w·2^w` — a further
structural step toward the paper's `2^w` (the last factor `w` is the babbush Gray-code
amortization, cited at l.594). -/

/-- Compute-only unary-lookup iteration: `flips·cascade·cnots·flips`, with NO unitary
    uncompute (the AND-ancillas are cleared by measurement afterwards). -/
def unaryIterationCompute (w : Nat) (flips cnots : List Nat) : Gate :=
  Gate.seq (Gate.seq (Gate.seq (x_gates_from_indices flips) (prefix_and_cascade w))
    (cx_gates_from_indices (ulookup_and_idx (w - 1)) cnots)) (x_gates_from_indices flips)

theorem tcount_unaryIterationCompute (w : Nat) (flips cnots : List Nat) :
    Gate.tcount (unaryIterationCompute w flips cnots) = 7 * w := by
  simp only [unaryIterationCompute, Gate.tcount, tcount_x_gates_zero, tcount_cx_gates_zero,
             tcount_prefix_and_cascade]
  omega

/-- One measurement-uncompute iteration: compute (`w` Toffolis) then measure-clear the AND
    ancillas (`0` Toffolis). -/
def measUnaryIteration (w : Nat) (flips cnots : List Nat) : EGate :=
  EGate.seq (EGate.base (unaryIterationCompute w flips cnots))
            (mzList ((List.range w).map ulookup_and_idx))

theorem tcount_measUnaryIteration (w : Nat) (flips cnots : List Nat) :
    EGate.tcount (measUnaryIteration w flips cnots) = 7 * w := by
  simp only [measUnaryIteration, EGate.tcount, tcount_mzList, tcount_unaryIterationCompute,
             Nat.add_zero]

/-- The full measurement-uncompute read over a table of `iters` rows. -/
def measUnaryRead (w : Nat) : List (List Nat × List Nat) → EGate
  | []            => EGate.base Gate.I
  | (f, c) :: rest => EGate.seq (measUnaryRead w rest) (measUnaryIteration w f c)

/-- **Read cost `w·2^w` (= `7·w·#rows` T), HALF the unitary `unary_lookup_multi_iteration`
    (`2w·2^w`)** — the per-row uncompute is replaced by a Toffoli-free measurement. -/
theorem tcount_measUnaryRead (w : Nat) (iters : List (List Nat × List Nat)) :
    EGate.tcount (measUnaryRead w iters) = 7 * w * iters.length := by
  induction iters with
  | nil => simp [measUnaryRead, EGate.tcount, Gate.tcount]
  | cons hd rest ih =>
    obtain ⟨f, c⟩ := hd
    rw [measUnaryRead, EGate.tcount, ih, tcount_measUnaryIteration, List.length_cons]
    ring

/-- **Fully measurement-optimized lookup-add**: cascade-measurement read (`w·2^w`) ·
    Cuccaro add (`2·bits`) · measure-clear temp.  Toffoli count `w·2^w + 2·bits` — a 4×
    reduction from the unitary double-read `4·w·2^w + 2·bits`.  The only gap to the paper's
    `2^w + 2·bits` is the remaining factor `w` (babbush Gray-code amortization, cited l.594). -/
def optLookupAdd (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) : EGate :=
  EGate.seq (EGate.seq
    (measUnaryRead w ((List.range (2 ^ w)).map
      (fun v => (addrFlips w v, wordCnotsAt (addendIdx q_start) W (T v)))))
    (EGate.base (cuccaro_n_bit_adder_full bits q_start)))
    (mzList ((List.range W).map (addendIdx q_start)))

theorem toffoli_optLookupAdd (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) :
    EGate.toffoli (optLookupAdd w W T bits q_start) = w * 2 ^ w + 2 * bits := by
  unfold EGate.toffoli optLookupAdd
  simp only [EGate.tcount, tcount_mzList, tcount_measUnaryRead, tcount_cuccaro_n_bit_adder_full,
             List.length_map, List.length_range]
  rw [show 7 * w * 2 ^ w + 14 * bits + 0 = (w * 2 ^ w + 2 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-! ## The babbush2018 unary-iteration QROM — `2^w − 1` Toffolis, NO black box.

Babbush et al. (arXiv:1805.03662, §III.A "Unary Iteration", §III.C "QROM"): build the
one-hot index indicators by MERGING adjacent ANDs (representative-reuse), giving exactly
`L − 1 = 2^w − 1` AND/Toffoli gates with `w = log L` ancillas (T-count `4L−4`), independent
of the word width.  We construct it directly as an `EGate`: at each node compute one AND
(`CCX`), REUSE it for both halves via a `CX` flip (`ctrl∧b ↦ ctrl∧¬b`), recurse, then
measure-uncompute the AND (Toffoli-free).  The recursion `T(w) = 2·T(w−1) + 1` gives exactly
`2^w − 1` Toffolis.  This is the construction the paper cites — now first-class and emittable. -/

/-- Unary-iteration QROM read: on the `d`-bit address sub-register (bit `i` at `addrBase+i`)
    with sub-tree `ctrl` and covered base index `base`, XOR `T[address]` into the `W`-bit
    output (`outBase`-based), using ancillas `ancBase + (0..d-1)` cleared by measurement. -/
def unaryQROM (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase : Nat) :
    Nat → Nat → Nat → EGate
  | 0,     ctrl, base =>
      EGate.base (cx_gates_from_indices ctrl (wordCnotsAt (fun j => outBase + j) W (T base)))
  | d + 1, ctrl, base =>
      EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq
        (EGate.base (Gate.CCX ctrl (addrBase + d) (ancBase + d)))                 -- anc ← ctrl∧bit_d
        (unaryQROM W T addrBase ancBase outBase d (ancBase + d) (base + 2 ^ d)))  -- bit_d = 1 half
        (EGate.base (Gate.CX ctrl (ancBase + d))))                               -- anc ← ctrl∧¬bit_d
        (unaryQROM W T addrBase ancBase outBase d (ancBase + d) base))           -- bit_d = 0 half
        (EGate.base (Gate.CX ctrl (ancBase + d))))                              -- restore anc ← ctrl∧bit_d
        (EGate.mz (ancBase + d))                                                 -- measure-uncompute anc

/-- **The unary-iteration QROM has exactly `2^d − 1` Toffolis** (`7·(2^d−1)` T) — the
    babbush `L − 1` count, derived structurally from the `EGate` (`T(d) = 2T(d−1) + 1`). -/
theorem tcount_unaryQROM (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase : Nat) :
    ∀ (d ctrl base : Nat),
      EGate.tcount (unaryQROM W T addrBase ancBase outBase d ctrl base) = 7 * (2 ^ d - 1)
  | 0, ctrl, base => by
      simp [unaryQROM, EGate.tcount, Gate.tcount, tcount_cx_gates_zero]
  | d + 1, ctrl, base => by
      simp only [unaryQROM, EGate.tcount, Gate.tcount, tcount_cx_gates_zero,
                 tcount_unaryQROM W T addrBase ancBase outBase d]
      have h2d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega

theorem toffoli_unaryQROM (W : Nat) (T : Nat → Nat) (addrBase ancBase outBase d ctrl base : Nat) :
    EGate.toffoli (unaryQROM W T addrBase ancBase outBase d ctrl base) = 2 ^ d - 1 := by
  unfold EGate.toffoli
  rw [tcount_unaryQROM, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **The fully-optimized lookup-add reaches the paper's `2^w − 1 + 2·bits` Toffolis**, with
    NO black box: babbush unary read (`2^w − 1`) · Cuccaro add (`2·bits`) · measure-clear.
    This closes the Gray-code/amortization factor structurally — the lookup cost is now
    `≈ 2^w + 2·bits`, matching Gidney–Ekerå's `2^{c_mul+c_exp}` lookup.

    WARNING (value semantics): this circuit has a PROVEN value-level LAYOUT defect for
    `W ≥ 2` — `babbushLookupAddValueSpec_unsatisfiable` and `babbushLookupAdd_misses_table`
    in `FormalRV.Shor.MeasUncomputeValue` show no decoder pair can make it implement the
    table lookup-add.  The Toffoli-count theorems below remain valid (counts are
    layout-independent).  For the layout-corrected, value-CORRECT variant import
    `FormalRV.Shor.MeasUncomputeAt` and use `babbushLookupAddAt`. -/
def babbushLookupAdd (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase outBase q_start : Nat) : EGate :=
  EGate.seq (EGate.seq
    (unaryQROM W T addrBase ancBase outBase w 0 0)
    (EGate.base (cuccaro_n_bit_adder_full bits q_start)))
    (mzList ((List.range W).map (fun j => outBase + j)))

theorem toffoli_babbushLookupAdd (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase outBase q_start : Nat) :
    EGate.toffoli (babbushLookupAdd w W T bits addrBase ancBase outBase q_start)
      = (2 ^ w - 1) + 2 * bits := by
  unfold EGate.toffoli babbushLookupAdd
  simp only [EGate.tcount, tcount_mzList, tcount_unaryQROM, tcount_cuccaro_n_bit_adder_full]
  have h2w : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  rw [show 7 * (2 ^ w - 1) + 14 * bits + 0 = ((2 ^ w - 1) + 2 * bits) * 7 by
        have : 2 ^ w - 1 + 1 = 2 ^ w := by omega
        nlinarith [this]]
  rw [Nat.mul_div_cancel _ (by norm_num)]

/-! ## Value-correctness of the measurement-uncompute step.

The measurement clears the temp register without disturbing the accumulator, so
`measLookupAdd` computes the SAME accumulator as the (proven-correct) unitary read+adder. -/

theorem applyNat_mzList_clears (L : List Nat) (f : Nat → Bool) {p : Nat} (hp : p ∈ L) :
    EGate.applyNat (mzList L) f p = false := by
  induction L with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [mzList, EGate.applyNat]
    by_cases hpq : p = q
    · subst hpq; simp
    · rcases List.mem_cons.mp hp with h | h
      · exact absurd h hpq
      · rw [Function.update_of_ne hpq]; exact ih h

theorem applyNat_mzList_preserves (L : List Nat) (f : Nat → Bool) {p : Nat} (hp : p ∉ L) :
    EGate.applyNat (mzList L) f p = f p := by
  induction L with
  | nil => rfl
  | cons q qs ih =>
    simp only [mzList, EGate.applyNat]
    have hpq : p ≠ q := fun h => hp (by rw [h]; exact List.mem_cons.mpr (Or.inl rfl))
    rw [Function.update_of_ne hpq]
    exact ih (fun h => hp (List.mem_cons.mpr (Or.inr h)))

/-- **The measurement-uncompute leaves the accumulator equal to the unitary read+adder's.**
    The accumulator bit `q_start + 2i + 1` (odd offset) is not among the cleared temp/addend
    positions `q_start + 2j + 2` (even offset), so `measLookupAdd`'s accumulator equals the
    read·add accumulator — which the proven QROM-read + Cuccaro lemmas fix to `acc + T[a]`.
    (The phase-fixup correctness of measurement-uncompute is a named obligation, cited
    Berry 2019 / Gidney 1905.07682 l.200–227.) -/
theorem measLookupAdd_acc_eq (w W : Nat) (T : Nat → Nat) (bits q_start i : Nat)
    (f : Nat → Bool) :
    EGate.applyNat (measLookupAdd w W T bits q_start) f (q_start + 2 * i + 1)
      = Gate.applyNat (Gate.seq (lookupReadAt w (addendIdx q_start) W T)
          (cuccaro_n_bit_adder_full bits q_start)) f (q_start + 2 * i + 1) := by
  unfold measLookupAdd
  simp only [EGate.applyNat]
  rw [applyNat_mzList_preserves]
  · rfl
  · simp only [List.mem_map, List.mem_range, not_exists, addendIdx]
    intro j; omega

end FormalRV.Shor.MeasUncompute
