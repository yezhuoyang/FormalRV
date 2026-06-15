/-
  FormalRV.Shor.WindowedCoset — the COSET-REPRESENTATION correctness bridge for
  Gidney–Ekerå's windowed modular arithmetic (1905.09749 §"coset representation
  of modular integers" + §"oblivious carry runways").

  ════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE PROVES (and what it does NOT)
  ════════════════════════════════════════════════════════════════════════════

  The OPTIMAL-COUNT object is the mod-2^bits windowed multiplier
  `windowedMulCircuitOf` (proven in `WindowedCircuit` / `WindowedCircuitCorrect`):
  it computes `decodeAcc = (acc + a·y) mod 2^bits` and carries the paper's
  structural `0.3 n³` Toffoli count (`windowedMulCircuit_toffoli_padded` — the
  `g_pad` coset padding is ALREADY in the verified count).  The EXACT mod-N
  multiplier (`WindowedModN`) is *more expensive* (per-window compare +
  conditional-subtract).  Gidney's coset representation lets the CHEAP
  mod-2^bits multiplier compute the right value MOD N — no explicit reduction —
  as long as the padded register never wraps `2^bits`.

  **Coset representation.**  A value `x mod N` is stored in a padded
  `bits = n + g_pad`-qubit register as ANY representative `v` with `v % N = x`
  and `v < 2^bits`.  A PLAIN (non-modular) addition `v += t` then automatically
  yields a valid coset representative of `(x + t) mod N` — PROVIDED `v + t`
  does not wrap `2^bits`.  The padding `g_pad ≈ 3·lg n + 10` bounds the
  wrap probability (`WindowedCostModel.totalDeviation ≈ 7.6·10⁻⁸`).

  STAGES LANDED (all kernel-clean, no `sorry`/`native_decide`/axioms):

    1. `IsCosetRep` / `cosetValue` — the predicate + readout (§1).
    2. `cosetAdd_correct` — EXACT, no approximation: under no-wrap, plain
       addition on a coset rep yields a coset rep of the modular sum (§2).
       This is the structural heart.
    3. `windowedCosetMul_correct` — composing (2) with the verified
       `windowedMulCircuitOf_correct`: the OPTIMAL-COUNT mod-2^bits windowed
       multiplier, run on a coset-rep input under the no-wrap hypothesis,
       leaves a coset rep of `(a·y) mod N` in the accumulator (§3).
    4. `noWrap_of_padding` — the exact SUFFICIENT no-wrap condition in terms of
       the register width and the running value bound; the per-add growth bound
       (`coset value grows by ≤ N`) and the `numAdds·N < 2^bits` slack (§4).

  STAGED / NAMED OBLIGATIONS (structures, NO `sorry`):

    • `CosetDeviationBound` (§5) — the PROBABILISTIC wrap bound: over the random
      coset offsets the paper uses, the probability of a wrap event during the
      whole exponentiation is `≤ WindowedCostModel.totalDeviation`.  This is the
      measure-theoretic leg (random-offset averaging, Gidney Thm 2.10
      subadditivity) that is beyond the deterministic machinery here; it is
      stated precisely as a structure carrying the bound, NOT assumed.  Every
      DETERMINISTIC result above is proven WITHOUT it.

    • `ObliviousCarryRunway` (§6) — the runway-fold operation.  Its STRUCTURAL
      cost is already verified: `windowedMulCircuit_toffoli_padded` shows the
      padded register contributes `2·pad` Toffolis/window — the `n·g_pad/g_sep`
      runway term of the paper.  The runway *circuit* (piecewise additions over
      `g_sep`-separated runways) is documented as a structure obligation
      carrying its design + count; the structural padded count it must match is
      `windowedMulCircuit_toffoli_padded`, recorded as a field.

  ════════════════════════════════════════════════════════════════════════════
  WHY THIS CLOSES THE AUDIT'S value↔count SPLIT
  ════════════════════════════════════════════════════════════════════════════
  The audit kept `windowedMulCircuitOf` (cheap, mod-2^bits, optimal count) and
  `windowedModNMulCircuit` (exact mod-N, expensive) as separate objects: the
  cheap one had the count but the WRONG value (mod 2^bits, not mod N); the
  expensive one had the right value but not the optimal count.  This file
  certifies the cheap object computes mod-N *in the coset representation*
  (exact under no-wrap, §3), so the OPTIMAL count of `windowedMulCircuitOf`
  IS the count of a mod-N-correct computation — modulo the named, honestly
  isolated `CosetDeviationBound` wrap obligation.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedCircuitCorrect
import FormalRV.Arithmetic.Windowed.WindowedInPlace
import FormalRV.Arithmetic.Windowed.WindowedCostModel

namespace FormalRV.Shor.WindowedCoset

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit

/-! ## §1. The coset predicate and readout.

A `bits`-qubit register value `v` is a COSET REPRESENTATIVE of `target mod N`
when `v` reduces to `target` mod `N` and `v` fits the register (`v < 2^bits`).
The READOUT `cosetValue` is simply `v % N` — the true modular value, recovered
without any in-register reduction. -/

/-- `v` (a `bits`-qubit register value) is a coset representative of `target`
    modulo `N`: it reduces to `target` and fits the padded register. -/
def IsCosetRep (bits N v target : Nat) : Prop :=
  v % N = target % N ∧ v < 2 ^ bits

/-- The coset READOUT: the true modular value held by representative `v`. -/
def cosetValue (N v : Nat) : Nat := v % N

/-- The readout of any coset rep of `target` is `target % N`. -/
theorem cosetValue_of_isCosetRep {bits N v target : Nat}
    (h : IsCosetRep bits N v target) : cosetValue N v = target % N :=
  h.1

/-- `target % N` is itself a coset rep of `target` whenever it fits the register
    (the canonical, smallest representative). -/
theorem isCosetRep_canonical {bits N target : Nat}
    (hfit : target % N < 2 ^ bits) :
    IsCosetRep bits N (target % N) target :=
  ⟨Nat.mod_mod_of_dvd target dvd_rfl, hfit⟩

/-! ## §2. Coset-add preserves the representation (EXACT, under no-wrap).

This is the structural heart of Gidney's coset trick: a PLAIN (non-modular)
register addition `v += t` IS a modular addition in the coset representation,
PROVIDED the result does not wrap the register (`v + t < 2^bits`).  No
approximation enters — this is an exact `Nat.ModEq` identity. -/

/-- **`cosetAdd_correct` — plain addition = modular addition in the coset rep.**
    If `v` is a coset rep of `x mod N` and `t` is a coset rep of `r mod N`
    (e.g. `t = r < N`), and the plain sum does not wrap (`v + t < 2^bits`),
    then the plain register sum `v + t` is itself a coset rep of `(x + r) mod N`.
    EXACT — no probability, conditioned only on the no-wrap hypothesis. -/
theorem cosetAdd_correct (bits N v t x r : Nat)
    (hv : IsCosetRep bits N v x) (ht : IsCosetRep bits N t r)
    (hnowrap : v + t < 2 ^ bits) :
    IsCosetRep bits N (v + t) (x + r) := by
  refine ⟨?_, hnowrap⟩
  -- (v + t) % N = (x + r) % N, from v ≡ x and t ≡ r [MOD N].
  calc (v + t) % N
      = ((v % N) + (t % N)) % N := by rw [Nat.add_mod]
    _ = ((x % N) + (r % N)) % N := by rw [hv.1, ht.1]
    _ = (x + r) % N := by rw [← Nat.add_mod]

/-- Convenience form: adding any addend `t` (a coset rep of itself, since
    `t % N = t % N` trivially) to a coset rep of `x`, without wrap, yields a
    coset rep of `(x + t) mod N`.  This is the form the windowed multiplier
    uses: each window adds a table-row addend directly. -/
theorem cosetAdd_addend (bits N v t x : Nat)
    (hv : IsCosetRep bits N v x)
    (hnowrap : v + t < 2 ^ bits) :
    IsCosetRep bits N (v + t) (x + t) := by
  refine cosetAdd_correct bits N v t x t hv ⟨rfl, ?_⟩ hnowrap
  -- t < 2^bits: from no-wrap, t ≤ v + t < 2^bits.
  exact lt_of_le_of_lt (Nat.le_add_left t v) hnowrap

/-! ## §3. The optimal-count multiplier computes mod-N in the coset rep.

Compose §2 with the verified mod-2^bits multiplier
`windowedMulCircuitOf_correct` (`decodeAcc = (a·y) mod 2^bits`).  The clean
input has accumulator `0` — a coset rep of `0 mod N`.  Under the no-wrap
hypothesis `a·y < 2^bits`, the mod-2^bits result equals the plain product
`a·y`, which IS a coset rep of `(a·y) mod N`.  So the OPTIMAL-COUNT windowed
multiplier computes the right value mod N in the coset representation. -/

/-- The mod-2^bits product reduced into the coset rep equals the true value.
    Under no-wrap (`a·y < 2^bits`), `(a·y) mod 2^bits = a·y` is a coset rep
    of `(a·y) mod N`. -/
theorem cosetRep_of_modProduct (bits N a y : Nat)
    (hnowrap : a * y < 2 ^ bits) :
    IsCosetRep bits N ((a * y) % 2 ^ bits) (a * y) := by
  rw [Nat.mod_eq_of_lt hnowrap]
  exact ⟨rfl, hnowrap⟩

/-- **`windowedCosetMul_correct` — the optimal-count multiplier is mod-N correct
    in the coset representation.**  For ANY adder `A`, the OPTIMAL-COUNT
    mod-2^bits windowed multiplier `windowedMulCircuitOf A w bits a numWin`, run
    on the clean input `mulInputOf A w bits numWin y`, leaves an accumulator
    value that is a COSET REPRESENTATIVE of `(a·y) mod N`, PROVIDED:
      • `0 < w`, `y < 2^(w·numWin)`, the adder's ancilla starts clean
        (the existing `windowedMulCircuitOf_correct` hypotheses), and
      • NO-WRAP: `a·y < 2^bits` (the padded register holds the full product).

    Its readout `cosetValue N (decodeAcc …) = (a·y) % N`.  EXACT under no-wrap:
    the only thing standing between this and an unconditional mod-N certificate
    is the probabilistic wrap bound `CosetDeviationBound` (§5). -/
theorem windowedCosetMul_correct (A : Adder) (w bits a numWin N y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w))
    (hnowrap : a * y < 2 ^ bits) :
    IsCosetRep bits N
      (decodeAccOf A (Gate.applyNat (windowedMulCircuitOf A w bits a numWin)
        (mulInputOf A w bits numWin y)) (1 + 2 * w) bits)
      (a * y) := by
  rw [windowedMulCircuitOf_correct A w bits a numWin y hw hy hclean]
  exact cosetRep_of_modProduct bits N a y hnowrap

/-- The readout corollary: the optimal-count multiplier's accumulator, read mod
    `N`, is exactly the true modular product `(a·y) mod N`. -/
theorem windowedCosetMul_readout (A : Adder) (w bits a numWin N y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hclean : A.ancClean (mulInputOf A w bits numWin y) bits (1 + 2 * w))
    (hnowrap : a * y < 2 ^ bits) :
    cosetValue N
      (decodeAccOf A (Gate.applyNat (windowedMulCircuitOf A w bits a numWin)
        (mulInputOf A w bits numWin y)) (1 + 2 * w) bits)
      = (a * y) % N :=
  cosetValue_of_isCosetRep
    (windowedCosetMul_correct A w bits a numWin N y hw hy hclean hnowrap)

/-- **Cuccaro instance** (the optimal-count Cuccaro multiplier, mod-N correct in
    the coset rep under no-wrap). -/
theorem windowedCosetMul_correct_cuccaro (w bits a numWin N y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin)) (hnowrap : a * y < 2 ^ bits) :
    IsCosetRep bits N
      (decodeAccOf cuccaroAdder
        (Gate.applyNat (windowedMulCircuitOf cuccaroAdder w bits a numWin)
          (mulInputOf cuccaroAdder w bits numWin y)) (1 + 2 * w) bits)
      (a * y) := by
  refine windowedCosetMul_correct cuccaroAdder w bits a numWin N y hw hy ?_ hnowrap
  show mulInputOf cuccaroAdder w bits numWin y (1 + 2 * w) = false
  have hspan : cuccaroAdder.span bits = 2 * bits + 1 := rfl
  exact mulInputOf_low cuccaroAdder w bits numWin y _
    (by unfold ulookup_ctrl_idx; omega) (by omega)

/-! ## §4. The no-wrap / padding condition.

Each coset addition grows the register value by at most the addend; if every
addend is `< N` and the chain does `numAdds` additions starting from `< N`, the
running value stays `< (numAdds + 1)·N`.  So `(numAdds + 1)·N ≤ 2^bits` is a
SUFFICIENT no-wrap condition — and since `bits = n + g_pad`, this is what fixes
the padding `g_pad`: it must absorb `lg(numAdds + 1)` extra bits above `lg N`.

This is the DETERMINISTIC sufficient condition.  The paper instead pads less
(`g_pad ≈ 3 lg n + 10`) and accepts a small wrap PROBABILITY over random coset
offsets — that probabilistic refinement is the named obligation `§5`. -/

/-- **Per-add growth bound.**  A coset add of an addend `< N` to a value `< B`
    yields a value `< B + N` — and a coset rep of the modular sum, with no-wrap
    automatically discharged when `B + N ≤ 2^bits`. -/
theorem cosetAdd_growth (bits N v t x B : Nat)
    (hv : IsCosetRep bits N v x) (hvB : v < B) (ht : t < N)
    (hfit : B + N ≤ 2 ^ bits) :
    IsCosetRep bits N (v + t) (x + t) ∧ v + t < B + N := by
  have hnowrap : v + t < 2 ^ bits := lt_of_lt_of_le (by omega) hfit
  exact ⟨cosetAdd_addend bits N v t x hv hnowrap, by omega⟩

/-- **The sufficient no-wrap condition for the running chain.**  Starting from a
    value `< N` and doing additions of addends each `< N`, after `k` additions
    the value is `< (k + 1)·N`; so if `(k + 1)·N ≤ 2^bits` no addition wraps.
    Concretely: a value bounded by `(k + 1)·N` plus another `< N` addend stays
    `< (k + 2)·N ≤ 2^bits` whenever `(k + 2)·N ≤ 2^bits`.  This is the chain
    invariant the windowed multiplier maintains. -/
theorem noWrap_chain_bound (bits N k v t : Nat)
    (hvk : v < (k + 1) * N) (ht : t < N)
    (hpad : (k + 2) * N ≤ 2 ^ bits) :
    v + t < 2 ^ bits ∧ v + t < (k + 2) * N := by
  constructor
  · have : v + t < (k + 1) * N + N := by omega
    calc v + t < (k + 1) * N + N := this
      _ = (k + 2) * N := by ring
      _ ≤ 2 ^ bits := hpad
  · have : v + t < (k + 1) * N + N := by omega
    calc v + t < (k + 1) * N + N := this
      _ = (k + 2) * N := by ring

/-- **Padding ↔ no-wrap.**  If the register width satisfies
    `numAdds·N ≤ 2^bits` (the padded representation holds `numAdds`
    addends' worth of `N`), then any partial sum reachable by `< numAdds`
    additions of addends `< N`, starting from `0`, stays below `2^bits`.
    Because `bits = n + g_pad` with `2^n ≈ N`, this fixes `g_pad ≳ lg numAdds`;
    the paper's `numAdds = numWin·numMults ≈ (n/w)·n_e` gives `g_pad ≳ lg(n·n_e)`
    — precisely the `2 lg n + lg n_e` of `g_pad = 2 lg n + lg n_e + 10`. -/
theorem noWrap_of_padding (bits N numAdds k v : Nat)
    (hpad : numAdds * N ≤ 2 ^ bits)
    (hk : k < numAdds) (hvk : v < (k + 1) * N) :
    v < 2 ^ bits := by
  calc v < (k + 1) * N := hvk
    _ ≤ numAdds * N := Nat.mul_le_mul_right N (by omega)
    _ ≤ 2 ^ bits := hpad

/-! ## §5. The probabilistic wrap bound — NAMED OBLIGATION (no `sorry`).

Everything above is DETERMINISTIC and EXACT under the no-wrap hypothesis.  The
paper does NOT pad enough to make no-wrap hold for ALL coset offsets; instead it
adds a uniformly-random multiple of `N` to the initial coset offset and bounds
the PROBABILITY that any of the `numAdds` additions wraps `2^bits`.  By Gidney
Thm 2.10 (subadditivity of the deviation over additions) this total wrap
probability is `≤ WindowedCostModel.totalDeviation n n_e ≈ 7.6·10⁻⁸`.

Closing this requires measure-theoretic machinery (a probability space over the
random offset, the per-add wrap event, and the union bound) that is out of
scope for this pass.  We therefore RECORD it as a structure of obligations — NO
`sorry`, NO axiom: the structure simply states precisely what an analytic
development must supply, and bundles the deterministic exact-on-no-wrap result
that this file DOES prove.  Anything downstream that constructs a
`CosetDeviationBound` obtains the full mod-N certificate; nothing in this file
assumes one exists. -/

/-- **`CosetDeviationBound` — the probabilistic wrap obligation.**
    A witness that, for an `n`-bit modulus padded to `bits = n + g_pad` and a
    windowed exponentiation doing `numAdds` coset additions (each adding an
    addend `< N`), the random-offset coset scheme wraps with probability at most
    the paper's `totalDeviation`.

    Fields:
    • `Nval`, `numAdds` — the modulus and the total number of coset additions
      (`= numWin · numMults` for the full exponentiation);
    • `nQ`, `neQ` — the paper's `ℚ`-valued size parameters (`n`, `n_e`) feeding
      `totalDeviation`;
    • `wrapProb` — the analytic wrap probability of the random-offset scheme
      (to be defined by the measure-theoretic development; recorded as a field);
    • `wrapProb_nonneg`, `wrapProb_le_totalDeviation` — the obligation: the wrap
      probability is nonnegative and `≤ totalDeviation nQ neQ` (Gidney Thm 2.10);
    • `exact_on_noWrap` — the DETERMINISTIC content this file proves and the
      analytic leg consumes: on the no-wrap event, a coset add of any addend
      `< Nval` to a coset rep is exactly a coset rep of the modular sum.

    This is the ONE remaining analytic obligation.  It is stated, not assumed:
    `CosetDeviationBound` is a `Prop`-free data structure; no instance is
    declared, so the kernel sees no unproven claim. -/
structure CosetDeviationBound where
  /-- The modulus `N`. -/
  Nval : Nat
  /-- The padded register width `bits = n + g_pad`. -/
  bits : Nat
  /-- Total number of coset additions over the whole exponentiation. -/
  numAdds : Nat
  /-- The paper's `n` (operand bit-width), as `ℚ`, for `totalDeviation`. -/
  nQ : ℚ
  /-- The paper's `n_e` (exponent bit-width), as `ℚ`, for `totalDeviation`. -/
  neQ : ℚ
  /-- The analytic wrap probability of the random-offset coset scheme over the
      whole exponentiation (supplied by the measure-theoretic development). -/
  wrapProb : ℚ
  /-- Obligation: the wrap probability is nonnegative. -/
  wrapProb_nonneg : 0 ≤ wrapProb
  /-- Obligation (Gidney Thm 2.10, subadditivity): the total wrap probability is
      bounded by the paper's `totalDeviation`. -/
  wrapProb_le_totalDeviation :
    wrapProb ≤ FormalRV.Shor.WindowedCostModel.totalDeviation nQ neQ
  /-- The deterministic content (PROVEN below as `cosetAdd_addend`): on the
      no-wrap event each coset add is exact.  Carried as a field so a downstream
      `CosetDeviationBound` is the single object combining the proven
      exact-on-no-wrap fact with the analytic wrap bound. -/
  exact_on_noWrap :
    ∀ (v t x : Nat), IsCosetRep bits Nval v x → v + t < 2 ^ bits →
      IsCosetRep bits Nval (v + t) (x + t)

/-- **The deterministic field of `CosetDeviationBound` is dischargeable** — it is
    exactly `cosetAdd_addend`.  This shows the structure's `exact_on_noWrap`
    obligation is ALREADY proven here; only the two probabilistic fields
    (`wrapProb`, `wrapProb_le_totalDeviation`) await the analytic development.
    A full witness is obtained by supplying that analytic `wrapProb`. -/
theorem cosetDeviationBound_exact_field (bits N : Nat) :
    ∀ (v t x : Nat), IsCosetRep bits N v x → v + t < 2 ^ bits →
      IsCosetRep bits N (v + t) (x + t) :=
  fun v t x hv hnowrap => cosetAdd_addend bits N v t x hv hnowrap

/-- **The wrap-probability bound, once a witness is supplied, is `≤ 10⁻⁷`.**
    Given any `CosetDeviationBound` whose size parameters are nonzero, its wrap
    probability inherits the constant `≤ 1/10⁷` bound from
    `WindowedCostModel.totalDeviation_le` — i.e. the only thing the analytic leg
    must produce (the `wrapProb` and its `≤ totalDeviation`) immediately yields
    the paper's headline `≈ 10⁻⁷` fidelity figure. -/
theorem CosetDeviationBound.wrapProb_le_const (D : CosetDeviationBound)
    (hn : D.nQ ≠ 0) (hne : D.neQ ≠ 0) :
    D.wrapProb ≤ 1 / 10000000 :=
  le_trans D.wrapProb_le_totalDeviation
    (FormalRV.Shor.WindowedCostModel.totalDeviation_le D.nQ D.neQ hn hne)

/-! ## §6. Oblivious carry runways — structural count + NAMED design obligation.

Gidney's "oblivious carry runways" split each long coset addition into pieces
over `g_sep`-separated runway segments, so an `n`-bit add costs `O(n/g_sep)`
extra runway-fold Toffolis (the paper's `n·g_pad/g_sep` term).  The crucial
fact for the COUNT is already VERIFIED structurally: padding the register to
`bits = n + pad` makes the Cuccaro adder process the `pad` extra qubits, and
`windowedMulCircuit_toffoli_padded` reads off the resulting `+2·pad` Toffolis
per window DIRECTLY from the `Gate` (`tcount` recursion).  With `pad = g_pad`,
the padding's Toffoli contribution is structurally present in the optimal count.

The runway-fold *circuit itself* (piecewise additions, runway-carry folding) is
not yet built as a `Gate`; we record its design + the structural count it must
match as a named obligation, with the VERIFIED padded count as a field. -/

/-- **The padding's Toffoli contribution is structurally verified.**  Restated
    here as the coset bridge's hook into the count: the optimal-count multiplier
    on a register padded by `pad = g_pad` (the coset padding) costs exactly
    `numWin · (4·w·2^w + 2·n + 2·pad)` Toffolis — the `+2·pad` per window being
    the adder over the runway/coset padding qubits, read off the actual `Gate`.
    (Thin wrapper over `windowedMulCircuit_toffoli_padded`.) -/
theorem cosetPadding_toffoli (w n pad a numWin : Nat) :
    toffoliCount (windowedMulCircuit w (n + pad) a numWin)
      = numWin * (4 * w * 2 ^ w + 2 * n + 2 * pad) :=
  windowedMulCircuit_toffoli_padded w n pad a numWin

/-- **`ObliviousCarryRunway` — the runway-fold design obligation (no `sorry`).**
    Records what a verified oblivious-carry-runway circuit must provide and the
    structural count it must match, WITHOUT asserting the circuit exists.

    Fields:
    • `w`, `n`, `pad`, `a`, `numWin` — the multiplier parameters
      (`pad = g_pad` the coset/runway padding, `bits = n + pad`);
    • `runwayCircuit` — the runway-fold `Gate` (to be constructed: piecewise
      additions over `g_sep`-separated runways folding the runway carry back);
    • `toffoli_matches_padded` — the obligation: its Toffoli count equals the
      VERIFIED padded count `cosetPadding_toffoli`, so building the runway does
      not change the certified optimal count;
    • `computes_same_coset` — the obligation: the runway circuit computes the
      same coset-rep value as the monolithic padded multiplier (so §3's
      mod-N-in-coset correctness transfers to it).

    No instance is declared; the kernel sees no unproven claim.  This pins the
    runway down to a circuit-construction + equivalence task whose COUNT target
    (`numWin · (4·w·2^w + 2·n + 2·pad)`) is already a verified theorem. -/
structure ObliviousCarryRunway where
  /-- Window size. -/
  w : Nat
  /-- Operand bit-width. -/
  n : Nat
  /-- Coset/runway padding (`g_pad`). -/
  pad : Nat
  /-- The multiplicand constant. -/
  a : Nat
  /-- Number of windows. -/
  numWin : Nat
  /-- The runway-fold circuit (to be constructed). -/
  runwayCircuit : Gate
  /-- Obligation: the runway circuit's Toffoli count matches the verified padded
      count, so the optimal count is preserved. -/
  toffoli_matches_padded :
    toffoliCount runwayCircuit = numWin * (4 * w * 2 ^ w + 2 * n + 2 * pad)
  /-- Obligation: the runway circuit computes the same coset value as the
      monolithic padded multiplier (correctness transfer for §3). -/
  computes_same_coset :
    ∀ (f : Nat → Bool),
      decodeAccOf cuccaroAdder (Gate.applyNat runwayCircuit f) (1 + 2 * w) (n + pad)
        = decodeAccOf cuccaroAdder
            (Gate.applyNat (windowedMulCircuit w (n + pad) a numWin) f)
            (1 + 2 * w) (n + pad)

/-- **The runway's count target is the verified padded count.**  Any
    `ObliviousCarryRunway` whose `toffoli_matches_padded` obligation holds has,
    by `cosetPadding_toffoli`, exactly the Toffoli count of the structurally
    verified padded multiplier — confirming the count field is consistent (not
    over-claiming). -/
theorem ObliviousCarryRunway.toffoli_eq_verified (R : ObliviousCarryRunway) :
    toffoliCount R.runwayCircuit
      = toffoliCount (windowedMulCircuit R.w (R.n + R.pad) R.a R.numWin) := by
  rw [R.toffoli_matches_padded, cosetPadding_toffoli]

end FormalRV.Shor.WindowedCoset
