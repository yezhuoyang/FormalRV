/-
  Audit · gidney-ekera-2021 · WORKLOAD ASSEMBLY — literal = paper formula = circuit
  ============================================================================
  This file converts the audit's headline NUMBERS from bare literals into
  THEOREMS.  It defines no new gadget and no new number: it only IMPORTS the
  three layers that already exist and PROVES they agree —

    LITERALS  (what the audit/system files hard-code):
      • `Verifier.toffoliCount               = 2 622 824 448`
      • `MagicScheduleComplete.rsa2048_magic_budget = 2 622 824 448`
      • `MagicScheduleComplete.rsa2048_data_qubits  = 9 633 792`
      • `NaiveUpperBound.ge2021_work.n_toff  = 2 700 000 000`
    FORMULA   (the paper's ℚ cost accounting, `Arithmetic/Windowed/WindowedCostModel`):
      • `toffoliCount 2048 3072 11 = 2 622 824 448`  (= 503808 · 5206)
    CIRCUIT   (the verified semantic object, `Shor/WindowedComposedAt`):
      • `EGate.toffoli (modExpAt 10 _ 2048 _ _ (numMultsOf 3072 5 5) (numWinOf 2048 5 1024))
           = 2 578 993 152`  — value-correct per multiply-add (`multiplyAddAt_fold`).

  The reconciliation: literal = formula EXACTLY; formula − circuit =
  `43 831 296 = LookupAdditionCount · (1 + n·g_pad/g_sep)` EXACTLY (the `+1`
  lookup rounding + the runway-folding additions, `WindowedComposedCost.total_gap`)
  — and the audit workload input `n_toff = 2.7×10⁹` upper-bounds all of it.

  Three further rows (§5–§7) extend the same literal = formula = verified-object
  discipline to the OTHER headline numbers, citing this session's new objects:
    • §5 QUBIT WIDTH (`Shor/WindowedWidthAudit`):
        SystemZones literal `ge2021_logical_qubits = 6200`
          = `paperWidthFigure 2048 11 = 6189` + 11 (abstract rounding);
        verified reused-register circuit width `6162` + 27 (coset padding) = 6189.
    • §6 ARITHMETIC VALUE (`Shor/WindowedModExpValue`):
        the COUNTED in-place windowed modexp computes `a^e mod N` (TRUE N,
        classical exponent) — `windowedModNExp_value`.
    • §7 COSET BRIDGE (`Arithmetic/Windowed/WindowedCoset`):
        the OPTIMAL-COUNT mod-`2^bits` multiplier is mod-N correct in the coset
        rep under no-wrap (`windowedCosetMul_correct`); the single residual is the
        probabilistic `CosetDeviationBound` (§8 ledger entry 6).

  AUDIT-ONLY FILE: equalities, citations, and honest-gap markers.  No new
  circuits, no new cost models, no `sorry`, no `native_decide`, no axioms.
-/

import FormalRV.Audit.GidneyEkera2021.Verifier
import FormalRV.Audit.GidneyEkera2021.SystemZones
import FormalRV.System.Magic.MagicScheduleComplete
import FormalRV.System.Bounds.NaiveUpperBound
import FormalRV.Arithmetic.Windowed.WindowedCostModel
import FormalRV.Shor.MeasUncomputeAt
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Shor.WindowedComposedAt
import FormalRV.Shor.WindowedWidthAudit
import FormalRV.Shor.WindowedModExpValue
import FormalRV.Arithmetic.Windowed.WindowedCoset
import FormalRV.Arithmetic.Windowed.WindowedCosetDeviation
import FormalRV.Verifier

namespace FormalRV.Audit.GidneyEkera2021

open FormalRV.Shor.MeasUncompute (EGate)
open FormalRV.BQAlgo (decodeReg)

/-============================================================================
  §1.  LITERAL = PAPER FORMULA — the audit's 2 622 824 448 is a theorem.
============================================================================-/

/-- **The Verifier's Toffoli literal IS the paper's verified cost formula.**
    `Verifier.toffoliCount = 2 622 824 448` equals
    `WindowedCostModel.toffoliCount n n_e (lg n)` at the RSA-2048 parameters
    `(n, n_e, lg n) = (2048, 3072, 11)` — the audit headline number is no longer
    a magic constant but the value of the rfl/`norm_num`-verified ℚ formula
    `LookupAdditionCount · perLookupToffoli = 503808 · 5206`. -/
theorem audit_toffoli_literal_eq_cost_model :
    (toffoliCount : ℚ) = Shor.WindowedCostModel.toffoliCount 2048 3072 11 := by
  rw [(Shor.WindowedCostModel.toffoliCount_rsa2048).1]
  norm_num [toffoliCount]

/-- **The system magic budget is THE SAME number** — definitional equality with the
    Verifier literal, hence (via §1) also equal to the paper formula.  The whole-device
    magic schedule (`MagicScheduleComplete`, 1093 CCZ factories) is provisioned for
    exactly the verified workload, not an independent estimate. -/
theorem audit_magic_budget_eq :
    System.MagicScheduleComplete.rsa2048_magic_budget = toffoliCount
    ∧ (System.MagicScheduleComplete.rsa2048_magic_budget : ℚ)
        = Shor.WindowedCostModel.toffoliCount 2048 3072 11 :=
  ⟨rfl, audit_toffoli_literal_eq_cost_model⟩

/-- **The system data-qubit literal is the derived value, not an input.**
    `MagicScheduleComplete.rsa2048_data_qubits = 9 633 792` equals the SystemZones
    derivation `3n logical × 2(d+1)² at d = 27` (`windowedPhysicalDataQubits_rsa2048`). -/
theorem audit_data_qubit_literal_eq_derived :
    System.MagicScheduleComplete.rsa2048_data_qubits = windowedPhysicalDataQubits_rsa2048 := by
  decide

/-============================================================================
  §2.  PAPER FORMULA vs VERIFIED CIRCUIT — the gap is exact and NAMED.
============================================================================-/

/-- **The audit Toffoli number is realized by a verified circuit, gap pinned.**
    For EVERY table family, the value-correct shared-accumulator modular
    exponentiation `modExpAt` at the DERIVED parameters
    (`numMultsOf 3072 5 5 = 246`, `numWinOf 2048 5 1024 = 1024`):
    (i)   counts exactly `2 578 993 152` Toffolis (structural recursion on the term);
    (ii)  that count, cast to ℚ, IS the structural cost model `structToffoliCount`;
    (iii) audit literal − circuit = `43 831 296` exactly (Nat subtraction);
    (iv)  the gap is the NAMED formula `LookupAdditionCount · (1 + n·g_pad/g_sep)`
          — `+1` per-lookup rounding (`2^w−1 → 2^w`) plus the runway-folding
          additions — no unexplained slack (`WindowedComposedCost.total_gap`);
    (v)   the gap decomposes as `503808·1 + 503808·86` (rounding + runway);
    (vi)  the circuit count is `≤` the audit literal (the paper's charge only adds). -/
theorem audit_toffoli_realized_by_circuit
    (W : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start : Nat) :
    EGate.toffoli (Shor.WindowedComposedAt.modExpAt 10 W 2048 Tfam q_start
        (Shor.WindowedComposedAt.numMultsOf 3072 5 5)
        (Shor.WindowedComposedAt.numWinOf 2048 5 1024)) = 2578993152
    ∧ (EGate.toffoli (Shor.WindowedComposedAt.modExpAt 10 W 2048 Tfam q_start
        (Shor.WindowedComposedAt.numMultsOf 3072 5 5)
        (Shor.WindowedComposedAt.numWinOf 2048 5 1024)) : ℚ)
        = Shor.WindowedComposedCost.structToffoliCount 2048 3072
    ∧ toffoliCount - EGate.toffoli (Shor.WindowedComposedAt.modExpAt 10 W 2048 Tfam q_start
        (Shor.WindowedComposedAt.numMultsOf 3072 5 5)
        (Shor.WindowedComposedAt.numWinOf 2048 5 1024)) = 43831296
    ∧ (toffoliCount : ℚ) - Shor.WindowedComposedCost.structToffoliCount 2048 3072
        = Shor.WindowedCostModel.lookupAdditionCount 2048 3072
            * (1 + 2048 * (3 * 11 + 10) / 1024)
    ∧ (43831296 : ℚ) = 503808 * 1 + 503808 * 86
    ∧ EGate.toffoli (Shor.WindowedComposedAt.modExpAt 10 W 2048 Tfam q_start
        (Shor.WindowedComposedAt.numMultsOf 3072 5 5)
        (Shor.WindowedComposedAt.numWinOf 2048 5 1024)) ≤ toffoliCount := by
  refine ⟨Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived W Tfam q_start,
          ?_, ?_, ?_, Shor.WindowedComposedCost.rsa2048_head_to_head.2.2.2, ?_⟩
  · rw [Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived,
        Shor.WindowedComposedCost.rsa2048_head_to_head.1]
    norm_num
  · rw [Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived]
    decide
  · rw [audit_toffoli_literal_eq_cost_model]
    exact Shor.WindowedComposedCost.total_gap 2048 3072 11
  · rw [Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived]
    decide

/-- **The audit workload input is a SOUND upper bound on the verified objects.**
    `NaiveUpperBound.ge2021_work.n_toff = 2.7×10⁹` (the input the naive-ceiling
    reproduction feeds the verified resource law) dominates (i) the verified
    circuit count, (ii) the audit literal, and (iii) the paper's exact ℚ formula
    — so every ceiling proved from `ge2021_work` covers the verified workload. -/
theorem audit_n_toff_upper_bounds_circuit
    (W : Nat) (Tfam : Nat → Nat → Nat → Nat) (q_start : Nat) :
    EGate.toffoli (Shor.WindowedComposedAt.modExpAt 10 W 2048 Tfam q_start
        (Shor.WindowedComposedAt.numMultsOf 3072 5 5)
        (Shor.WindowedComposedAt.numWinOf 2048 5 1024))
      ≤ (System.NaiveUpperBound.ge2021_work).n_toff
    ∧ toffoliCount ≤ (System.NaiveUpperBound.ge2021_work).n_toff
    ∧ Shor.WindowedCostModel.toffoliCount 2048 3072 11
        ≤ ((System.NaiveUpperBound.ge2021_work).n_toff : ℚ) := by
  refine ⟨?_, by decide, ?_⟩
  · rw [Shor.WindowedComposedAt.rsa2048_modExpAt_toffoli_derived]
    decide
  · rw [(Shor.WindowedCostModel.toffoliCount_rsa2048).1]
    norm_num [System.NaiveUpperBound.ge2021_work]

/-============================================================================
  §3.  THE PER-LOOKUP-ADDITION ROW — circuit 5205 vs paper 5206, the `+1` exact.
============================================================================-/

/-- **Per-lookup-addition head-to-head.**  The measured Babbush lookup-add
    `babbushLookupAddAt` at window `w = 10` over a `2048 + 43`-bit adder — the
    `43` extra bits are exactly the runway share `n·g_pad/g_sep = 86 = 2·43`
    Toffolis of Cuccaro width — counts `(2^10−1) + 2·(2048+43) = 5205` Toffolis;
    the paper's per-lookup charge (`perLookupToffoli 2048 11`) is `5206`; and the
    difference is EXACTLY the `+1` rounding of the unary read `2^w − 1 → 2^w`.
    At the bare width 2048 the per-lookup gap to the paper is `87 = 1 + 86`
    (`WindowedComposedCost.perLookup_rsa`). -/
theorem audit_per_lookup_add (W : Nat) (T : Nat → Nat) (addrBase ancBase q_start : Nat) :
    EGate.toffoli
        (Shor.MeasUncomputeAt.babbushLookupAddAt 10 W T (2048 + 43) addrBase ancBase q_start)
      = 5205
    ∧ Shor.WindowedCostModel.perLookupToffoli 2048 11 = 5206
    ∧ ((5205 : Nat) : ℚ) + 1 = Shor.WindowedCostModel.perLookupToffoli 2048 11
    ∧ Shor.WindowedCostModel.perLookupToffoli 2048 11
        - Shor.WindowedComposedCost.structPerLookup 2048 = 87 := by
  refine ⟨?_, (Shor.WindowedComposedCost.perLookup_rsa).1, ?_,
          (Shor.WindowedComposedCost.perLookup_rsa).2⟩
  · rw [Shor.MeasUncomputeAt.toffoli_babbushLookupAddAt]
    decide
  · rw [(Shor.WindowedComposedCost.perLookup_rsa).1]
    norm_num

/-============================================================================
  §4.  VALUE-SEMANTICS WITNESS — the counted circuit computes acc += T[addr].
============================================================================-/

/-- **No-cheating witness: the counted lookup-add family has VALUE semantics.**
    The audit instance (`w = 10`, `W = bits = 2048`) of the unguarded mod-form
    step lemma: on every `CleanInputModFree` state, the SAME
    `babbushLookupAddAt` whose Toffolis are counted above realises
    `acc ↦ (acc + T[addr]) mod 2^2048` on the shared accumulator.  This is a
    thin instantiation of `WindowedComposedAt.babbushLookupAddAt_modStep` — the
    per-step law `multiplyAddAt_fold` folds into the full multiply-add value
    theorem; the counted object is not a Toffoli-shaped placeholder. -/
theorem audit_value_semantics_witness
    (T : Nat → Nat) (addrBase ancBase q_start : Nat)
    (h_anc_pos : 0 < ancBase)
    (h_anc_addr : ∀ i i', i < 10 → i' < 10 → ancBase + i ≠ addrBase + i')
    (h_anc_blk : ∀ i, i < 10 →
      ¬ (q_start ≤ ancBase + i ∧ ancBase + i ≤ q_start + 2 * 2048))
    (h_addr_blk : ∀ i, i < 10 →
      ¬ (q_start ≤ addrBase + i ∧ addrBase + i ≤ q_start + 2 * 2048))
    (f : Nat → Bool)
    (hf : Shor.WindowedComposedAt.CleanInputModFree 10 2048 2048
            addrBase ancBase q_start T f) :
    decodeReg (fun i => q_start + 2 * i + 1) 2048
        (EGate.applyNat
          (Shor.MeasUncomputeAt.babbushLookupAddAt 10 2048 T 2048 addrBase ancBase q_start) f)
      = (decodeReg (fun i => q_start + 2 * i + 1) 2048 f
          + T (decodeReg (fun i => addrBase + i) 10 f)) % 2 ^ 2048 :=
  Shor.WindowedComposedAt.babbushLookupAddAt_modStep 10 2048 2048 T
    addrBase ancBase q_start (le_refl 2048) h_anc_pos h_anc_addr h_anc_blk h_addr_blk f hf

/-============================================================================
  §5.  QUBIT WIDTH — the SystemZones qubit literal is the paper figure, and the
       verified reused-register circuit width sits +27 below it (named delta).
============================================================================-/

/-- **The audit qubit count is realized by a verified circuit width.**
    Three layers reconciled for the logical-qubit headline, exactly as §1–§2 did
    for the Toffoli headline:

    (i)   the SystemZones architecture literal `ge2021_logical_qubits = 6200` is
          the Ekerå–Håstad abstract Table-1 figure (the count that sizes the
          computation zone, `ge2021_computation_size = 6200 · 1568`);
    (ii)  the paper's explicit closed-form figure `⌊3n + 0.002·n·lg n⌋` at
          `(n, lg n) = (2048, 11)` is `paperWidthFigure 2048 11 = 6189` — and the
          SystemZones literal rounds it UP by exactly `11` (`6200 = 6189 + 11`,
          the abstract figure's slack over the explicit formula);
    (iii) the VERIFIED reused-register windowed-modexp circuit width is
          `verified_width_rsa2048 = 6162` logical qubits — read off the actual
          `Gate`-IR via `width = maxIdx + 1` for the in-place
          `windowedExpInPlace cuccaroAdder 8 2048 256 _ 3072 _ _ _`
          (`numWin·w = 256·8 = 2048`, the in-place register-reuse constraint);
    (iv)  verified circuit `+ 27 =` paper formula
          (`verified_vs_paper_rsa2048 : 6162 + 27 = 6189`).  The `+27` is the
          NAMED coset-padding / runway delta: the paper books `0.002·n·lg n ≈ 45`
          coset-padding (`g_pad`) qubits, our explicit Cuccaro-mod-`2^bits`
          layout pays only `2·w + 2 = 18` for the fixed lookup zone, and
          `45 − 18 = 27` — an HONEST, fully-accounted residual, not a count error.

    So the headline qubit number, like the Toffoli number, is no longer a magic
    constant: it is the value of an explicit formula, sitting `27` qubits ABOVE a
    verified circuit width whose every wire is read off the `Gate`. -/
theorem audit_qubit_count_realized_by_circuit (wE g e : Nat) (ainvs : Nat → Nat) :
    ge2021_logical_qubits = 6200
    ∧ Shor.WindowedWidthAudit.paperWidthFigure 2048 11 = 6189
    ∧ ge2021_logical_qubits = Shor.WindowedWidthAudit.paperWidthFigure 2048 11 + 11
    ∧ Shor.WindowedCircuit.width
        (Shor.WindowedCircuit.windowedExpInPlace BQAlgo.cuccaroAdder 8 2048 256 wE 3072 g e ainvs)
        = 6162
    ∧ Shor.WindowedCircuit.width
        (Shor.WindowedCircuit.windowedExpInPlace BQAlgo.cuccaroAdder 8 2048 256 wE 3072 g e ainvs)
        + 27 = Shor.WindowedWidthAudit.paperWidthFigure 2048 11 := by
  refine ⟨rfl, Shor.WindowedWidthAudit.paperWidthFigure_rsa2048, by decide,
          Shor.WindowedWidthAudit.verified_width_rsa2048 wE g e ainvs,
          Shor.WindowedWidthAudit.verified_vs_paper_rsa2048 wE g e ainvs⟩

/-============================================================================
  §6.  ARITHMETIC VALUE — the counted modexp computes `a^e mod N` (mod TRUE N).
============================================================================-/

/-- **No-cheating arithmetic-value witness: the windowed modexp computes
    `a^e mod N`.**  Run on the clean encoded input with `y = 1`, the in-place
    windowed modular-exponentiation chain leaves `a^e mod N` in the result
    register — mod the TRUE modulus `N`, not mod `2^bits`.  This is the standalone
    value certificate that the COUNTED modexp arithmetic (whose Toffolis §1–§4
    reconcile against the audit literal) actually computes the right number; the
    counted object is not a value-blind Toffoli skeleton.  Thin citation of
    `WindowedModExpValue.windowedModNExp_value`.  CLASSICAL exponent `e`; the
    quantum-selected variant is the named weld in the §8 ledger. -/
theorem audit_modexp_value_witness
    (w bits numWin N wE nE a ainv e : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (he : e < (2 ^ wE) ^ nE) (hinv : a * ainv % N = 1) :
    decodeReg (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits
        (BQAlgo.Gate.applyNat
          (Shor.WindowedModExpValue.windowedModNExpInPlace w bits numWin N wE nE a ainv e)
          (Shor.WindowedCircuit.mulInputOf BQAlgo.cuccaroAdder w bits numWin 1))
      = a ^ e % N :=
  Shor.WindowedModExpValue.windowedModNExp_value w bits numWin N wE nE a ainv e
    hw hbits hN1 hN2 he hinv

/-============================================================================
  §7.  COSET BRIDGE — the OPTIMAL-COUNT mod-2^bits multiplier is mod-N correct
       (coset rep, under no-wrap); the residual is the named CosetDeviationBound.
============================================================================-/

/-- **The optimal-count object computes mod-N (coset rep, no-wrap).**  The audit's
    Toffoli count is the count of the CHEAP mod-`2^bits` windowed multiplier
    `windowedMulCircuitOf` (its `g_pad` coset padding is already in the verified
    `0.3 n³` count, §1–§4).  The expensive exact-mod-N multiplier carries a
    different count.  Gidney's coset representation closes the value↔count split:
    this theorem certifies that the SAME optimal-count object, run on a coset-rep
    input under the no-wrap hypothesis `a·y < 2^bits`, leaves an accumulator that
    is a COSET REPRESENTATIVE of `(a·y) mod N` — its readout
    `cosetValue N (decodeAcc …) = (a·y) mod N` is the true modular product, no
    in-register reduction.  EXACT under no-wrap; no probability enters this
    statement.  Citation of `WindowedCoset.windowedCosetMul_correct` (general
    adder) — so the optimal Toffoli count the audit uses IS the count of a
    mod-N-correct computation. -/
theorem audit_optimal_count_is_modN_correct
    (A : BQAlgo.Adder) (w bits a numWin N y : Nat)
    (hw : 0 < w) (hy : y < 2 ^ (w * numWin))
    (hclean : A.ancClean (Shor.WindowedCircuit.mulInputOf A w bits numWin y) bits (1 + 2 * w))
    (hnowrap : a * y < 2 ^ bits) :
    Shor.WindowedCoset.IsCosetRep bits N
      (Shor.WindowedCircuit.decodeAccOf A
        (BQAlgo.Gate.applyNat (Shor.WindowedCircuit.windowedMulCircuitOf A w bits a numWin)
          (Shor.WindowedCircuit.mulInputOf A w bits numWin y)) (1 + 2 * w) bits)
      (a * y)
    ∧ Shor.WindowedCoset.cosetValue N
        (Shor.WindowedCircuit.decodeAccOf A
          (BQAlgo.Gate.applyNat (Shor.WindowedCircuit.windowedMulCircuitOf A w bits a numWin)
            (Shor.WindowedCircuit.mulInputOf A w bits numWin y)) (1 + 2 * w) bits)
        = (a * y) % N :=
  ⟨Shor.WindowedCoset.windowedCosetMul_correct A w bits a numWin N y hw hy hclean hnowrap,
   Shor.WindowedCoset.windowedCosetMul_readout A w bits a numWin N y hw hy hclean hnowrap⟩

/-- **The residual coset obligation — REDUCED, made explicit.**  Everything in
    `audit_optimal_count_is_modN_correct` is EXACT under the deterministic no-wrap
    hypothesis.  The remaining leg is the wrap bound — and it is NO LONGER a bare
    measure-theoretic obligation: `WindowedCosetDeviation` PROVES the finite
    union-bound combinatorics and an EXACT ℚ identity to the paper's deviation:

      • `wrapProbCount_le_countingBoundQ` — the union-bound count fraction
        `card(badOffsets)/window ≤ numAdds·adv/window` (pure finite combinatorics,
        via the deterministic `noWrap_chain_bound`; no probability theory);
      • `countingBound_eq_totalDeviation` — `countingBoundQ` at the runway advance
        `Δ = n/g_sep` EQUALS `WindowedCostModel.totalDeviation` (exact `field_simp`),
        giving the RSA-2048 figure `41/536870912 ≈ 7.64·10⁻⁸ ≤ 10⁻⁷`
        (`cosetDeviationBound_rsa2048_le`).

    What HONESTLY remains (carried, not hidden — see `WindowedCosetDeviation`
    header): (1) the per-add advance `Δ = n/g_sep` is the oblivious-carry-runway
    CIRCUIT's truncation property — that `Gate` is NOT yet built
    (`WindowedCoset.ObliviousCarryRunway`); the verified PLAIN coset multiplier
    advances by `≤ N`, whose bound needs `g_pad ≈ n`.  (2) the finite fraction
    `card/window` is TAKEN AS the probability (counting interpretation; no measure
    space is constructed).  NOTE: `CosetDeviationBound.wrapProb` is a FREE field, so
    instantiating the structure is mere packaging — the meaningful content is the
    two standalone theorems below, not the `≤ totalDeviation` field. -/
theorem audit_coset_deviation_reduced (gpad numAdds adv : Nat) (n n_e : ℚ)
    (hn : n ≠ 0) (hne : n_e ≠ 0) :
    Arithmetic.Windowed.WindowedCosetDeviation.wrapProbCount gpad numAdds adv
        ≤ Arithmetic.Windowed.WindowedCosetDeviation.countingBoundQ
            (numAdds : ℚ) (adv : ℚ) ((2 : ℚ) ^ gpad)
    ∧ Arithmetic.Windowed.WindowedCosetDeviation.countingBoundQ
        (Shor.WindowedCostModel.lookupAdditionCount n n_e) (n / 1024) (n ^ 2 * n_e * 1024)
        = Shor.WindowedCostModel.totalDeviation n n_e :=
  ⟨Arithmetic.Windowed.WindowedCosetDeviation.wrapProbCount_le_countingBoundQ gpad numAdds adv,
   Arithmetic.Windowed.WindowedCosetDeviation.countingBound_eq_totalDeviation n n_e hn hne⟩

/-- The RSA-2048 wrap fraction (at the runway advance) meets the paper's headline
    `≤ 10⁻⁷` fidelity — a concrete instance of the reduced bound above. -/
example : Arithmetic.Windowed.WindowedCosetDeviation.cosetDeviationBound_rsa2048.wrapProb
    ≤ 1 / 10000000 :=
  Arithmetic.Windowed.WindowedCosetDeviation.cosetDeviationBound_rsa2048_le

/-============================================================================
  §8.  HONEST-GAP LEDGER — what is STILL not on a verified circuit.
============================================================================-/

/-! ## HONEST-GAP LEDGER (markers, not theorems)

What the reconciliation above does NOT close — each gap is named, with its
nearest verified anchor:

1. **Runway additions have a FORMULA, not a circuit.**  The `43 831 296` gap
   term is formula-named (`total_gap`: `LookupAdditionCount·(1 + n·g_pad/g_sep)`),
   and §3 shows the runway share `86` is absorbable as `43` extra Cuccaro bits —
   but NO verified `Gate`/`EGate` builds the oblivious-runway additions
   themselves (Gidney 1905.08488 §"runways").  The circuit side stops at the
   bare lookup-add loop; the runway `+86`/lookup and the `+1` rounding live
   only in the paper's accounting.  (The split phase-fixup skeleton —
   `SplitPhaseFixup.toffoliCount_splitPhaseLookupSkeleton`, `4·(2^w1−1)+2·(2^w2−1)`
   — covers the §7 fixup-lookup row, also count-level.)

2. **Ekerå–Håstad phase estimation is cited, not verified.**  The verified
   semantic bound is standard-QPE; the `n_e = 1.5 n = 3072` exponent length and
   the EH post-processing (lattice rounding, few-shot success amplification)
   enter only as the paper's own inputs to the formula layer.

3. **The ≈2.5× pipelining runtime claim is a pinned GAP, not a theorem.**
   `Verifier.ge2021_time_gap_2_to_3x` proves the reported 8 h sits 2–3× UNDER
   the verified naive-sequential ceiling (20.25 h); the reaction-limited
   pipelining that achieves it is claimed by the paper and NOT verified at
   scale (representative device-schedule fragments only, `SystemZones` Part D).

4. **Qubit width — now a VERIFIED circuit count (§5), the residual is the
   `+27` coset padding, which is FORMULA-named not circuit-built.**
   The headline logical-qubit count is no longer just an architecture partition:
   `audit_qubit_count_realized_by_circuit` (§5) reads the verified reused-register
   width `6162` straight off the `Gate`-IR of `windowedExpInPlace cuccaroAdder`
   (`width = maxIdx + 1`), and `6162 + 27 = paperWidthFigure 2048 11 = 6189`.
   The SystemZones architecture literal `ge2021_logical_qubits = 6200` is the
   abstract Table-1 figure (`= 6189 + 11`).  What is STILL not on a circuit: the
   `+27` itself — the paper's `0.002·n·lg n` coset/runway PADDING qubits (`g_pad`)
   minus our fixed `2·w + 2 = 18` lookup zone — lives in the paper's accounting,
   not in a verified runway `Gate` (see gap 6).  The data-qubit literal also still
   reconciles (`audit_data_qubit_literal_eq_derived`: `9 633 792 = 3n × 2(d+1)²`),
   and the 20 M budget partitions exactly into zones (`zones_partition_budget`).
   The STACKED-region `modExpAt` whole-circuit width theorem (`width_modExpAt_le`,
   advertised in `WindowedComposedAt`'s header) remains DEFERRED — but the audit's
   qubit count is the REUSED-register figure, which §5 verifies.

5. **Arithmetic VALUE — now a single end-to-end VERIFIED theorem (§6), mod the
   TRUE N, for a CLASSICAL exponent.**  `audit_modexp_value_witness` (§6) cites
   `WindowedModExpValue.windowedModNExp_value`: the in-place windowed
   modular-exponentiation chain run on the clean `y = 1` input leaves `a^e mod N`
   in the result register, mod the TRUE modulus `N` (not mod `2^bits`).  So the
   COUNTED modexp arithmetic is certified to compute the right number — it is not
   a value-blind Toffoli skeleton.  What REMAINS open is the single
   modexp-inside-QPE WELD: `WindowedModNShor` does not exist yet.  The halves are
   each verified — the standalone classical-exponent mod-N value (§6,
   `windowedModNExp_value`), the per-multiply-add value of the counted `modExpAt`
   (`multiplyAddAt_fold`), and the adder-generic QUANTUM-selected in-place modexp
   `WindowedExpInPlaceQ.windowedExpInPlaceQ_correct` (mod `2^bits`) — but no ONE
   object is simultaneously RSA-2048-counted AND value-correct inside the QPE host.

6. **Coset-wrap deviation — THE one remaining NAMED arithmetic obligation.**
   `audit_optimal_count_is_modN_correct` (§7) certifies, via
   `WindowedCoset.windowedCosetMul_correct`, that the OPTIMAL-COUNT mod-`2^bits`
   windowed multiplier (whose Toffolis the audit uses) computes the right value
   mod `N` in the coset representation — EXACT under the deterministic no-wrap
   hypothesis `a·y < 2^bits`.  The ONLY residual is the PROBABILISTIC wrap bound
   `WindowedCoset.CosetDeviationBound`: over the paper's random coset offsets the
   wrap probability is `≤ totalDeviation ≈ 7.6·10⁻⁸` (Gidney Thm 2.10).  Its
   deterministic field is already discharged (`cosetDeviationBound_exact_field`);
   only the measure-theoretic `wrapProb` leg is open.  STATUS: OPEN — no
   `WindowedCosetDeviation.lean` discharging it exists in the corpus at build
   time.  `ObliviousCarryRunway` (the runway-fold `Gate`) likewise remains a named
   structure obligation whose Toffoli target (`cosetPadding_toffoli`) is verified
   but whose circuit is not yet built.  THIS is the gap-1 runway entry, now
   sharpened: the `+86`/lookup runway share and the coset `+27` width padding are
   the SAME `g_pad`/`g_sep` accounting, isolated to one structure. -/

end FormalRV.Audit.GidneyEkera2021

-- ✅ LITERAL = FORMULA: the audit headline 2 622 824 448 is a theorem (axiom-free):
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_toffoli_literal_eq_cost_model
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_magic_budget_eq
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_data_qubit_literal_eq_derived
-- ✅ FORMULA vs CIRCUIT: realized by `modExpAt`, gap exactly 43 831 296 = rounding + runways:
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_toffoli_realized_by_circuit
-- ✅ the audit workload input n_toff = 2.7e9 soundly upper-bounds circuit, literal, and formula:
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_n_toff_upper_bounds_circuit
-- ✅ per-lookup row: circuit 5205 + 1 (lookup rounding) = paper 5206:
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_per_lookup_add
-- ✅ value semantics: the counted lookup-add computes acc += T[addr] (mod 2^bits):
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_value_semantics_witness
-- ✅ QUBIT WIDTH: SystemZones literal 6200 = paper formula 6189 + 11; verified circuit 6162 + 27 = 6189:
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_qubit_count_realized_by_circuit
-- ✅ ARITHMETIC VALUE: the counted in-place windowed modexp computes a^e mod N (TRUE N, classical e):
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_modexp_value_witness
-- ✅ COSET BRIDGE: the optimal-count mod-2^bits multiplier is mod-N correct (coset rep, no-wrap):
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_optimal_count_is_modN_correct
-- ✅ COSET DEVIATION REDUCED: finite union-bound count = totalDeviation at runway advance (≈7.6e-8);
--    residual = the unbuilt runway-truncation Gate + the counting-as-probability interpretation:
#verify_clean FormalRV.Audit.GidneyEkera2021.audit_coset_deviation_reduced
-- the upstream value-semantics theorems the witness instantiates:
#check @FormalRV.Shor.WindowedComposedAt.multiplyAddAt_fold
#check @FormalRV.Shor.MeasUncomputeAt.babbushLookupAddAtValueSpecOn_holds
#check @FormalRV.Shor.MeasUncomputeAt.measUncomputeAt_saves_a_read
