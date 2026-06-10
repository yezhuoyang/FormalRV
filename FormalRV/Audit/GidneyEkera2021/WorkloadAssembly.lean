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

  AUDIT-ONLY FILE: equalities, citations, and honest-gap markers.  No new
  circuits, no new cost models, no `sorry`, no `native_decide`, no axioms.
-/

import FormalRV.Audit.GidneyEkera2021.Verifier
import FormalRV.Audit.GidneyEkera2021.SystemZones
import FormalRV.System.MagicScheduleComplete
import FormalRV.System.NaiveUpperBound
import FormalRV.Arithmetic.Windowed.WindowedCostModel
import FormalRV.Shor.MeasUncomputeAt
import FormalRV.Shor.WindowedComposedCost
import FormalRV.Shor.WindowedComposedAt
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
  §5.  HONEST-GAP LEDGER — what is STILL not on a verified circuit.
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

4. **Qubit-count totals are architecture partitions, not circuit widths.**
   The data-qubit literal reconciles (`audit_data_qubit_literal_eq_derived`:
   `9 633 792 = 3n × 2(d+1)²`), and the 20 M budget partitions exactly into
   zones (`zones_partition_budget`) — but only per-gadget widths are
   circuit-derived; the `modExpAt` whole-circuit width theorem
   (`maxIdx_modExpAt_le` / `width_modExpAt_le`, advertised in
   `WindowedComposedAt`'s header) is DEFERRED and not yet in the corpus.

5. **The single windowed-modexp-inside-QPE object is the named WELD, in flight.**
   `WindowedModNShor` does not exist yet.  The two halves are each verified:
   `modExpAt` (THIS file's counted object, per-multiply-add value semantics via
   `multiplyAddAt_fold`) and the adder-generic quantum-selected in-place modexp
   `Arithmetic/Windowed/WindowedExpInPlaceQ.windowedExpInPlaceQ_correct` — but
   no one object is simultaneously RSA-2048-counted AND value-correct inside
   the QPE host.  Until that weld lands, "circuit count" above means the
   counted `modExpAt` whose value laws are per-multiply-add. -/

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
-- the upstream value-semantics theorems the witness instantiates:
#check @FormalRV.Shor.WindowedComposedAt.multiplyAddAt_fold
#check @FormalRV.Shor.MeasUncomputeAt.babbushLookupAddAtValueSpecOn_holds
#check @FormalRV.Shor.MeasUncomputeAt.measUncomputeAt_saves_a_read
