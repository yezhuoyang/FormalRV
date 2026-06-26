/-
  Audit · Gidney–Ekerå 2021 · END-TO-END LOGICAL AUDIT
  ════════════════════════════════════════════════════════════════════════════
  ONE importable capstone bundling every verified component of the windowed
  modular-exponentiation Shor implementation, at the LOGICAL level (above PPM /
  Pauli measurement).  `import FormalRV.Audit.GidneyEkera2021.EndToEnd` pulls the
  whole audited stack; the `#check`s below witness that all pieces are
  simultaneously available and kernel-clean.

  ════════════════════════════════════════════════════════════════════════════
  THE END-TO-END LEDGER — every reported logical-level quantity, its VERIFIED
  semantic object, and the honest residual.
  ════════════════════════════════════════════════════════════════════════════

  (A) THE ALGORITHM SUCCEEDS.  `gidney_ekera_2021_shor_succeeds`
      (= `WindowedModNShor.windowedModNMul_shor_correct`): the windowed mod-N
      multiplier, welded into the order-finding family, gives
      `probability_of_success ≥ κ / (log₂ N)⁴` — the Ekerå-style Shor bound, on a
      concrete verified `EncodeRoundTripModMul` object (NOT a black box).

  (B) IT COMPUTES THE RIGHT VALUE.  `WindowedModExpValue.windowedModNExp_value`:
      the in-place windowed modexp leaves `a^e mod N` (true modulus, classical e).

  (C) ★ VERIFIED RESOURCE — THE SAME-OBJECT WELD (the resource result we stand behind).
      `ModExpAtSameObjectWeld.ge2021_oracle_correct_AND_counted_AND_bound`: for the per-iterate
      MEASURED windowed modular-multiply gate `G i := measWindowedModNEncodeGate …`, ALL THREE
      hold about the IDENTICAL syntactic gate —
        (1) ORACLE CORRECTNESS  `applyNat (G i) (encode x) = encode ((a^(2^i)·x) % N)`;
        (2) TOFFOLI COUNT       `toffoli (G i) = 2·numWin·(4·w·2^w + 8·bits)`  (G's OWN count);
        (3) SHOR BOUND          `≥ κ/(log₂ N)⁴` for the modexp family G realises (via the PROVEN
                                `egate_matches_rev` density-level match).
      The resource number is attached ONLY to a gate whose oracle semantics AND success bound are
      proven — no count on an object we did not prove.

  (C-paper) UN-WELDED PAPER-REPRODUCTION FIGURE — `2 578 993 152` is NOT a verified-oracle cost.
      `audit_toffoli_literal_eq_cost_model` reproduces the paper's cost FORMULA `2 622 824 448`
      exactly; `audit_toffoli_realized_by_circuit`: the STACKED `modExpAt` term has Toffoli count
      `2 578 993 152` (gap `43 831 296 = LookupAdditionCount·(1 + n·g_pad/g_sep)` = +1 rounding +
      runway-folding; per-lookup unit `5205 + 1 = 5206`, `audit_per_lookup_add`).  HONEST SCOPE —
      these reproduce the PAPER's accounting and are checked internally consistent, but they are
      NOT welded to verified semantics: the stacked `modExpAt`'s only proven value is an INNER
      multiply-add block's coset value (`ShorComposed.countOptimal_value_and_count_rsa2048`); the
      full modexp value `a^e mod N` is proven on a DIFFERENT (reused-register) object (B), and the
      success bound rides yet another gate (the exact multiplier).  So treat `2.58·10⁹` / `2.7·10⁹`
      as paper-reproduction figures, NOT as the verified oracle's resource cost — that is (C).

  (D) QUBIT COUNT.  `audit_qubit_count_realized_by_circuit`: the reused-register
      in-place multiplier has verified width `6162`, and `6162 + 27 = 6189` (the
      `+27` = the lg-n coset padding); the SystemZones literal `6200 = 6189 + 11`.

  (E) FIDELITY / approximation deviation.  `audit_coset_deviation_reduced` and
      `RunwayDeviationFaithful.totalWrapFracD_eq_totalDeviation`: the per-runway
      wrap fraction — with numerator the CIRCUIT's real deferred-carry occupancy
      and the paper's offset space `D = n²·n_e·1024 = 2^g_pad` — EQUALS the cost
      model's `totalDeviation` (≈ `7.64·10⁻⁸ ≤ 10⁻⁷`).

  (F) THE OBLIVIOUS CARRY RUNWAY ADDER (own folder, fully verified).
      `RunwayAdderContiguous.runwayAddK_contiguous`: the segmented runway adder
      computes `a + b` exactly (contiguous reading).  `…MultiAdd.runwayAddK_iter_contiguous`:
      `t`-fold accumulation `= a + t·b` under per-segment no-overflow (the
      deterministic condition the (E) deviation bounds).  `ParallelDepth.parallelDepth_runwayAddK_eq`:
      its parallel (ASAP critical-path) depth is INDEPENDENT of the segment count
      `k` — `O(g_sep)` vs a plain adder's `O(n)`: the oblivious-carry depth
      advantage, now a THEOREM.  Numerically cross-checked (`verify_qasm.py`): the
      emitted QASM adds correctly on all tested basis states.

  ════════════════════════════════════════════════════════════════════════════
  HONEST RESIDUAL — what is NOT yet one welded object / is cited not verified:
  ════════════════════════════════════════════════════════════════════════════
   • SAME-OBJECT WELD: count + oracle-correctness + Shor bound are now ALL on ONE gate (C) —
     the measured windowed multiplier `measWindowedModNEncodeGate` — which IS the verified
     resource result.  What is NOT welded is the paper's SPECIFIC `2.58·10⁹` STACKED `modExpAt`
     figure (C-paper): pinning the success bound to that exact term would need a measured stacked
     in-place multiplier (a from-scratch construction), so `2.58·10⁹` stays a paper-reproduction
     figure, not a count on the verified oracle.  (The standalone success bound (A) rides the
     exact reversible multiplier; the full-modexp value (B) rides the reused-register multiplier.)
   • The runway adder (F) is verified standalone; its integration as the inner
     adder of the windowed lookup loop is not yet wired (the loop currently uses
     the plain Cuccaro adder; both correct).
   • The deviation (E) carries ONE interpretive floor: the per-runway `1/D` is the
     counting fraction TAKEN AS the uniform probability (no Mathlib measure space).
   • Ekerå–Håstad phase estimation: the success bound (A) is standard-QPE /
     continued-fractions; the EH short-DLP post-processing is the paper's input.
   • The ~2.5× reaction-limited pipelining (8 h vs the verified 20.25 h ceiling)
     is the paper's empirical claim, not verified at scale.

  Kernel-clean throughout: axioms exactly `[propext, Classical.choice, Quot.sound]`.
-/
import FormalRV.Audit.GidneyEkera2021.WorkloadAssembly
import FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld
import FormalRV.Shor.WindowedModNShor
import FormalRV.Arithmetic.ObliviousRunwayAdder

namespace FormalRV.Audit.GidneyEkera2021.EndToEnd

/-- **THE END-TO-END HEADLINE — the algorithm succeeds.**  The windowed mod-N
    multiplier, as a verified `EncodeRoundTripModMul` welded into the order-finding
    family, attains the Shor success bound `≥ κ/(log₂ N)⁴`.  (Alias of
    `WindowedModNShor.windowedModNMul_shor_correct`.) -/
alias gidney_ekera_2021_shor_succeeds :=
  FormalRV.BQAlgo.WindowedModNShor.windowedModNMul_shor_correct

/-- **THE VERIFIED RESOURCE HEADLINE — the same-object weld.**  Oracle correctness, Toffoli
    count, and the Shor success bound, ALL on ONE syntactic gate (the measured windowed
    modular multiplier `measWindowedModNEncodeGate`).  This is the resource result the audit
    stands behind: the count rides a gate whose semantics are proven.  The paper's
    `2 578 993 152`-Toffoli STACKED `modExpAt` figure is a SEPARATE, un-welded paper-reproduction
    (ledger entry (C-paper)) — NOT a count on the verified oracle. -/
alias gidney_ekera_2021_resource_weld :=
  FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld.ge2021_oracle_correct_AND_counted_AND_bound

/-! ## The full bundle — all verified components, simultaneously importable. -/

-- (A) algorithm success bound:
#check @FormalRV.BQAlgo.WindowedModNShor.windowedModNMul_shor_correct
-- (B) end-to-end value a^e mod N:
#check @FormalRV.Shor.WindowedModExpValue.windowedModNExp_value
-- (C) ★ VERIFIED RESOURCE — the SAME-OBJECT weld: oracle-correctness ∧ count ∧ bound, one gate:
#check @FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld.ge2021_oracle_correct_AND_counted_AND_bound
-- (C-paper) un-welded paper-reproduction figures (2.58e9 stacked modExpAt; literal=formula):
#check @FormalRV.Audit.GidneyEkera2021.audit_toffoli_literal_eq_cost_model
#check @FormalRV.Audit.GidneyEkera2021.audit_toffoli_realized_by_circuit
#check @FormalRV.Audit.GidneyEkera2021.audit_per_lookup_add
-- (D) qubit count:
#check @FormalRV.Audit.GidneyEkera2021.audit_qubit_count_realized_by_circuit
-- (E) fidelity / deviation:
#check @FormalRV.Audit.GidneyEkera2021.audit_coset_deviation_reduced
#check @FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayDeviationFaithful.totalWrapFracD_eq_totalDeviation
-- (F) the oblivious carry runway adder: correctness + multi-add + parallel-depth advantage:
#check @FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous.runwayAddK_contiguous
#check @FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd.runwayAddK_iter_contiguous
#check @FormalRV.Arithmetic.ObliviousRunwayAdder.ParallelDepth.parallelDepth_runwayAddK_eq

end FormalRV.Audit.GidneyEkera2021.EndToEnd
