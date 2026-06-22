/-
  Audit · gidney-2025 · VERIFIER — end-to-end obligation + anti-cheat gate
  ============================================================================
  RESOURCE: the physical-qubit footprint TALLY is internally consistent and
  under budget (897,864 < 1,000,000) — axiom-free.  SEMANTIC: the CFS residue-
  arithmetic engine computes g^e mod N exactly (pre-truncation, L2); Ekerå–
  Håstad recovery extracts the factor from the discrete log.  ✅ #verify_clean
  ACCEPTS these.

  THE ONE CONJECTURE — Assumption 1 (a prime set with ∏P ≥ N^m and Δ_N < 2^{-f}
  exists) — is STATED as a Prop and NEVER asserted (⬜).  GAP: the QUANTUM half
  (QPE recovers the discrete log w.h.p.; anchored by the shared success bound in
  Audit/Peng2022) — see README.

  ## What "verify" means here — and what it does NOT
  This file verifies the paper's INTERNAL ARITHMETIC consistency (its component
  tallies add up to its stated totals — the SystemZones `decide` theorems) and
  the SEMANTIC CORE of the algorithm's novel content (the CFS residue-arithmetic
  engine, proved bottom-up and axiom-clean in `FormalRV.Shor.CFS`).  It is NOT a
  closed whole-circuit semantic theorem that the circuit factors RSA-2048.

  Chosen parameters (grid-scan-selected, minimizing `q³·t`; main.tex:1006–1037):
    `s = 8`, `ℓ = 21`, `w₁ = 6`, `w₃ = 3`, `w₄ = 5`, `f = 33`, `|P| ≈ 640` primes,
    `m = 1280`, peak active logical ≈ 1409, `E(shots) ≈ 9.2`, `P_dev = 1.25%`.

  The SEMANTIC CORE — the CFS residue-arithmetic engine (six axiom-clean,
  `#verify_clean`-accepted modules; formulas cited from this paper's
  §"Approximate Residue Arithmetic"; engine `#verify_clean`'d in L2_Arithmetic):
    (1) `CFS.ResidueArith.residue_modexp_exact_of_lt` — residue modexp is EXACT,
        `(∏ M_k^{e_k}) % L % N = g^e mod N` when `L ≥ N^m` (no wraparound);
    (2) `CFS.ResidueNumberSystem.rns_faithful` — the RNS over the prime set `P`
        (`∏P = L`) is FAITHFUL (CRT injectivity), so modexp runs componentwise;
    (3) `CFS.Reconstruction.reconstruction` — the EXACT CRT reconstruction and
        the full chain `residue_modexp_via_crt : … % L % N = g^e mod N`;
    (4) `CFS.TruncationBound.sum_truncBits_error_double` — the APPROXIMATE
        reconstruction (each of `|P|·ℓ` terms truncated to `f` bits) deviates by
        `< |P|·ℓ·2^{-f}` (eq:modevbound);
    (5) `CFS.ModularDeviation.modDev_triangle/modDev_chain` — the paper's `Δ_N`
        metric is a pseudometric accumulating linearly over an op chain;
    (6) `CFS.Assumptions.SmallPrimeRNSModulusExists` — the one genuine conjecture
        (the `ℓ`-bit prime set), a `Prop`, never asserted.

  HONEST caveats on the RESOURCE numbers:
    * active-hot logical `131` and loop4 peak `1409` are paper-stated LITERALS
      (they do NOT decompose as `3f+2ℓ+⌈log m⌉ = 152` / `m+3f+2ℓ+len m = 1432`);
      the SYSTEM total `1537 = 1280+131+126` does reconcile;
    * the Toffoli count `6.5×10⁹` is a grid-scan OPTIMIZATION output, a paper-
      claim `def`, never a theorem conclusion;
    * the runtime (≈4.96 days) is the least-grounded headline (per-op latencies +
      `(1−10⁻¹⁵)^(6.9×10¹³) ≈ 93.3%` survival, none circuit-verified);
    * yoked surface codes (cold 430), cultivation, 8T→CCZ factories have NO Lean
      construction — coarse Nat placeholders;
    * minor textual slip (reported): runtime states "9.2 shots" then computes
      with "9.1".  Negligible.

  No `sorry`, no new `axiom`.
-/
import FormalRV.Audit.Gidney2025.SystemZones
import FormalRV.Shor.CFS.EkeraHastad
import FormalRV.Shor.CFS.Assumptions
import FormalRV.Verifier

namespace FormalRV.Audit.Gidney2025

/-- **GIDNEY 2025 — resource footprint reproduced + under budget.**  The cold +
    active-hot + idle-hot physical-qubit tally equals the paper's `897,864`, which
    is `< 1,000,000` with ≈100k slack (the `< 1M` headline) — and the encoded
    workload's logical count `1537` reconciles with the component tally.  An
    arithmetic-consistency reproduction (axiom-free); the semantic core is the
    CFS engine (`#verify_clean`'d in L2_Arithmetic). -/
theorem gidney2025_resource_reproduced :
    (1280 * 430 + 131 * 1352 + 7 * 18 * 1352 = 897864)
    ∧ (897864 < 1000000 ∧ 1000000 - 897864 = 102136)
    ∧ gidney2025_work.n_logical = 1280 + 131 + 7 * 18 :=
  ⟨gidney2025_physical_tally, gidney2025_slack, gidney2025_work_consistent⟩

end FormalRV.Audit.Gidney2025

-- ✅ SEMANTIC: the CFS engine yields factor recovery from the discrete log (axiom-free):
#verify_clean FormalRV.CFS.ekera_hastad_recovery
-- ✅ RESOURCE: the physical footprint tally is exact and under budget (axiom-free):
#verify_clean FormalRV.Audit.Gidney2025.gidney2025_physical_tally  -- ✅ 897,864 < 1,000,000
-- ✅ CAPSTONE: resource footprint reproduced + under budget + logical count reconciles:
#verify_clean FormalRV.Audit.Gidney2025.gidney2025_resource_reproduced
-- ⬜ the one conjecture, stated as a Prop and NEVER asserted:
#check @FormalRV.CFS.SmallPrimeRNSModulusExists
