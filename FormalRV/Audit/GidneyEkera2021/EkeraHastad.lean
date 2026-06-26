/-
  Audit · Gidney–Ekerå 2021 · EKERÅ–HÅSTAD (EH) SHORT-DLP HEADLINE
  ════════════════════════════════════════════════════════════════════════════
  The published GE2021 algorithm (arXiv:1905.09749, "How to factor 2048-bit RSA
  integers in 8 hours…") does NOT run textbook single-register order finding — it
  runs the **Ekerå–Håstad short discrete-logarithm** variant (`n_e ≈ 1.5·n` exponent
  qubits), then recovers the RSA factorisation from the recovered short DL `d = p+q`.

  The GE2021 audit's previous "headline" (`EndToEnd.gidney_ekera_2021_shor_succeeds`)
  is merely an alias of STANDARD single-register QPE order finding
  (`windowedModNMul_shor_correct`, `≥ κ/(log₂ N)⁴`) — it carries ZERO Ekerå–Håstad
  content even though the EH machinery is fully PROVEN elsewhere in the repo.  This
  file wires that proven EH machinery into the GE2021 audit, by REUSE (no proof is
  duplicated):

    * the EH per-run success ≥ 1/8 on the paper's two-register measurement formula
      (`FormalRV.Audit.Gidney2025.EkeraEndToEnd.ehShor_endToEnd`,
       built on Lemma 7 `ekera_lemma7_unconditional` + the EH good-pair count lemma);
    * the deterministic factor recovery from the short DL `d = a+b` of the RSA
      modulus `N = (2a+1)(2b+1)` (same `ehShor_endToEnd`, via `ekera_recover_actual`);
    * the push-to-1 amplified bound (Ekerå 2023 Thm 1) via
      `FormalRV.Shor.CFS.EkeraSuccess.EkeraDLPSuccess.success_ge` + `ekeraGoodFactor_ge`.

  ════════════════════════════════════════════════════════════════════════════
  THE THREE CARRIED OBLIGATIONS (for a FULL circuit-level EH bound — honest)
  ════════════════════════════════════════════════════════════════════════════
  Matching the repo's established methodology (named obligations, NOT axioms, NOT
  faked), a fully circuit-level EH success bound for GE2021 still carries exactly:

   (i)  THE ORACLE-BORN WELD.  `ehProb ℓ m d j k` is PROVEN equal to the Born
        probability of the EH QFT+measurement (`prob_partial_meas_eq_ehCircuitMeasProb`,
        `Audit/Gidney2025/EkeraHastadCircuitMeasurement.lean`), but the modular-
        exponentiation oracle entanglement feeding the QFT is abstracted as the posited
        output state `twoRegOracleState` — i.e. "formula = Born amplitude" is closed
        modulo that oracle-state abstraction (the same QFT boundary order finding lives
        at `Shor_final_state` / `QPE_MMI_correct`).

   (ii) LEMMA 1 (`good_obl`) + LEMMA 2 (`balanced_obl`) — the two distributional
        lattice bounds of Ekerå 2023 Thm 1, carried as STRUCTURE FIELDS of
        `EkeraDLPSuccess` (`FormalRV.Shor.CFS.EkeraSuccess`).  Lemma 1 is the trigamma
        good-pair bound; Lemma 2 is the t-balanced-lattice fraction — research-grade:
        Mathlib has geometry-of-numbers EXISTENCE (`IsZLattice`, Minkowski, covolume)
        but no LLL / CVP / lattice-distribution theory, so the measured-`j` lattice
        distribution is not yet derivable inside Mathlib.

   (iii) THE `n_e = 1.5·n` REGISTER SIZING is not yet a verified circuit width — the
         EH bounds here are parametric in `(ℓ, m)`; that the GE2021 circuit instantiates
         them with `ℓ + m ≈ 1.5·n` exponent qubits is the paper's sizing, not a verified
         circuit dimension in this development.

  ════════════════════════════════════════════════════════════════════════════
  WHAT IS UNCONDITIONAL HERE vs WHAT CARRIES AN OBLIGATION
  ════════════════════════════════════════════════════════════════════════════
   • `ge2021_ekera_hastad_per_run`  — UNCONDITIONAL (kernel-clean): the honest EH
     headline.  Per-run success ≥ 1/8 ON THE PAPER'S EH MEASUREMENT FORMULA `ehProb`,
     AND deterministic recovery of the RSA factors from `d = p+q`.  (`ehProb` = Born
     prob modulo obligation (i); the ≥ 1/8 and the recovery are both proven on it.)
   • `ge2021_ekera_hastad_amplified` — CONDITIONAL on an `EkeraDLPSuccess` witness
     (its `good_obl` = Lemma 1, `balanced_obl` = Lemma 2, obligation (ii)).  Given that
     witness, per-run success ≥ `(1 − 3/2^τ)·ekeraBalancedFactor Δ t τ`, the push-to-1
     bound.  We state the dependency explicitly — it is the honest carried obligation.

  No proof is re-proved here; every result is an instantiation / packaging of an
  already-PROVEN lemma.  Kernel-clean on the unconditional part:
  `#print axioms ge2021_ekera_hastad_per_run ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import FormalRV.Audit.Gidney2025.EkeraEndToEnd
import FormalRV.Shor.CFS.EkeraSuccess

namespace FormalRV.Audit.GidneyEkera2021.EkeraHastad

open scoped BigOperators
open FormalRV.Audit.Gidney2025.EkeraEndToEnd (ehProb goodOutcomes kPair ehShor_endToEnd)
open FormalRV.CFS (EkeraDLPSuccess ekeraGoodFactor ekeraBalancedFactor
  ekeraGoodFactor_ge ekeraBalancedFactor_nonneg)

/-! ## §1. The honest EH headline — UNCONDITIONAL (kernel-clean).

`ge2021_ekera_hastad_per_run` is the Ekerå–Håstad short-DLP per-run statement for the
GE2021/RSA setting, obtained by REUSING `ehShor_endToEnd` (no proof duplicated):

  (a) PER-RUN SUCCESS ≥ 1/8 on the paper's EH two-register measurement formula
      `ehProb` — the probability of observing SOME good pair in one run is `≥ 1/8`
      (Lemma 7 `ekera_lemma7_unconditional` × the EH good-pair count `≥ 2^{ℓ+m-1}`);
  (b) DETERMINISTIC FACTOR RECOVERY of the RSA factors `p = 2a+1`, `q = 2b+1` of
      `N = (2a+1)(2b+1)` from the recovered short discrete log `d = a+b`, via the
      quadratic `(d+1) ± √((d+1)² − N)` (`ekera_recover_actual`).

Honest scope: `ehProb` is the paper's measurement FORMULA, PROVEN = the Born
probability of the EH QFT+measurement modulo the abstracted oracle state
`twoRegOracleState` (carried obligation (i)).  The ≥ 1/8 bound and the factor recovery
are both unconditional on that formula. -/

/-- **★ THE HONEST EKERÅ–HÅSTAD GE2021 HEADLINE (per run) — UNCONDITIONAL. ★**

    For the GE2021/RSA short-DLP setting with first register `ℓ + m` qubits, second
    register `ℓ` qubits, short discrete log `d = a + b` (`b ≤ a`), and RSA modulus
    `N = (2a+1)(2b+1)`:

      (a) one EH run observes a good pair with probability `≥ 1/8` on the paper's
          EH measurement formula `ehProb`, AND
      (b) the RSA factors `2a+1`, `2b+1` are deterministically recovered from `d` as
          `(d+1) ± √((d+1)² − N)`.

    A direct re-export of the PROVEN `ehShor_endToEnd` — no proof re-proved.  This is
    the EH content GE2021 actually uses (short DLP, `n_e ≈ 1.5n`), in place of the
    standard single-register order-finding alias.  Kernel-clean: `#print axioms ⊆
    {propext, Classical.choice, Quot.sound}`. -/
theorem ge2021_ekera_hastad_per_run (ℓ m d : ℕ)
    (hℓ : 1 ≤ ℓ) (hm : 2 ≤ m) (hd0 : 0 < d) (hdlt : d < 2 ^ m)
    (a b N : ℕ) (hab : b ≤ a) (hd : d = a + b) (hN : N = (2 * a + 1) * (2 * b + 1)) :
    (1 / 8 : ℝ) ≤ ∑ j ∈ goodOutcomes ℓ m d, ehProb ℓ m d j (kPair ℓ m d j)
      ∧ ((d + 1) + ((d + 1) * (d + 1) - N).sqrt = 2 * a + 1
          ∧ (d + 1) - ((d + 1) * (d + 1) - N).sqrt = 2 * b + 1) :=
  ehShor_endToEnd ℓ m d hℓ hm hd0 hdlt a b N hab hd hN

/-! ## §2. The push-to-1 amplified bound — CONDITIONAL on an `EkeraDLPSuccess` witness.

The ≥ 1/8 per-run floor (§1) is amplified to `≥ 1 − negligible` by Ekerå 2023
Theorem 1.  That bound is a PRODUCT of two distributional factors, each carried as a
named obligation of `EkeraDLPSuccess` (`good_obl` = Lemma 1, `balanced_obl` = Lemma 2,
carried obligation (ii)).  We do NOT discharge those obligations — we REUSE the proven
`EkeraDLPSuccess.success_ge` and `ekeraGoodFactor_ge`, and state the dependency on the
witness `S` explicitly.  This is the honest carried obligation, NOT a faked bound. -/

/-- **★ THE EKERÅ–HÅSTAD GE2021 AMPLIFIED (push-to-1) BOUND — CONDITIONAL. ★**

    GIVEN an `EkeraDLPSuccess` witness `S` for the GE2021 short-DLP run (which CARRIES
    Lemma 1 as `S.good_obl` and Lemma 2 as `S.balanced_obl` — the two distributional
    lattice obligations, carried obligation (ii)), the per-run recovery probability is

        `S.successProb ≥ (1 − 3/2^S.τ) · ekeraBalancedFactor S.Δ S.t S.τ`,

    i.e. Factor 1 → 1 exponentially in the security parameter `τ` (Ekerå 2023 Cor 1 /
    Table 1) — the push-to-1 upgrade over the constant `1/8` floor of §1.  This is the
    qualitative EH advantage GE2021 relies on for high single-shot success.

    Proof = `EkeraDLPSuccess.success_ge` (the two-factor product, PROVEN) composed with
    `ekeraGoodFactor_ge` (Factor 1 ≥ 1 − 3/2^τ, PROVEN) and Factor-2 nonnegativity — no
    proof re-proved.  CONDITIONAL on `S` (whose `good_obl`/`balanced_obl` are the honest
    EH distributional obligations). -/
theorem ge2021_ekera_hastad_amplified (S : EkeraDLPSuccess) :
    (1 - 3 / (2 : ℝ) ^ S.τ) * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb :=
  le_trans
    (mul_le_mul_of_nonneg_right (ekeraGoodFactor_ge S.τ)
      (ekeraBalancedFactor_nonneg S.Δ S.t S.τ))
    S.success_ge

/-! ## §3. Witnesses — all pieces simultaneously importable, kernel-clean on (1). -/

-- (1) UNCONDITIONAL honest EH headline (per-run ≥ 1/8 on ehProb + deterministic recovery):
#check @ge2021_ekera_hastad_per_run
-- (2) CONDITIONAL push-to-1 bound (depends on the EkeraDLPSuccess witness S; good_obl/balanced_obl):
#check @ge2021_ekera_hastad_amplified

end FormalRV.Audit.GidneyEkera2021.EkeraHastad
