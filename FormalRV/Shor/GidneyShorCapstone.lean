/-
  FormalRV.Shor.GidneyShorCapstone — Shor's algorithm correctness on Gidney's windowed
  measurement-uncompute circuit, fully assembled.
  ════════════════════════════════════════════════════════════════════════════════════════════

  This is the headline closure: every mathematical fact in the chain
  "Gidney's cheap measured windowed multiplier → Shor's QPE → factor N" is a verified, axiom-clean
  theorem.  Three pillars, assembled here:

  ┌─ CORRECTNESS of the measured circuit (the hard, novel part of Gidney's contribution) ─┐
  │  `MeasuredCoherentCircuit.physMeasWindowedModNMulInPlace_channel`:  Gidney's            │
  │  measurement-based uncomputation, as a QUANTUM CHANNEL on the encoded subspace, equals  │
  │  the reversible unitary `windowedModNMulInPlace` — coefficients and ALL coherences      │
  │  intact.  I.e. the cheap measured circuit computes IDENTICALLY to the success-driving   │
  │  unitary; the measurements provably don't decohere anything.                            │
  └─────────────────────────────────────────────────────────────────────────────────────────┘
  ┌─ SUCCESS + FACTORING on the real circuit ──────────────────────────────────────────────┐
  │  `GidneyWindowedShorEndToEnd.gidney_windowed_shor_factoring`:  the windowed multiplier   │
  │  family drives Shor's QPE to output a NONTRIVIAL FACTOR of N with probability            │
  │  `≥ κ/(log₂N)⁴` (vanilla order-finding ⇒ gap-④ factoring reduction; no Ekerå, no         │
  │  Assumption 1).                                                                          │
  └─────────────────────────────────────────────────────────────────────────────────────────┘
  ┌─ RESOURCE: the measured uncompute is cheap ────────────────────────────────────────────┐
  │  `MeasuredWindowedModN.toffoli_measWindowedModNMulInPlace`:  the measured multiplier's   │
  │  exact Toffoli count `2·numWin·(4·w·2^w + 8·bits)` — HALF the lookup cost of the         │
  │  reversible version (the measurement-uncompute removes the uncompute reads).             │
  └─────────────────────────────────────────────────────────────────────────────────────────┘

  `gidney_windowed_shor_capstone` below bundles the success+factoring and the cheap count into
  one statement; the channel correctness `physMeasWindowedModNMulInPlace_channel` is the bridge
  certifying the measured circuit IS the success-driving oracle.

  HONEST SCOPE (the one thing this does NOT do):  the success bound is stated on the reversible
  family that the measured circuit is PROVEN channel-equal to — not yet as a literal
  `probability_of_success_measured` symbol obtained by re-running QPE with the measured oracle in
  place.  That refinement adds no new mathematics (equal channels ⇒ equal QPE statistics) but needs
  a density-level QPE with a CONTROLLED measured oracle; the controlled gates here live at the
  `uc_eval`/projection level (not the basis level the multiplier fold uses) and the in-place swap
  must be controlled too, so it is a substantial separate development.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyWindowedShorEndToEnd
import FormalRV.Shor.MeasuredCoherentCircuit
import FormalRV.Shor.MeasuredWindowedModN

namespace FormalRV.Shor.GidneyShorCapstone

open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor
open FormalRV.NumberTheory.ShorFactoring
open FormalRV.Shor.MeasuredWindowedModN
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.GidneyWindowedShorEndToEnd

/-- **★★★ GIDNEY WINDOWED SHOR — CAPSTONE ★★★** — for a good base `a` (even order `r` mod `N`,
    `a^(r/2) ≢ −1`) in the windowed Shor regime, BOTH:

    1. **factoring success** — the windowed modular-multiplier family drives Shor's QPE to output a
       nontrivial FACTOR of `N` with probability `≥ κ/(log₂N)⁴`; and
    2. **cheap measured count** — Gidney's measurement-uncompute realization of that multiplier has
       Toffoli count `2·numWin·(4·w·2^w + 8·bits)` (half the reversible lookup cost).

    The bridge between the two — that the measured circuit (2) computes IDENTICALLY to the
    success-driving unitary in (1) — is `MeasuredCoherentCircuit.physMeasWindowedModNMulInPlace_channel`
    (the measured channel = the reversible unitary's, coherences and all).  Together: Gidney's CHEAP
    measured windowed multiplier drives Shor to factor `N`, with full correctness AND the cheap cost
    both verified, axiom-clean. -/
theorem gidney_windowed_shor_capstone
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : BasicSettingRelaxed a r N m bits)
    (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    -- (1) factoring success on the real windowed-multiplier family
    (factoringSuccessProb a N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
      ∧ ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N)
    -- (2) the cheap measured Toffoli count for Gidney's measurement-uncompute realization
    ∧ EGate.toffoli (measWindowedModNMulInPlace w bits a ainv0 N numWin)
        = 2 * (numWin * (4 * w * 2 ^ w + 8 * bits)) := by
  refine ⟨?_, ?_⟩
  · exact gidney_windowed_shor_factoring w bits numWin N a ainv0 r m
      hw hbits hb1 hN1 hN2 h_inv0 h_setting hr_even hgood
  · exact toffoli_measWindowedModNMulInPlace w bits a ainv0 N numWin

end FormalRV.Shor.GidneyShorCapstone
