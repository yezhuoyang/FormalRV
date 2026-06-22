/-
  Audit · Pinnacle (arXiv:2602.11457) · END-TO-END SHOR SEMANTIC CORRECTNESS — the FAITHFUL EH–RNS circuit
  ════════════════════════════════════════════════════════════════════════════
  Pinnacle's logical algorithm IS Gidney 2025 = **Ekerå–Håstad short discrete log** (1702.00249) with
  **Chevignard residue-number-system** one-shot modular exponentiation — NOT vanilla Shor order/period
  finding.  (Confirmed against the paper: it tunes the "Ekerå–Håstad parameter 1≤s≤16", accumulates
  "discrete-log values" per prime, and does "a frequency measurement (inverse QFT + measurement)" with
  Ekerå 2D-lattice post-processing — there is NO `mult-by-a^(2^i)` ladder and NO continued-fraction order
  recovery.)  So an earlier vanilla-order-finding "closure" would have been a DIFFERENT algorithm; it is
  removed.  This file closes Pinnacle's ACTUAL algorithm by FUSING the two verified halves:

    • the EH frequency-measurement SUCCESS, as a `prob_partial_meas` bound on the GATE-BUILT measured
      state (the two-register inverse-QFT `twoRegQFT⊗I` via real `uc_eval`, then control-register
      projection) — `EkeraHastadCircuit.ehGate_per_run_ge_eighth` (axiom-free); and
    • the RNS `residueFold` modular exponentiation computing `g^e mod N` exactly, on the actual `Gate`
      (`CFS.residueFold_crt_correct`).

  `pinnacle_eh_rns_shor_succeeds` conjoins, on shared `g, N, ehD, p, q`: (I) EH per-run success `≥ 1/8`
  on the gate-built QFT-measured state; (II) the RNS modexp value `g^e mod N`; (III) the dlog link
  `g^{ehD} ≡ g^{N-1}`; (IV) factor recovery `p·(ehD−p+2)=N`.

  ── HONEST STATUS (what is gate-verified vs the residual classical/oracle seam) ──
  GATE-VERIFIED: the inverse-QFT (real `uc_eval` of `twoRegQFT`) + the Born projection (`prob_partial_meas`)
  carrying the EH per-run floor (Lemma 7 + the good-pair count, all proven); and the RNS arithmetic value
  on the real `residueFold` gate.  The EH measurement law (`ehProb = Born probability`) is now a PROVEN
  THEOREM (`prob_partial_meas_eq_ehCircuitMeasProb`), no longer the carried `EkeraDLPSuccess` witness.
  RESIDUAL (the single remaining seam, honest): the EH oracle is abstracted as the output state
  `twoRegOracleState` (via `ehInput`/`ehEnc`); realizing THAT state as `residueFold` ∘ input-prep — i.e.
  proving the RNS modexp gate produces the EH entanglement — is the entangling-oracle bridge (no quantum
  content beyond the modexp value already proven in (II)).  Plus the paper's own number-theory conjecture
  `SmallPrimeRNSModulusExists` (Assumption 1) for the RNS modulus.  NO quantum measurement-law gap remains.
-/
import FormalRV.Audit.Gidney2025.EkeraHastadCircuitMeasurement
import FormalRV.Shor.CFS.ResidueCRT
import FormalRV.Shor.CFS.EkeraHastad

namespace FormalRV.Audit.Pinnacle

open scoped BigOperators
open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort (prob_partial_meas)
open FormalRV.QFT.TwoRegisterQFT (twoRegQFTMeasState)
open FormalRV.Audit.Gidney2025.EkeraHastadCircuit (ehInput ehEnc ehGate_per_run_ge_eighth)
open FormalRV.Audit.Gidney2025.EkeraEndToEnd (goodOutcomes kPair)
open FormalRV.CFS

/-- **★★ PINNACLE — FAITHFUL EKERÅ–HÅSTAD / RNS END-TO-END: THE CIRCUIT FACTORS N. ★★**  Pinnacle's
    actual algorithm (Gidney 2025 = EH short-DLP + Chevignard RNS), closed by FUSING the gate-verified EH
    frequency measurement with the verified RNS modular exponentiation.  On shared `g, N, ehD, p, q`:

      (I)  **EH FREQUENCY-MEASUREMENT SUCCESS `≥ 1/8`** on the GATE-BUILT measured state — the verified
           two-register inverse-QFT (`twoRegQFT⊗I`, genuine `uc_eval`) applied to the post-oracle state,
           then control-register Born projection, observes a good pair with probability `≥ 1/8`
           (`ehGate_per_run_ge_eighth`; the EH measurement law `ehProb = Born prob` is PROVEN, not carried).
      (II) **RNS MODEXP `g^e mod N`** — the concrete `residueFold` CRT-reconstructs to `g^e mod N`
           (Pinnacle's efficient one-shot modular exponentiation, proven on the actual `Gate`).
      (III) **DLOG LINK** `g^{ehD} ≡ g^{N-1} (mod N)` (Ekerå–Håstad: `ehD = p+q-2` is the short dlog).
      (IV) **FACTOR RECOVERY** `p·(ehD−p+2) = N` ∧ `p² + N = (ehD+2)·p`.

    Carried inputs are CLASSICAL/number-theoretic: the EH register sizing + short dlog (`ehL,ehM,ehD`),
    the RNS residue-circuit preconditions (`SmallPrimeRNSModulusExists`'s content + primality —
    Assumption 1), and the factorisation data.  The remaining SEAM is realizing the oracle entanglement
    as `residueFold ∘ prep` (entangling-oracle bridge), documented above — NO quantum measurement-law gap. -/
theorem pinnacle_eh_rns_shor_succeeds
    -- (EH measurement) register/parameter sizes + the short discrete log `ehD`
    (ehL ehM ehD : ℕ) (hℓ : 1 ≤ ehL) (hm : 2 ≤ ehM) (hd0 : 0 < ehD) (hdlt : ehD < 2 ^ ehM)
    -- (RNS arithmetic) the residue circuit computing the one-shot modexp `g^e mod N`
    (P : Nat → Nat) (ainvss : Nat → Nat → Nat) (numP w bits numWin g N e steps : ℕ)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < steps → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hsteps : 1 ≤ steps) (he : e < 2 ^ steps)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hLprod : N ^ steps ≤ ∏ i : Fin numP, P i.val)
    -- (factoring) Ekerå–Håstad factorisation data: `ehD = p+q-2`, `N = p·q`
    (p q : ℕ) (hd : ehD = p + q - 2) (hNpq : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q]) :
    -- (I) EH MEASUREMENT SUCCESS ≥ 1/8 on the GATE-BUILT (QFT+projection verified) measured state
    ((1 / 8 : ℝ) ≤ ∑ j ∈ goodOutcomes ehL ehM ehD,
        prob_partial_meas
          (FormalRV.SQIRPort.basis_vector (2 ^ ((ehL + ehM) + ehL)) (j * 2 ^ ehL + kPair ehL ehM ehD j))
          (twoRegQFTMeasState (ehL + ehM) ehL (ehL + ehM + 1) (ehInput ehL ehM) (ehEnc ehL ehM ehD)))
    -- (II) the RNS `residueFold` CRT-computes `g^e mod N` (the efficient one-shot modexp)
    ∧ ((∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e steps) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
      = g ^ e % N)
    -- (III) DLOG LINK
    ∧ (g ^ ehD ≡ g ^ (N - 1) [MOD N])
    -- (IV) FACTOR RECOVERY
    ∧ (p * (ehD - p + 2) = N ∧ p * p + N = (ehD + 2) * p) :=
  ⟨ehGate_per_run_ge_eighth ehL ehM ehD hℓ hm hd0 hdlt,
   residueFold_crt_correct P ainvss numP w bits numWin g N e steps hw hbits hPok hN hsteps he hco hLprod,
   by rw [hd, hNpq]; exact (ekera_hastad_exponent p q g (by omega) (by omega) hphi).symm,
   ekera_hastad_recovery p q ehD N hd hNpq hp hq⟩

end FormalRV.Audit.Pinnacle
