/-
  FormalRV.Shor.CFS.SemanticClosure — closing the CFS Shor semantic-correctness seam.

  ## The discovery that unblocks closure

  The CFS peak law (`QPEPeakLaw.residueShorFinalState_peak_law`) and the capstone carried the
  structural bridge `h_orbit_exists` (the circuit's QPE output state HAS the orbit-superposition form)
  as the "framework-`control`-stub-blocked Phase-4 gap".  THAT GAP IS STALE: the framework now PROVES
  the QPE circuit semantics, axiom-clean —

    * `SQIRPort.qpe_on_eigenstate_correct` — `uc_eval (QPE_var_lsb m anc f)·(|0^m⟩⊗ψ) = qpe_phase_state m θ ⊗ ψ`
      for any eigenstate `ψ` (the unconditional QPE-on-eigenstate theorem);
    * `CosetOrbitEngine.qpe_var_lsb_on_eigenfamily_initial` — the generic orbit engine (eigenfamily →
      orbit form), via `kron`-linearity per orbit term;
    * `QPEModmultEigenstate.*` — the modular-multiplier eigenstate spectrum: for ANY `ModMulImpl` oracle,
      the eigenstates satisfy the LSB eigenvalue property + orthonormality + orbit decomposition;
    * `PostQFTCompletion.QPE_MMI_correct` — **now a THEOREM (the deleted axiom's replacement)**: from
      `BasicSetting + ModMulImpl + well-typed + k<r` it PROVES `prob_partial_meas(s_closest) ≥ 4/(π²r)`
      on `Shor_final_state`, constructing `h_orbit_exists` internally (no longer carried);
    * `PostQFTCompletion.Shor_correct_var` — **PROVEN**: `probability_of_success ≥ κ/(log₂N)⁴` for any
      `ModMulImpl` oracle (the totient lower bound is now supplied, not carried).

  So `h_orbit_exists` is no longer a carried obligation — it follows from `ModMulImpl`.  This file
  closes the CFS quantum seam down to the clean classical oracle spec:

    * `residueShorFinalState_peak_law_closed` — the CFS QPE peak law `≥ 4/(π²r)` carrying ONLY
      `ModMulImpl` (the orbit-form bridge DISCHARGED via `QPE_MMI_correct`).
    * `cfs_shor_semantic_correctness` — the END-TO-END statement: the quantum period-finding SUCCESS is
      now PROVEN (`Shor_correct_var`, not the abstract `EkeraDLPSuccess` witness), composed with the CFS
      residue circuit's exact modexp (T7), the dlog link, and factor recovery.

  ## What remains carried (honest)

  Only genuine, non-quantum obligations:
    * `ModMulImpl a N n anc u` for the period-finding oracle `u` — the CLASSICAL spec "the oracle
      multiplies by `a^{2^i} mod N`".  For the textbook verified multiplier this is PROVEN axiom-clean
      (`Shor_correct_verified_no_modmult_axioms`); for an oracle implemented via the CFS residue
      arithmetic, proving it is the per-prime encoding bridge (a classical basis-action correspondence,
      no quantum content) — the one remaining CFS-specific classical seam.
    * the residue-circuit preconditions = `SmallPrimeRNSModulusExists`'s content (`∏P ≥ N^m`, coprime) + primality.
    * `SmallPrimeRNSModulusExists` itself — the paper's number-theoretic conjecture.
  The QUANTUM half (QPE semantics, peak law, orbit form, success bound) is now PROVEN, not carried.
-/
import FormalRV.Shor.CFS.QPEPeakLaw
import FormalRV.Shor.CFS.ResidueCRT
import FormalRV.Shor.CFS.EkeraHastad
import FormalRV.Shor.PostQFT.PostQFTCompletion
import FormalRV.Shor.VerifiedShor.VerifiedShorTheorem
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open scoped BigOperators

/-! ## §1. The CFS QPE peak law with `h_orbit_exists` DISCHARGED. -/

/-- **The CFS peak law, orbit-form bridge CLOSED.**  For the residue QPE oracle, the measurement peak
    `≥ 4/(π²r)` follows from `ModMulImpl` ALONE — the carried `h_orbit_exists` of
    `residueShorFinalState_peak_law` is now DISCHARGED by the proven `QPE_MMI_correct` (which
    constructs the orbit form from the modmult eigenstate spectrum).  Well-typedness is proven; the
    only remaining input is the clean classical oracle spec `ModMulImpl`. -/
theorem residueShorFinalState_peak_law_closed
    (a r N m steps w bits numWin pj : Nat) (n anc : Nat)
    (cs cinvs : Nat → Nat → Nat) (k : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ n + anc)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc
              (residueOracleFamily w bits numWin pj steps (n + anc) cs cinvs))
    (hk : k < r) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.SQIRPort.basis_vector (2 ^ m) (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc
          (residueOracleFamily w bits numWin pj steps (n + anc) cs cinvs))
      ≥ 4 / (Real.pi ^ 2 * (r : ℝ)) :=
  FormalRV.SQIRPort.QPE_MMI_correct a r N m n anc k _ h_basic h_mmi
    (fun i _ => residueOracleFamily_wellTyped w bits numWin pj steps (n + anc) cs cinvs
                  hw hbits hdim i)
    hk

/-! ## §2. The end-to-end CFS semantic correctness — quantum success now PROVEN. -/

/-- **★ CFS SHOR SEMANTIC CORRECTNESS (end to end, quantum half PROVEN) ★.**  Composes, on shared
    `a, r, N, g, e, d, p, q`:

      (I)  **QUANTUM PERIOD-FINDING SUCCEEDS** — `probability_of_success ≥ κ/(log₂N)⁴` for the
           period-finding oracle `u` (`Shor_correct_var`).  This is now a PROVEN theorem (the QPE
           semantics + orbit form + Dirichlet peak + totient bound are all discharged), NOT the
           abstract `EkeraDLPSuccess` witness the earlier capstone carried.
      (II) **THE CFS RESIDUE CIRCUIT COMPUTES `g^e mod N`** — the concrete `residueFold`, read out and
           CRT-reconstructed, equals `g^e mod N` (T7, `residueFold_crt_correct`).  The efficient
           residue implementation of the modexp the algorithm period-finds.
      (III) **DLOG LINK** — `g^d ≡ g^{N-1} (mod N)`: `d` is the dlog of `h = g^{N-1}` (Ekerå–Håstad).
      (IV) **FACTOR RECOVERY** — `p·(d-p+2) = N`, `p² + N = (d+2)·p` from `d = p+q-2`, `N = p·q`.

    The carried inputs are the classical oracle spec `ModMulImpl u` (proven for the verified
    multiplier; the residue-oracle encoding bridge for a CFS-implemented oracle), the residue-circuit
    preconditions (`SmallPrimeRNSModulusExists`'s content + primality), and the Ekerå–Håstad factorisation data.  The
    QUANTUM correctness is no longer carried — it is proven by `Shor_correct_var`. -/
theorem cfs_shor_semantic_correctness
    -- the quantum period-finding oracle (a verified modular multiplier; ModMulImpl)
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i))
    -- the CFS residue circuit data (the efficient modexp implementation, T7)
    (P : Nat → Nat) (ainvss : Nat → Nat → Nat) (numP w bits numWin g e : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hL : N ^ m ≤ ∏ i : Fin numP, P i.val)
    -- the factorisation data (Ekerå–Håstad)
    (p q d : Nat) (hd : d = p + q - 2) (hNpq : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q]) :
    -- (I) QUANTUM PERIOD-FINDING SUCCEEDS — PROVEN (Shor_correct_var)
    (FormalRV.SQIRPort.probability_of_success a r N m n anc u
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4)
    -- (II) the CFS residue circuit computes `g^e mod N` (T7)
    ∧ ((∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
      = g ^ e % N)
    -- (III) DLOG LINK
    ∧ (g ^ d ≡ g ^ (N - 1) [MOD N])
    -- (IV) FACTOR RECOVERY
    ∧ (p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p) :=
  ⟨FormalRV.SQIRPort.Shor_correct_var a r N m n anc u h_basic h_mmi h_wt,
   residueFold_crt_correct P ainvss numP w bits numWin g N e m hw hbits hPok hN hm he hco hL,
   by rw [hd, hNpq]; exact (ekera_hastad_exponent p q g (by omega) (by omega) hphi).symm,
   ekera_hastad_recovery p q d N hd hNpq hp hq⟩

/-! ## §3. The FULLY-CONCRETE closure — quantum half with NO carried oracle hypothesis. -/

/-- **★★ CFS SHOR SEMANTIC CORRECTNESS — FULLY CONCRETE QUANTUM HALF ★★.**  The strongest closure:
    the quantum period-finding success is the FULLY AXIOM-CLEAN, CONCRETE-ORACLE theorem
    `Shor_correct_verified_no_modmult_axioms` — it uses the SQIR-verified modular multiplier
    `f_modmult_circuit_verified_bits` (whose `ModMulImpl` is PROVEN internally), so there is NO carried
    `ModMulImpl`, NO `h_orbit_exists`, and NO quantum hypothesis at all.  Composed with the CFS residue
    circuit's exact modexp (T7) and Ekerå–Håstad recovery.

      (I)  **QUANTUM SUCCESS (fully proven, concrete oracle)** — `probability_of_success ≥ κ/(log₂N)⁴`
           for the verified multiplier `f_modmult_circuit_verified_bits g ainv N (…)`.
      (II) **CFS RESIDUE MODEXP** — the concrete `residueFold` CRT-reconstructs to `g^e mod N` (T7).
      (III)/(IV) the dlog link + factor recovery.

    The ONLY remaining inputs are CLASSICAL, non-quantum preconditions: `BasicSettingRelaxed` (the
    number-theoretic regime — `g` has order `r` mod `N`, register sizing), the modular inverse
    `g·ainv ≡ 1`, the residue-circuit preconditions (`SmallPrimeRNSModulusExists`'s content + primality), and the
    Ekerå–Håstad factorisation data.  THE QUANTUM HALF OF CFS SHOR IS PROVEN (axiom-clean, for the
    verified modmult oracle) — the `f_modmult_circuit_verified_bits` oracle and the CFS `residueFold`
    are two implementations of the same modexp `g^· mod N`, the former carrying the (verified)
    period-finding, the latter the (verified, T7) efficient arithmetic; FUSING them into ONE oracle —
    i.e. proving the residue circuit, lifted to a QPE oracle, satisfies the basis-action spec
    (`ModMulImpl` for the residue oracle, the per-prime encoding correspondence) — is the sole
    remaining classical CFS seam.  No quantum obligation remains; only this classical bridge and
    `SmallPrimeRNSModulusExists` (the number-theoretic conjecture). -/
theorem cfs_shor_semantic_correctness_concrete
    (g r N e m ainv : Nat)
    (h_basic_r : FormalRV.BQAlgo.BasicSettingRelaxed g r N m (Nat.log2 (2 * N) + 1))
    (h_inv : g * ainv % N = 1)
    -- the CFS residue circuit data (T7, the efficient modexp implementation)
    (P : Nat → Nat) (ainvss : Nat → Nat → Nat) (numP w bits numWin : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hL : N ^ m ≤ ∏ i : Fin numP, P i.val)
    -- the factorisation data (Ekerå–Håstad)
    (p q d : Nat) (hd : d = p + q - 2) (hNpq : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q]) :
    -- (I) QUANTUM PERIOD-FINDING SUCCEEDS — fully proven, concrete verified oracle, NO quantum hypothesis
    (FormalRV.SQIRPort.probability_of_success g r N m (Nat.log2 (2 * N) + 1)
        (FormalRV.BQAlgo.sqir_modmult_rev_anc (Nat.log2 (2 * N) + 1))
        (FormalRV.BQAlgo.f_modmult_circuit_verified_bits g ainv N (Nat.log2 (2 * N) + 1))
        ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4)
    -- (II) the CFS residue circuit computes `g^e mod N` (T7)
    ∧ ((∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
      = g ^ e % N)
    -- (III) DLOG LINK
    ∧ (g ^ d ≡ g ^ (N - 1) [MOD N])
    -- (IV) FACTOR RECOVERY
    ∧ (p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p) :=
  ⟨FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms g r N m ainv h_basic_r h_inv,
   residueFold_crt_correct P ainvss numP w bits numWin g N e m hw hbits hPok hN hm he hco hL,
   by rw [hd, hNpq]; exact (ekera_hastad_exponent p q g (by omega) (by omega) hphi).symm,
   ekera_hastad_recovery p q d N hd hNpq hp hq⟩

/-! ## The semantic-closure theorems pass the VERIFIER gate (axiom-clean). -/

#verify_clean residueShorFinalState_peak_law_closed
#verify_clean cfs_shor_semantic_correctness
#verify_clean cfs_shor_semantic_correctness_concrete

end FormalRV.CFS
