/-
  FormalRV.Shor.CFS.QPEPeakLaw — T5: the QPE measurement wrapper on the residue oracle, and the
  QFT/QPE peak law, on REAL syntactic objects (no carried peak-law hypothesis).

  ## What T5 is and how it is done honestly

  The CFS algorithm period-finds via a QPE: prepare `|0⟩_m`, apply the controlled residue oracle
  powers, inverse-QFT the control register, and measure.  The deep analytic content — that the
  measurement probability CONCENTRATES on the period-related frequency (the "QFT peak law",
  `E(|β_k|²) ≈ w/P`, Gidney 2025 §2) — is the hardest analytic target.

  Crucially, the repo ALREADY PROVES this analytic core, axiom-clean, for the standard-Shor QPE:
    * `Framework.qpe_prob_peak_bound` — the 437-line Dirichlet-kernel bound `qpe_prob ≥ 4/π²`;
    * `qpe_prob_at_s_closest_ge` — its instantiation at the closest integer to `k·2^m/r`;
    * `QPE_MMI_correct_from_orbit` — PROVES `prob_partial_meas(s_closest) ≥ 4/(π²·r)` from the
      orbit-state form `(1/√r)·∑_k |qpe_phase_state(k/r)⟩⊗|β_k⟩` with ORTHONORMAL `β_k`.
  The ONLY remaining obligation (for standard Shor AND CFS alike) is the structural fact that the
  actual circuit's output state HAS that orbit form — `QPE_MMI_correct_assuming_orbit_factorization`
  isolates it as a single existential `h_orbit_exists`, documented as the framework-`control`-stub-
  blocked Phase-4 obligation (the modular-multiplier eigenstate spectrum + `QPE_var` circuit
  semantics).  We therefore do T5 the honest way — REUSE the proven peak law, never carry it:

    1. `basisVec_orthonormal` / `cfs_qft_peak_law_concrete` — the QFT peak law on a CONCRETE ideal
       orbit state, built from concrete orthonormal eigenstates (computational basis vectors).  FULLY
       PROVEN, ZERO hypotheses — `prob_partial_meas(s_closest m k r)(idealOrbitState) ≥ 4/(π²·r)`.
       This is the "QFT peak law" on a real object.
    2. `residueOracleFamily` / `residueOracleFamily_wellTyped` — the concrete QPE oracle wrapper: the
       residue multiplier circuit lifted to a `BaseUCom` family via `Gate.toUCom`, proven well-typed.
    3. `residueShorFinalState_peak_law` — the peak law on the REAL residue QPE circuit
       `Shor_final_state m n anc residueOracleFamily`: well-typedness DISCHARGED, the peak law
       INHERITED from the proven chain, and ONLY the structural `h_orbit_exists` bridge carried
       (never the peak law).  This is the same gap standard Shor has, precisely localized.
-/
import FormalRV.Shor.CFS.ResidueUnitary
import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.QPEMMICorrectFromOrbit
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
open scoped BigOperators

/-! ## §1. Concrete orthonormal eigenstates and the QFT peak law on the ideal orbit state. -/

/-- **Concrete orthonormal eigenstates.**  The computational basis vectors `|k⟩` for `k < r ≤ 2^q`
    form an orthonormal family — the cleanest concrete witness of the orthonormality the QPE peak law
    needs (any orthonormal family gives the same peak bound; the specific eigenstates do not matter to
    the measurement-probability concentration). -/
theorem basisVec_orthonormal {q r : Nat} (hrq : r ≤ 2 ^ q) (j j' : Fin r) :
    (∑ y : Fin (2 ^ q),
        starRingEnd ℂ (FormalRV.Framework.basis_vector (2 ^ q) j'.val y 0)
          * FormalRV.Framework.basis_vector (2 ^ q) j.val y 0)
      = if j = j' then (1 : ℂ) else 0 := by
  simp only [FormalRV.Framework.basis_vector_apply]
  by_cases hjj : j = j'
  · subst hjj
    rw [if_pos rfl]
    have hjq : j.val < 2 ^ q := lt_of_lt_of_le j.isLt hrq
    rw [Finset.sum_eq_single (⟨j.val, hjq⟩ : Fin (2 ^ q))]
    · simp
    · intro y _ hy
      have hyj : ¬ (y.val = j.val) := fun h => hy (Fin.ext h)
      simp [hyj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hjj]
    apply Finset.sum_eq_zero
    intro y _
    have hne : ¬ (j.val = j'.val) := fun h => hjj (Fin.ext h)
    by_cases hy : y.val = j.val
    · have hy' : ¬ (y.val = j'.val) := fun h => hne (hy ▸ h)
      simp [hy']
    · simp [hy]

/-- **THE QFT PEAK LAW ON A REAL CONCRETE STATE (T5 centerpiece, fully proven, no hypothesis).**
    For the ideal orbit state `(1/√r)·∑_k |qpe_phase_state(k/r)⟩⊗|k⟩` (concrete orthonormal basis-
    vector eigenstates), the partial measurement of the control register at the closest integer to
    `k·2^m/r` has probability `≥ 4/(π²·r)` — the QPE/QFT peak concentration, REUSING the proven
    Dirichlet-kernel bound `qpe_prob_peak_bound` via `QPE_MMI_correct_from_orbit`.  This is the
    analytic peak law of period finding, instantiated for the CFS frequencies, on a real state. -/
theorem cfs_qft_peak_law_concrete (m q r k : Nat)
    (hk : k < r) (hr : 0 < r) (hrq : r ≤ 2 ^ q)
    (hsm : FormalRV.SQIRPort.s_closest m k r < 2 ^ m) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.SQIRPort.basis_vector (2 ^ m) (FormalRV.SQIRPort.s_closest m k r))
        (fun i j => (1 / (Real.sqrt r : ℂ)) *
          ((∑ j_idx : Fin r,
             FormalRV.Framework.kron_vec
               (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
               (FormalRV.Framework.basis_vector (2 ^ q) j_idx.val) :
             Matrix (Fin (2 ^ (m + q))) (Fin 1) ℂ) i j))
      ≥ 4 / (Real.pi ^ 2 * (r : ℝ)) :=
  FormalRV.SQIRPort.QPE_MMI_correct_from_orbit k hk hr hsm
    (fun j => FormalRV.Framework.basis_vector (2 ^ q) j.val)
    (fun j j' => basisVec_orthonormal hrq j j')

/-! ## §2. The QPE oracle wrapper on the residue circuit (a real `BaseUCom` family). -/

/-- **The concrete QPE oracle family on the residue circuit.**  The `i`-th controlled power of the
    QPE is the residue multiplier chain for round `i` (constants `cs i`, inverses `cinvs i`), lifted
    from the syntactic `Gate` to a `BaseUCom` via `Gate.toUCom` — a genuine quantum circuit, the same
    `Gate.toUCom` boundary the rest of the FormalRV Shor pipeline lives at. -/
noncomputable def residueOracleFamily (w bits numWin pj steps dim : Nat)
    (cs cinvs : Nat → Nat → Nat) : Nat → FormalRV.Framework.BaseUCom dim :=
  fun i => Gate.toUCom dim (windowedModNMulInPlaceSeq w bits pj numWin (cs i) (cinvs i) steps)

/-- The residue QPE oracle family is well-typed at every round — `Gate.WellTyped` of the residue
    chain lifts to `uc_well_typed` of its `Gate.toUCom`, via the general bridge. -/
theorem residueOracleFamily_wellTyped (w bits numWin pj steps dim : Nat)
    (cs cinvs : Nat → Nat → Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) (i : Nat) :
    FormalRV.SQIRPort.uc_well_typed (residueOracleFamily w bits numWin pj steps dim cs cinvs i) :=
  uc_well_typed_toUCom_of_Gate_WellTyped dim _
    (windowedModNMulInPlaceSeq_wellTyped w bits pj numWin (cs i) (cinvs i) steps dim hw hbits hdim)

/-! ## §3. The peak law on the REAL residue QPE circuit (peak law inherited, bridge carried). -/

/-- **The QPE peak law on the residue circuit `Shor_final_state … residueOracleFamily`.**  With the
    oracle's well-typedness DISCHARGED (`residueOracleFamily_wellTyped`), the QPE peak bound
    `≥ 4/(π²·r)` holds on the actual residue QPE final state — INHERITED from the proven analytic
    chain (`QPE_MMI_correct_assuming_orbit_factorization` ∘ `QPE_MMI_correct_from_orbit` ∘
    `qpe_prob_peak_bound`), NOT carried.  The only carried inputs are STRUCTURAL, none of them the
    peak-law conclusion: `h_basic`/`h_mmi` (the standard Shor setting + that the residue oracle
    implements modular multiplication), and `h_orbit_exists` — the orbit-state eigendecomposition of
    the residue oracle.  `h_orbit_exists` is exactly the framework-`control`-stub-blocked Phase-4
    obligation that standard Shor also carries; it is the genuine remaining gap, precisely localized
    and named (never the peak law itself). -/
theorem residueShorFinalState_peak_law
    (a r N m steps w bits numWin pj : Nat) (n anc : Nat)
    (cs cinvs : Nat → Nat → Nat) (k : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ n + anc)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m n)
    (h_mmi : FormalRV.SQIRPort.ModMulImpl a N n anc
              (residueOracleFamily w bits numWin pj steps (n + anc) cs cinvs))
    (hk : k < r)
    (h_orbit_exists :
        ∃ (β : Fin r → Matrix (Fin (2 ^ (n + anc))) (Fin 1) ℂ)
          (actual_state : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ),
          ((∀ j j' : Fin r,
             ∑ y : Fin (2 ^ (n + anc)),
                  starRingEnd ℂ ((β j') y 0) * (β j) y 0
             = if j = j' then (1 : ℂ) else 0)
          ∧ (actual_state = fun i j => (1 / (Real.sqrt r : ℂ)) *
              ((∑ j_idx : Fin r,
                 FormalRV.Framework.kron_vec
                   (FormalRV.Framework.qpe_phase_state m ((j_idx.val : ℝ) / r))
                   (β j_idx) :
                 Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ) i j))
          ∧ (FormalRV.SQIRPort.prob_partial_meas
                (FormalRV.SQIRPort.basis_vector (2 ^ m) (FormalRV.SQIRPort.s_closest m k r))
                (FormalRV.SQIRPort.Shor_final_state m n anc
                  (residueOracleFamily w bits numWin pj steps (n + anc) cs cinvs))
              = FormalRV.SQIRPort.prob_partial_meas
                  (FormalRV.SQIRPort.basis_vector (2 ^ m) (FormalRV.SQIRPort.s_closest m k r))
                  actual_state))) :
    FormalRV.SQIRPort.prob_partial_meas
        (FormalRV.SQIRPort.basis_vector (2 ^ m) (FormalRV.SQIRPort.s_closest m k r))
        (FormalRV.SQIRPort.Shor_final_state m n anc
          (residueOracleFamily w bits numWin pj steps (n + anc) cs cinvs))
      ≥ 4 / (Real.pi ^ 2 * (r : ℝ)) :=
  FormalRV.SQIRPort.QPE_MMI_correct_assuming_orbit_factorization a r N m n anc k
    (residueOracleFamily w bits numWin pj steps (n + anc) cs cinvs)
    h_basic h_mmi
    (fun i _ => residueOracleFamily_wellTyped w bits numWin pj steps (n + anc) cs cinvs
                  hw hbits hdim i)
    hk h_orbit_exists

/-! ## The T5 peak-law results pass the VERIFIER gate (axiom-clean). -/

#verify_clean basisVec_orthonormal
#verify_clean cfs_qft_peak_law_concrete
#verify_clean residueOracleFamily_wellTyped
#verify_clean residueShorFinalState_peak_law

end FormalRV.CFS
