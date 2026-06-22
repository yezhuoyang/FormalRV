/-
  FormalRV.Shor.CFS.ShortDLPOrbit — the short-DLP joint ORBIT STATE (the 2-register eigenstate),
  constructed and proven, REUSING order finding's basis-generic Fourier-eigenstate machinery.

  ## What this file PROVES (genuine, axiom-clean)

  The Ekerå–Håstad short-DLP algorithm runs a TWO-register QPE; the relevant joint eigenstate is the
  tensor (Kronecker) product of two `fourierEigenstate` instances, one per register (1702.00249
  App A.2.1, "the joint phase register decouples into a tensor product").  We CONSTRUCT that joint
  state (`short_dlp_orbit_state`) and PROVE it is a joint eigenstate of the two per-register
  cyclic-shift operators with the PRODUCT phase `exp(2πi·sM·kM/rM)·exp(2πi·sL·kL/rL)`
  (`short_dlp_orbit_joint_eigen`), by applying the proven 1-register
  `SQIRPort.fourierEigenstate_eigen_lsb` ONCE PER REGISTER (the two per-register shift hypotheses are
  genuinely used, one each — exactly as the 1-register lemma uses its single `h_shift`).

  ## What this file does NOT claim (honesty)

  This is the orbit-state *building block* only.  It does NOT close the **residue-to-phase bridge**
  (turning `EHGoodPair m ℓ d j k`, one bound on the joint residue, into the two per-register phase
  bounds the peak law consumes).  A faithful bridge requires the FIXED eigenphase determined by the
  discrete log `d` (not a per-outcome choice) and the paper's actual Lemma-7 argument (a single sum
  over `b` with one phase angle + Cauchy-Schwarz over the `T_e` machinery), which does NOT reduce to
  the factorised two-1-register-peak idealisation.  That bridge remains the open analytic target; we
  do not fake it with outcome-dependent phases.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.OrderFinding.FourierEigenstate
import FormalRV.Core.QuantumLib
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open FormalRV.Framework
open scoped BigOperators

/-- **The short-DLP joint orbit state.**  For orbit periods `rM`, `rL` and per-register eigenbases
    `φM : Fin rM → QState (2^a)`, `φL : Fin rL → QState (2^b)`, the joint character eigenstate
    `fourierEigenstate rM φM kM ⊗ᵥ fourierEigenstate rL φL kL` — the 2-register short-DLP eigenstate
    (App A.2.1). -/
noncomputable def short_dlp_orbit_state
    {a b rM rL : Nat}
    (φM : Fin rM → Matrix (Fin (2 ^ a)) (Fin 1) ℂ)
    (φL : Fin rL → Matrix (Fin (2 ^ b)) (Fin 1) ℂ)
    (kM : Fin rM) (kL : Fin rL) :
    Matrix (Fin (2 ^ (a + b))) (Fin 1) ℂ :=
  FormalRV.Framework.kron_vec
    (FormalRV.SQIRPort.fourierEigenstate rM φM kM)
    (FormalRV.SQIRPort.fourierEigenstate rL φL kL)

/-- **Per-register eigenvalue, register `M`.**  REUSES `fourierEigenstate_eigen_lsb` on register `M`. -/
theorem fourierEigenstate_eigen_M
    {a rM : Nat} (h_rM : 0 < rM)
    (φM : Fin rM → Matrix (Fin (2 ^ a)) (Fin 1) ℂ)
    (MM : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℂ) (sM : Nat) (kM : Fin rM)
    (h_shiftM : ∀ j : Fin rM,
        MM * φM j = φM ⟨(sM + j.val) % rM, Nat.mod_lt _ h_rM⟩) :
    MM * FormalRV.SQIRPort.fourierEigenstate rM φM kM
      = Complex.exp
          (((2 * Real.pi * (sM : ℝ) * (kM.val : ℝ) / (rM : ℝ) : ℝ) : ℂ) * Complex.I)
        • FormalRV.SQIRPort.fourierEigenstate rM φM kM :=
  FormalRV.SQIRPort.fourierEigenstate_eigen_lsb h_rM φM MM sM kM h_shiftM

/-- **THE JOINT ORBIT-STATE EIGENVALUE THEOREM** (App A.2.1, "the joint phase register decouples into
    a tensor product").  Applying the register-`M` shift to the high factor and the register-`L`
    shift to the low factor, the joint orbit state picks up the PRODUCT phase
    `exp(2πi·sM·kM/rM)·exp(2πi·sL·kL/rL)`.  PROVEN by REUSE: `fourierEigenstate_eigen_lsb` on EACH
    register (`h_shiftM`/`h_shiftL` genuinely used, one each), then the tensor-factor scalar laws. -/
theorem short_dlp_orbit_joint_eigen
    {a b rM rL : Nat} (h_rM : 0 < rM) (h_rL : 0 < rL)
    (φM : Fin rM → Matrix (Fin (2 ^ a)) (Fin 1) ℂ)
    (φL : Fin rL → Matrix (Fin (2 ^ b)) (Fin 1) ℂ)
    (MM : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℂ) (sM : Nat)
    (ML : Matrix (Fin (2 ^ b)) (Fin (2 ^ b)) ℂ) (sL : Nat)
    (kM : Fin rM) (kL : Fin rL)
    (h_shiftM : ∀ j : Fin rM,
        MM * φM j = φM ⟨(sM + j.val) % rM, Nat.mod_lt _ h_rM⟩)
    (h_shiftL : ∀ j : Fin rL,
        ML * φL j = φL ⟨(sL + j.val) % rL, Nat.mod_lt _ h_rL⟩) :
    FormalRV.Framework.kron_vec
        (MM * FormalRV.SQIRPort.fourierEigenstate rM φM kM)
        (ML * FormalRV.SQIRPort.fourierEigenstate rL φL kL)
      = (Complex.exp
            (((2 * Real.pi * (sM : ℝ) * (kM.val : ℝ) / (rM : ℝ) : ℝ) : ℂ) * Complex.I)
          * Complex.exp
            (((2 * Real.pi * (sL : ℝ) * (kL.val : ℝ) / (rL : ℝ) : ℝ) : ℂ) * Complex.I))
        • short_dlp_orbit_state φM φL kM kL := by
  rw [FormalRV.SQIRPort.fourierEigenstate_eigen_lsb h_rM φM MM sM kM h_shiftM,
      FormalRV.SQIRPort.fourierEigenstate_eigen_lsb h_rL φL ML sL kL h_shiftL]
  rw [FormalRV.Framework.kron_vec_smul_left, FormalRV.Framework.kron_vec_smul_right,
      smul_smul]
  rfl

/-! ## The orbit-state results pass the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean fourierEigenstate_eigen_M
#verify_clean short_dlp_orbit_joint_eigen

end FormalRV.CFS
