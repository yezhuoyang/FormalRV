/-
  FormalRV.Shor.PPMShorMaster — the whole-circuit INTEGRATION theorem.

  Chains the building blocks into ONE causal statement for the full pipeline:

    (realization)  the PPM program reproduces the compiled circuit's final state
                   (its data channel = the compiled unitary — `GadgetChannel`,
                   `magic_realizes_list_fold`), so its success is EXACTLY the
                   compiled circuit's (`prob_of_success_congr`);
    (approximation) the AQFT-compiled Clifford+T circuit's final state is within
                   `ε` (Born-normSq distance) of the verified circuit's, so its
                   success is within `ε` (`prob_of_success_transfer_normSqDist`);
    (verified)     the verified circuit succeeds with prob `≥ κ/(log₂N)⁴`
                   (`correct_general_via_interface`).

  ⇒ the PPM realization succeeds with prob `≥ κ/(log₂N)⁴ − ε`.

  This is the single end-to-end statement: a PPM-realized, AQFT-approximate Shor
  circuit's success degrades from the verified bound by exactly the (state-level)
  approximation error — no exact `uc_eval` equality required.

  The two inputs `h_realize` (exact realization) and `h_eps` (AQFT state-distance)
  are the conclusions of the gadget-channel and AQFT-error layers; assembling them
  at full RSA scale is the remaining engineering, but the master theorem that
  combines them — and degrades the verified bound by the approximation — is here.
  No `sorry`, no new `axiom`.
-/
import FormalRV.Shor.OrderFinding.ProbabilityTransfer
import FormalRV.Shor.ApproxTransfer
import FormalRV.Shor.VerifiedShor.ControlledModAddLayer

namespace FormalRV.SQIRPort

open VerifiedShor

/-- **Whole-circuit PPM-Shor master theorem.**  A PPM realization `f_ppm` that
    reproduces the final state of the AQFT-compiled circuit `f_comp`
    (`h_realize`), whose final state is within `ε` of the verified circuit's
    (`h_eps`), succeeds with probability `≥ κ/(log₂N)⁴ − ε`.  A single causal
    chain: realization (exact) → approximation (`ε`) → verified bound. -/
theorem ppm_shor_pipeline_master
    (a r N m bits ainv : Nat)
    (f_ppm f_comp : Nat → BaseUCom (bits + ModMul.ancillaWidth bits))
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1)
    (h_realize :
      Shor_final_state m bits (ModMul.ancillaWidth bits) f_ppm
        = Shor_final_state m bits (ModMul.ancillaWidth bits) f_comp)
    (ε : ℝ)
    (h_eps :
      ApproxTransfer.normSqDist
        (Shor_final_state m bits (ModMul.ancillaWidth bits) f_comp)
        (Shor_final_state m bits (ModMul.ancillaWidth bits)
          (ModMul.circuitFamily a ainv N bits)) ≤ ε) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits) f_ppm
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 - ε := by
  -- realization: prob(f_ppm) = prob(f_comp)
  rw [prob_of_success_congr a r N m bits (ModMul.ancillaWidth bits) f_ppm f_comp h_realize]
  -- approximation: |prob(f_comp) − prob(f_ver)| ≤ normSqDist ≤ ε
  have htrans := ApproxTransfer.prob_of_success_transfer_normSqDist a r N m bits
    (ModMul.ancillaWidth bits) f_comp (ModMul.circuitFamily a ainv N bits)
  -- verified bound: prob(f_ver) ≥ κ/(log₂N)⁴
  have hver := correct_general_via_interface a r N m bits ainv h_setting h_sizing h_inv
  have hge := (abs_le.mp (le_trans htrans h_eps)).1
  linarith [hver, hge]

/-- Non-vacuity: the master theorem fires at `ε = 0` with the identity realization
    (`f_ppm = f_comp = the verified family`), recovering the exact verified bound. -/
theorem ppm_shor_pipeline_master_representative
    (a r N m bits ainv : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    probability_of_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits)
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 - 0 := by
  refine ppm_shor_pipeline_master a r N m bits ainv
    (ModMul.circuitFamily a ainv N bits) (ModMul.circuitFamily a ainv N bits)
    h_setting h_sizing h_inv rfl 0 ?_
  simp [ApproxTransfer.normSqDist]

end FormalRV.SQIRPort
