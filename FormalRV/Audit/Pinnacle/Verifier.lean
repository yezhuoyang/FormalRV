/-
  Audit · Pinnacle · VERIFIER — end-to-end obligation + anti-cheat gate
  ============================================================================
  STATUS: the GB-code-PARAMETER framework is verified on a representative code
  (L4: a real [[72,12,6]] GB code, k DERIVED from the constructed matrices); the
  RSA-scale code, the measurement gadget, the magic engine, and the < 100k
  resource bound are the ROADMAP (README STILL UNSOLVED).  The end-to-end
  < 100k obligation is OPEN — shown openly, not faked.  ✅ verify-clean on what
  is genuinely proven.
-/
import FormalRV.Audit.Pinnacle.L2_ArithmeticFaithful
import FormalRV.Audit.Pinnacle.L3_PPM
import FormalRV.Audit.Pinnacle.L4_Code
import FormalRV.Audit.Pinnacle.ParallelReduction
import FormalRV.Audit.Pinnacle.EndToEndQPE
import FormalRV.Audit.Pinnacle.ResourceCheck
import FormalRV.Audit.Pinnacle.FactoringClosure
import FormalRV.Audit.Pinnacle.PPMEndToEnd
import FormalRV.Verifier

-- ✅ the recorded RSA-2048 GB code instance ⟦510,16,24⟧ (n_pb=1620 recorded separately; axiom-free):
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_rsa_code_recorded
-- ✅ the Pinnacle-specific logical-arithmetic result: the parallel binary-tree reduction equals the
--    serial accumulator (paper Eq.20), and its deviation stays bounded — semantic, axiom-clean:
#verify_clean FormalRV.Audit.Pinnacle.ParallelReduction.parallelReduction_eq_serial
#verify_clean FormalRV.Audit.Pinnacle.ParallelReduction.parallelReduction_modDev
-- ✅ SEAM CLOSED: the parallel SCHEDULE's own per-register truncated accumulator (not just the exact
--    value) meets the SAME normalised deviation bound Δ_N/N ≤ (ρ·c)/2^f — the per-schedule fidelity
--    claim the paper argued only in prose (and got wrong in v1).  Axiom-clean:
#verify_clean FormalRV.Audit.Pinnacle.ParallelReduction.parallelSchedule_apprAcc_deviation
#verify_clean FormalRV.Audit.Pinnacle.ParallelReduction.parallelSchedule_apprAcc_modDev
-- ✅ STRONGER (the real content of the above): the parallel SCHEDULE's per-register truncated
--    accumulator is EXACTLY EQUAL to the serial one — so the serial bound transfers verbatim:
#verify_clean FormalRV.Audit.Pinnacle.ParallelReduction.parApprAcc_eq_serial
-- ✅ END-TO-END QPE / ORDER-FINDING CAPSTONE (arithmetic/logical-circuit object): the `residueFold`
--    RNS modexp computes g^e mod N (circuit-derived) → short dlog → factors, PLUS a true bound on the
--    carried Ekerå witness (success seam) AND the assembled RNS-modexp Toffoli count on the SAME gate,
--    AND the abstract parallel-reduction identity (Eq.20).  Axiom-clean:
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_modexp_endToEnd
-- ✅ END-TO-END SHOR SEMANTIC CORRECTNESS — THE FAITHFUL EKERÅ–HÅSTAD / RNS CIRCUIT FACTORS N
--    (Pinnacle's ACTUAL algorithm = Gidney2025 EH short-DLP + Chevignard RNS, NOT vanilla order-finding):
--    (I) EH frequency-measurement success ≥ 1/8 on the GATE-BUILT QFT-measured state (inverse-QFT via
--    real uc_eval + Born projection; the EH measurement law ehProb=Born prob is PROVEN, not carried)
--    ∧ (II) the RNS residueFold CRT-computes g^e mod N ∧ (III) dlog link ∧ (IV) factor recovery:
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_eh_rns_shor_succeeds
-- ✅ PPM-LEVEL END-TO-END: the RNS residueFold modexp Gate lowered to a magic-aware PPM program
--    (Pauli-product measurements + one factory-DISTILLED |T⟩ per Toffoli) RUNS and its CRT-reconstructed
--    measured output = g^e mod N — semantic correctness at the PPM layer; distilled-T demand = Toffoli count:
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_modexp_ppm_realized
-- ✅ L1: Pinnacle's ACTUAL algorithm success route — Ekerå–Håstad single-run dlog recovery
--    (corrected from the prior vanilla-order-finding #check; the EH-RNS bound the factoring uses):
#verify_clean FormalRV.Audit.Pinnacle.pinnacle_dlog_recovery_succeeds
-- ✅ L3 (PPM-level): any logical Pauli-product computation preserves the GB code (scale-free induction):
#verify_clean FormalRV.Audit.Pinnacle.gb_logical_computation_preserves_code
-- ✅ L2 FAITHFUL per-gadget Toffoli equations on value-correct measured gadgets (now IN the build+gate):
#verify_clean FormalRV.Audit.Pinnacle.Faithful.pinnacle_addition_toffoli
#verify_clean FormalRV.Audit.Pinnacle.Faithful.pinnacle_lookup_toffoli
-- ✅ ABOVE-PPM RESOURCE CHECK: every Table V row satisfies the stated conventions (2·LC = 3·T; T=4·Toff)
--    and υ/Λ are correctly assembled — Table V is internally consistent (no column-relation mistake):
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.addL1_consistency
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.lookupL1_consistency
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.upsilon_assembly
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.tau_consistency
-- ✅ REPORTED-VALUE SWEEP: κ register-count identity MATCHES; + the 2 minor discrepancies found
--    (magic-engine p_r 19p vs 49p tension; the FH p=10⁻⁴ displayed-equation wrong constant +1807 vs +592):
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.pinnacle_kappa_components
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.pinnacle_magic_reject_tension
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.pinnacle_FH_eq_constant_overcount
-- ✅ GADGET GROUNDING: the PHASEUP is the ONE cost equation NOT grounded by a faithful verified circuit —
--    our value-correct √-phaseup is a GENERAL table-phase lookup (18 @ w=4), the paper's is the
--    SPECIALIZED Hamming-weight phase-gradient (2 @ w=4); different gadgets, so the paper's count is
--    neither confirmed nor refuted (honest open item, NOT a confirmed error):
#verify_clean FormalRV.Audit.Pinnacle.ResourceCheck.pinnacle_phaseup_general_vs_specialized
-- the GB-code-parameter foundation (➗ native_decide — k DERIVED from matrices):
#check @FormalRV.Audit.Pinnacle.pinnacle_gb_72_k_derived
