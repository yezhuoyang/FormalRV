/-
================================================================================
  AUDIT — gidney-ekera-2021, 20M qubits / ~8 h (arXiv:1905.09749)
================================================================================
  Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm ·
  L2_Arithmetic · L3_PPM · L4_Code · Verifier · WorkloadAssembly · Codegen).  Every
  file lives in ONE flat namespace `FormalRV.Audit.GidneyEkera2021`.  See
  `GidneyEkera2021/README.md` for claim, settings, approach, and the per-layer
  ledger + GAP.

  Verify:  `lake build FormalRV.Audit.GidneyEkera2021`
-/
import FormalRV.Audit.GidneyEkera2021.Hardware
-- The coset/runway machine FACTORS (concrete oracle, one composed circuit) — kernel-clean.
import FormalRV.Audit.GidneyEkera2021.CosetFactoringSucceeds
-- …and on a genuinely CIRCUIT-PREPARED input |0…0⟩ (one prep+QPE circuit) — closes audit seam G1, kernel-clean.
import FormalRV.Audit.GidneyEkera2021.CosetFactoringCircuitPrepared
-- Measured-weld (gap 4): the Shor bound AND the measured Toffoli count on ONE genuinely-measured count-bearing gate
-- (measWindowedModNEncodeGate, egate_matches_rev PROVEN via measurement-uncompute) — kernel-clean.
import FormalRV.Audit.GidneyEkera2021.ModExpAtResidueInstance
-- Reduction weld (gap 4, ride the LITERAL multiplyAddAt): the Shor bound AND the HONEST count decomposition
-- tcount = multiplyAddAt + adaptOutReduce, on a block containing multiplyAddAt literally — CONDITIONAL on a now-SATISFIABLE
-- (non-T-free) ModExpAtReductionAdapter (the T-free version is provably unsatisfiable). Kernel-clean.
import FormalRV.Audit.GidneyEkera2021.ModExpAtReductionWeld
-- Toward the UNCONDITIONAL literal-multiplyAddAt reduction read-out (direct-eg route): foundational, kernel-clean infrastructure.
-- The whole weld reduces to ONE remaining gate (R2: a windowed inverse-mod-mul with quotient-uncompute in the stacked layout).
import FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput   -- S1: multiplyAddAt full-output (M1/M2/M3) + decodeReg↔cuccaro bridge
import FormalRV.Audit.GidneyEkera2021.DivModNAt            -- S3: q_start-shifted divModN reduction at the accumulator band
import FormalRV.Audit.GidneyEkera2021.TranscodeBand        -- S4: T-free interleaved→big-endian band mover
import FormalRV.Audit.GidneyEkera2021.PaddedRevFamily      -- S7a: padded rev family + anc-generic egate_matches_rev (native anc)
import FormalRV.Audit.GidneyEkera2021.InPlaceMulData       -- reusable in-place mod-mul on the data band (transcode bridge, numWin≤2)
import FormalRV.Audit.GidneyEkera2021.InPlaceMulDataAt     -- reusable in-place mod-mul on the data band (relabel route, ANY numWin)
-- HONEST STATUS of the literal-STACKED-multiplyAddAt weld (ModExpAtReductionDirect): NOT cleanly achievable. multiplyAddAt is a
-- MEASURED EGate (babbushLookupAddAt/EGate.mz, irreversible) that produces only the UN-reduced forward product; the bridge-reuse
-- in-place gate therefore (a) is CONDITIONAL on the named measurement-uncompute obligation `UnmulSpecRfree`, and (b) renders the
-- literal multiplyAddAt FUNCTIONALLY DECORATIVE (the reused reversible windowedModNMulInPlace does the real in-place work). The
-- UNCONDITIONAL gap-4 answer is the MEASURED-gate weld (ModExpAtResidueInstance.ge2021_measEncode_shor_AND_count).
import FormalRV.Audit.GidneyEkera2021.ModExpAtReductionDirect
-- Discharge of the UnmulSpecRfree obligation: a concrete reversible `unmulConcrete` (= reverse of a Bennett-reversible mirror of
-- the measured count gate, proven to agree with multiplyAddAt on clean inputs) makes egRfree's residue UNCONDITIONAL
-- (egRfree_matchesResidue_unconditional : a real ModExpAtEncodedMatchesResidue instance). Caveat persists: multiplyAddAt stays
-- FUNCTIONALLY DECORATIVE in egRfree (the in-place multiply is the reused windowedModNMulInPlace via inPlaceMulDataAt).
import FormalRV.Audit.GidneyEkera2021.ModExpAtUnmul
-- ★ FULL END-TO-END BOUND on the literal-multiplyAddAt-containing reversible gate: egRfree_shor_AND_count gives the Shor success
-- bound ≥ κ/(log₂N)⁴ AND the honest count decomposition (multiplyAddAt + reversible reconstruction + 2·divModNAt + in-place
-- finisher) on egRfree — UNCONDITIONAL (only standard sizing + ShorSetting), kernel-clean. Caveat: multiplyAddAt is functionally
-- decorative (in-place work = reused windowedModNMulInPlace); the bound rides the padded reversible family egRfree provably matches.
import FormalRV.Audit.GidneyEkera2021.ModExpAtReductionBound
-- ★ THE SAME-OBJECT WELD (no cheating): ge2021_oracle_correct_AND_counted_AND_bound states ORACLE CORRECTNESS + TOFFOLI COUNT +
-- the SHOR BOUND all about the IDENTICAL gate measWindowedModNEncodeGate. The count is THAT gate's honest count, NOT multiplyAddAt's
-- forward-only 2.58e9 (which is NOT the oracle and is NOT presented as a resource result). Resource is attached only to a
-- gate whose semantics are proven.
import FormalRV.Audit.GidneyEkera2021.ModExpAtSameObjectWeld
-- ★ THE EKERÅ–HÅSTAD (EH) SHORT-DLP HEADLINE — the EH content GE2021 actually runs (n_e ≈ 1.5n exponent qubits),
-- in place of the standard single-register order-finding alias. Wires the PROVEN EH stack into this audit by REUSE:
--   • ge2021_ekera_hastad_per_run  — UNCONDITIONAL (kernel-clean): per-run success ≥ 1/8 on the paper's EH measurement
--     formula ehProb, AND deterministic RSA factor recovery (2a+1, 2b+1) from the short DL d = a+b of N = (2a+1)(2b+1).
--   • ge2021_ekera_hastad_amplified — CONDITIONAL on an EkeraDLPSuccess witness (carries Lemma 1/Lemma 2): push-to-1 bound.
-- Honest carried obligations are documented in the file header (oracle-Born weld; Lemma 1/2 lattice distribution; n_e=1.5n sizing).
import FormalRV.Audit.GidneyEkera2021.EkeraHastad
import FormalRV.Audit.GidneyEkera2021.L1_Algorithm
import FormalRV.Audit.GidneyEkera2021.L2_Arithmetic
import FormalRV.Audit.GidneyEkera2021.L3_PPM
import FormalRV.Audit.GidneyEkera2021.L4_Code
import FormalRV.Audit.GidneyEkera2021.PhysicalSyndrome
import FormalRV.Audit.GidneyEkera2021.SystemZones
import FormalRV.Audit.GidneyEkera2021.Verifier
import FormalRV.Audit.GidneyEkera2021.WorkloadAssembly
import FormalRV.Audit.GidneyEkera2021.Codegen
import FormalRV.Audit.GidneyEkera2021.ShorComposed
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
import FormalRV.Audit.GidneyEkera2021.ShorModExpAt
import FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance
