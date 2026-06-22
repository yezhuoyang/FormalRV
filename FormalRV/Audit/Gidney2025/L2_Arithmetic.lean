/-
  Audit · gidney-2025 · LAYER 2 — ARITHMETIC (the CFS residue-arithmetic engine)
  ----------------------------------------------------------------------------
  The strength of this audit: the residue engine is proved FROM FIRST PRINCIPLES and is
  AXIOM-CLEAN — exact modexp via faithful RNS (CRT injectivity), exact CRT reconstruction
  with a CONSTRUCTED basis, and a bounded truncation error.  All ✅ verify-clean.
-/
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Shor.CFS.CRTBasis
import FormalRV.Shor.CFS.TruncatedAccumulation
import FormalRV.Verifier

#verify_clean FormalRV.CFS.rns_faithful                    -- RNS faithful = CRT injectivity
#verify_clean FormalRV.CFS.reconstruction_explicit         -- exact CRT reconstruction (constructed basis)
#verify_clean FormalRV.CFS.residue_modexp_via_crt_explicit -- full exact RNS chain → g^e mod N
#verify_clean FormalRV.CFS.modDev_truncAcc_normalized      -- bounded truncation: Δ_N/N ≤ |P|·ℓ·2^{-f}
