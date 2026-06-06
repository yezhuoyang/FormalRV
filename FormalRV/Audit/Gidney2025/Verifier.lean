/-
  Audit · gidney-2025 · VERIFIER — end-to-end obligation + anti-cheat gate
  ----------------------------------------------------------------------------
  RESOURCE: the physical-qubit footprint TALLY is internally consistent and under budget
  (897,864 < 1,000,000) — axiom-free.  SEMANTIC: the CFS engine computes g^e mod N exactly
  (pre-truncation, L2); Ekerå–Håstad recovery extracts the factor from the discrete log.
  ✅ #verify_clean ACCEPTS these.

  THE ONE CONJECTURE — Assumption 1 (a prime set with ∏P ≥ N^m and Δ_N < 2^{-f} exists) — is
  STATED as a Prop and NEVER asserted (⬜).  GAP: the QUANTUM half (QPE recovers the discrete
  log w.h.p.; anchored by the shared success bound in Audit/Peng2022) — see README.
-/
import FormalRV.Audit.Gidney2025.Gidney2025
import FormalRV.Shor.CFS.EkeraHastad
import FormalRV.Shor.CFS.Assumptions
import FormalRV.Verifier

#verify_clean FormalRV.CFS.ekera_hastad_recovery                              -- ✅ factor recovery from the dlog
#verify_clean FormalRV.Audit.Gidney2025.Gidney2025.gidney2025_physical_tally  -- ✅ 897,864 < 1,000,000
#check @FormalRV.CFS.Assumption1                                              -- ⬜ the one conjecture (never asserted)
