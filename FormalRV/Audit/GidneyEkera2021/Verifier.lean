/-
  Audit · gidney-ekera-2021 · VERIFIER — end-to-end obligation + anti-cheat gate
  ----------------------------------------------------------------------------
  END-TO-END (resource reproduction): GE2021's 20M qubits / 8 h is reproduced as a
  FEASIBLE CEILING — the reported footprint IS the verified surface-code area ceiling
  (19.44M ≤ 20M), and the 8 h sits 2-3× UNDER the verified naive-sequential time ceiling.
  The capstone `gidney_ekera_2021_reproduced` is axiom-free (#verify_clean ACCEPTS it).
  The 2-3× time gap = reaction-limited pipelining, claimed but not verified at full scale (GAP).
-/
import FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction
import FormalRV.Verifier

-- ✅ CAPSTONE: GE2021 reproduced via the verified surface-code area/time law (axiom-free):
#verify_clean FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction.gidney_ekera_2021_reproduced
-- the resource ceilings the capstone rests on (➗ arithmetic):
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction.ge2021_qubits_derived          -- 19,443,200
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction.ge2021_qubits_reproduce_reported-- ≤ 20M
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction.ge2021_time_ceiling            -- ~20.25 h
#check @FormalRV.Audit.GidneyEkera2021.GidneyEkera2021Reproduction.ge2021_time_gap_2_to_3x        -- 8 h < ceiling
