/-
  Audit · gidney-2025 · LAYER 4 — THE QEC CODE
  ----------------------------------------------------------------------------
  The hot-region rotated distance-25 surface code, 2·(d+1)² = 2·26² = 1352
  physical qubits per logical (paper §3.2, notes line 128).  The yoked cold-
  storage region (d ≈ 8-10, 430 phys/logical) is a separate construction the
  framework does not model (recorded in SystemZones).
  ⬜ RECORDED: the (n,k,d) tuple is bound, but the parity matrices are not
  constructed here (it is the standard surface code; the resource law uses
  2(d+1)²).  See README GAP.

  This file also holds the full Gidney-2025 parametric tuple
  `gidney2025_instance` (Shor × QECCode × hardware), since it bundles the L1
  algorithm, this L4 code, and the hardware parameters.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.Audit.Gidney2025.Hardware
import FormalRV.Audit.Gidney2025.L1_Algorithm

namespace FormalRV.Audit.Gidney2025

open FormalRV.Framework FormalRV.Qualtran

/-- Gidney 2025 hot-region surface-code patch: distance-25 rotated surface
code, 1352 physical qubits per logical (paper §3.2 / notes line 128:
`2(d+1)² = 2·26² = 1352`).  Parity matrices stubbed `[]` — a later tick can
encode the d=25 stabilizer schedule. -/
def gidney2025_code : QECCode :=
  { n := 1352, k := 1, d := 25, hx := [], hz := [] }

/-- The full parametric tuple for the Gidney 2025 instance. -/
def gidney2025_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (gidney2025_shor, gidney2025_code, gidney2025_hw)

/-- Smoke: paper-stated parameters read back. s = 8; d = 25;
hardware matches the Qualtran factory. -/
example : gidney2025_instance.1.q_A = 8 := by rfl
example : gidney2025_instance.2.1.n = 1352 ∧
          gidney2025_instance.2.1.k = 1 ∧
          gidney2025_instance.2.1.d = 25 := ⟨rfl, rfl, rfl⟩
example : gidney2025_instance.2.2 = gidney_fowler_realistic := rfl

/-- Hot patch size: `2·(d+1)² = 2·26² = 1352` at `d = 25` (main.tex:1162). -/
theorem gidney2025_hot_patch_size : 2 * (25 + 1) ^ 2 = 1352 := by decide

end FormalRV.Audit.Gidney2025

#check @FormalRV.Audit.Gidney2025.gidney2025_code    -- QECCode (d = 25 hot surface tile)
