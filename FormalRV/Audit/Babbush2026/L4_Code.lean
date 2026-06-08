/-
  Audit · babbush-2026 · LAYER 4 — THE QEC CODE
  ----------------------------------------------------------------------------
  The surface code [[425, 1, 14]]: distance ≈ 14, ~425 physical qubits per
  logical, sized so that 1175 logical qubits × 425 phys/logical ≈ 500,000
  physical qubits (notes lines 222, 225; distance back-solved from
  2(d+1)² ≈ 425 — d = 14 is the matching distance).
  ⬜ RECORDED: the (n,k,d) tuple is bound, but the parity matrices are not
  constructed here.  See README GAP.

  This file also holds the full Babbush parametric tuple `babbush_instance`
  (Shor × QECCode × hardware), since it bundles the L1 algorithm, this L4 code,
  and the hardware parameters.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.Audit.Babbush2026.Hardware
import FormalRV.Audit.Babbush2026.L1_Algorithm

namespace FormalRV.Audit.Babbush2026

open FormalRV.Framework FormalRV.Qualtran

/-- Babbush surface-code instance: distance ≈ 14, ~425 physical qubits per
logical (back-solved from notes line 222 `1175 logical qubits` × notes line 225
`500_000 physical qubits` ÷ 1175 ≈ 425; 2(d+1)² = 450 gives d = 14 as the
matching distance).  Parity matrices stubbed `[]`. -/
def babbush_code : QECCode :=
  { n := 425, k := 1, d := 14, hx := [], hz := [] }

/-- The full parametric tuple for the Babbush 2026 instance. -/
def babbush_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (babbush_shor, babbush_code, babbush_hw)

/-- Smoke: paper-stated parameters read back. q_A = 8; [[425,1,14]];
hardware matches the Qualtran factory. -/
example : babbush_instance.1.q_A = 8 := by rfl
example : babbush_instance.2.1.n = 425 ∧
          babbush_instance.2.1.k = 1 ∧
          babbush_instance.2.1.d = 14 := ⟨rfl, rfl, rfl⟩
example : babbush_instance.2.2 = gidney_fowler_realistic := rfl

end FormalRV.Audit.Babbush2026

#check @FormalRV.Audit.Babbush2026.babbush_code   -- QECCode ([[425,1,14]] surface tile)
