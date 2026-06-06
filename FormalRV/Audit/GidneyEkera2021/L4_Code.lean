/-
  Audit · gidney-ekera-2021 · LAYER 4 — THE QEC CODE
  ----------------------------------------------------------------------------
  The rotated distance-27 surface code, 2·(d+1)² = 1568 physical qubits per
  logical (paper §2.14 + Fig. 8, formula `n = 2(d+1)²`).
  ⬜ RECORDED: the (n,k,d) tuple is bound, but the parity matrices are not
  constructed here (it is the standard surface code; resource law uses 2(d+1)²).
  See README GAP.

  This file also holds the full GE2021 parametric tuple `ge2021_instance`
  (Shor × QECCode × hardware), since it bundles the L1 algorithm, this L4 code,
  and the hardware parameters.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.Audit.GidneyEkera2021.Hardware
import FormalRV.Audit.GidneyEkera2021.L1_Algorithm

namespace FormalRV.Audit.GidneyEkera2021

open FormalRV.Framework FormalRV.Qualtran

/-- Gidney–Ekerå surface-code patch: distance-27 rotated surface code,
1568 physical qubits per logical (paper §2.14 + Fig. 8, formula
`n = 2(d+1)²`). Parity matrices stubbed `[]` — a later tick can
encode the d=27 stabilizer schedule. -/
def ge2021_code : QECCode :=
  { n := 1568, k := 1, d := 27, hx := [], hz := [] }

/-- The full parametric tuple for the Gidney–Ekerå 2021 instance. -/
def ge2021_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (ge2021_shor, ge2021_code, ge2021_hw)

/-- Smoke: paper-stated parameters read back. q_A ≈ 3·n; d = 27;
hardware matches the Qualtran factory. -/
example : ge2021_instance.1.q_A = 3072 := by rfl
example : ge2021_instance.2.1.n = 1568 ∧
          ge2021_instance.2.1.k = 1 ∧
          ge2021_instance.2.1.d = 27 := ⟨rfl, rfl, rfl⟩
example : ge2021_instance.2.2 = gidney_fowler_realistic := rfl

end FormalRV.Audit.GidneyEkera2021

#check @FormalRV.Audit.GidneyEkera2021.ge2021_code    -- QECCode (d = 27 surface tile)
