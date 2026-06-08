/-
  Audit · peng-2022 · LAYER 4 — THE QEC CODE
  ----------------------------------------------------------------------------
  ⬜ GAP — Peng 2022 has NO QEC code (notes/peng-2022.md lines 54-55): no
  surface code, no qLDPC, no distillation, no surgery.  A trivial `(1, 1, 1)`
  placeholder is bound for interface uniformity; the verified success bound is
  code-AGNOSTIC by design.

  This file also holds the full Peng 2022 parametric tuple `peng_instance`
  (Shor × QECCode × hardware), since it bundles the L1 algorithm, this L4 code,
  and the hardware parameters.
-/
import FormalRV.Framework.L4_QECCode
import FormalRV.Audit.Peng2022.Hardware
import FormalRV.Audit.Peng2022.L1_Algorithm

namespace FormalRV.Audit.Peng2022

open FormalRV.Framework FormalRV.Qualtran

/-- Peng 2022 has **no QEC stack** (notes line 54-55).  The L4 slot gets a
trivial placeholder `(n, k, d) = (1, 1, 1)`; the framework's modulus-agnostic
parametric tuple still type-checks.  The honest review-status conclusion is
"Peng L4 = not modelled". -/
def peng_code : QECCode :=
  { n := 1, k := 1, d := 1, hx := [], hz := [] }

/-- The full parametric tuple for the Peng 2022 instance. -/
def peng_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (peng_shor, peng_code, peng_hw)

/-- Smoke: paper-stated parameters read back. q_A = 1 (single-window);
trivial (1,1,1) code; default placeholder hardware. -/
example : peng_instance.1.q_A = 1 := by rfl
example : peng_instance.2.1.n = 1 ∧
          peng_instance.2.1.k = 1 ∧
          peng_instance.2.1.d = 1 := ⟨rfl, rfl, rfl⟩
example : peng_instance.2.2 = default_params := rfl

end FormalRV.Audit.Peng2022

#check @FormalRV.Audit.Peng2022.peng_code   -- trivial placeholder (no QEC stack)
