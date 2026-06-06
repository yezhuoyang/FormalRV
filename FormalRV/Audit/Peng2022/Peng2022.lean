/-
  FormalRV.Audit.Peng2022.Peng2022 — Phase-C corpus paper #7 (last).

  Peng et al. 2022, the **SQIR/Coq mechanised proof** of Shor's
  algorithm. End-to-end formally verified in Coq using SQIR + RCIR
  (see `SQIR/examples/shor/` in this repo).

  **Special role in the corpus.** Peng 2022 is the only paper that
  has a *machine-checked* algorithm correctness theorem.  But it has
  **no QEC stack** — no surface code, no qLDPC, no distillation, no
  surgery (notes/peng-2022.md lines 54-55). It's pure algorithm-
  layer formalism.  So in our four-layer framework Peng 2022
  occupies a degenerate L4 slot (trivial / not-modeled QEC code)
  while L1 carries the genuine verified-Shor anchor.

  Recording Peng 2022 alongside the resource-estimate papers makes
  the asymmetry visible in Lean: it is the only corpus paper with a
  formally-verified L1, and the only one with no real L4.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : q_A = 1 (single-window, classical Shor;
                           SQIR-style)
    L4 QECCode           : trivial `(1, 1, 1)` placeholder — Peng
                           does not provide a code (notes line 54-55).
    HW QualtranPhysical  : `default_params` — Peng is algorithm-
                           level and does not specify hardware.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Audit.Peng2022.Peng2022

open FormalRV.Framework FormalRV.Qualtran

/-- Peng / SQIR Shor instance: classical single-window phase
estimation (no Ekerå–Håstad multi-window optimisation).  This is
the **machine-checked algorithm anchor** of the corpus. -/
def peng_shor : ShorAlgorithm :=
  { N := 0, q_A := 1 }

/-- Peng 2022 has **no QEC stack** (notes line 54-55). The L4 slot
gets a trivial placeholder `(n, k, d) = (1, 1, 1)`; the framework's
modulus-agnostic parametric tuple still type-checks. The honest
review-status conclusion is "Peng L4 = not modelled". -/
def peng_code : QECCode :=
  { n := 1, k := 1, d := 1, hx := [], hz := [] }

/-- Peng 2022 specifies no hardware — use Qualtran's `default_params`
(1e-3, 1 μs) as a neutral placeholder. -/
def peng_hw : QualtranPhysicalParameters :=
  default_params

/-- The full parametric tuple. -/
def peng_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (peng_shor, peng_code, peng_hw)

/-- Smoke: paper-stated parameters read back. -/
example : peng_instance.1.q_A = 1 := by rfl
example : peng_instance.2.1.n = 1 ∧
          peng_instance.2.1.k = 1 ∧
          peng_instance.2.1.d = 1 := ⟨rfl, rfl, rfl⟩
example : peng_instance.2.2 = default_params := rfl

end FormalRV.Audit.Peng2022.Peng2022
