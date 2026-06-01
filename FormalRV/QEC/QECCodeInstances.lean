/-
  FormalRV.Framework.QECCodeInstances — concrete QEC code
  instances (identifiers for implementer submissions).

  Codes provided:
  * Steane [[7, 1, 3]]
  * Surface code at distances d = 3, 5, 7, 11, 25
    (non-rotated count: [[d², 1, d]])
  * Bivariate-bicycle qLDPC [[144, 18, 12]] (Cain–Xu et al. 2026
    space-efficient memory code variant)

  Each code carries `(n, k, d)`; concrete parity matrices `hx`,
  `hz` are filled in per-submission (`steane_713_parity` below
  for the demonstrative Steane case).

  ## L4 → L3 contract: implementer-supplied, not framework-derived

  Per John's directive (2026-05-25): the cycle-level logical
  error rate is an INPUT to the framework, justified by the
  implementer through their lower-level code analysis (Monte
  Carlo, analytic ansatz, decoder model, etc.).  The framework
  does NOT compute it from `p_g` and `d`; that would presuppose
  a specific code family + subthreshold formula, which is the
  implementer's responsibility.

  Concretely: the implementer supplies `HardwareErrorParams`
  with per-syscall error rates already computed; the framework
  composes them via union bound.

  No Mathlib dependency; pure Nat for `decide`.
-/

import FormalRV.Framework.L4_QECCode
import FormalRV.System.HardwareErrorParams

namespace FormalRV.Framework

/-! ## Concrete QEC code instances -/

/-- Steane [[7, 1, 3]] code.  CSS, distance 3, 7 physical qubits
    per logical.  Smallest demonstrative QEC code. -/
def steane_713 : QECCode :=
  { n := 7, k := 1, d := 3, hx := [], hz := [] }

/-- Surface code distance 3, [[9, 1, 3]] (non-rotated). -/
def surface_d3 : QECCode :=
  { n := 9, k := 1, d := 3, hx := [], hz := [] }

/-- Surface code distance 5, [[25, 1, 5]]. -/
def surface_d5 : QECCode :=
  { n := 25, k := 1, d := 5, hx := [], hz := [] }

/-- Surface code distance 7, [[49, 1, 7]]. -/
def surface_d7 : QECCode :=
  { n := 49, k := 1, d := 7, hx := [], hz := [] }

/-- Surface code distance 11, [[121, 1, 11]].
    Typical Gidney-Ekerå 2021 / Gidney 2025 working distance for
    RSA-2048 surface-code resource estimates. -/
def surface_d11 : QECCode :=
  { n := 121, k := 1, d := 11, hx := [], hz := [] }

/-- Surface code distance 25, [[625, 1, 25]].
    Hot-storage distance for Gidney 2025 yoked-surface architecture. -/
def surface_d25 : QECCode :=
  { n := 625, k := 1, d := 25, hx := [], hz := [] }

/-- Cain–Xu et al. 2026 space-efficient lifted-product
    `[[2610, 744, ≤ 16]]` qLDPC code.  Used in qianxu's RSA-2048
    estimate; encodes many logical qubits per code block.

    For per-logical analysis we use the per-logical
    perspective: each logical qubit costs `n / k ≈ 3.5` physical
    qubits on this code, much smaller than surface code.  Here
    we provide the [[144, 18, 12]] bivariate-bicycle variant
    (smaller demonstrative instance from Bravyi et al. 2024). -/
def lp_144_18_12 : QECCode :=
  { n := 144, k := 18, d := 12, hx := [], hz := [] }

/-! ## Steane [[7, 1, 3]] parity matrices (concrete)

    The standard Steane code parity-check matrices.  Both `Hx`
    and `Hz` equal the [7, 4] Hamming-code parity check.  Three
    stabilizer generators each, weight-4 each. -/

/-- Steane [[7, 1, 3]] code WITH concrete parity matrices.
    Used for the demonstrative Cuccaro-on-Steane submission. -/
def steane_713_with_parity : QECCode :=
  { n := 7, k := 1, d := 3
  , hx := [ [false, false, false, true,  true,  true,  true ]
          , [false, true,  true,  false, false, true,  true ]
          , [true,  false, true,  false, true,  false, true ] ]
  , hz := [ [false, false, false, true,  true,  true,  true ]
          , [false, true,  true,  false, false, true,  true ]
          , [true,  false, true,  false, true,  false, true ] ] }

end FormalRV.Framework
