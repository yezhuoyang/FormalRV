/-
  FormalRV.Framework.HardwareErrorParams — implementer-side
  error-rate inputs.

  These numbers are the implementer's hardware-and-compilation
  characterization, expressed in parts-per-million (ppm) for
  decidability.  Each field is what the L3 → L2 / L4 → L3 inter-
  layer contracts produce when given a specific QEC code, gate
  error rate, and PPM gadget set.  The implementer JUSTIFIES
  each number by citing the contract and the underlying
  paper/derivation; the framework just consumes the numbers and
  composes them via union bound.

  ## Why these fields specifically

  The framework's coarse PPM compilation produces SysCalls of
  four kinds: PPM-like (Pauli-product measurement),
  magicReq (magic-state injection: T or CCZ), route (atom
  transport), and feedback (classical decoder reaction).  Each
  contributes a different error.  The fields below capture the
  per-syscall logical-error contribution in ppm.

  ## Conservatism

  Each field is a **maximum** — the implementer should report
  the upper bound on the error contribution from the worst-case
  instance of that syscall kind.  The framework then sums via
  union bound; the result is a conservative over-estimate of
  the total logical error budget.

  No Mathlib dependency.  All-Nat for `decide`.
-/

namespace FormalRV.Framework

/-- The per-SysCall error-rate inputs the implementer supplies.

    Each field has units of parts-per-million (ppm) of the final
    output state's logical-error contribution.  E.g.,
    `ppm_op_error_ppm = 100` means each PPM operation contributes
    at most 100 ppm = 1e-4 to the union-bound error budget. -/
structure HardwareErrorParams where
  /-- Per-PPM logical error in ppm.  From the L3 → L2 contract:
      `per_op_error ≤ c_cycle · cycle_logical_error_rate`, with the
      cycle count `c_cycle` reflecting the PPM gadget's duration
      and the cycle-level logical error from the L4 code. -/
  ppm_op_error_ppm : Nat
  /-- Per-T-state magic-state infidelity in ppm.  From the L3
      magic factory's cultivation + 15-to-1 distillation output. -/
  magic_t_error_ppm : Nat
  /-- Per-CCZ-state magic-state infidelity in ppm.  From the L3
      magic factory's 8T-to-CCZ stage output. -/
  magic_ccz_error_ppm : Nat
  /-- Per-route atom-transport logical error in ppm.  Reflects
      the per-cycle idling error during atom movement, integrated
      over the route's duration. -/
  transit_error_ppm : Nat
  /-- Per-feedback classical-reaction error in ppm.  Typically
      zero (feedback is classical bookkeeping), but the
      framework includes the slot for completeness. -/
  feedback_error_ppm : Nat
  deriving Repr, Inhabited

namespace HardwareErrorParams

/-- A "qianxu-class" default: gate error 1e-3, T-state infidelity
    1e-6 from 15-to-1, CCZ infidelity 1e-6 from 8T-to-CCZ, transit
    idling ~10 ppm per route.  These are illustrative defaults
    only; real submissions must cite specific contracts. -/
def qianxu_class : HardwareErrorParams :=
  { ppm_op_error_ppm    := 100      -- ~1e-4 per PPM
  , magic_t_error_ppm   := 1        -- ~1e-6 per T after distillation
  , magic_ccz_error_ppm := 2        -- ~2e-6 per CCZ
  , transit_error_ppm   := 10       -- ~1e-5 per route
  , feedback_error_ppm  := 0
  }

end HardwareErrorParams

end FormalRV.Framework
