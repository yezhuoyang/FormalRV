/-
  FormalRV.Qualtran.Bridge — Python→Lean shim for Qualtran.

  Phase A.6 of the paper plan (`PAPER_PLAN.md`). Qualtran provides
  engineering-layer scaffolding for L2 logical gadgets (arithmetic,
  RSA phase estimation) and a Beverland-style surface-code physical
  cost model.  Qualtran has NO qLDPC support (verified across the
  Qualtran source tree, `notes/qualtran-2024.md`); the L4 qLDPC
  content of our framework is novel.

  This file is the bridge: Lean shim structures mirroring Qualtran
  Python types so corpus-paper instantiation (Phase C) can name
  Qualtran objects without round-tripping through Python.

  Mirrors `Qualtran/qualtran/surface_code/physical_parameters.py`
  (read 2026-05-15 13:44).  The Qualtran `@frozen class
  PhysicalParameters` carries:

      physical_error : float = 1e-3          -- two-qubit physical err rate
      cycle_time_us  : float = 1.0           -- error-correction cycle time

  with named factory methods `make_beverland_et_al` and
  `make_gidney_fowler` for the two canonical superconducting models.
  Float is unavailable Nat-domain; we encode `physical_error` in 1/1000
  units and `cycle_time_us` in 1/10 μs units.  A later tick can refine
  to mathlib `Real` once needed.
-/

namespace FormalRV.Qualtran

/-- Lean mirror of Qualtran's `PhysicalParameters` (surface-code
physical cost model). `physical_error_thousandths` is the two-qubit
physical-error rate in 1/1000 units (default 1 ↔ 1e-3); `cycle_time_us_tenths`
is the error-correction cycle time in 1/10 μs units (default 10 ↔ 1.0 μs). -/
structure QualtranPhysicalParameters where
  /-- Two-qubit physical-error rate × 1000 (1 ↔ 1e-3). -/
  physical_error_thousandths : Nat
  /-- Error-correction cycle time × 10, in μs. -/
  cycle_time_us_tenths : Nat
  deriving Inhabited

/-- Default per Qualtran source (`physical_error=1e-3, cycle_time_us=1.0`). -/
def default_params : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1
    cycle_time_us_tenths := 10 }

/-- Beverland-et-al superconducting realistic model
(`t_gate_ns = 50, t_meas_ns = 100`, so `cycle_time_ns = 4·50 + 2·100 = 400`
i.e. `0.4 μs ↔ tenths = 4`). -/
def beverland_superconducting_realistic : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1
    cycle_time_us_tenths := 4 }

/-- Gidney–Fowler superconducting realistic model
(`physical_error = 1e-3`, `cycle_time_us = 1.0`). -/
def gidney_fowler_realistic : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1
    cycle_time_us_tenths := 10 }

/-- Lean mirror of a Qualtran bloq signature: the name + the
T-count Qualtran's compiler attributes to the bloq.  Used to
cross-check Lean-derived counts against Qualtran's numbers in
Phase C. -/
structure QualtranBloqSignature where
  name : String
  t_count : Nat
  deriving Inhabited

/-- Smoke checks: each `def` is callable and the Beverland cycle time
matches the formula `4·50 + 2·100 = 400 ns`. -/
example : default_params.physical_error_thousandths = 1 := by rfl
example : beverland_superconducting_realistic.cycle_time_us_tenths = 4 := by rfl
example : gidney_fowler_realistic.cycle_time_us_tenths = 10 := by rfl

end FormalRV.Qualtran
