# FormalRV.Qualtran

A thin **data bridge** mirroring [Qualtran](https://github.com/quantumlib/Qualtran)
(Google Quantum AI) Python types into Lean. Qualtran supplies engineering-layer
scaffolding for L2 logical gadgets and a Beverland-style surface-code physical
cost model; this folder lets Phase-C corpus-paper instantiation name those
objects natively in Lean. Note: Qualtran has **no qLDPC support**, so FormalRV's
L4 qLDPC content is novel and lives elsewhere.

## Layout
- `Bridge.lean` — the entire folder: Python→Lean shim structures + canonical
  parameter presets + smoke checks. No sub-folders or split files.

## Key definitions
- `QualtranPhysicalParameters` (`Bridge.lean`) — Lean mirror of Qualtran's
  `@frozen PhysicalParameters`; floats are Nat-encoded (`physical_error_thousandths`
  in 1/1000 units, `cycle_time_us_tenths` in 1/10 μs).
- `default_params` (`Bridge.lean`) — Qualtran source defaults (1e-3, 1.0 μs).
- `beverland_superconducting_realistic` (`Bridge.lean`) — Beverland-et-al model;
  cycle time 0.4 μs (`tenths = 4`) from `4·50 + 2·100 = 400 ns`.
- `gidney_fowler_realistic` (`Bridge.lean`) — Gidney–Fowler model (1e-3, 1.0 μs).
- `QualtranBloqSignature` (`Bridge.lean`) — a bloq name + the T-count Qualtran's
  compiler attributes to it, for cross-checking Lean-derived counts in Phase C.

## Key theorems
- `default_params.physical_error_thousandths = 1` (`Bridge.lean`) — default preset
  is callable and carries the documented value — **Arithmetic-only** (`rfl`).
- `beverland_superconducting_realistic.cycle_time_us_tenths = 4` (`Bridge.lean`) —
  Beverland cycle time matches the `4·50 + 2·100 = 400 ns` formula — **Arithmetic-only** (`rfl`).
- `gidney_fowler_realistic.cycle_time_us_tenths = 10` (`Bridge.lean`) — Gidney–Fowler
  preset carries the documented 1.0 μs cycle time — **Arithmetic-only** (`rfl`).

## Status
This is a **data-shim layer only**: it transcribes Qualtran's `PhysicalParameters`
and bloq-signature shapes into Nat-encoded Lean records. There is no semantic
theorem here — the three `example`s are `rfl`-level smoke checks. Float fields are
Nat-approximated pending a later refinement to mathlib `Real`.
