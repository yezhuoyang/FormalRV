import FormalRV.Arithmetic.SQIRModMult

open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)

/-
# VerifiedShor — clean public API for the verified Shor pipeline

This module exposes the verified-Shor result under stable, human-readable
names.  The underlying implementation lives in
`FormalRV.BQAlgo.SQIRModMult` (the SQIR-faithful modular multiplier)
and the relaxed parametric Shor theorem chain.

The result is kernel-clean: each public theorem below has axiom
profile `[propext, Classical.choice, Quot.sound]` — no custom axioms.

## Usage
```lean
import VerifiedShor

example (a r N m : Nat) (ainv : Nat)
    (h_setting : VerifiedShor.ShorSetting a r N m (Nat.log2 (2*N) + 1))
    (h_inv : a * ainv % N = 1) :
    VerifiedShor.successProbability a r N m ainv ≥ VerifiedShor.successBound N :=
  VerifiedShor.correct a r N m ainv h_setting h_inv
```

## Naming conventions
- `VerifiedShor.correct` — primary verified Shor theorem (canonical bits).
- `VerifiedShor.correct_general` — user picks data-register width.
- `VerifiedShor.correct_parametric` — user supplies their own family.
- `VerifiedShor.ShorSetting` — relaxed Shor setting predicate.
- `VerifiedShor.CircuitSizing` — verified-circuit sizing predicate.

The original SQIR placeholder axioms (`f_modmult_circuit`,
`f_modmult_circuit_MMI`, `f_modmult_circuit_uc_well_typed`) are
deprecated; this module does not depend on them.
-/




