/-
  FormalRV.BQAlgo.WindowedShorConnection — wiring the
  windowed-arithmetic modular multiplier up to the HEADLINE
  Shor success-probability theorem.

  ## What this file proves (honest scope — UPDATED: the chain is CLOSED)

  This file defines THE multiplier interface and connects it — and the
  windowed multiplier — all the way to the Shor success bound, kernel-clean:

    * `EncodeRoundTripModMul N bits anc` — THE pluggable multiplier
      interface: a gate family that, per multiplier constant `c`,
      round-trips the canonical `encodeDataZeroAnc` layout
      (`x ↦ (c*x) % N`) and is well-typed.  The `roundTrip` field
      carries an INVERTIBILITY GUARD (`∃ d, c*d % N = 1`) — a
      soundness necessity, not a weakening: well-typed gates are
      injective on basis states, while `x ↦ (c*x) % N` is
      non-injective for non-invertible `c` (the unguarded version is
      provably uninhabitable).  Shor only ever instantiates
      `c := a^(2^i)` with invertible `a`, where the guard is free.
    * `EncodeRoundTripModMul.toVerifiedModMulFamily` /
      `shor_correct_of_encodeRoundTrip` — ANY instance yields the
      framework's `VerifiedModMulFamily` and the HEADLINE bound
      `≥ κ / (log₂ N)^4`, via the matrix-level MCP bridge.
      Every layer above the round-trip is reusable.
    * **The windowed path is CONNECTED** (§5b–§9 below):
      `windowedInplaceModMulGate` (forward load+selected-add ; SWAP ;
      inverse-clear ; unload) round-trips `encodeDataZeroAnc`
      unconditionally, giving `windowedModMulFamily` and the
      UNCONDITIONAL `windowed_shor_correct`.
    * Sibling instances for the two ripple-adder multipliers
      (`cuccaroMultiplier`, `gidneyMultiplier`) live in
      `Shor/MultiplierInstances.lean` — three independent multiplier
      routes to the same Shor bound, all through this one interface.

  ## What remains (honest residuals)

    * `WindowedCompletion` (§5) is an ALTERNATIVE completion-style
      route kept for its interface value; its `roundTrip` carries the
      same invertibility guard.  The live windowed route (§5b–§9)
      does not go through it.
    * The count-optimal babbush EGate mod-exp (`Shor/WindowedComposed`)
      still rides a different circuit variant than the semantics
      apex here; unifying them is the named
      `BabbushLookupAddValueSpec` obligation.

  ## Honesty tier (per CLAUDE.md)

  All reduction and connection theorems below are **Verified**
  (semantic, not arithmetic-only) and kernel-clean
  (`[propext, Classical.choice, Quot.sound]`).
-/

-- Re-export shim: split into WindowedShorConnection/ submodules (same namespace); importers unchanged.
import FormalRV.Shor.WindowedShorConnection.Obligation
import FormalRV.Shor.WindowedShorConnection.ForwardGate
import FormalRV.Shor.WindowedShorConnection.Residual
import FormalRV.Shor.WindowedShorConnection.SwapAtoms
import FormalRV.Shor.WindowedShorConnection.SwapCascade
import FormalRV.Shor.WindowedShorConnection.Parity
import FormalRV.Shor.WindowedShorConnection.Multiplier
import FormalRV.Shor.WindowedShorConnection.Headline
