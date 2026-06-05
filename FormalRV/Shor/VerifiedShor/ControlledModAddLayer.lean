import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.SqirModMulFamilyInstance

namespace VerifiedShor
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


/-- **SQIR/Cuccaro instance of the verified-multiplier contract.**  The
existing `ModMul.circuitFamily` (= `f_modmult_circuit_verified_bits`)
fits the generic `VerifiedModMulFamily` interface.  Any other
verified implementation (Gidney, windowed lookup, etc.) would expose
itself as a different `def` returning `VerifiedModMulFamily ...`. -/
noncomputable def verifiedSqirModMulFamily
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    VerifiedModMulFamily a N bits (ModMul.ancillaWidth bits) where
  family := ModMul.circuitFamily a ainv N bits
  mmi := ModMul.circuitFamily_modMulImpl a ainv N bits
      h_sizing.1 h_N_ge_2 h_sizing.2.1 h_sizing.2.2 h_inv
  wellTyped := ModMul.circuitFamily_wellTyped a ainv N bits
      h_sizing.1 (by omega) h_sizing.2.1 h_sizing.2.2

/-- **`correct_general` via the interface.**  Shows that the existing
`correct_general` theorem factors through `VerifiedModMulFamily` —
constructing the SQIR instance and applying the generic
`shorCorrect`.  Use this when prototyping with a different multiplier
implementation: replace `verifiedSqirModMulFamily` with your own
`VerifiedModMulFamily` instance. -/
theorem correct_general_via_interface
    (a r N m bits ainv : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (ModMul.ancillaWidth bits)
      (ModMul.circuitFamily a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 := by
  have h_a_pos : 0 < a := h_setting.1.1
  have h_a_lt : a < N := h_setting.1.2
  have h_N_pos : 0 < N := Nat.lt_of_lt_of_le h_a_pos (Nat.le_of_lt h_a_lt)
  have h_N_ge_2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h_lt | h_ge
    · exfalso
      have hN_eq : N = 1 := by omega
      rw [hN_eq, Nat.mod_one] at h_inv
      exact absurd h_inv (by decide)
    · exact h_ge
  exact (verifiedSqirModMulFamily a ainv N bits h_sizing h_N_ge_2 h_inv).shorCorrect
    r m h_setting

/-! ## Controlled modular addition layer (Phase R4b)

`VerifiedShor.ControlledModAdd` is the **first reusable contract**
below `VerifiedModMulFamily`.  It exposes the controlled-modular-add
primitive that the multiplier proof chain currently consumes via
`sqir_style_controlledModAddConst_gate_clean`.

### Scope (R4b)
This phase ONLY makes the contract visible.  The existing multiplier
proof chain (`sqir_modmult_step_target_decode`,
`sqir_modmult_inplace_candidate_state_eq`, etc.) still uses the
SQIR-specific theorem directly.  A future tick (R4c) will refactor
the multiplier proof to consume `ControlledModAddImpl` instead.

### Design choice
The `R4b` interface is **Cuccaro-layout-specific**: it exposes the
existing `cuccaro_target_val` / `cuccaro_read_val` decoders and the
hard-coded positions `1` (flag) / `2 + 2*bits` (top carry).
Layout-agnosticism is reserved for a future `RegisterLayout`
abstraction (Phase R5/R6).

### For contributors
**To add a new controlled modular adder** (e.g. a Gidney-AND-based,
QFT-adder-based, or windowed lookup-table variant):
1. Implement the gate construction returning a `Gate`.
2. Prove the 6-conjunct `clean` bundle: well-typed + target decode +
   read-zero + top-carry-false + flag-false + control-preserved.
3. Package as a term of type `ControlledModAddImpl`.

Once the multiplier-proof chain is refactored (R4c), any such instance
will plug into `VerifiedModMulFamily.shorCorrect` without additional
proofs.

### What this interface does NOT support
- **Different register layouts**: the decoders are Cuccaro-fixed in
  R4b.  Use `RegisterLayout` (future R5/R6) for variants like reverse
  bit-order or QFT-encoded targets.
- **Measurement and qubit reuse**: the `gate` field returns a `Gate`
  (deterministic, reversible).  Measurement-based adder variants
  (e.g. Gidney's measurement-AND uncompute) require a future
  `CircuitBackend` abstraction or must be compiled away upstream.

### Layer position
```
VerifiedModMulFamily       (the Shor-level contract, Phase R3)
  └── ControlledModAddImpl (this layer, Phase R4b)
      └── (future) ModAddImpl   (Phase R5)
          └── (future) AddConstImpl  (Phase R5)
              └── (future) RegisterLayout / CircuitBackend (R6/R7)
``` -/

end VerifiedShor
