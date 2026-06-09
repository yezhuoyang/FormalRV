import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.ShorSuccessProbabilityTheorems
import FormalRV.Shor.VerifiedShor.VerifiedShorTheorem

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


/-! ## Verified Shor success-probability theorems -/

/-- **PRIMARY verified Shor theorem** (canonical bits).  Kernel-clean:
axioms = `[propext, Classical.choice, Quot.sound]`. -/
theorem correct
    (a r N m ainv : Nat)
    (h_setting : ShorSetting a r N m (canonicalBits N))
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m (canonicalBits N)
      (FormalRV.BQAlgo.sqir_modmult_rev_anc (canonicalBits N))
      (FormalRV.BQAlgo.f_modmult_circuit_verified_bits a ainv N (canonicalBits N))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  FormalRV.BQAlgo.Shor_correct_with_sqir_verified_modmult_canonical_bits
    a r N m ainv h_setting h_inv

/-- **General verified Shor theorem** — user picks the data-register
width `bits` and supplies `CircuitSizing N bits`.

**Note**: definitionally identical to `correct_general_via_interface`
applied with the canonical SQIR/Cuccaro instance — they both reduce
to `Shor_correct_with_sqir_verified_modmult_usable`.  Prefer
`correct_general_via_interface` when prototyping with a different
modular-multiplier implementation. -/
theorem correct_general
    (a r N m bits ainv : Nat)
    (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
      (FormalRV.BQAlgo.sqir_modmult_rev_anc bits)
      (FormalRV.BQAlgo.f_modmult_circuit_verified_bits a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  FormalRV.BQAlgo.Shor_correct_with_sqir_verified_modmult_usable
    a r N m bits ainv h_setting h_sizing h_inv

/-- **Parametric verified Shor theorem** — user supplies their own
oracle family `u` along with `ModMulImpl` and `uc_well_typed` proofs. -/
theorem correct_parametric
    (a r N m n anc : Nat) (u : Nat → FormalRV.SQIRPort.BaseUCom (n + anc))
    (h_setting : ShorSetting a r N m n)
    (h_modmul : FormalRV.SQIRPort.ModMulImpl a N n anc u)
    (h_wt : ∀ i, i < m → FormalRV.SQIRPort.uc_well_typed (u i)) :
    FormalRV.SQIRPort.probability_of_success a r N m n anc u
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  FormalRV.BQAlgo.Shor_correct_var_relaxed a r N m n anc u h_setting h_modmul h_wt

/-! ## Framework interface: pluggable verified modular multipliers

`VerifiedModMulFamily` is the first reusable framework contract.  Any
future verified modular-multiplier implementation (Cuccaro/SQIR,
Gidney, QFT-based, lookup-table-windowed, measurement-and-reuse,
etc.) should expose itself as a `VerifiedModMulFamily`.

The Shor success-probability theorem `VerifiedModMulFamily.shorCorrect`
depends ONLY on the contract — not on any particular implementation —
so swapping implementations is a one-line change at the application
site.

### To add a new multiplier
1. Pick concrete `(a N bits anc)` parameters (or generalize over them).
2. Construct a term of type `VerifiedModMulFamily a N bits anc`,
   providing `family`, `mmi`, and `wellTyped`.
3. Apply `VerifiedModMulFamily.shorCorrect` to get the Shor bound.

### To use a different ancilla count
The structure carries `anc` as a type parameter, so implementations
with different ancilla budgets are different types.  The Shor wrapper
is `anc`-generic.

### Future implementation targets
- Gidney AND-based modular multiplier.
- Windowed lookup-table multiplier (will require a small extension
  of the contract: a sum-of-window-contributions correctness lemma).
- Measurement-and-reuse multiplier (will require a future
  `CircuitBackend` abstraction; the `family` field's `BaseUCom` type
  is the current backend signature). -/

/-- **`VerifiedModMulFamily a N bits anc`** — the reusable framework
contract for a verified modular-multiplier oracle family.  Any
implementation that produces this structure can plug directly into
`shorCorrect`. -/
structure VerifiedModMulFamily (a N bits anc : Nat) where
  /-- The QPE-iterate-indexed oracle family. -/
  family : Nat → FormalRV.SQIRPort.BaseUCom (bits + anc)
  /-- `ModMulImpl` contract: each iterate `i` realises multiplication
  by `a^(2^i) mod N`. -/
  mmi : FormalRV.SQIRPort.ModMulImpl a N bits anc family
  /-- Every iterate is well-typed at total dimension `bits + anc`. -/
  wellTyped : ∀ i, FormalRV.SQIRPort.uc_well_typed (family i)

end VerifiedShor
