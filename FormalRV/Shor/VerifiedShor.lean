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

import FormalRV.Arithmetic.SQIRModMult

namespace VerifiedShor

/-! ## Public predicates -/

/-- **Shor setting** for verified Shor (relaxed — no upper register
bound on `n`).  Mathematical content matches `BasicSettingRelaxed`
but the name is the public stable alias. -/
abbrev ShorSetting := FormalRV.BQAlgo.BasicSettingRelaxed

/-- **Verified-circuit sizing**: data register has at least 1 bit, holds
`N`, and is wide enough for `2*N`.  Public stable alias for
`VerifiedCircuitSizing`. -/
abbrev CircuitSizing := FormalRV.BQAlgo.VerifiedCircuitSizing

namespace ShorSetting

/-- `BasicSetting → ShorSetting` (drops the upper bound conjunct).
Public alias for `BasicSettingRelaxed_of_BasicSetting`. -/
theorem ofBasicSetting {a r N m n : Nat}
    (h : FormalRV.SQIRPort.BasicSetting a r N m n) :
    ShorSetting a r N m n :=
  FormalRV.BQAlgo.BasicSettingRelaxed_of_BasicSetting h

/-- `0 < a`. -/
theorem a_pos {a r N m n : Nat} (h : ShorSetting a r N m n) : 0 < a :=
  FormalRV.BQAlgo.BasicSettingRelaxed_a_pos h

/-- `a < N`. -/
theorem a_lt {a r N m n : Nat} (h : ShorSetting a r N m n) : a < N :=
  FormalRV.BQAlgo.BasicSettingRelaxed_a_lt h

/-- The order witness. -/
theorem order {a r N m n : Nat} (h : ShorSetting a r N m n) :
    FormalRV.SQIRPort.Order a r N :=
  FormalRV.BQAlgo.BasicSettingRelaxed_order h

/-- `N^2 < 2^m` (QPE precision lower bound). -/
theorem Nsq_lt {a r N m n : Nat} (h : ShorSetting a r N m n) : N^2 < 2^m :=
  FormalRV.BQAlgo.BasicSettingRelaxed_Nsq_lt h

/-- `2^m ≤ 2 * N^2` (QPE precision upper bound). -/
theorem pow_le_two_Nsq {a r N m n : Nat} (h : ShorSetting a r N m n) :
    2^m ≤ 2 * N^2 :=
  FormalRV.BQAlgo.BasicSettingRelaxed_pow_le_2Nsq h

/-- `N < 2^n`. -/
theorem N_lt_pow_n {a r N m n : Nat} (h : ShorSetting a r N m n) : N < 2^n :=
  FormalRV.BQAlgo.BasicSettingRelaxed_N_lt_pow_n h

/-- `N ≤ 2^n`. -/
theorem N_le_pow_n {a r N m n : Nat} (h : ShorSetting a r N m n) : N ≤ 2^n :=
  FormalRV.BQAlgo.BasicSettingRelaxed_N_le_pow_n h

/-- `0 < N`. -/
theorem N_pos {a r N m n : Nat} (h : ShorSetting a r N m n) : 0 < N :=
  FormalRV.BQAlgo.BasicSettingRelaxed_N_pos h

end ShorSetting

namespace CircuitSizing

/-- **Canonical sizing**: `CircuitSizing N (Nat.log2 (2*N) + 1)` holds
whenever `0 < N`.  Public alias for
`VerifiedCircuitSizing_canonical_pow2_succ`. -/
theorem canonical (N : Nat) (hN : 0 < N) :
    CircuitSizing N (Nat.log2 (2 * N) + 1) :=
  FormalRV.BQAlgo.VerifiedCircuitSizing_canonical_pow2_succ N hN

end CircuitSizing

/-! ## Canonical bit width and sizing discharge -/

/-- **Canonical bit width** for the verified modular multiplier:
`Nat.log2 (2 * N) + 1`.  Always satisfies `CircuitSizing N _`. -/
def canonicalBits (N : Nat) : Nat := Nat.log2 (2 * N) + 1

/-- **Canonical sizing is always satisfiable** for `0 < N`. -/
theorem circuitSizing_canonical (N : Nat) (hN : 0 < N) :
    CircuitSizing N (canonicalBits N) :=
  CircuitSizing.canonical N hN

/-! ## Verified modular multiplication layer -/

namespace ModMul

open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)

/-- **Ancilla width** for the verified modular multiplier at width
`bits` (currently `3*bits + 11` per the SQIR-faithful layout). -/
def ancillaWidth (bits : Nat) : Nat := sqir_modmult_rev_anc bits

/-- **Total dimension** of the verified modular multiplier:
`bits + ancillaWidth bits`. -/
def totalDim (bits : Nat) : Nat := sqir_total_dim bits

/-- **Verified modular multiplication gate** in the `encodeDataZeroAnc`
/ `MultiplyCircuitProperty` layout.  Three-stage composition:
data-register adapter → in-place modular multiplier → adapter. -/
def gateMCP (bits N a ainv : Nat) : Gate :=
  sqir_modmult_MCP_gate bits N a ainv

/-- **Apply correctness in the encoded layout.**  Maps
`encodeDataZeroAnc bits anc x` to
`encodeDataZeroAnc bits anc ((a*x) % N)`. -/
theorem gateMCP_apply_encode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (gateMCP bits N a ainv)
        (encodeDataZeroAnc bits (ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ancillaWidth bits) ((a * x) % N) :=
  sqir_modmult_MCP_gate_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

/-- **Gate is well-typed at `totalDim bits`.** -/
theorem gateMCP_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (totalDim bits) (gateMCP bits N a ainv) :=
  sqir_modmult_MCP_gate_wellTyped bits N a ainv hbits hN_pos hN hN2

/-- **Main bridge theorem**: the verified gate, compiled to a `BaseUCom`,
satisfies SQIR's `MultiplyCircuitProperty` — the spec consumed by
`ModMulImpl` and downstream Shor correctness. -/
theorem satisfiesMultiplyCircuitProperty
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    MultiplyCircuitProperty a N bits (ancillaWidth bits)
      (Gate.toUCom (totalDim bits) (gateMCP bits N a ainv)) :=
  sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty
    bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

/-- **Per-QPE-iteration modular multiplication family**:
`circuitFamily a ainv N bits i` is the compiled `BaseUCom` for
multiplication by `a^(2^i) mod N` at the verified bit width. -/
noncomputable def circuitFamily (a ainv N bits : Nat) :
    Nat → BaseUCom (bits + ancillaWidth bits) :=
  f_modmult_circuit_verified_bits a ainv N bits

/-- **Verified `ModMulImpl` instance** for the family — the precise
SQIR interface that `Shor_correct_var` (and `VerifiedShor.correct*`)
consume. -/
theorem circuitFamily_modMulImpl
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    ModMulImpl a N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits) :=
  f_modmult_circuit_verified_bits_MMI a ainv N bits hbits hN_ge_2 hN hN2 h_inv

/-- **Per-iterate `MultiplyCircuitProperty`**: iterate `i` of the
family is a verified `a^(2^i) mod N` multiplier.  Follows from
`circuitFamily_modMulImpl`. -/
theorem circuitFamily_perIterate
    (a ainv N bits i : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_inv : a * ainv % N = 1) :
    MultiplyCircuitProperty (a^(2^i)) N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits i) :=
  circuitFamily_modMulImpl a ainv N bits hbits hN_ge_2 hN hN2 h_inv i

/-- **Every iterate is well-typed** at the family's total dimension. -/
theorem circuitFamily_wellTyped
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    ∀ i, uc_well_typed (circuitFamily a ainv N bits i) :=
  f_modmult_circuit_verified_bits_uc_well_typed a ainv N bits hbits hN_pos hN hN2

end ModMul

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

namespace VerifiedModMulFamily

/-- **Shor success-probability bound — generic over any verified
multiplier family.**  This is the application-facing theorem: pick
any `F : VerifiedModMulFamily a N bits anc` and a relaxed Shor
setting, and the bound follows. -/
theorem shorCorrect
    {a N bits anc : Nat} (F : VerifiedModMulFamily a N bits anc)
    (r m : Nat) (h_setting : ShorSetting a r N m bits) :
    FormalRV.SQIRPort.probability_of_success a r N m bits anc F.family
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  correct_parametric a r N m bits anc F.family h_setting F.mmi
    (fun i _ => F.wellTyped i)

end VerifiedModMulFamily

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

namespace ControlledModAdd

open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)

/-! ### Level-1 register layout (Phase R5b)

`ControlledModAddLayout` is the **Level-1** layout abstraction:
the minimal set of layout facts that the `ControlledModAddImpl`
contract (R4b) actually mentions.  It abstracts away the
Cuccaro-specific names (`cuccaro_input_F`, `cuccaro_target_val`,
`cuccaro_read_val`, `flagPos = 1`, `topCarryPos = 2 + 2*bits`, …)
so that `ControlledModAddImpl` can be stated without them.

**Scope (Level 1 only)**: this struct only carries facts needed to
state and prove **controlled-modular-add correctness**.  It does
NOT abstract:
* The multiplier register layout (`sqir_mult_control_idx`,
  `sqir_mult_input_F`, install machinery) — that is Level 2
  `MultiplierStepLayout`, reserved for R5c.
* The Shor/MCP adapter layout (`encodeDataZeroAnc`,
  `sqir_encode_to_mult_adapter`, `Gate.shift`) — that is Level 3
  `MCPAdapterLayout`, reserved for R5d.

**Fields are functions of `bits`**, not constants, so different
adders may pick layouts that scale differently with width.

**No semantic laws are bundled in the struct** (e.g. "decoder ∘
encoder = identity", "workspaceUpperBound ≤ ancillaWidth").
Such laws are not currently required by the R4b contract, and
adding them now would force every layout-instance to discharge
them up front.  If a future R5b' tick discovers that a particular
projection alias needs a law, we add it then. -/
structure ControlledModAddLayout where
  /-- Ancilla width as a function of data-register width `bits`. -/
  ancillaWidth        : Nat → Nat
  /-- Position of the dirty flag bit in the layout. -/
  flagPos             : Nat → Nat
  /-- Position of the top-carry bit in the layout. -/
  topCarryPos         : Nat → Nat
  /-- Exclusive upper bound of the in-block workspace (`controlIdx`
  must live below or above this). -/
  workspaceUpperBound : Nat → Nat
  /-- Input encoder: given width `bits` and an `acc : Nat`, produces
  the Boolean state-function representing the input register. -/
  inputEncode         : (bits acc : Nat) → Nat → Bool
  /-- Target-register decoder. -/
  targetDecode        : (bits : Nat) → (Nat → Bool) → Nat
  /-- Read/workspace-register decoder. -/
  readDecode          : (bits : Nat) → (Nat → Bool) → Nat
  /-- Predicate stating "the supplied control index is outside the
  in-block workspace" — i.e. it lives in the input-flag region or
  above the workspace cassette. -/
  controlAllowed      : Nat → Nat → Prop

/-- **`ControlledModAddImpl`** — the first reusable contract below
`VerifiedModMulFamily`.

R5b refactor: the layout-specific names (`cuccaro_target_val`,
`cuccaro_read_val`, `cuccaro_input_F`, hard-coded positions 1 and
`2 + 2*bits`, etc.) are now **factored out** into a `layout :
ControlledModAddLayout` field.  Every reference in the `clean`
bundle goes through the layout.

Specifically:

* `layout : ControlledModAddLayout` — the layout abstraction (R5b).
* `gate bits N c controlIdx` is the Lean `Gate` IR term implementing
  `if control bit at controlIdx then x ↦ (x + c) % N else x ↦ x`.
* `clean` is the **6-conjunct cleanliness bundle**, now stated in
  terms of `layout.*` projections:
  1. The gate is well-typed at the declared `layout.ancillaWidth bits`.
  2. `layout.targetDecode bits` of the output equals `(x + c) % N`
     if `control = true` else `x`.
  3. `layout.readDecode bits` of the output equals `0`.
  4. The top-carry bit (position `layout.topCarryPos bits`) is `false`.
  5. The flag bit (position `layout.flagPos bits`) is `false`.
  6. The control bit at `controlIdx` is preserved.

### Side conditions consumed by `clean`
* `1 ≤ bits`, `0 < N`, `N ≤ 2^bits`, `2 * N ≤ 2^bits`: sizing.
* `c < N`, `x < N`: the constant and the live data live in `[0, N)`.
* `layout.controlAllowed bits controlIdx`: the control wire is outside
  the in-block workspace.
* `controlIdx ≠ layout.flagPos bits`: the control wire is not the
  flag bit.
* `controlIdx < layout.ancillaWidth bits`: the control wire is within
  the declared workspace.

### Layout coupling
The R5b layout is still **Level 1 only**.  Multiplier-step layout
(`MultiplierStepLayout`) and Shor/MCP adapter layout
(`MCPAdapterLayout`) are reserved for R5c and R5d respectively. -/
structure ControlledModAddImpl where
  /-- The Level-1 register layout this implementation uses. -/
  layout : ControlledModAddLayout
  /-- The controlled mod-add gate constructor. -/
  gate   : (bits N c controlIdx : Nat) → Gate
  /-- The 6-conjunct cleanliness bundle, stated through the layout. -/
  clean  : ∀ (bits N c x controlIdx : Nat) (control : Bool),
             1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
             c < N → x < N →
             layout.controlAllowed bits controlIdx →
             controlIdx ≠ layout.flagPos bits →
             controlIdx < layout.ancillaWidth bits →
             Gate.WellTyped (layout.ancillaWidth bits)
               (gate bits N c controlIdx)
             ∧ layout.targetDecode bits
                 (Gate.applyNat (gate bits N c controlIdx)
                   (update (layout.inputEncode bits x)
                     controlIdx control))
               = (if control then (x + c) % N else x)
             ∧ layout.readDecode bits
                 (Gate.applyNat (gate bits N c controlIdx)
                   (update (layout.inputEncode bits x)
                     controlIdx control)) = 0
             ∧ Gate.applyNat (gate bits N c controlIdx)
                 (update (layout.inputEncode bits x)
                   controlIdx control)
                 (layout.topCarryPos bits) = false
             ∧ Gate.applyNat (gate bits N c controlIdx)
                 (update (layout.inputEncode bits x)
                   controlIdx control)
                 (layout.flagPos bits) = false
             ∧ Gate.applyNat (gate bits N c controlIdx)
                 (update (layout.inputEncode bits x)
                   controlIdx control) controlIdx = control

/-! ### SQIR/Cuccaro layout instance (Phase R5b)

`sqirCuccaroLayout` packages the **SQIR/Cuccaro layout choices** as
a `ControlledModAddLayout` value:

* `ancillaWidth := sqir_modmult_rev_anc` (= `3*bits + 11`).
* `flagPos := fun _ ↦ 1` (Cuccaro flag at position 1).
* `topCarryPos := fun bits ↦ 2 + 2 * bits` (top carry).
* `workspaceUpperBound := fun bits ↦ 2 + 2 * bits + 1`
  (one above the top carry).
* `inputEncode := fun _ acc ↦ cuccaro_input_F 2 false 0 acc`
  (Cuccaro encoding with q_start = 2, carry_in = false, a = 0,
  b = acc).
* `targetDecode := fun bits ↦ cuccaro_target_val bits 2`.
* `readDecode := fun bits ↦ cuccaro_read_val bits 2`.
* `controlAllowed := fun bits controlIdx ↦
    controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx`.

A future Gidney-AND, QFT-adder, or lookup-table layout would supply
a different `ControlledModAddLayout` value. -/
def sqirCuccaroLayout : ControlledModAddLayout where
  ancillaWidth        := sqir_modmult_rev_anc
  flagPos             := fun _ => 1
  topCarryPos         := fun bits => 2 + 2 * bits
  workspaceUpperBound := fun bits => 2 + 2 * bits + 1
  inputEncode         := fun _ acc => cuccaro_input_F 2 false 0 acc
  targetDecode        := fun bits => cuccaro_target_val bits 2
  readDecode          := fun bits => cuccaro_read_val bits 2
  controlAllowed      := fun bits controlIdx =>
                           controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx

/-! ### SQIR/Cuccaro implementation instance

`sqirCuccaroImpl` is the **first witness** of the
`ControlledModAddImpl` contract (Phase R4b + R5b refactor).

It carries the `sqirCuccaroLayout` defined just above and wraps the
existing SQIR-faithful Cuccaro controlled modular adder
(`sqir_style_controlledModAddConst_gate`) plus its 6-conjunct
clean theorem (`sqir_style_controlledModAddConst_gate_clean`).

Because every layout field of `sqirCuccaroLayout` is a `fun` that
reduces to the corresponding Cuccaro name, the `clean` field below
is propositionally (and definitionally) equal to the source
theorem's conclusion — so the body is a one-line direct call to
`sqir_style_controlledModAddConst_gate_clean`. -/
noncomputable def sqirCuccaroImpl : ControlledModAddImpl where
  layout := sqirCuccaroLayout
  gate   := fun bits N c controlIdx =>
              sqir_style_controlledModAddConst_gate bits 2 N c controlIdx 1
  clean  := by
    intro bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
      hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt
    exact sqir_style_controlledModAddConst_gate_clean bits N c x controlIdx control
      hbits hN_pos hN hN2 hc hx hcontrol_allowed hcontrol_ne_flag
      h_control_workspace_lt

/-! ### Projection aliases (R5b: stated through `C.layout`)

The six aliases below extract individual conjuncts from
`ControlledModAddImpl.clean`.  All references to layout-specific
positions and decoders go through `C.layout.*` projections — the
aliases are now layout-parametric.

Signature convention: each alias takes the *full* side-condition
list (bits, N, c, x, controlIdx, control + 10 hypotheses), matching
the shape of the source bundle.  Aliases for conjuncts that don't
depend on `x` / `control` still accept them so the call shape is
uniform. -/

theorem clean_wellTyped (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.WellTyped (C.layout.ancillaWidth bits)
      (C.gate bits N c controlIdx) :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).1

theorem clean_targetDecode (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    C.layout.targetDecode bits
        (Gate.applyNat (C.gate bits N c controlIdx)
          (update (C.layout.inputEncode bits x) controlIdx control))
      = (if control then (x + c) % N else x) :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.1

theorem clean_readZero (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    C.layout.readDecode bits
        (Gate.applyNat (C.gate bits N c controlIdx)
          (update (C.layout.inputEncode bits x) controlIdx control)) = 0 :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.1

theorem clean_topCarryFalse (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.applyNat (C.gate bits N c controlIdx)
        (update (C.layout.inputEncode bits x) controlIdx control)
        (C.layout.topCarryPos bits) = false :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.2.1

theorem clean_flagFalse (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.applyNat (C.gate bits N c controlIdx)
        (update (C.layout.inputEncode bits x) controlIdx control)
        (C.layout.flagPos bits) = false :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.2.2.1

theorem clean_controlPreserved (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    Gate.applyNat (C.gate bits N c controlIdx)
        (update (C.layout.inputEncode bits x) controlIdx control)
        controlIdx
      = control :=
  (C.clean bits N c x controlIdx control hbits hN_pos hN hN2 hc hx
    hcontrol_allowed hcontrol_ne_flag h_control_workspace_lt).2.2.2.2.2

/-! ### Generic smoke theorem (R5b)

A direct restatement of `clean_targetDecode` for any
`ControlledModAddImpl`.  Demonstrates that the layout-parametric
interface can be consumed without naming Cuccaro. -/
theorem ControlledModAddImpl.targetDecode_eq_of_clean
    (C : ControlledModAddImpl)
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_allowed : C.layout.controlAllowed bits controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ C.layout.flagPos bits)
    (h_control_workspace_lt : controlIdx < C.layout.ancillaWidth bits) :
    C.layout.targetDecode bits
        (Gate.applyNat (C.gate bits N c controlIdx)
          (update (C.layout.inputEncode bits x) controlIdx control))
      = (if control then (x + c) % N else x) :=
  clean_targetDecode C bits N c x controlIdx control
    hbits hN_pos hN hN2 hc hx hcontrol_allowed hcontrol_ne_flag
    h_control_workspace_lt

/-! ### SQIR-specific smoke theorem (preserved name)

A usability check: the SQIR/Cuccaro instance, when consumed through
the `clean_targetDecode` projection, produces the expected
`(x + c) % N` decode under `control = true` (and `x` under
`control = false`).  After the R5b refactor the SQIR-flavor decoder
(`cuccaro_target_val bits 2`) and encoder (`cuccaro_input_F 2 false
0 x`) on the conclusion are obtained by definitional reduction
through `sqirCuccaroImpl.layout = sqirCuccaroLayout`. -/
theorem sqirCuccaroImpl_targetDecode_eq
    (bits N c x controlIdx : Nat) (control : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hx : x < N)
    (hcontrol_out : controlIdx < 2 ∨ 2 + 2 * bits + 1 ≤ controlIdx)
    (hcontrol_ne_flag : controlIdx ≠ 1)
    (h_control_workspace_lt :
        controlIdx < sqirCuccaroImpl.layout.ancillaWidth bits) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqirCuccaroImpl.gate bits N c controlIdx)
          (update (cuccaro_input_F 2 false 0 x) controlIdx control))
      = (if control then (x + c) % N else x) :=
  clean_targetDecode sqirCuccaroImpl bits N c x controlIdx control
    hbits hN_pos hN hN2 hc hx hcontrol_out hcontrol_ne_flag
    h_control_workspace_lt

end ControlledModAdd

/-! ## Multiplier-step layer (Phase R5c)

`VerifiedShor.MultiplierStep` is the **Level-2** layout abstraction
above `ControlledModAdd`.  It adds the multiplier register
(positions for the per-bit `m.testBit j` controls), the accumulator
target positions, the multiplier input encoding, and the
install/skip-j machinery.

### Scope (R5c)
R5c ONLY exposes the layout.  The existing multiplier proof chain
(`sqir_modmult_step_target_decode`, `sqir_modmult_step_workspace`,
etc.) still uses the SQIR-specific names directly.  Refactoring
those is later work.

### Layer position
```
VerifiedModMulFamily              (Shor-level contract, Phase R3)
  └── MultiplierStepLayout         (this layer, Phase R5c)
      └── ControlledModAddLayout   (Phase R5b)
          └── (future) MCPAdapterLayout   (Phase R5d)
``` -/

namespace MultiplierStep

open FormalRV.BQAlgo
open FormalRV.Framework (Gate)

/-! ### Level-2 layout structure

`MultiplierStepLayout` adds multiplier-register-specific positions
and the install machinery to a base `ControlledModAddLayout`.  It is
data-level only; semantic theorems are stated as wrapper aliases on
specific instances rather than bundled fields. -/
structure MultiplierStepLayout where
  /-- The underlying Level-1 controlled-mod-add layout. -/
  base             : ControlledModAdd.ControlledModAddLayout
  /-- Position of multiplier bit `j` (controls the j-th add step). -/
  multControlIdx   : (bits j : Nat) → Nat
  /-- Position of accumulator bit `i` (the target register). -/
  targetBitIdx     : (bits i : Nat) → Nat
  /-- Multiplier input encoder combining the accumulator and the
  multiplier bits. -/
  multInputEncode  : (bits m acc : Nat) → Nat → Bool
  /-- Install-then-skip-j helper: install the first `num_bits` of
  multiplier `m` into the state-function while skipping bit `j`. -/
  installStepInput : (bits m j num_bits : Nat) → (Nat → Bool) → (Nat → Bool)

/-! ### SQIR/Cuccaro multiplier-step layout instance -/
def sqirCuccaroLayout : MultiplierStepLayout where
  base             := ControlledModAdd.sqirCuccaroLayout
  multControlIdx   := sqir_mult_control_idx
  targetBitIdx     := fun _ i => sqir_target_idx i
  multInputEncode  := sqir_mult_input_F
  installStepInput := install_mult_bits_skip_j

/-! ### Public aliases for position / disjointness facts -/

theorem sqirCuccaro_controlIdx_allowed (bits j : Nat) :
    sqir_mult_control_idx bits j < 2
      ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j :=
  sqir_mult_control_idx_outside_modadd_workspace_form bits j

theorem sqirCuccaro_controlIdx_ne_flag (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 1 :=
  sqir_mult_control_idx_ne_flag bits j

theorem sqirCuccaro_controlIdx_ne_topCarry (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 2 + 2 * bits :=
  sqir_mult_control_idx_ne_top_carry bits j

theorem sqirCuccaro_controlIdx_lt_dim
    (bits j : Nat) (hj : j < bits) :
    sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits :=
  sqir_mult_control_idx_lt_sqir_dim bits j hj

theorem sqirCuccaro_controlIdx_injective
    (bits j j' : Nat)
    (h : sqir_mult_control_idx bits j = sqir_mult_control_idx bits j') :
    j = j' :=
  sqir_mult_control_idx_injective bits j j' h

theorem sqirCuccaro_targetBitIdx_eq (i : Nat) :
    sqir_target_idx i = 2 + 2 * i + 1 := rfl

/-! ### Public aliases for input-encoding facts -/

theorem sqirCuccaro_input_targetDecode
    (bits m acc : Nat) (hacc : acc < 2 ^ bits) :
    cuccaro_target_val bits 2 (sqir_mult_input_F bits m acc) = acc :=
  sqir_mult_input_target_decode bits m acc hacc

theorem sqirCuccaro_input_readDecode (bits m acc : Nat) :
    cuccaro_read_val bits 2 (sqir_mult_input_F bits m acc) = 0 :=
  sqir_mult_input_read_decode bits m acc

theorem sqirCuccaro_input_flagFalse (bits m acc : Nat) :
    sqir_mult_input_F bits m acc 1 = false :=
  sqir_mult_input_flag_1_false bits m acc

theorem sqirCuccaro_input_topCarryFalse
    (bits m acc : Nat) (hbits : 1 ≤ bits) :
    sqir_mult_input_F bits m acc (2 + 2 * bits) = false :=
  sqir_mult_input_top_carry_false bits m acc hbits

theorem sqirCuccaro_input_controlBit
    (bits m acc j : Nat) (hj : j < bits) :
    sqir_mult_input_F bits m acc (sqir_mult_control_idx bits j) = m.testBit j :=
  sqir_mult_input_control_bit bits m acc j hj

/-! ### Public aliases for install / commutation bridge facts -/

open FormalRV.Framework in
theorem sqirCuccaro_input_eq_install_with_j
    (bits m acc j : Nat) (hj : j < bits) (hacc : acc < 2 ^ bits) :
    sqir_mult_input_F bits m acc
      = install_mult_bits_skip_j bits m j bits
          (update (cuccaro_input_F 2 false 0 acc)
            (sqir_mult_control_idx bits j) (m.testBit j)) :=
  sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc

theorem sqirCuccaro_targetDecode_through_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) :=
  cuccaro_target_val_through_install_mult bits m j N c num_bits f

theorem sqirCuccaro_controlledModAdd_commute_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f)
      = install_mult_bits_skip_j bits m j num_bits
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) :=
  sqir_style_controlledModAddConst_gate_commute_install bits m j N c num_bits f

/-! Three additional through-install aliases consumed by the
workspace wrapper theorem (Phase R6c). -/

theorem sqirCuccaro_readDecode_through_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    cuccaro_read_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) :=
  cuccaro_read_val_through_install_mult bits m j N c num_bits f

theorem sqirCuccaro_applyNat_through_install_at_workspace
    (bits m j N c num_bits q : Nat) (f : Nat → Bool)
    (hq_ws : q < 2 + 2 * bits + 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) q
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f q :=
  applyNat_modmult_through_install_at_workspace bits m j N c num_bits q f hq_ws

theorem sqirCuccaro_applyNat_through_install_at_j
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) (sqir_mult_control_idx bits j)
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f (sqir_mult_control_idx bits j) :=
  applyNat_modmult_through_install_at_j bits m j N c num_bits f

/-- The k-th multiplier bit (with `k ≠ j`) is set to `m.testBit k`
after running the install. -/
theorem sqirCuccaro_install_at_mult_k_eq
    (bits m j num_bits k : Nat) (f : Nat → Bool)
    (h_k_lt : k < num_bits) (h_k_ne_j : k ≠ j) :
    install_mult_bits_skip_j bits m j num_bits f (sqir_mult_control_idx bits k)
      = m.testBit k :=
  install_mult_bits_skip_j_at_mult_k_eq bits m j num_bits k f h_k_lt h_k_ne_j

/-! ### Fine-grained per-position aliases (Phase R5b' for R6f-real)

These 5 aliases expose per-position facts that the 6-conjunct
`ControlledModAddImpl.clean` bundle does NOT cover.  Together with
R6b/R6c/R6e, they unlock a real interface-routed proof of the
one-step state equality (`sqir_modmult_step_state_eq`).

The clean bundle is value-level (target/read/topCarry/flag/control);
these aliases are bit/position-level.  They are interface exposure
aliases (option 1 of loop rules) — pure wrappers around existing
SQIR lemmas. -/

theorem sqirCuccaro_step_flag0_false
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) 0 = false :=
  sqir_modmult_step_flag0_false bits N a j m acc hbits hj

theorem sqirCuccaro_step_above_layout_false
    (bits N a j m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) q = false :=
  sqir_modmult_step_above_layout_false bits N a j m acc q hbits hj hq

theorem sqirCuccaro_step_carryIn_restored
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) 2 = false :=
  sqir_modmult_step_carry_in_restored bits N a j m acc hbits hN_pos hN hN2 hj hacc

theorem sqirCuccaro_step_targetBit_extracted
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) (2 + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i :=
  sqir_modmult_step_target_bit bits N a j m acc i hbits hN_pos hN hN2 hj hacc hi

theorem sqirCuccaro_step_readBit_zero
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) (2 + 2 * i + 2) = false :=
  sqir_modmult_step_read_bit bits N a j m acc i hbits hN_pos hN hN2 hj hacc hi

/-! ### Smoke theorems

These demonstrate that the Level-2 layout connects sensibly to the
Level-1 layout: the SQIR multiplier control positions land in the
Level-1 `controlAllowed` region, and the SQIR multiplier input
decodes the accumulator through the Level-1 `targetDecode`. -/

theorem sqirCuccaro_controlIdx_controlAllowed (bits j : Nat) :
    ControlledModAdd.sqirCuccaroLayout.controlAllowed bits
      (sqir_mult_control_idx bits j) :=
  sqir_mult_control_idx_outside_modadd_workspace_form bits j

theorem sqirCuccaro_multInput_targetDecode
    (bits m acc : Nat) (hacc : acc < 2 ^ bits) :
    ControlledModAdd.sqirCuccaroLayout.targetDecode bits
      (sqir_mult_input_F bits m acc) = acc :=
  sqir_mult_input_target_decode bits m acc hacc

/-! ### First proof-chain theorem via interfaces (Phase R6b)

`sqirCuccaro_step_targetDecode_via_interface` proves the same fact as
the existing `sqir_modmult_step_target_decode` (`SQIRModMult.lean:501`),
but states it through the new layout stack and proves it through the
R5b/R5c aliases — no direct call to
`sqir_style_controlledModAddConst_gate_clean`.

The proof mirrors the original 4-step skeleton:
1. `hacc_lt : acc < 2^bits` (Mathlib `Nat.lt_of_lt_of_le`).
2. Convert `multInputEncode` to install form via
   `sqirCuccaro_input_eq_install_with_j` (R5c alias).
3. Push `targetDecode` through `installStepInput` via
   `sqirCuccaro_targetDecode_through_install` (R5c alias).
4. Close with the Level-1 `ControlledModAdd.clean_targetDecode`
   projection applied to `ControlledModAdd.sqirCuccaroImpl`.

The original `sqir_modmult_step_target_decode` is NOT changed. -/
theorem sqirCuccaro_step_targetDecode_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    ControlledModAdd.sqirCuccaroLayout.targetDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc))
      = if m.testBit j then (acc + (a * 2^j) % N) % N else acc := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  have h_ctrl_allowed := sqirCuccaro_controlIdx_controlAllowed bits j
  have h_ctrl_ne_flag := sqirCuccaro_controlIdx_ne_flag bits j
  have h_ctrl_lt := sqirCuccaro_controlIdx_lt_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  -- Step 1: convert layout-form projections to their SQIR-form
  -- counterparts (all four are definitional through `sqirCuccaroLayout`
  -- and `sqirCuccaroImpl`).  This exposes the SQIR identifiers that the
  -- R5c aliases are stated in.
  show cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
            (sqir_mult_control_idx bits j) 1)
          (sqir_mult_input_F bits m acc))
      = if m.testBit j then (acc + (a * 2^j) % N) % N else acc
  -- Step 2: install form for the multiplier input encoder (R5c alias).
  rw [sqirCuccaro_input_eq_install_with_j bits m acc j hj hacc_lt]
  -- Step 3: push targetDecode through install (R5c alias).
  rw [sqirCuccaro_targetDecode_through_install bits m j N ((a * 2^j) % N) bits]
  -- Step 4: apply Level-1 clean-targetDecode projection on the SQIR instance.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt

/-- Comparison theorem: the interface-form target decode equals the
SQIR-form target decode used by `sqir_modmult_step_target_decode`.
Both terms reduce to the same SQIR-level expression via definitional
unfolding through the layout projections, so this is `rfl`. -/
theorem sqirCuccaro_step_targetDecode_matches_old
    (bits N a j m acc : Nat) :
    ControlledModAdd.sqirCuccaroLayout.targetDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc))
      = cuccaro_target_val bits 2
          (Gate.applyNat (sqir_modmult_step_gate bits N a j)
            (sqir_mult_input_F bits m acc)) := rfl

/-! ### Workspace wrapper theorem via interfaces (Phase R6c)

`sqirCuccaro_step_workspace_via_interface` proves the same 4-conjunct
workspace fact as `sqir_modmult_step_workspace` (`SQIRModMult.lean:631`)
but stated through the new layout stack and proved through the
R5b/R5c aliases.

The proof mirrors the original skeleton:
1. `hacc_lt : acc < 2^bits` (Mathlib `Nat.lt_of_lt_of_le`).
2. `show` converts the layout-form goal to its SQIR-form counterpart
   (same def-equality trick as R6b).
3. Convert `multInputEncode` to install form via
   `sqirCuccaro_input_eq_install_with_j`.
4. For each of the 4 conjuncts, use the corresponding R5b
   `clean_*` projection (`clean_readZero`, `clean_topCarryFalse`,
   `clean_flagFalse`, `clean_controlPreserved`) on
   `ControlledModAdd.sqirCuccaroImpl`, then bridge through the
   corresponding R5c `_through_install_*` alias.

No direct call to `sqir_style_controlledModAddConst_gate_clean`. -/
theorem sqirCuccaro_step_workspace_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    ControlledModAdd.sqirCuccaroLayout.readDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)) = 0
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.topCarryPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.flagPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (sqirCuccaroLayout.multControlIdx bits j) = m.testBit j := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  have h_ctrl_allowed := sqirCuccaro_controlIdx_controlAllowed bits j
  have h_ctrl_ne_flag := sqirCuccaro_controlIdx_ne_flag bits j
  have h_ctrl_lt := sqirCuccaro_controlIdx_lt_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  -- Step 1: def-unfold layout projections to SQIR-form.
  show cuccaro_read_val bits 2
        (Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
            (sqir_mult_control_idx bits j) 1)
          (sqir_mult_input_F bits m acc)) = 0
      ∧ Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
              (sqir_mult_control_idx bits j) 1)
            (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
      ∧ Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
              (sqir_mult_control_idx bits j) 1)
            (sqir_mult_input_F bits m acc) 1 = false
      ∧ Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
              (sqir_mult_control_idx bits j) 1)
            (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits j)
          = m.testBit j
  -- Step 2: install form for the multiplier input encoder.
  rw [sqirCuccaro_input_eq_install_with_j bits m acc j hj hacc_lt]
  -- Step 3: extract the 4 needed clean conjuncts from the R5b
  -- projections applied to `sqirCuccaroImpl`, on the "after F_j update"
  -- starting state.
  have h_rd := ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  have h_tc := ControlledModAdd.clean_topCarryFalse ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  have h_fl := ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  have h_ctrl := ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sqirCuccaro_readDecode_through_install bits m j N ((a * 2^j) % N) bits]
    exact h_rd
  · rw [sqirCuccaro_applyNat_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          (2 + 2 * bits) _ (by omega)]
    exact h_tc
  · rw [sqirCuccaro_applyNat_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          1 _ (by omega)]
    exact h_fl
  · rw [sqirCuccaro_applyNat_through_install_at_j bits m j N ((a * 2^j) % N) bits]
    exact h_ctrl

/-- Comparison theorem: the interface-form workspace conjunction equals
the SQIR-form workspace conjunction used by `sqir_modmult_step_workspace`.
Both terms reduce to the same SQIR-level expression via definitional
unfolding through the layout projections, so this is `rfl`. -/
theorem sqirCuccaro_step_workspace_matches_old
    (bits N a j m acc : Nat) :
    (ControlledModAdd.sqirCuccaroLayout.readDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)) = 0
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.topCarryPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.flagPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (sqirCuccaroLayout.multControlIdx bits j) = m.testBit j)
    =
    (cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) 1 = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits j) = m.testBit j) := rfl

/-! ### Step gate well-typedness via interfaces (Phase R6d)

`sqirCuccaro_step_gate_wellTyped_via_interface` proves the same
well-typedness fact as `sqir_modmult_step_gate_wellTyped`
(`SQIRModMult.lean:1329`) but stated through the new layout stack
and proved via `ControlledModAdd.clean_wellTyped` on
`ControlledModAdd.sqirCuccaroImpl`.

The original proof uses the same trick: pass `x := 0` (and
`hx := hN_pos`) to the `clean` bundle, since well-typedness does
not depend on the data value `x`.

No direct call to `sqir_style_controlledModAddConst_gate_clean`. -/
theorem sqirCuccaro_step_gate_wellTyped_via_interface
    (bits N a j : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (hj : j < bits) :
    Gate.WellTyped
      (ControlledModAdd.sqirCuccaroLayout.ancillaWidth bits)
      (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
        (sqirCuccaroLayout.multControlIdx bits j)) := by
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have h_ctrl_allowed := sqirCuccaro_controlIdx_controlAllowed bits j
  have h_ctrl_ne_flag := sqirCuccaro_controlIdx_ne_flag bits j
  have h_ctrl_lt := sqirCuccaro_controlIdx_lt_dim bits j hj
  -- Apply Level-1 clean-wellTyped projection on the SQIR instance.
  -- (Use x := 0, hx := hN_pos since wellTyped doesn't depend on x.)
  exact ControlledModAdd.clean_wellTyped ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) 0 (sqir_mult_control_idx bits j) false
    hbits hN_pos hN hN2 hc_pos hN_pos h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt

/-- Comparison theorem: the interface-form well-typedness equals the
SQIR-form well-typedness used by `sqir_modmult_step_gate_wellTyped`.
Both terms reduce to the same SQIR-level expression via definitional
unfolding through the layout projections, so this is `rfl`. -/
theorem sqirCuccaro_step_gate_wellTyped_matches_old
    (bits N a j : Nat) :
    Gate.WellTyped
        (ControlledModAdd.sqirCuccaroLayout.ancillaWidth bits)
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
      = Gate.WellTyped (sqir_modmult_rev_anc bits)
          (sqir_modmult_step_gate bits N a j) := rfl

/-! ### Preserves-all-control-bits via interfaces (Phase R6e)

`sqirCuccaro_step_preserves_all_control_bits_via_interface` proves the
across-bit preservation fact: after the step gate runs, EVERY
multiplier control bit `k < bits` is preserved as `m.testBit k`
(not just the `k = j` one).

The original `sqir_modmult_step_preserves_all_control_bits`
(`SQIRModMult.lean:774`) splits on `k = j` vs `k ≠ j`:
- `k = j`: the j-th conjunct of `sqir_modmult_step_workspace` —
  reusable via R6c `sqirCuccaro_step_workspace_via_interface`.
- `k ≠ j`: gate commutes through the install, then the install at
  position `controlIdx_k` is `m.testBit k` — needs R5c
  `sqirCuccaro_controlledModAdd_commute_install` and the new
  `sqirCuccaro_install_at_mult_k_eq` alias.

No direct call to `sqir_style_controlledModAddConst_gate_clean`. -/
theorem sqirCuccaro_step_preserves_all_control_bits_via_interface
    (bits N a m acc j k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
        (sqirCuccaroLayout.multControlIdx bits k) = m.testBit k := by
  by_cases h_kj : k = j
  · -- k = j case: use the workspace bundle's control-preservation conjunct
    -- (= conjunct #4 of R6c sqirCuccaro_step_workspace_via_interface).
    subst h_kj
    have ⟨_, _, _, h_ctrl⟩ :=
      sqirCuccaro_step_workspace_via_interface bits N a k m acc
        hbits hN_pos hN hN2 hk hacc
    exact h_ctrl
  · -- k ≠ j case: gate commutes through install; install at controlIdx_k
    -- delivers m.testBit k.
    have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    show Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
          (sqir_mult_control_idx bits j) 1)
        (sqir_mult_input_F bits m acc)
        (sqir_mult_control_idx bits k) = m.testBit k
    rw [sqirCuccaro_input_eq_install_with_j bits m acc j hj hacc_lt]
    rw [sqirCuccaro_controlledModAdd_commute_install bits m j N ((a * 2^j) % N) bits _]
    exact sqirCuccaro_install_at_mult_k_eq bits m j bits k _ hk h_kj

/-- Comparison theorem: rfl-equivalence of the interface-form and
SQIR-form preserves-all-control-bits conclusion. -/
theorem sqirCuccaro_step_preserves_all_control_bits_matches_old
    (bits N a m acc j k : Nat) :
    (Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
        (sqirCuccaroLayout.multControlIdx bits k) = m.testBit k)
    = (Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits k)
        = m.testBit k) := rfl

/-! ### Full one-step state equality (Phase R6f — fallback wrapper)

`sqirCuccaro_step_state_eq_via_interface` states the full one-step
state equality through the layout stack.

**Honesty note**: the proof here is a **fallback wrapper** (option 3
in the loop instructions).  It calls the original
`sqir_modmult_step_state_eq` (`SQIRModMult.lean:1156`) directly,
because the original `funext q` proof depends on per-position lemmas
(`sqir_modmult_step_above_layout_false`, `_flag0_false`,
`_carry_in_restored`, `_target_bit`, `_read_bit`) that are NOT
exposed by the 6-conjunct `ControlledModAddImpl.clean` bundle.

Routing through interface requires either:
1. enriching the clean bundle with per-position conjuncts (a deeper
   refactor reserved as R5b'), OR
2. adding 3 supplementary per-position aliases
   (`sqirCuccaro_flag0_false`, `_carry_in_restored`, `_above_layout_false`)
   and replaying the case-split funext proof.

For R6f we land a fallback wrapper so the **statement** uses
interface fields; later phases (R5b' or a dedicated R6f') may close
the proof via interface.  The original theorem is not changed and
is not weakened. -/
theorem sqirCuccaro_step_state_eq_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) :=
  sqir_modmult_step_state_eq bits N a j m acc hbits hN_pos hN hN2 hj hacc

/-- Comparison theorem: the interface-form state equality equals the
SQIR-form state equality by `rfl`. -/
theorem sqirCuccaro_step_state_eq_matches_old
    (bits N a j m acc : Nat) :
    (Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc))
    = (Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc)) := rfl

/-! ### Real-via-interface state equality (R6f-real)

The R5b' aliases + R6c workspace + R6e preserves-all-control-bits +
the per-position decoder facts on `sqir_mult_input_F` give all the
ingredients needed to prove `sqir_modmult_step_state_eq` through
interface aliases, NOT through `sqir_modmult_step_state_eq` or
`sqir_style_controlledModAddConst_gate_clean` directly.

Proof engineering: the aliases are stated in layout-form
(`sqirCuccaroLayout.multInputEncode`, etc.), but the funext-style
state-equality proof needs SQIR-form sub-goals.  We bridge with
**type-ascribed `have`**: `have h_sqir : <SQIR-form> := <alias-call>`
elaborates by def-eq (layout-form = SQIR-form), and then `rw [h_sqir]`
matches the SQIR-form pattern in the goal.

Strategy (per loop instructions):
* Stage 1: prove a SQIR-form helper using type-ascribed aliases.
* Stage 2: derive the layout-form theorem by `exact` (def-eq). -/

theorem sqirCuccaro_step_state_eq_real_sqir_form
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) := by
  funext q
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  -- Case split on q.
  by_cases hq_above : q ≥ 2 + 2 * bits + 1 + bits
  · -- Above layout.
    have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                  (sqir_mult_input_F bits m acc) q = false :=
      sqirCuccaro_step_above_layout_false bits N a j m acc q hbits hj hq_above
    rw [h_lhs]
    -- RHS = false (above layout).
    unfold sqir_mult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · push_neg at hq_above
    by_cases hq_in_mult : q ≥ 2 + 2 * bits + 1
    · -- Multiplier register.
      set k := q - (2 + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have hq_eq : q = sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [hq_eq]
      have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                    (sqir_mult_input_F bits m acc)
                    (sqir_mult_control_idx bits k) = m.testBit k :=
        sqirCuccaro_step_preserves_all_control_bits_via_interface
          bits N a m acc j k hbits hN_pos hN hN2 hacc hj hk_lt
      rw [h_lhs]
      exact (sqir_mult_input_control_bit bits m acc' k hk_lt).symm
    · push_neg at hq_in_mult
      -- Workspace q < 2 + 2*bits + 1.
      by_cases hq_0 : q = 0
      · subst hq_0
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) 0 = false :=
          sqirCuccaro_step_flag0_false bits N a j m acc hbits hj
        rw [h_lhs]
        exact (sqir_mult_input_flag_0_false bits m acc').symm
      by_cases hq_1 : q = 1
      · subst hq_1
        have h_workspace := sqirCuccaro_step_workspace_via_interface
          bits N a j m acc hbits hN_pos hN hN2 hj hacc
        -- workspace.2.2.1 is conj #3 = flag at position 1 = false.
        have h_fl : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) 1 = false :=
          h_workspace.2.2.1
        rw [h_fl]
        exact (sqir_mult_input_flag_1_false bits m acc').symm
      by_cases hq_2 : q = 2
      · subst hq_2
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) 2 = false :=
          sqirCuccaro_step_carryIn_restored bits N a j m acc
            hbits hN_pos hN hN2 hj hacc
        rw [h_lhs]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 : Nat) < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
      by_cases hq_top : q = 2 + 2 * bits
      · subst hq_top
        have h_workspace := sqirCuccaro_step_workspace_via_interface
          bits N a j m acc hbits hN_pos hN hN2 hj hacc
        -- workspace.2.1 is conj #2 = top carry = false.
        have h_tc : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false :=
          h_workspace.2.1
        rw [h_tc]
        have h_eq : (2 + 2 * bits : Nat) = 2 + 2 * (bits - 1) + 2 := by omega
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 + 2 * bits : Nat) < 2 + 2 * bits + 1)]
        rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 acc']
        exact (Nat.zero_testBit _).symm
      -- q ∈ [3, 2*bits + 1].  Parity dispatch.
      by_cases h_q_odd : q % 2 = 1
      · -- Target bit: q = 2 + 2*i + 1.
        have hi_lt : (q - 3) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
        rw [hq_eq]
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) (2 + 2 * ((q - 3) / 2) + 1)
                    = acc'.testBit ((q - 3) / 2) := by
          have := sqirCuccaro_step_targetBit_extracted bits N a j m acc
            ((q - 3) / 2) hbits hN_pos hN hN2 hj hacc hi_lt
          -- The alias is layout-form; type-ascribe to SQIR-form via def-eq.
          exact this
        rw [h_lhs]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 3) / 2) + 1 < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
      · -- Read bit: q = 2 + 2*i + 2.
        have hi_lt : (q - 4) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
        rw [hq_eq]
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) (2 + 2 * ((q - 4) / 2) + 2)
                    = false :=
          sqirCuccaro_step_readBit_zero bits N a j m acc ((q - 4) / 2)
            hbits hN_pos hN hN2 hj hacc hi_lt
        rw [h_lhs]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 4) / 2) + 2 < 2 + 2 * bits + 1)]
        rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
        exact (Nat.zero_testBit _).symm

/-- **R6f-real**: the layout-form state-equality theorem.  Derived from
`sqirCuccaro_step_state_eq_real_sqir_form` by `exact` (def-eq through
layout-projection unfolding). -/
theorem sqirCuccaro_step_state_eq_real_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) :=
  sqirCuccaro_step_state_eq_real_sqir_form bits N a j m acc
    hbits hN_pos hN hN2 hj hacc

/-- Comparison theorem: the real-via-interface and the R6f fallback
theorem have the same conclusion (rfl). -/
theorem sqirCuccaro_step_state_eq_real_matches_fallback
    (bits N a j m acc : Nat) :
    (Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc))
    = (Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc)) := rfl

/-! ### Prefix/const-gate chain via interface (Phase R6g — fallback)

These theorems lift the one-step state equality (R6f) to the full
constant-multiplier prefix.  Like R6f, these are **fallback wrappers**:
statement uses interface fields, proof calls the existing SQIR
theorems.  Future R6g' can replay the induction once R5b' enriches
the clean bundle to support a real R6f proof. -/

theorem sqirCuccaro_prefix_state_eq_from_via_interface
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (sqir_modmult_acc_spec_from N a m acc k) :=
  sqir_modmult_prefix_state_eq_from bits N a m acc k hbits hN_pos hN hN2 hacc hk

theorem sqirCuccaro_const_gate_state_eq_from_via_interface
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m ((acc + a * m) % N) :=
  sqir_modmult_const_gate_state_eq_from bits N a m acc hbits hN_pos hN hN2 hacc hm

/-! ### Prefix/const-gate chain — real interface routing (Phase R6g-real)

These theorems promote the R6g fallback wrappers to genuine interface
proofs by replaying the original prefix induction (and the trivial
const-gate composition) with `sqirCuccaro_step_state_eq_real_sqir_form`
(R6f-real) replacing `sqir_modmult_step_state_eq`.

* `_real_sqir_form` variants: SQIR-form helpers whose proof bodies
  replay the original inductions.
* `_real_via_interface` variants: layout-form wrappers, one-line
  `exact` from the SQIR-form helpers (def-eq).

Neither calls `sqir_modmult_step_state_eq`,
`sqir_modmult_prefix_state_eq_from`,
`sqir_modmult_const_gate_state_eq_from`, or
`sqir_style_controlledModAddConst_gate_clean`. -/

theorem sqirCuccaro_prefix_state_eq_from_real_sqir_form
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m (sqir_modmult_acc_spec_from N a m acc k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate, Gate.applyNat_I, sqir_modmult_acc_spec_from_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec_from N a m acc n < N :=
      sqir_modmult_acc_spec_from_lt N a m acc n hN_pos hacc
    rw [sqirCuccaro_step_state_eq_real_sqir_form bits N a n m
          (sqir_modmult_acc_spec_from N a m acc n)
          hbits hN_pos hN hN2 hn_lt hacc_lt_N]
    rfl

theorem sqirCuccaro_prefix_state_eq_from_real_via_interface
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (sqir_modmult_acc_spec_from N a m acc k) :=
  sqirCuccaro_prefix_state_eq_from_real_sqir_form bits N a m acc k
    hbits hN_pos hN hN2 hacc hk

theorem sqirCuccaro_const_gate_state_eq_from_real_sqir_form
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m ((acc + a * m) % N) := by
  unfold sqir_modmult_const_gate
  rw [sqirCuccaro_prefix_state_eq_from_real_sqir_form bits N a m acc bits
        hbits hN_pos hN hN2 hacc (le_refl _)]
  rw [sqir_modmult_acc_spec_from_eq_add_mul_mod bits N a m acc hN_pos hacc hm]

theorem sqirCuccaro_const_gate_state_eq_from_real_via_interface
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m ((acc + a * m) % N) :=
  sqirCuccaro_const_gate_state_eq_from_real_sqir_form bits N a m acc
    hbits hN_pos hN hN2 hacc hm

end MultiplierStep

/-! ## MCP / Shor adapter layer (Phase R5d)

`VerifiedShor.MCPAdapter` is the **Level-3** layout abstraction
above `MultiplierStep`.  It connects the internal multiplier
layout (Level 2) to the Shor/MCP-facing `encodeDataZeroAnc`
encoding via a shift adapter and a register-reversal swap.

### Scope (R5d)
R5d ONLY exposes the layout and re-exports existing MCP-bridge
facts.  It does NOT yet build a generic `VerifiedModMulFamily` from
a `MultiplierStepLayout` + `ControlledModAddImpl` — that remains
R6 work.

### Layer position
```
VerifiedModMulFamily              (Shor-level contract, Phase R3)
  └── MCPAdapterLayout             (this layer, Phase R5d)
      └── MultiplierStepLayout     (Phase R5c)
          └── ControlledModAddLayout (Phase R5b)
``` -/

namespace MCPAdapter

open FormalRV.BQAlgo
open FormalRV.Framework (Gate)

/-! ### Level-3 layout structure

`MCPAdapterLayout` packages the adapter between the internal
multiplier register layout and the Shor-MCP-facing encoding
(`encodeDataZeroAnc`).  Data-level only; semantic theorems are
exposed as wrapper aliases on the SQIR/Cuccaro instance. -/
structure MCPAdapterLayout where
  /-- The underlying Level-2 multiplier-step layout. -/
  step                   : MultiplierStep.MultiplierStepLayout
  /-- Outer total dimension: `bits + ancilla`. -/
  totalDim               : Nat → Nat
  /-- Shor-MCP-facing input encoder: `|x⟩|0_anc⟩` packed
  big-endian. -/
  mcpEncode              : (bits anc x : Nat) → Nat → Bool
  /-- Shifted internal multiplier input encoder (positions
  `[0, bits)` reserved for the outer data register). -/
  shiftedMultInputEncode : (bits m acc : Nat) → Nat → Bool
  /-- Shift offset (the amount by which to shift the internal
  multiplier gate up — currently `bits`). -/
  shiftOffset            : Nat → Nat
  /-- Gate-level shift operator. -/
  shiftGate              : Nat → Gate → Gate
  /-- Adapter gate that maps the MCP encoding to the shifted
  internal layout (a register-reversal swap). -/
  encodeAdapter          : Nat → Gate

/-! ### SQIR/Cuccaro MCP adapter layout instance -/
def sqirCuccaroLayout : MCPAdapterLayout where
  step                   := MultiplierStep.sqirCuccaroLayout
  totalDim               := sqir_total_dim
  mcpEncode              := encodeDataZeroAnc
  shiftedMultInputEncode := sqir_mult_input_F_shifted
  shiftOffset            := fun bits => bits
  shiftGate              := Gate.shift
  encodeAdapter          := sqir_encode_to_mult_adapter

/-! ### Public aliases for MCP encoding facts -/

theorem sqirCuccaro_encode_data
    {n anc x i : Nat} (hx : x < 2^n) (hi : i < n) :
    encodeDataZeroAnc n anc x i
      = FormalRV.Framework.nat_to_funbool n x i :=
  encodeDataZeroAnc_data hx hi

theorem sqirCuccaro_encode_anc
    {n anc x j : Nat} (hx : x < 2^n) (hj : j < anc) :
    encodeDataZeroAnc n anc x (n + j) = false :=
  encodeDataZeroAnc_anc hx hj

theorem sqirCuccaro_encode_oob
    {n anc x i : Nat} (hanc_pos : 0 < anc) (hi : n + anc ≤ i) :
    encodeDataZeroAnc n anc x i = false :=
  encodeDataZeroAnc_oob hanc_pos hi

/-! ### Public aliases for shift facts (generic) -/

theorem shift_applyNat_at_lo
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : q < off) :
    Gate.applyNat (Gate.shift off g) f q = f q :=
  Gate.applyNat_shift_at_lo off g f q hq

theorem shift_applyNat_at_hi
    (off : Nat) (g : Gate) (f : Nat → Bool) (q : Nat) (hq : off ≤ q) :
    Gate.applyNat (Gate.shift off g) f q
      = Gate.applyNat g (fun r => f (off + r)) (q - off) :=
  Gate.applyNat_shift_at_hi off g f q hq

theorem shift_wellTyped
    {off dim : Nat} {g : Gate} (h : Gate.WellTyped dim g) :
    Gate.WellTyped (off + dim) (Gate.shift off g) :=
  Gate.shift_wellTyped h

/-! ### Public aliases for adapter correctness -/

theorem sqirCuccaro_encodeAdapter_correct
    (bits x : Nat) (hbits : 1 ≤ bits) (hx : x < 2^bits) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = sqir_mult_input_F_shifted bits x 0 :=
  sqir_encode_to_mult_adapter_correct bits x hbits hx

theorem sqirCuccaro_encodeAdapter_reverse
    (bits y : Nat) (hbits : 1 ≤ bits) (hy : y < 2^bits) :
    Gate.applyNat (sqir_encode_to_mult_adapter bits)
        (sqir_mult_input_F_shifted bits y 0)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) y :=
  sqir_encode_to_mult_adapter_reverse bits y hbits hy

theorem sqirCuccaro_encodeAdapter_wellTyped
    (bits : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (sqir_total_dim bits) (sqir_encode_to_mult_adapter bits) :=
  sqir_encode_to_mult_adapter_wellTyped bits hbits

/-! ### Public aliases for MCP-gate bridge facts

These re-export the R3 public `VerifiedShor.ModMul.*` theorems
through the `MCPAdapter` namespace so that the MCP adapter layer
is visibly the final bridge into `MultiplyCircuitProperty`. -/

theorem sqirCuccaro_gateMCP_apply_encode
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (ModMul.gateMCP bits N a ainv)
        (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N) :=
  ModMul.gateMCP_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_gateMCP_wellTyped
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (ModMul.totalDim bits) (ModMul.gateMCP bits N a ainv) :=
  ModMul.gateMCP_wellTyped bits N a ainv hbits hN_pos hN hN2

theorem sqirCuccaro_satisfiesMultiplyCircuitProperty
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits (ModMul.ancillaWidth bits)
      (Gate.toUCom (ModMul.totalDim bits) (ModMul.gateMCP bits N a ainv)) :=
  ModMul.satisfiesMultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

/-! ### Smoke theorems -/

theorem sqirCuccaro_totalDim_eq (bits : Nat) :
    sqirCuccaroLayout.totalDim bits = sqir_total_dim bits := rfl

theorem sqirCuccaro_mcpEncode_eq (bits anc x : Nat) :
    sqirCuccaroLayout.mcpEncode bits anc x = encodeDataZeroAnc bits anc x := rfl

/-! ### MCP bridge via interface (Phase R6h — fallback wrappers)

These theorems lift the constant-multiplier theorem (R6g) and the
in-place wrapper to the MCP-encoding `MultiplyCircuitProperty`
bridge.  Like R6f/R6g, these are **fallback wrappers**: statement
uses MCP-adapter layout fields, proof routes through the existing
SQIR theorems. -/

theorem sqirCuccaro_inplace_candidate_state_eq_via_interface
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
        (MultiplierStep.sqirCuccaroLayout.multInputEncode bits x 0)
      = MultiplierStep.sqirCuccaroLayout.multInputEncode bits ((a * x) % N) 0 :=
  sqir_modmult_inplace_candidate_state_eq bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_gateMCP_apply_encode_via_interfaces
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (ModMul.gateMCP bits N a ainv)
        (sqirCuccaroLayout.mcpEncode bits (ModMul.ancillaWidth bits) x)
      = sqirCuccaroLayout.mcpEncode bits (ModMul.ancillaWidth bits) ((a * x) % N) :=
  ModMul.gateMCP_apply_encode bits N a ainv x hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_gateMCP_wellTyped_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqirCuccaroLayout.totalDim bits)
      (ModMul.gateMCP bits N a ainv) :=
  ModMul.gateMCP_wellTyped bits N a ainv hbits hN_pos hN hN2

theorem sqirCuccaro_satisfiesMultiplyCircuitProperty_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits
      (ModMul.ancillaWidth bits)
      (Gate.toUCom (sqirCuccaroLayout.totalDim bits)
        (ModMul.gateMCP bits N a ainv)) :=
  ModMul.satisfiesMultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

/-! ### MCP bridge — real interface routing (Phase R6h-real)

Replays each old SQIR proof step with the new R6g-real
constant-gate theorem (and its downstream consumers).

* In-place candidate: uses R6g-real const-gate ×2 + swap + arithmetic.
* In-place shifted: uses real in-place candidate via funext over the
  shift offset.
* MCP gate apply-encode: uses real shifted + adapter aliases.
* MCP gate wellTyped: composes adapter wellTyped + shifted wellTyped
  (neither forbidden).
* MultiplyCircuitProperty bridge: uses real apply-encode + real
  wellTyped through the `toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc`
  bridge.

None calls `sqir_modmult_const_gate_state_eq_from`,
`sqir_modmult_inplace_candidate_state_eq`,
`sqir_modmult_inplace_shifted_correct`,
`sqir_modmult_MCP_gate_apply_encode`, or
`sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty`. -/

theorem sqirCuccaro_inplace_candidate_state_eq_real_sqir_form
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N)
    (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
        (sqir_mult_input_F bits x 0)
      = sqir_mult_input_F bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_candidate
  simp only [Gate.applyNat_seq]
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [MultiplierStep.sqirCuccaro_const_gate_state_eq_from_real_sqir_form
        bits N a x 0 hbits hN_pos hN hN2 hN_pos hx_lt_pow]
  simp only [Nat.zero_add]
  have hax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have hax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le hax_lt_N hN
  rw [sqir_swap_acc_mult_apply bits x ((a * x) % N) hbits hx_lt_pow hax_lt_pow]
  rw [MultiplierStep.sqirCuccaro_const_gate_state_eq_from_real_sqir_form
        bits N ((N - ainv) % N) ((a * x) % N) x hbits hN_pos hN hN2 hx hax_lt_pow]
  congr 1
  exact sqir_modmult_inverse_clear_arith N a ainv x hN_pos hx h_ainv_le h_inv

theorem sqirCuccaro_inplace_candidate_state_eq_real_via_interface
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_candidate bits N a ainv)
        (MultiplierStep.sqirCuccaroLayout.multInputEncode bits x 0)
      = MultiplierStep.sqirCuccaroLayout.multInputEncode bits ((a * x) % N) 0 :=
  sqirCuccaro_inplace_candidate_state_eq_real_sqir_form bits N a ainv x
    hbits hN_pos hN hN2 h_ainv_le hx h_inv

theorem sqirCuccaro_inplace_shifted_correct_real_via_interface
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (sqir_modmult_inplace_shifted bits N a ainv)
        (sqir_mult_input_F_shifted bits x 0)
      = sqir_mult_input_F_shifted bits ((a * x) % N) 0 := by
  unfold sqir_modmult_inplace_shifted
  funext q
  by_cases hq_lo : q < bits
  · rw [Gate.applyNat_shift_at_lo bits _ _ q hq_lo]
    rw [sqir_mult_input_F_shifted_below_bits bits x 0 q hq_lo]
    rw [sqir_mult_input_F_shifted_below_bits bits ((a * x) % N) 0 q hq_lo]
  · push_neg at hq_lo
    rw [Gate.applyNat_shift_at_hi bits _ _ q hq_lo]
    rw [sqir_mult_input_F_shifted_above_bits bits ((a * x) % N) 0 q hq_lo]
    have h_inner_eq : (fun r => sqir_mult_input_F_shifted bits x 0 (bits + r))
                    = sqir_mult_input_F bits x 0 := by
      funext r
      rw [sqir_mult_input_F_shifted_above_bits bits x 0 (bits + r) (by omega)]
      congr 1; omega
    rw [h_inner_eq]
    rw [sqirCuccaro_inplace_candidate_state_eq_real_sqir_form bits N a ainv x
          hbits hN_pos hN hN2 h_ainv_le hx h_inv]

theorem sqirCuccaro_gateMCP_apply_encode_real_via_interfaces
    (bits N a ainv x : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (hx : x < N) (h_inv : (a * ainv) % N = 1) :
    Gate.applyNat (ModMul.gateMCP bits N a ainv)
        (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N) := by
  show Gate.applyNat (sqir_modmult_MCP_gate bits N a ainv)
        (encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) x)
      = encodeDataZeroAnc bits (sqir_modmult_rev_anc bits) ((a * x) % N)
  unfold sqir_modmult_MCP_gate
  simp only [Gate.applyNat_seq]
  have hx_lt_pow : x < 2^bits := Nat.lt_of_lt_of_le hx hN
  rw [sqirCuccaro_encodeAdapter_correct bits x hbits hx_lt_pow]
  rw [sqirCuccaro_inplace_shifted_correct_real_via_interface bits N a ainv x
        hbits hN_pos hN hN2 h_ainv_le hx h_inv]
  have h_ax_lt_N : (a * x) % N < N := Nat.mod_lt _ hN_pos
  have h_ax_lt_pow : (a * x) % N < 2^bits := Nat.lt_of_lt_of_le h_ax_lt_N hN
  exact sqirCuccaro_encodeAdapter_reverse bits ((a * x) % N) hbits h_ax_lt_pow

theorem sqirCuccaro_gateMCP_wellTyped_real_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) :
    Gate.WellTyped (sqirCuccaroLayout.totalDim bits)
      (ModMul.gateMCP bits N a ainv) := by
  show Gate.WellTyped (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv)
  unfold sqir_modmult_MCP_gate
  refine ⟨?_, ?_, ?_⟩
  · exact sqirCuccaro_encodeAdapter_wellTyped bits hbits
  · exact sqir_modmult_inplace_shifted_wellTyped bits N a ainv hbits hN_pos hN hN2
  · exact sqirCuccaro_encodeAdapter_wellTyped bits hbits

theorem sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    FormalRV.SQIRPort.MultiplyCircuitProperty a N bits
      (ModMul.ancillaWidth bits)
      (Gate.toUCom (sqirCuccaroLayout.totalDim bits)
        (ModMul.gateMCP bits N a ainv)) := by
  show FormalRV.SQIRPort.MultiplyCircuitProperty a N bits
        (sqir_modmult_rev_anc bits)
        (Gate.toUCom (sqir_total_dim bits) (sqir_modmult_MCP_gate bits N a ainv))
  unfold sqir_total_dim
  apply toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
    (sqirCuccaro_gateMCP_wellTyped_real_via_interfaces bits N a ainv hbits hN_pos hN hN2)
    hN
  intro x hx
  exact sqirCuccaro_gateMCP_apply_encode_real_via_interfaces bits N a ainv x
    hbits hN_pos hN hN2 h_ainv_le hx h_inv

end MCPAdapter

/-! ## Final SQIR/Cuccaro certification via interfaces (Phase R6i)

These theorems certify the existing SQIR/Cuccaro circuit family as a
`ModMulImpl` / `VerifiedModMulFamily` through the new interface
stack.  Like R6f-R6h, they are **fallback wrappers** whose statements
reference interface fields but whose proofs route through the
existing `ModMul.*` theorems.

This achieves R6 Goal A — the interface stack carries the full
multiplier chain from `ControlledModAddImpl` (R4b) all the way to
the `MultiplyCircuitProperty` Shor input — even if the proofs are
currently fallback wrappers.

Real interface routing across the entire chain requires R5b'
(enrich `ControlledModAddImpl.clean` bundle with per-position
conjuncts) and replaying the funext-style proofs of
`sqir_modmult_step_state_eq` and downstream theorems.  All of that
work would replace the wrapper proofs without changing the
statements below. -/

namespace ModMul

open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)

theorem circuitFamily_modMulImpl_via_interfaces
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    ModMulImpl a N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits) :=
  circuitFamily_modMulImpl a ainv N bits hbits hN_ge_2 hN hN2 h_inv

theorem satisfiesMultiplyCircuitProperty_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    MultiplyCircuitProperty a N bits (ancillaWidth bits)
      (Gate.toUCom (totalDim bits) (gateMCP bits N a ainv)) :=
  satisfiesMultiplyCircuitProperty bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

end ModMul

/-- **Final R6i certification**: the existing SQIR/Cuccaro instance
of `VerifiedModMulFamily`, with the same conclusion as
`verifiedSqirModMulFamily` but with each field provided by an
interface-routed `_via_interfaces` theorem.

Currently equals `verifiedSqirModMulFamily` by `rfl` because all the
`_via_interfaces` components are fallback wrappers around the
original `ModMul.*` theorems. -/
noncomputable def verifiedSqirModMulFamily_via_interfaces
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    VerifiedModMulFamily a N bits (ModMul.ancillaWidth bits) where
  family := ModMul.circuitFamily a ainv N bits
  mmi := ModMul.circuitFamily_modMulImpl_via_interfaces a ainv N bits
      h_sizing.1 h_N_ge_2 h_sizing.2.1 h_sizing.2.2 h_inv
  wellTyped := ModMul.circuitFamily_wellTyped a ainv N bits
      h_sizing.1 (by omega) h_sizing.2.1 h_sizing.2.2

theorem verifiedSqirModMulFamily_via_interfaces_eq
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    verifiedSqirModMulFamily a ainv N bits h_sizing h_N_ge_2 h_inv
      = verifiedSqirModMulFamily_via_interfaces a ainv N bits
          h_sizing h_N_ge_2 h_inv := rfl

/-! ## R6i-real: SQIR/Cuccaro family certified through real interfaces

These theorems certify `ModMul.circuitFamily` as a `ModMulImpl`
through the R6h-real `MultiplyCircuitProperty` bridge (the genuinely
interface-routed one), and package the result as a
`VerifiedModMulFamily`.

* `ModMul.satisfiesMultiplyCircuitProperty_real_via_interfaces`:
  layout-form `MultiplyCircuitProperty` for `gateMCP`, derived from
  `MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces`
  (R6h-real) via def-eq.
* `ModMul.circuitFamily_modMulImpl_real_via_interfaces`:
  the per-iterate `ModMulImpl` proof, replaying the structure of
  `f_modmult_circuit_verified_bits_MMI` (SQIRModMult.lean:2639) but
  using `MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces`
  in place of `sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty`.
* `verifiedSqirModMulFamily_real_via_interfaces`: the `VerifiedModMulFamily`
  package using the real MMI.
* `verifiedSqirModMulFamily_real_via_interfaces_eq` (rfl): the real
  package equals the existing `verifiedSqirModMulFamily`.

None of these calls
`sqir_modmult_MCP_gate_satisfies_MultiplyCircuitProperty`,
`ModMul.circuitFamily_modMulImpl`,
`f_modmult_circuit_verified_bits_MMI`, or any other forbidden
theorem.  Allowed deps: `MultiplyCircuitProperty_of_mod` (mod-up
lift), `pow_iter_inverse_mod` (arithmetic), and the R6h-real
`MCPAdapter` theorem. -/

namespace ModMul

open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)

theorem satisfiesMultiplyCircuitProperty_real_via_interfaces
    (bits N a ainv : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_ainv_le : ainv ≤ N) (h_inv : (a * ainv) % N = 1) :
    MultiplyCircuitProperty a N bits (ancillaWidth bits)
      (Gate.toUCom (totalDim bits) (gateMCP bits N a ainv)) :=
  MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces
    bits N a ainv hbits hN_pos hN hN2 h_ainv_le h_inv

theorem circuitFamily_modMulImpl_real_via_interfaces
    (a ainv N bits : Nat) (hbits : 1 ≤ bits) (hN_ge_2 : 2 ≤ N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (h_inv : a * ainv % N = 1) :
    ModMulImpl a N bits (ancillaWidth bits)
      (circuitFamily a ainv N bits) := by
  intro i
  unfold circuitFamily f_modmult_circuit_verified_bits
  have hN_pos : 0 < N := by omega
  have h_ainv_lt_N : (ainv^(2^i)) % N < N := Nat.mod_lt _ hN_pos
  have h_ainv_le : (ainv^(2^i)) % N ≤ N := Nat.le_of_lt h_ainv_lt_N
  have h_inv_i : ((a^(2^i)) % N) * ((ainv^(2^i)) % N) % N = 1 :=
    pow_iter_inverse_mod a ainv N i hN_ge_2 h_inv
  apply MultiplyCircuitProperty_of_mod hN_pos
  -- Use the R6h-real MCP bridge directly (def-eq through layout projections
  -- handles the form alignment).
  exact MCPAdapter.sqirCuccaro_satisfiesMultiplyCircuitProperty_real_via_interfaces
    bits N ((a^(2^i)) % N) ((ainv^(2^i)) % N)
    hbits hN_pos hN hN2 h_ainv_le h_inv_i

end ModMul

/-- **Final R6i-real**: the existing SQIR/Cuccaro instance of
`VerifiedModMulFamily`, with the MMI field provided by the
real-interface-routed theorem (R6i-real), which in turn routes
through R6h-real, R6g-real, R6f-real, R6e, R6c, R6b, R5b'/R5c/R5b
aliases.

Currently equals `verifiedSqirModMulFamily` and the R6i fallback
package by `rfl` — the change is only in *which proof certifies*
the MMI field. -/
noncomputable def verifiedSqirModMulFamily_real_via_interfaces
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    VerifiedModMulFamily a N bits (ModMul.ancillaWidth bits) where
  family := ModMul.circuitFamily a ainv N bits
  mmi := ModMul.circuitFamily_modMulImpl_real_via_interfaces a ainv N bits
      h_sizing.1 h_N_ge_2 h_sizing.2.1 h_sizing.2.2 h_inv
  wellTyped := ModMul.circuitFamily_wellTyped a ainv N bits
      h_sizing.1 (by omega) h_sizing.2.1 h_sizing.2.2

theorem verifiedSqirModMulFamily_real_via_interfaces_eq
    (a ainv N bits : Nat) (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    verifiedSqirModMulFamily a ainv N bits h_sizing h_N_ge_2 h_inv
      = verifiedSqirModMulFamily_real_via_interfaces a ainv N bits
          h_sizing h_N_ge_2 h_inv := rfl

/-- **Public consumer**: the generic Shor success-probability bound
applied to the real-interface-routed SQIR/Cuccaro family.  This is
the cleanest demonstration that the new interface-routed proof chain
plugs into `VerifiedModMulFamily.shorCorrect` without changing any
top-level theorem. -/
theorem correct_general_via_real_interface
    {a N bits : Nat} (ainv : Nat)
    (r m : Nat) (h_setting : ShorSetting a r N m bits)
    (h_sizing : CircuitSizing N bits)
    (h_N_ge_2 : 2 ≤ N) (h_inv : a * ainv % N = 1) :
    FormalRV.SQIRPort.probability_of_success a r N m bits
        (ModMul.ancillaWidth bits)
        (verifiedSqirModMulFamily_real_via_interfaces a ainv N bits
          h_sizing h_N_ge_2 h_inv).family
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ)^4 :=
  VerifiedModMulFamily.shorCorrect
    (verifiedSqirModMulFamily_real_via_interfaces a ainv N bits
      h_sizing h_N_ge_2 h_inv) r m h_setting

/-! ## Windowed/lookup backend (Phase R7)

`VerifiedShor.Windowed` defines pure arithmetic specs and interface
structures for a windowed-lookup modular-multiplier backend.

R7 scope (this phase):
* R7a (inspection): the existing `Gate` IR (I/X/CX/CCX/seq) is
  expressive enough for windowed-lookup arithmetic without
  measurement.  Recommendation: interface-first, circuit deferred.
* R7b (arithmetic specs): `windowValue`, `numWindows`, `tableValue`,
  `windowedStepSpec` + bound lemmas.
* R7c (interfaces): `WindowLayout`, `LookupTableImpl`,
  `WindowedLookupModMulSpec`.

R7d (toy circuit) and R7e (`WindowedLookupModMulImpl →
VerifiedModMulFamily`) are reserved for future phases. -/

namespace Windowed

open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)

/-! ### Pure arithmetic specs (R7b) -/

/-- The k-th w-bit window of `m`: bits `[k*w, (k+1)*w)` interpreted
as a `Nat` in `[0, 2^w)`. -/
def windowValue (m w k : Nat) : Nat := (m / 2^(k * w)) % 2^w

/-- Number of windows needed to cover `bits` bits with window size `w`.
For `w = 0`, returns `0` (degenerate). -/
def numWindows (bits w : Nat) : Nat :=
  if w = 0 then 0 else (bits + w - 1) / w

/-- Table value for window `k` and value `v`: `(a * 2^(k*w) * v) % N`.
Used as the precomputed lookup entry for the k-th window. -/
def tableValue (a N w k v : Nat) : Nat := (a * 2^(k * w) * v) % N

/-- One windowed-step accumulator update:
`(acc + tableValue a N w k v) % N`. -/
def windowedStepSpec (a N w k acc v : Nat) : Nat :=
  (acc + tableValue a N w k v) % N

/-! ### Arithmetic bound lemmas -/

theorem windowValue_lt (m w k : Nat) (_hw : 0 < w) :
    windowValue m w k < 2^w := by
  unfold windowValue
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem tableValue_lt_N (a N w k v : Nat) (hN_pos : 0 < N) :
    tableValue a N w k v < N := by
  unfold tableValue
  exact Nat.mod_lt _ hN_pos

theorem windowedStepSpec_lt_N (a N w k acc v : Nat) (hN_pos : 0 < N) :
    windowedStepSpec a N w k acc v < N := by
  unfold windowedStepSpec
  exact Nat.mod_lt _ hN_pos

theorem tableValue_zero (a N w k : Nat) :
    tableValue a N w k 0 = 0 := by
  unfold tableValue
  rw [Nat.mul_zero, Nat.zero_mod]

theorem windowedStepSpec_zero (a N w k acc : Nat) :
    windowedStepSpec a N w k acc 0 = acc % N := by
  unfold windowedStepSpec
  rw [tableValue_zero, Nat.add_zero]

/-- Window value at `k = 0` is `m % 2^w`. -/
theorem windowValue_zero (m w : Nat) :
    windowValue m w 0 = m % 2^w := by
  unfold windowValue
  simp

/-- A `0`-sized window decodes to `0`. -/
theorem windowValue_w_zero (m k : Nat) :
    windowValue m 0 k = 0 := by
  unfold windowValue
  simp [Nat.mod_one]

/-! ### Interface structures (R7c) -/

/-- **`WindowLayout`**: layout descriptor for the windowed register
arrangement.  Data-level only.

Future extensions (when circuit construction lands) may add fields
for window-bit positions, ancilla locations, and lookup table
registers. -/
structure WindowLayout where
  /-- Window size (number of multiplier bits per lookup step). -/
  windowSize : Nat
  /-- Number of windows as a function of the multiplier bit width. -/
  numWindows : Nat → Nat

/-- **`LookupTableImpl`**: a precomputed lookup table for windowed
modular multiplication.

`tableValue a N w k v` is the precomputed value `(a * 2^(k*w) * v) % N`.
`lookupCorrect` is the semantic field certifying the implementation
agrees with the arithmetic spec.

For R7c this is a pure data + correctness package; circuit-level
loading is deferred. -/
structure LookupTableImpl where
  /-- The table value function. -/
  tableValue : (a N w k v : Nat) → Nat
  /-- Agreement with the arithmetic spec `(a * 2^(k*w) * v) % N`. -/
  lookupCorrect :
    ∀ a N w k v, 0 < N → tableValue a N w k v = Windowed.tableValue a N w k v

/-- **`WindowedLookupModMulSpec`**: a *spec-level* windowed-lookup
modular-multiplier description.

For R7c we only require:
* `layout`: window descriptor.
* `table`: precomputed values agreeing with `tableValue`.
* `stepSpec`: an arithmetic-only correctness field — given window
  index `k`, current accumulator `acc < N`, and window value
  `v < 2^windowSize`, the next accumulator is `windowedStepSpec
  a N windowSize k acc v`.

This structure does NOT yet carry a circuit family.  R7d/R7e will
extend it (or introduce a `WindowedLookupModMulImpl` subclass) with
a `family` field once toy circuit construction is in place. -/
structure WindowedLookupModMulSpec (a N : Nat) where
  layout : WindowLayout
  table  : LookupTableImpl
  /-- Spec: applying the k-th windowed step with value `v` advances
  the accumulator by `tableValue a N w k v` modulo `N`. -/
  stepSpec :
    ∀ k acc v, 0 < N → acc < N → v < 2^layout.windowSize →
      ∃ acc', acc' = windowedStepSpec a N layout.windowSize k acc v

/-- **Identity `LookupTableImpl`**: uses `Windowed.tableValue` directly.
Demonstrates the structure is non-empty. -/
def identityLookupTable : LookupTableImpl where
  tableValue   := Windowed.tableValue
  lookupCorrect := fun _ _ _ _ _ _ => rfl

/-- **Trivial spec instance** at `windowSize = 1` for `(a, N)`.
Demonstrates the structure is inhabited; `stepSpec` is trivially
witnessed by `windowedStepSpec` itself. -/
def trivialSpec (a N : Nat) : WindowedLookupModMulSpec a N where
  layout := {
    windowSize := 1
    numWindows := fun bits => bits
  }
  table := identityLookupTable
  stepSpec := fun k acc v _ _ _ =>
    ⟨windowedStepSpec a N 1 k acc v, rfl⟩

/-! ### Future work skeleton (R7d/R7e)

A real `WindowedLookupModMulImpl` extending the spec with a circuit
family would look approximately like:

```
structure WindowedLookupModMulImpl (a N bits anc : Nat)
    extends WindowedLookupModMulSpec a N where
  family : Nat → FormalRV.SQIRPort.BaseUCom (bits + anc)
  familyCorrect : ...  -- ties the circuit family to stepSpec
```

The connection to `VerifiedModMulFamily` would be:

```
theorem WindowedLookupModMulImpl.toVerifiedModMulFamily
    {a N bits anc : Nat}
    (W : WindowedLookupModMulImpl a N bits anc) :
    VerifiedModMulFamily a N bits anc :=
  { family := W.family
  , mmi := ...  -- derived from familyCorrect + per-iterate spec
  , wellTyped := ...  -- circuit well-typedness
  }
```

Missing pieces for this connection:
* Toy lookup circuit construction (equality-test on w bits with
  CCX cascade + reversible flag uncomputation; `2^w` controlled
  modular-add applications composed in sequence).
* Proof that the circuit family realizes `MultiplyCircuitProperty`
  for `a^(2^i) mod N` at each QPE iterate (this requires linking
  the per-window step proof to the full per-iterate multiplication).

These are the next R7d/R7e targets. -/

/-! ### R7d: toy windowed-lookup case-3 selected-add (windowSize = 2)

A minimal **Route A** circuit-level demonstration that windowed-lookup
arithmetic fits in the existing `Gate` IR — combined with a
**Route B** interface for the spec-level correctness.

The CONCRETE `Gate` IR construction below shows that the existing
primitives (CCX + the R4b `ControlledModAdd.sqirCuccaroImpl.gate`)
are sufficient to express one case (v=3) of a windowSize=2 lookup
step.  This answers the R7a feasibility question definitively:
**no new primitive is needed**.

Circuit structure (for v=3, the simplest case):
1. `CCX b0Idx b1Idx flagIdx` — compute equality test:
   flag becomes (b0 AND b1), which is true iff v = 3.
2. `ControlledModAdd.sqirCuccaroImpl.gate bits N c_3 flagIdx` — the
   R4b mod-add gate, controlled by the equality flag.  Adds c_3
   (= `tableValue a N 2 k 3`) to target if flag is true; otherwise
   no-op.
3. `CCX b0Idx b1Idx flagIdx` — uncompute the equality flag.  b0 and
   b1 are above the mod-add workspace, so they're unchanged by
   step 2, and the same CCX inverts step 1.

For cases v=1, v=2, the analogous gate inserts X-flips around the
CCX cascade.  Generalizing to all 4 values yields the full
windowSize=2 lookup step.

**Soundness rule honored**: no sorry/admit/axiom.  The `def` lands
as a concrete `Gate` term; the correctness theorem is packaged at
the spec level (Route B) via `Window2LookupCase3Spec`.  A future
tick can land the full Lean proof of `case3Gate` against this spec
— the proof outline (which exists; see docstring on
`Window2LookupCase3Spec.gateCorrect`) requires a few `Framework.update`
commutation lemmas not yet in the public surface. -/

/-- One window step's selected-add gate for the v=3 case.
Concrete `Gate` IR term using only `CCX` + R4b's mod-add. -/
noncomputable def toyWindow2Case3Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 3
  Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
    (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
              (Gate.CCX b0Idx b1Idx flagIdx))

/-- Input encoding for the toy case-3 gate: SQIR/Cuccaro accumulator
encoding (with empty multiplier-input region) plus the two window
bits at `b0Idx`, `b1Idx`. -/
def toyWindow2Case3Input
    (acc : Nat) (b0Idx b1Idx : Nat) (b0 b1 : Bool) : Nat → Bool :=
  update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1

/-! ### Spec interface for windowSize=2 case 3 (Route B)

`Window2LookupCase3Spec` is the layer-1 contract for a selected-add
component covering the v=3 case of a windowSize=2 lookup step.

Any backend (the toy CCX-based gate above, or a future Gidney-AND,
QFT-adder, or QROM-based variant) can provide this contract by
implementing the gate field and proving the `case3Correct` field.

Once a `Window2LookupCase3Spec` instance lands, composing with the
analogous v=1, v=2 specs gives the full windowSize=2 lookup step.
Composing across windows k = 0 .. numWindows N 2 yields a windowed
multiplier suitable for `VerifiedModMulFamily` (R7e). -/
structure Window2LookupCase3Spec (a N : Nat) where
  /-- The gate constructor, parameterized by width and window index. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Correctness: when the window bits encode v = 3 (both true),
  the target advances by `tableValue a N 2 k 3`; else target
  unchanged.  The hypothesis set matches what the toy CCX-based
  construction would consume. -/
  case3Correct :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      cuccaro_target_val bits 2
          (Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
        = if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc

/-- Arithmetic helper: `tableValue` at the v=3 case unfolds to its
defining expression.  Useful for instantiating the spec. -/
theorem tableValue_window2_v3_eq (a N k : Nat) :
    tableValue a N 2 k 3 = (a * 2^(k * 2) * 3) % N := rfl

/-- Arithmetic helper: `windowedStepSpec` for v=3 equals
the target-decode formula. -/
theorem windowedStepSpec_window2_v3
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 3 = (acc + tableValue a N 2 k 3) % N := by
  unfold windowedStepSpec
  rfl

/-- **R7d' — toy case-3 selected-add correctness**.

The toy windowSize=2 case-3 gate satisfies the spec: when both
window bits are true (v = 3), the target accumulator advances by
`tableValue a N 2 k 3`; otherwise it is unchanged.

Proof route:
1. The outer CCX only updates `flagIdx` (< 2), which is outside the
   Cuccaro workspace.  By `cuccaro_target_val_update_outside_workspace`,
   the target value is invariant.
2. The inner CCX computes `update F0 flagIdx (b0 AND b1)` since
   `F0 flagIdx = false` (from the cuccaro_input_F at `flagIdx < 2`).
3. Updates at `b0Idx`, `b1Idx` (both above the workspace) commute
   with the mod-add (via `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`)
   and are invisible to `cuccaro_target_val` (via the outside-workspace
   lemma).
4. The remaining `Gate.applyNat (mod-add) (update (cuccaro_input_F ...) flagIdx ctrl)`
   is exactly the input shape `ControlledModAdd.clean_targetDecode`
   handles.

**No direct call to `sqir_style_controlledModAddConst_gate_clean`** —
the mod-add target is extracted through the R4b/R5b projection
`ControlledModAdd.clean_targetDecode`. -/
theorem toyWindow2Case3Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc := by
  -- Auxiliary facts.
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Convert the gate to SQIR-form (the mod-add is the only layout-coupled term).
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc
  simp only [Gate.applyNat_seq]
  -- Step 1: outer CCX is just an update at flagIdx, outside workspace.
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Step 2: compute the inner CCX result.
  rw [Gate.applyNat_CCX]
  -- Compute F0 reads at b0Idx, b1Idx, flagIdx.
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  -- xor false (b0 && b1) = b0 && b1.
  simp only [Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx update closest to cuccaro_input_F.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b0Idx, b1Idx updates outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Step 5: drop the outside-workspace updates from cuccaro_target_val.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Step 6: apply R4b/R5b clean_targetDecode (def-eq absorbs the layout-form).
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx (b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- **R7d' — spec implementation.**  Package
`toyWindow2Case3Gate` as a `Window2LookupCase3Spec` instance.
This demonstrates the case-3 selected-add backend satisfies the
spec contract; chaining with v=1 and v=2 specs (R7d'') produces a
full windowSize=2 lookup step. -/
noncomputable def toyWindow2Case3SpecImpl (a N : Nat) :
    Window2LookupCase3Spec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx
  case3Correct := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                      h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                      h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2Case3Gate_correct bits N a k acc flagIdx b0Idx b1Idx b0 b1
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ### R7d'' — cases v=1 and v=2

For v=1 (binary 01, b0=true b1=false) and v=2 (binary 10, b0=false
b1=true), the equality test requires X-normalization of the
relevant bit before the CCX cascade.

* v=1 gate: `X b1Idx ; CCX b0 b1 flag ; modAdd[flag] ; CCX b0 b1 flag ; X b1Idx`
  After the first X, b1 becomes `!b1` so the CCX computes
  `b0 ∧ !b1`, which is true iff (b0, b1) = (true, false), i.e. v=1.
* v=2 gate: symmetric with X on `b0Idx`.

Correctness proof mirrors v=3 with three extra rewriting steps:
1. Strip the outermost X (outside workspace at b0Idx or b1Idx) via
   `cuccaro_target_val_update_outside_workspace`.
2. Compute the inner X-flip's effect on the relevant bit
   (`F0 b1Idx = b1` so `! F0 b1Idx = !b1`).
3. Merge the double-update at the flipped bit position via
   `Framework.update_idem`. -/

/-- Arithmetic helper: `tableValue` for v=1. -/
theorem tableValue_window2_v1_eq (a N k : Nat) :
    tableValue a N 2 k 1 = (a * 2^(k * 2) * 1) % N := rfl

/-- Arithmetic helper: `tableValue` for v=2. -/
theorem tableValue_window2_v2_eq (a N k : Nat) :
    tableValue a N 2 k 2 = (a * 2^(k * 2) * 2) % N := rfl

/-- Arithmetic helper: `windowedStepSpec` for v=1. -/
theorem windowedStepSpec_window2_v1
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 1 = (acc + tableValue a N 2 k 1) % N := by
  unfold windowedStepSpec
  rfl

/-- Arithmetic helper: `windowedStepSpec` for v=2. -/
theorem windowedStepSpec_window2_v2
    (a N k acc : Nat) (_hN_pos : 0 < N) :
    windowedStepSpec a N 2 k acc 2 = (acc + tableValue a N 2 k 2) % N := by
  unfold windowedStepSpec
  rfl

/-- One window step's selected-add gate for the v=1 case
(binary 01).  X-normalizes b1 before/after the CCX cascade. -/
noncomputable def toyWindow2Case1Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 1
  Gate.seq (Gate.X b1Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b1Idx))))

/-- One window step's selected-add gate for the v=2 case
(binary 10).  X-normalizes b0 before/after the CCX cascade. -/
noncomputable def toyWindow2Case2Gate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 2
  Gate.seq (Gate.X b0Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (ControlledModAdd.sqirCuccaroImpl.gate bits N c flagIdx)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b0Idx))))

/-- **R7d'' — toy case-1 selected-add correctness.**

When v=1 (b0=true, b1=false), the target accumulator advances by
`tableValue a N 2 k 1`; otherwise unchanged.  Proof mirrors v=3
with the X-flip handling described above. -/
theorem toyWindow2Case1Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc
  simp only [Gate.applyNat_seq]
  -- Outermost X(b1Idx): outside workspace.
  rw [Gate.applyNat_X]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  -- Outer-second CCX: outside workspace (flagIdx).
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Compute the inner CCX result, factoring through the inner X(b1Idx).
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  -- F0 reads.  Here F0 = update (update G b0Idx b0) b1Idx b1; we
  -- compute its values at the three positions, and also at b1Idx
  -- *after* the X-flip — which is just !b1 by update_idem.
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- After the X-flip, the state at b1Idx is !b1; at b0Idx is b0; at flagIdx is false.
  rw [h_F0_b1]
  -- Now reads on (update F0 b1Idx (!b1)):
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b1Idx
        = !b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  -- Merge the double-update at b1Idx via update_idem.
  rw [FormalRV.Framework.update_idem]
  -- Now: update (update (update G b0Idx b0) b1Idx (!b1)) flagIdx (b0 && !b1)
  -- Reorder via update_comm to bring flagIdx update closest to G.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b0Idx, b1Idx updates outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx (!b1) _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Drop the outside-workspace updates from cuccaro_target_val.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx (!b1) _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Close via R4b clean_targetDecode.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx (b0 && !b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- **R7d'' — toy case-2 selected-add correctness.**

When v=2 (b0=false, b1=true), the target accumulator advances by
`tableValue a N 2 k 2`; otherwise unchanged.  Symmetric to v=1
with X on b0Idx. -/
theorem toyWindow2Case2Gate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if !b0 && b1 then (acc + tableValue a N 2 k 2) % N else acc := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change cuccaro_target_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = if !b0 && b1 then (acc + tableValue a N 2 k 2) % N else acc
  simp only [Gate.applyNat_seq]
  -- Outermost X(b0Idx): outside workspace.
  rw [Gate.applyNat_X]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  -- Outer-second CCX: outside workspace (flagIdx).
  rw [Gate.applyNat_CCX]
  rw [cuccaro_target_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Compute inner CCX result via inner X(b0Idx).
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  -- Reads on (update F0 b0Idx (!b0)):
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b0Idx
        = !b0 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  -- For the case-2 gate, the b0Idx update sequence is:
  -- update (update G b0Idx b0) b1Idx b1 -> (X) -> update (update (update G b0Idx b0) b1Idx b1) b0Idx (!b0)
  -- Reorder to bring the b0Idx (!b0) update to the right place:
  --   = update (update (update G b1Idx b1) b0Idx b0) b0Idx (!b0)   -- commute b1 and b0
  --   = update (update G b1Idx b1) b0Idx (!b0)                       -- update_idem
  -- Then update flagIdx ctrl on top, then commute.  Let's do it directly:
  -- The current expression after rw is:
  --   update (update (update (update G b0Idx b0) b1Idx b1) b0Idx (!b0)) flagIdx (!b0 && b1)
  -- First commute: swap the outer b0Idx (!b0) with b1Idx b1:
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  -- Now: update (update (update (update G b0Idx b0) b0Idx (!b0)) b1Idx b1) flagIdx ...
  -- Merge the double-update at b0Idx:
  rw [FormalRV.Framework.update_idem]
  -- Now: update (update (update G b1Idx b1) b0Idx (!b0)) flagIdx (!b0 && b1)
  -- Wait — the update_idem merged the b0Idx updates that were at the
  -- innermost (b0Idx b0) and the middle (b0Idx (!b0)) wrapping the
  -- swapped b1Idx update.  So after the swap+idem, the order is:
  --   update (update (update G b1Idx b1) b0Idx (!b0)) flagIdx ctrl
  -- The outermost update under flagIdx is at b0Idx, not b1Idx.
  -- So we must first swap flagIdx past b0Idx, then past b1Idx.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  -- Push b0Idx, b1Idx updates outside the mod-add.  Outermost is b0Idx.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx (!b0) _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  -- Drop the outside-workspace updates.  Outermost is b0Idx.
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx (!b0) _ h_b0_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  -- Close via R4b clean_targetDecode.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx (!b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-! ### R7d''' — composed windowSize=2 selected-add gate

The composed gate runs all three nonzero-case selected-add gates in
sequence.  For any input window value `v ∈ {0, 1, 2, 3}`, exactly
one case fires (or none, for v=0), advancing the target accumulator
by `tableValue a N 2 k v` modulo `N`. -/

/-- Composed windowSize=2 selected-add gate: case1 ; case2 ; case3. -/
noncomputable def toyWindow2SelectedAddGate
    (bits N a k : Nat) (flagIdx b0Idx b1Idx : Nat) : Gate :=
  Gate.seq (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
    (Gate.seq (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx))

/-- Arithmetic helper: `windowedStepSpec` for v=0 reduces to `acc`
when `acc < N`. -/
theorem windowedStepSpec_window2_v0
    (a N k acc : Nat) (_hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpec a N 2 k acc 0 = acc := by
  unfold windowedStepSpec
  rw [tableValue_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt hacc

/-! ### R7d^v — case-3 gate window-bit preservation helpers

These per-position helpers prove that `toyWindow2Case3Gate` preserves
the values at the external multiplier register positions `b0Idx`
and `b1Idx`.  They are the cleanest "outside workspace" cases and
the first step toward the full state-equality theorem
`toyWindow2Case3Gate_state_eq` (deferred to a follow-up tick).

Proof pattern (used by both):
1. Unfold the gate's 3-gate seq structure.
2. `change` to convert layout-form mod-add to SQIR-form (def-eq).
3. `simp only [Gate.applyNat_seq]` to expose the nested `Gate.applyNat`s.
4. Peel the outer CCX via `Gate.applyNat_CCX` + `update_neq` (direction:
   `h_bX_ne_flag`, since the pattern is `update _ flagIdx _ bXIdx`).
5. Peel the inner CCX via `Gate.applyNat_CCX`.
6. Substitute input reads at the three positions.
7. Simplify `xor false (true && true) = true`.
8. Reorder updates via `update_comm` (twice) to bring flagIdx innermost.
9. Push b0Idx/b1Idx outside the mod-add via
   `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`.
10. Finish with `update_eq`. -/

/-- The case-3 gate preserves the value `true` at the external
multiplier register position `b0Idx`. -/
theorem toyWindow2Case3Gate_preserves_b0Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) b0Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
      = true
  simp only [Gate.applyNat_seq]
  -- Peel outer CCX (writes at flagIdx; we read at b0Idx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  -- Peel inner CCX.
  rw [Gate.applyNat_CCX]
  -- Compute input's value at the three positions.
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  -- xor false (true && true) = true.
  simp only [Bool.and_self, Bool.false_xor]
  -- Reorder updates: bring flagIdx update innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- State is now: update (update (update G flagIdx true) b0Idx true) b1Idx true.
  -- Push b1Idx (outermost) outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  -- Read at b0Idx through outer b1Idx update (b0Idx ≠ b1Idx).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  -- Push b0Idx outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  -- Read at b0Idx via update_eq.
  rw [FormalRV.Framework.update_eq]

/-- The case-3 gate restores the equality flag at `flagIdx` to its
original value `false` after the full CCX/modadd/CCX cycle.

The proof tracks the state through all three stages:
1. After the inner CCX, flagIdx is set to `xor false (true && true) = true`.
2. After the mod-add, flagIdx is preserved at `true` (via R4b's
   `clean_controlPreserved`).
3. After the outer CCX, flagIdx becomes `xor true (true && true) = false`. -/
theorem toyWindow2Case3Gate_restores_flagIdx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Helper: the input's values at b0Idx, b1Idx, flagIdx.
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Inner state values (after mod-add ∘ CCX1 applied to input).
  -- We prove (a) MA b0Idx = true, (b) MA b1Idx = true, (c) MA flagIdx = true.
  -- Each follows the same skeleton as in `_preserves_b0Idx`.
  -- Set the inner expression abbreviation isn't ergonomic with simp/rw,
  -- so we inline each subproof.
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        b0Idx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        b1Idx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_flag :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
        flagIdx = true := by
    rw [Gate.applyNat_CCX]
    rw [h_input_b0, h_input_b1, h_input_flag]
    simp only [Bool.and_self, Bool.false_xor]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    -- Goal: Gate.applyNat (...) (update (cuccaro_input_F 2 false 0 acc) flagIdx true) flagIdx = true
    -- This is R4b clean_controlPreserved on sqirCuccaroImpl.
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 3) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  -- Combine.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide

/-- The case-3 gate preserves the value `true` at the external
multiplier register position `b1Idx`.  Symmetric to
`_preserves_b0Idx`. -/
theorem toyWindow2Case3Gate_preserves_b1Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) b1Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- State: update (update (update G flagIdx true) b0Idx true) b1Idx true.
  -- Push b1Idx (outermost) outside the mod-add, then read via update_eq.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_eq]

/-! ### R7d^vii — scalar Cuccaro-workspace helpers for case-3 gate

These three per-position helpers prove that the case-3 toy gate
restores the internal Cuccaro-workspace scalar positions:

* Position 1 (Cuccaro dirty flag): `false`.
* Position 2 (Cuccaro carry-in): `false`.
* Position `2 + 2*bits` (top carry): `false`.

Each proof follows the same skeleton as `_preserves_b0Idx` /
`_preserves_b1Idx`, but the finishing rule is:
* `clean_flagFalse` for position 1.
* `sqir_style_controlledModAddConst_gate_carry_in_restored` for
  position 2 (the carry-in restore theorem is not in the R4b
  bundle, so we use the SQIR theorem directly — it's NOT in the
  forbidden list).
* `clean_topCarryFalse` for position `2 + 2*bits`. -/

/-- The case-3 gate restores the internal Cuccaro dirty flag at
position 1 to `false`. -/
theorem toyWindow2Case3Gate_internalFlagFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
  have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
  have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 1
      = false
  simp only [Gate.applyNat_seq]
  -- Peel outer CCX2 (writes at flagIdx; we read at 1, ≠ flagIdx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  -- Peel inner CCX1.
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b1Idx outside mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  -- Push b0Idx outside mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  -- Apply clean_flagFalse on sqirCuccaroImpl with control = true.
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-3 gate restores the Cuccaro carry-in at position 2 to
`false`. -/
theorem toyWindow2Case3Gate_carryInRestored
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  -- Apply the SQIR carry_in_restored theorem (NOT in the forbidden list).
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- The case-3 gate restores the Cuccaro top carry at position
`2 + 2*bits` to `false`. -/
theorem toyWindow2Case3Gate_topCarryFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * bits) = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_tc_ne_flag : (2 + 2 * bits : Nat) ≠ flagIdx := by omega
  have h_tc_ne_b0 : (2 + 2 * bits : Nat) ≠ b0Idx := by omega
  have h_tc_ne_b1 : (2 + 2 * bits : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) (2 + 2 * bits)
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_flag]
  rw [Gate.applyNat_CCX]
  have h_input_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_input_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_input_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_input_b0, h_input_b1, h_input_flag]
  simp only [Bool.and_self, Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_tc_ne_b0]
  -- Apply clean_topCarryFalse on sqirCuccaroImpl with control = true.
  exact ControlledModAdd.clean_topCarryFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-! ### R7d^viii: target-bit and read-bit extraction for case-3 gate

These per-position helpers extract individual target/read register bits
from the case-3 gate's output, via the converse decoder lemmas
`cuccaro_target_val_eq_implies_bits_match` and
`cuccaro_read_val_eq_implies_bits_match`.

For the target-bit helper we instantiate `toyWindow2Case3Gate_correct`
at `b0 = b1 = true` (case 3 firing condition) to get the
target_val decode equality, then apply the converse.

For the read-bit helper we first prove a `_readVal` companion (mirroring
`toyWindow2Case3Gate_correct` but routing through `clean_readZero`
instead of `clean_targetDecode`), then apply the converse at `S = 0`.

**No direct call to `sqir_style_controlledModAddConst_gate_clean`** —
the mod-add target/read are extracted through the R4b/R5b projections
`ControlledModAdd.clean_targetDecode` and `ControlledModAdd.clean_readZero`. -/

/-- The case-3 gate leaves the Cuccaro read register at `0` after the
full sequence (independent of the window bits `b0`, `b1`).

Proof mirrors `toyWindow2Case3Gate_correct` but uses
`cuccaro_read_val_update_outside_workspace` for the outside-workspace
invariance steps and `ControlledModAdd.clean_readZero` at the finish. -/
theorem toyWindow2Case3Gate_readVal
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_read_val bits 2
        (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  -- Auxiliary facts (mirror toyWindow2Case3Gate_correct).
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- Convert the gate to SQIR-form.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  -- Step 1: outer CCX is just an update at flagIdx, outside workspace.
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  -- Step 2: compute the inner CCX result.
  rw [Gate.applyNat_CCX]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  -- xor false (b0 && b1) = b0 && b1.
  simp only [Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx update closest to cuccaro_input_F.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b0Idx, b1Idx updates outside the mod-add.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  -- Step 5: drop the outside-workspace updates from cuccaro_read_val.
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  -- Step 6: apply R4b/R5b clean_readZero.
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 3) acc flagIdx (b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-3 gate's output at target-bit position `2 + 2*i + 1`
(for `i < bits`) equals the `i`-th bit of `(acc + tableValue a N 2 k 3) % N`.

Proof: instantiate `toyWindow2Case3Gate_correct` at `b0 = b1 = true`
(case 3 firing condition) to get the target_val decode equality, then
apply the converse decoder `cuccaro_target_val_eq_implies_bits_match`.

This is the bit-level analog of `sqir_modmult_step_target_bit`. -/
theorem toyWindow2Case3Gate_targetBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 3) % N).testBit i := by
  have h_correct := toyWindow2Case3Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  -- h_correct: cuccaro_target_val ... = if true && true then ... else acc
  -- Reduce to: cuccaro_target_val ... = (acc + tableValue) % N.
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx true true))
        = (acc + tableValue a N 2 k 3) % N := by
    simpa using h_correct
  -- Bound check for the converse.
  have h_acc'_lt_N : (acc + tableValue a N 2 k 3) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 3) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  -- Apply the converse decoder.
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- The case-3 gate's output at read-bit position `2 + 2*i + 2`
(for `i < bits`) equals `false`.

Proof: use `toyWindow2Case3Gate_readVal` to get the read_val = 0
equality, then apply the converse decoder
`cuccaro_read_val_eq_implies_bits_match` at `S = 0`; finish with
`Nat.zero_testBit`.

This is the bit-level analog of `sqir_modmult_step_read_bit`. -/
theorem toyWindow2Case3Gate_readBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case3Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]

/-! ### R7d^ix: above-layout helper for case-3 gate

For positions `q ≥ 2 + 2*bits + 1` distinct from `b0Idx`, `b1Idx`,
`flagIdx`, the case-3 gate leaves `q` at `false` (its input value).

Proof strategy mirrors the SQIRModMult `sqir_modmult_step_at_untouched_pos`
trick: at q the input is `false`, so `update input q false = input` (no-op).
By the SQIR commute lemma, the mod-add commutes with this trivial update,
yielding `applyNat mod-add input q = false` directly.

The CCX layers also commute with the q-update (q ∉ {b0Idx, b1Idx, flagIdx}),
so the full gate's output at q equals the input's value at q, which is
false by `cuccaro_input_F_above_eq_false`. -/

/-- The case-3 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`) that is distinct from the
window bits `b0Idx`/`b1Idx` and the lookup equality flag `flagIdx`. -/
theorem toyWindow2Case3Gate_aboveLayoutFalse
    (bits N a k acc flagIdx b0Idx b1Idx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (hq_above : 2 + 2 * bits + 1 ≤ q)
    (hq_ne_b0 : q ≠ b0Idx) (hq_ne_b1 : q ≠ b1Idx) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true) q = false := by
  -- Auxiliary facts.
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  -- Convert the gate to SQIR-form.
  unfold toyWindow2Case3Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) q
      = false
  simp only [Gate.applyNat_seq]
  -- Step 1: peel the outer CCX (q ≠ flagIdx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  -- Step 2: peel the inner CCX.
  rw [Gate.applyNat_CCX]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  have h_F0_flag :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F0_b0, h_F0_b1, h_F0_flag]
  simp only [Bool.and_self, Bool.false_xor]
  -- Step 3: reorder updates to bring flagIdx innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Step 4: push b1Idx, b0Idx updates outside the mod-add and read through.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 3) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  -- Goal: Gate.applyNat (mod-add) (update F flagIdx true) q = false.
  -- Use the commute trick: input at q is false, so mod-add output at q is false.
  have h_input_q :
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
    exact cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_in_eq :
      update (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q false
        = update (cuccaro_input_F 2 false 0 acc) flagIdx true := by
    -- Cannot use `rw [show false = (...) q from h_input_q.symm]` here because
    -- `cuccaro_input_F 2 false 0 acc` contains a `false` literal that would
    -- be hit by the rewrite.  Use funext instead.
    funext p
    by_cases hpq : p = q
    · subst hpq
      rw [FormalRV.Framework.update_eq]
      exact h_input_q.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hpq]
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 3) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-! ### R7d^x: full state equality for case-3 gate

Funext-assembly theorem combining all nine per-position helpers
(R7d^v through R7d^ix).  This is the compositional building block
needed for the eventual `toyWindow2SelectedAddGate_correct`. -/

/-- **Full state equality for the case-3 selected-add gate.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx true true`,
the case-3 gate produces exactly
`toyWindow2Case3Input ((acc + tableValue a N 2 k 3) % N) b0Idx b1Idx true true`.

The accumulator advances by `tableValue a N 2 k 3` (mod N), the
two window bits remain `true`, the equality flag is restored, and
the entire SQIR/Cuccaro workspace is restored to `0` (carry-in,
internal flag, read register, top carry).

Proof: `funext q`, case-split on `q`'s position class (b0Idx,
b1Idx, flagIdx, above-layout, scalar workspace, parametric
target/read bit), dispatch each case to the appropriate R7d^v
through R7d^ix helper.  The proof mirrors `sqir_modmult_step_state_eq`
from SQIRModMult.lean but is parameterized over `b0Idx`/`b1Idx`/
`flagIdx` rather than the SQIR multiplier control index. -/
theorem toyWindow2Case3Gate_state_eq
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 3) % N)
          b0Idx b1Idx true true := by
  funext q
  set acc' := (acc + tableValue a N 2 k 3) % N with hacc'_def
  have hacc'_lt_N : acc' < N := Nat.mod_lt _ hN_pos
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  -- From `flagIdx < 2 ∧ flagIdx ≠ 1`, `flagIdx = 0`.
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Case on q = b1Idx.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [toyWindow2Case3Gate_preserves_b1Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- Case on q = b0Idx (q ≠ b1Idx).
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [toyWindow2Case3Gate_preserves_b0Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Case on q = flagIdx (q ≠ b1Idx, q ≠ b0Idx).
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    rw [toyWindow2Case3Gate_restores_flagIdx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Now q ≠ b0Idx, q ≠ b1Idx, q ≠ flagIdx.
  -- Simplify the RHS to `cuccaro_input_F 2 false 0 acc' q`.
  have h_rhs :
      toyWindow2Case3Input acc' b0Idx b1Idx true true q
        = cuccaro_input_F 2 false 0 acc' q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  -- Case on q ≥ 2 + 2*bits + 1 (above layout).
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [toyWindow2Case3Gate_aboveLayoutFalse bits N a k acc flagIdx b0Idx b1Idx q
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          hq_above hq_b0 hq_b1 hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc' q hq_above hacc'_lt).symm
  push_neg at hq_above
  -- Now q < 2 + 2*bits + 1.
  -- Case q = 2 (carry-in).
  by_cases hq_2 : q = 2
  · subst hq_2
    rw [toyWindow2Case3Gate_carryInRestored bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
  -- Case q = 1 (internal Cuccaro flag).
  by_cases hq_1 : q = 1
  · subst hq_1
    rw [toyWindow2Case3Gate_internalFlagFalse bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  -- Case q = 0 is excluded since q ≠ flagIdx = 0.
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  -- Now q ≥ 3, q ≤ 2 + 2*bits.  Parity dispatch.
  by_cases h_q_odd : q % 2 = 1
  · -- Target bit: q = 2 + 2*((q-3)/2) + 1.
    have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    rw [toyWindow2Case3Gate_targetBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 3) / 2) hi_lt]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
  · -- Read bit: q = 2 + 2*((q-4)/2) + 2.
    have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    rw [toyWindow2Case3Gate_readBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 4) / 2) hi_lt]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
    exact (Nat.zero_testBit _).symm

/-! ### R7d^xi: case-1 read-value companion + full state equality

For the case-1 read-bit dispatch we need a companion theorem to
`toyWindow2Case1Gate_correct` proving the Cuccaro read register
remains 0 after the full case-1 gate (regardless of b0/b1).
Mirrors the case-1 `_correct` proof structurally but finishes
through `ControlledModAdd.clean_readZero` instead of
`clean_targetDecode`.

The full state-equality theorem then dispatches each q-position
inline.  We don't add separate per-position helpers (as for case
3); instead the dispatch is inlined in `_state_eq` to keep the
total line count bounded.  The X-flip on `b1Idx` is handled
specially in the q = b1Idx branch; for other q, the X-flips peel
trivially via `update_neq`. -/

/-- The case-1 gate leaves the Cuccaro read register at `0` after
the full sequence (independent of the window bits `b0`, `b1`).
Mirrors `toyWindow2Case1Gate_correct` structurally but routes
through `clean_readZero`. -/
theorem toyWindow2Case1Gate_readVal
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_read_val bits 2
        (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) b1Idx
        = !b1 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b1Idx (!b1) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx (!b1) _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx (!b1) _ h_b1_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx b0 _ h_b0_out]
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx (b0 && !b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-1 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`) that is distinct from the
window bits `b0Idx`/`b1Idx` and the lookup equality flag `flagIdx`.
Mirrors `toyWindow2Case3Gate_aboveLayoutFalse` with two extra
`Gate.applyNat_X` peelings for the X-flip layers. -/
theorem toyWindow2Case1Gate_aboveLayoutFalse
    (bits N a k acc flagIdx b0Idx b1Idx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (hq_above : 2 + 2 * bits + 1 ≤ q)
    (hq_ne_b0 : q ≠ b0Idx) (hq_ne_b1 : q ≠ b1Idx) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) q = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) q
      = false
  simp only [Gate.applyNat_seq]
  -- Peel outer X (X2, last applied): writes b1Idx.
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  -- Peel outer CCX (C2): writes flagIdx.
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  -- Peel inner CCX (C1) and compute its action.
  rw [Gate.applyNat_CCX]
  -- Peel inner X (X1): writes b1Idx.
  rw [Gate.applyNat_X]
  -- Substitute input reads.
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  -- Merge the double update on b1Idx via update_idem.
  rw [FormalRV.Framework.update_idem]
  -- Reorder updates to bring flagIdx innermost.
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  -- Push b1Idx, b0Idx outside mod-add and read through.
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  -- Now finish via the commute trick at q (same as case-3 aboveLayoutFalse).
  have h_input_q :
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
    exact cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_in_eq :
      update (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q false
        = update (cuccaro_input_F 2 false 0 acc) flagIdx true := by
    funext p
    by_cases hpq : p = q
    · subst hpq
      rw [FormalRV.Framework.update_eq]
      exact h_input_q.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hpq]
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 1) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-! ### R7d^xi: case-1 per-position helpers (continued)

Following the case-3 skeleton (R7d^v–R7d^ix), case 1 needs analogous
per-position helpers.  Most adaptations require only that we add an
outer `Gate.applyNat_X` peel layer (for the X2 = `Gate.X b1Idx` applied
last) and handle the X1 = `Gate.X b1Idx` applied first.  For positions
q ≠ b1Idx, both X-flips peel via `update_neq`; the inner CCX/mod-add
reasoning then mirrors the case-3 helper.

The exception is q = b1Idx itself: the X-flips give net !(!false) = false. -/

/-- Case-1 preserves the value `true` at the window-0 bit position
`b0Idx`. -/
theorem toyWindow2Case1Gate_preserves_b0Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) b0Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) b0Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_eq]

/-- Case-1 gate's output at target-bit position `2 + 2*i + 1`
(for `i < bits`) equals the `i`-th bit of `(acc + tableValue a N 2 k 1) % N`.
Derived from `toyWindow2Case1Gate_correct` + bits_match converse. -/
theorem toyWindow2Case1Gate_targetBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 1) % N).testBit i := by
  have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    true false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx true false))
        = (acc + tableValue a N 2 k 1) % N := by
    simpa using h_correct
  have h_acc'_lt_N : (acc + tableValue a N 2 k 1) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 1) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- Case-1 gate's output at read-bit position `2 + 2*i + 2`
(for `i < bits`) equals `false`. -/
theorem toyWindow2Case1Gate_readBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    true false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]

/-! ### R7d^xi^b — case-1 b1Idx preservation

The case-1 gate's outer X-flip layers (X b1Idx applied first AND last)
make the b1Idx-preservation proof more subtle than the case-3 analog.
We use a layered peel-and-prove pattern:

1. Peel the final X (X2): reduces goal to proving the value at b1Idx
   just before X2 is `true`.
2. Peel the second CCX (C2): writes only flagIdx, so reading at b1Idx
   passes through via `update_neq`.
3. Use the SQIR commute lemma at b1Idx (which is outside the workspace,
   ≠ 1, ≠ flagIdx) to show the mod-add preserves the value at b1Idx.
4. Prove the value at b1Idx after `C1 ∘ X1` is `true`: peel C1 (writes
   flagIdx), peel X1 (flips b1Idx from `false` to `true`).

The key trick is `set state := (CCX ∘ X) input`-style abstraction
before invoking the commute lemma — this avoids the unification
failures from R7d^xi. -/

/-- Case-1 preserves the value `false` at the window-1 bit position
`b1Idx`. The X-flips give net !(!false) = false. -/
theorem toyWindow2Case1Gate_preserves_b1Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) b1Idx = false := by
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  -- Step 1: unfold to SQIR form.
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) b1Idx
      = false
  simp only [Gate.applyNat_seq]
  -- Step 2: peel the outermost X (X2 applied last in applyNat order).
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_eq]
  -- Goal: !((applyNat C2 (applyNat M (applyNat C1 (applyNat X1 input)))) b1Idx) = false
  -- Step 3: peel C2 (writes flagIdx ≠ b1Idx).
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
  -- Goal: !((applyNat M (applyNat C1 (applyNat X1 input))) b1Idx) = false
  -- Step 4: prove the inner state at b1Idx equals true.
  have h_state_b1 :
      Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)) b1Idx
        = true := by
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    -- Goal: !((update (update F b0Idx true) b1Idx false) b1Idx) = true
    rw [FormalRV.Framework.update_eq]
    -- Goal: !false = true
    rfl
  -- Step 5: abstract the inner state.
  set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.applyNat (Gate.X b1Idx)
                    (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false))
    with hstate_def
  -- h_state_b1: state b1Idx = true.
  -- Show: update state b1Idx true = state (no-op update).
  have h_in_eq : update state b1Idx true = state := by
    funext p
    by_cases hp : p = b1Idx
    · subst hp
      rw [FormalRV.Framework.update_eq]
      exact h_state_b1.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  -- Use the SQIR commute lemma at b1Idx with v = true.
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 1) flagIdx b1Idx true state
      h_b1_out h_b1_ne_one h_b1_ne_flag
  -- h_commute : applyNat M (update state b1Idx true) = update (applyNat M state) b1Idx true
  rw [h_in_eq] at h_commute
  -- h_commute : applyNat M state = update (applyNat M state) b1Idx true
  have h_at := congr_fun h_commute b1Idx
  rw [FormalRV.Framework.update_eq] at h_at
  -- h_at : (applyNat M state) b1Idx = true
  rw [h_at]
  -- Goal: !true = false.
  rfl

/-! ### R7d^xi^c — remaining case-1 scalar helpers

Three helpers needed for the case-1 state_eq assembly:
- `_internalFlagFalse` (position 1, finishes through `clean_flagFalse`).
- `_carryInRestored` (position 2, finishes through
  `sqir_style_controlledModAddConst_gate_carry_in_restored`).
- `_restores_flagIdx` (flagIdx, three inner h_MA_* haves + outer
  C2 dispatch, mirrors case-3 with X1/X2 layers + `update_idem`). -/

/-- The case-1 gate forces the Cuccaro internal flag at position 1
to `false` after the full sequence. -/
theorem toyWindow2Case1Gate_internalFlagFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
  have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
  have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) 1
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 1) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-1 gate restores the Cuccaro carry-in at position 2 to
`false` after the full sequence. -/
theorem toyWindow2Case1Gate_carryInRestored
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  rw [h_F0_b1]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 1) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- The case-1 gate restores the external equality flag at `flagIdx`
to its original value `false` after the full sequence.

Proof mirrors case-3's `_restores_flagIdx` with the addition of X1/X2
peelings and a single `update_idem` merge step. -/
theorem toyWindow2Case1Gate_restores_flagIdx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  -- Input read at b1Idx (used to substitute the X1's !input b1Idx).
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  -- Post-X1 reads at b0Idx, b1Idx, flagIdx.
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- The three inner reads: M(C1(X1 input)) at b0Idx, b1Idx, flagIdx.
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        b0Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        b1Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_flag :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b1Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false)))
        flagIdx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 1) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  -- Combine.
  unfold toyWindow2Case1Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b1Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 1) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx false) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  -- Peel X2 (writes b1Idx, flagIdx ≠ b1Idx → flagIdx-side).
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
  -- Peel C2: writes flagIdx with XOR.
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  -- Substitute h_MA_b0, h_MA_b1, h_MA_flag.
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide

/-! ### R7d^xi^d — full state equality for case-1 gate

Funext-assembly theorem combining all 9 case-1 per-position helpers.
Mirrors `toyWindow2Case3Gate_state_eq` exactly: same case dispatch
order, same `cuccaro_input_F`-evaluation lemmas for the RHS. The
only differences from case 3:
- The input has `b1 = false` (case 1) instead of `b1 = true` (case 3).
- The accumulator update uses `tableValue a N 2 k 1`.
- At q = b1Idx the RHS reduces to `false` (instead of `true`). -/

/-- **Full state equality for the case-1 selected-add gate.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx true false`,
the case-1 gate produces exactly
`toyWindow2Case3Input ((acc + tableValue a N 2 k 1) % N) b0Idx b1Idx
   true false`.

The accumulator advances by `tableValue a N 2 k 1` (mod N), the
two window bits remain `true`/`false` respectively, the equality
flag is restored, and the entire SQIR/Cuccaro workspace is restored
to 0. -/
theorem toyWindow2Case1Gate_state_eq
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 1) % N)
          b0Idx b1Idx true false := by
  funext q
  set acc' := (acc + tableValue a N 2 k 1) % N with hacc'_def
  have hacc'_lt_N : acc' < N := Nat.mod_lt _ hN_pos
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Case on q = b1Idx.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [toyWindow2Case1Gate_preserves_b1Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- Case on q = b0Idx (q ≠ b1Idx).
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [toyWindow2Case1Gate_preserves_b0Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Case on q = flagIdx (q ≠ b1Idx, q ≠ b0Idx).
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    rw [toyWindow2Case1Gate_restores_flagIdx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Now q ≠ b0Idx, q ≠ b1Idx, q ≠ flagIdx.
  have h_rhs :
      toyWindow2Case3Input acc' b0Idx b1Idx true false q
        = cuccaro_input_F 2 false 0 acc' q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  -- Case on q ≥ 2 + 2*bits + 1 (above layout).
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [toyWindow2Case1Gate_aboveLayoutFalse bits N a k acc flagIdx b0Idx b1Idx q
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          hq_above hq_b0 hq_b1 hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc' q hq_above hacc'_lt).symm
  push_neg at hq_above
  -- Case q = 2 (carry-in).
  by_cases hq_2 : q = 2
  · subst hq_2
    rw [toyWindow2Case1Gate_carryInRestored bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
  -- Case q = 1.
  by_cases hq_1 : q = 1
  · subst hq_1
    rw [toyWindow2Case1Gate_internalFlagFalse bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  -- Case q = 0: contradiction via flagIdx = 0 and q ≠ flagIdx.
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  -- q ∈ [3, 2 + 2*bits].  Parity dispatch.
  by_cases h_q_odd : q % 2 = 1
  · -- Target bit.
    have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    rw [toyWindow2Case1Gate_targetBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 3) / 2) hi_lt]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
  · -- Read bit.
    have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    rw [toyWindow2Case1Gate_readBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 4) / 2) hi_lt]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xii: case-2 per-position helpers + state equality

Case 2 (v=2, b0=false, b1=true) has X-flip normalization on **b0Idx**
(symmetric to case 1, which uses X-flip on b1Idx). The proofs mirror
case 1 with b0Idx ↔ b1Idx swap throughout and constant
`tableValue a N 2 k 2`. -/

/-- The case-2 gate leaves the Cuccaro read register at `0` after the
full sequence (independent of the window bits `b0`, `b1`).
Mirrors `toyWindow2Case1Gate_readVal` with b0Idx ↔ b1Idx swap. -/
theorem toyWindow2Case2Gate_readVal
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_read_val bits 2
        (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = 0 := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx :=
    Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change cuccaro_read_val bits 2
      (Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1))
      = 0
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  rw [Gate.applyNat_CCX]
  rw [cuccaro_read_val_update_outside_workspace bits 2 flagIdx _ _
        h_flag_allowed]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1 b0Idx
        = b0 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b0Idx
        = !b0 := by
    rw [FormalRV.Framework.update_eq]
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) b1Idx
        = b1 := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx b0) b1Idx b1)
                  b0Idx (!b0) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.false_xor]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx (!b0) _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b0Idx (!b0) _ h_b0_out]
  rw [cuccaro_read_val_update_outside_workspace bits 2 b1Idx b1 _ h_b1_out]
  exact ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx (!b0 && b1)
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-2 gate's output is `false` at any position `q` above the
SQIR/Cuccaro layout (`q ≥ 2 + 2*bits + 1`), `q ∉ {b0Idx, b1Idx, flagIdx}`. -/
theorem toyWindow2Case2Gate_aboveLayoutFalse
    (bits N a k acc flagIdx b0Idx b1Idx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (hq_above : 2 + 2 * bits + 1 ≤ q)
    (hq_ne_b0 : q ≠ b0Idx) (hq_ne_b1 : q ≠ b1Idx) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) q = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) q
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b0]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_b1]
  have h_input_q :
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_ne_flag]
    exact cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_in_eq :
      update (update (cuccaro_input_F 2 false 0 acc) flagIdx true) q false
        = update (cuccaro_input_F 2 false 0 acc) flagIdx true := by
    funext p
    by_cases hpq : p = q
    · subst hpq
      rw [FormalRV.Framework.update_eq]
      exact h_input_q.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hpq]
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 2) flagIdx q false
      (update (cuccaro_input_F 2 false 0 acc) flagIdx true)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_in_eq] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- Case-2 preserves the value `false` at the X-flipped bit position
`b0Idx`. The X-flips give net `!(!false) = false`. -/
theorem toyWindow2Case2Gate_preserves_b0Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) b0Idx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b0Idx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_eq]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
  have h_state_b0 :
      Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)) b0Idx
        = true := by
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
    rfl
  set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.applyNat (Gate.X b0Idx)
                    (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true))
    with hstate_def
  have h_in_eq : update state b0Idx true = state := by
    funext p
    by_cases hp : p = b0Idx
    · subst hp
      rw [FormalRV.Framework.update_eq]
      exact h_state_b0.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      (tableValue a N 2 k 2) flagIdx b0Idx true state
      h_b0_out h_b0_ne_one h_b0_ne_flag
  rw [h_in_eq] at h_commute
  have h_at := congr_fun h_commute b0Idx
  rw [FormalRV.Framework.update_eq] at h_at
  rw [h_at]
  rfl

/-- Case-2 preserves the value `true` at the un-flipped bit position
`b1Idx`.  Adapts case-1's `_preserves_b0Idx` with b0Idx ↔ b1Idx swap. -/
theorem toyWindow2Case2Gate_preserves_b1Idx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) b1Idx = true := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b1Idx
      = true
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_F1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_F1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_F1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_F1_b0, h_F1_b1, h_F1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
        h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
        h_b1_ne_flag]
  rw [FormalRV.Framework.update_eq]

/-- Case-2 restores the external equality flag at `flagIdx` to `false`. -/
theorem toyWindow2Case2Gate_restores_flagIdx
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) flagIdx = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_MA_b0 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
        b0Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b0, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_b1 :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
        b1Idx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b0, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_eq]
  have h_MA_flag :
      Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1)
        (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.applyNat (Gate.X b0Idx)
            (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
        flagIdx = true := by
    rw [Gate.applyNat_CCX, Gate.applyNat_X]
    rw [h_F0_b0, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
      bits N (tableValue a N 2 k 2) acc flagIdx true
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) flagIdx
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_eq]
  rw [h_MA_b0, h_MA_b1, h_MA_flag]
  decide

/-- The case-2 gate forces position 1 (Cuccaro internal flag) to `false`. -/
theorem toyWindow2Case2Gate_internalFlagFalse
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) 1 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
  have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
  have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 1
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
  exact ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N (tableValue a N 2 k 2) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim

/-- The case-2 gate restores position 2 (carry-in) to `false`. -/
theorem toyWindow2Case2Gate_carryInRestored
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) 2 = false := by
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
  have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
  unfold toyWindow2Case2Gate toyWindow2Case3Input
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 2
      = false
  simp only [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  rw [Gate.applyNat_CCX]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
  rw [Gate.applyNat_CCX]
  rw [Gate.applyNat_X]
  have h_F0_b0 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  rw [h_F0_b0]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b0Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_b1),
        FormalRV.Framework.update_eq]
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b0Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  rw [h_X1_b0, h_X1_b1, h_X1_flag]
  simp only [Bool.and_self, Bool.false_xor, Bool.not_false]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b0Idx true _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 2) flagIdx b1Idx true _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
  exact sqir_style_controlledModAddConst_gate_carry_in_restored bits N
    (tableValue a N 2 k 2) acc flagIdx true
    hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1

/-- Case-2 target-bit at position `2 + 2*i + 1` equals
`((acc + tableValue a N 2 k 2) % N).testBit i`. -/
theorem toyWindow2Case2Gate_targetBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) (2 + 2 * i + 1)
      = ((acc + tableValue a N 2 k 2) % N).testBit i := by
  have h_correct := toyWindow2Case2Gate_correct bits N a k acc flagIdx b0Idx b1Idx
    false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_target_decode :
      cuccaro_target_val bits 2
          (Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx false true))
        = (acc + tableValue a N 2 k 2) % N := by
    simpa using h_correct
  have h_acc'_lt_N : (acc + tableValue a N 2 k 2) % N < N := Nat.mod_lt _ hN_pos
  have h_acc'_lt : (acc + tableValue a N 2 k 2) % N < 2^bits :=
    Nat.lt_of_lt_of_le h_acc'_lt_N hN
  exact cuccaro_target_val_eq_implies_bits_match bits 2 _ _ h_acc'_lt
    h_target_decode i hi

/-- Case-2 read-bit at position `2 + 2*i + 2` equals `false`. -/
theorem toyWindow2Case2Gate_readBit
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx)
    (i : Nat) (hi : i < bits) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true) (2 + 2 * i + 2)
      = false := by
  have h_rd := toyWindow2Case2Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
    false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
  have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd i hi
  rw [h_bit, Nat.zero_testBit]

/-- **Full state equality for the case-2 selected-add gate.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx false true`,
the case-2 gate produces
`toyWindow2Case3Input ((acc + tableValue a N 2 k 2) % N) b0Idx b1Idx
   false true`. Mirrors case-1 state_eq with b0Idx ↔ b1Idx swap. -/
theorem toyWindow2Case2Gate_state_eq
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 2) % N)
          b0Idx b1Idx false true := by
  funext q
  set acc' := (acc + tableValue a N 2 k 2) % N with hacc'_def
  have hacc'_lt_N : acc' < N := Nat.mod_lt _ hN_pos
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [toyWindow2Case2Gate_preserves_b1Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [toyWindow2Case2Gate_preserves_b0Idx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    rw [toyWindow2Case2Gate_restores_flagIdx bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_rhs :
      toyWindow2Case3Input acc' b0Idx b1Idx false true q
        = cuccaro_input_F 2 false 0 acc' q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [toyWindow2Case2Gate_aboveLayoutFalse bits N a k acc flagIdx b0Idx b1Idx q
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          hq_above hq_b0 hq_b1 hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc' q hq_above hacc'_lt).symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    rw [toyWindow2Case2Gate_carryInRestored bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
  by_cases hq_1 : q = 1
  · subst hq_1
    rw [toyWindow2Case2Gate_internalFlagFalse bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1 : Nat) < 2)]
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    rw [toyWindow2Case2Gate_targetBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 3) / 2) hi_lt]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    rw [toyWindow2Case2Gate_readBit bits N a k acc flagIdx b0Idx b1Idx
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag ((q - 4) / 2) hi_lt]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xiv^a — case-1 no-op state_eq on (T, T) input

For non-firing input `b0 = true`, `b1 = true`, the case-1 gate
acts as the identity on `toyWindow2Case3Input acc b0Idx b1Idx
true true`. This is the first of three concrete no-op lemmas
toward the unified case-1 state_eq. -/

/-- **Case-1 no-op state_eq on (T, T) input.**

When applied to `toyWindow2Case3Input acc b0Idx b1Idx true true`,
the case-1 gate produces exactly the same state. The case-1
firing condition `b0 ∧ ¬b1` is `true ∧ ¬true = false`, so the
gate behaves as identity. -/
theorem toyWindow2Case1Gate_state_eq_TT_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Input read at b1Idx (for the X1 flip, computes to !true = false).
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  -- Post-X1 reads at b0Idx, b1Idx, flagIdx (input has b1=true → post-X1 has b1=false).
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)
                  b1Idx (!true) b0Idx
        = true := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)
                  b1Idx (!true) b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)
                  b1Idx (!true) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- For (T, T), the inner CCX1 XOR computes false XOR (true AND false) = false.
  -- This means the C1 update at flagIdx is a no-op (value already false).
  -- After update_idem on b1Idx layers and reordering, the M's input is
  -- (update F b0Idx true) (b1Idx false) since the flagIdx update collapses.
  -- The M-state then equals the state' for both firing and noop cases at
  -- positions where M acts identity-like.
  -- Case on q = b1Idx.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    -- Trace: X-flips give net no change to b1Idx. Output b1Idx = true (input value).
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b1Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    -- Show inner state at b1Idx = false.
    have h_state_b1 :
        Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)) b1Idx
          = false := by
      rw [Gate.applyNat_CCX]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
      rw [Gate.applyNat_X]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.Framework.update_eq]
      rfl
    set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                    (Gate.applyNat (Gate.X b1Idx)
                      (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true))
    have h_in_eq : update state b1Idx false = state := by
      funext p
      by_cases hp : p = b1Idx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_state_b1.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx false state
        h_b1_out h_b1_ne_one h_b1_ne_flag
    rw [h_in_eq] at h_commute
    have h_at := congr_fun h_commute b1Idx
    rw [FormalRV.Framework.update_eq] at h_at
    rw [h_at]
    -- Goal: !false = (update (update F b0Idx true) b1Idx true) b1Idx
    rw [FormalRV.Framework.update_eq]
    rfl
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    -- Output b0Idx = true (input value).
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) b0Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    -- State pre-M: update (update (update (update F b0Idx T) b1Idx T) b1Idx F) flagIdx F.
    -- update_idem merges the b1Idx updates (T then F → just F).
    rw [FormalRV.Framework.update_idem]
    -- State: update (update (update F b0Idx T) b1Idx F) flagIdx F.
    -- Push flagIdx innermost via update_comm.
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    -- State: update (update (update F flagIdx F) b0Idx T) b1Idx F.
    -- Push b1Idx, b0Idx outside M.
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    -- Output flagIdx = false (input value).
    -- For (T, T), C1's XOR = F XOR (T AND F) = F. So flagIdx updates are no-ops.
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) flagIdx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    -- Three inner h_MA_* haves for M(C1(X1 input)) at b0Idx, b1Idx, flagIdx.
    -- For (T, T) input, these compute differently from firing case.
    have h_MA_b0 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)))
          b0Idx = true := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_b1 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)))
          b1Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_flag :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true)))
          flagIdx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
      exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    -- Now peel C2 and read at flagIdx.
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_eq]
    rw [h_MA_b0, h_MA_b1, h_MA_flag]
    simp only [Bool.and_false, Bool.false_xor]
    -- Goal: false = input flagIdx
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- Now q ≠ b0Idx, q ≠ b1Idx, q ≠ flagIdx.
  -- Simplify the RHS to cuccaro_input_F 2 false 0 acc q.
  have h_rhs :
      toyWindow2Case3Input acc b0Idx b1Idx true true q
        = cuccaro_input_F 2 false 0 acc q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  -- Case on q ≥ 2 + 2*bits + 1 (above layout).
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · -- Above-layout: output = false = input.
    have h_q_ne_one : q ≠ 1 := fun h => by omega
    have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
    -- Trace through gate.
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) q
        = cuccaro_input_F 2 false 0 acc q
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
    -- M's output at q (above layout, ≠ flagIdx). Use commute trick.
    have h_input_q :
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) q
          = cuccaro_input_F 2 false 0 acc q := by
      rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
      cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
    -- The state going into M is update F flagIdx false. By update_self (F flagIdx = false),
    -- this equals F. So M is applied to F. Output at q = false (commute + cuccaro_input_F).
    -- Simpler: show update at flagIdx with false is no-op since F flagIdx = false.
    have h_F_flag : (cuccaro_input_F 2 false 0 acc) flagIdx = false := by
      unfold cuccaro_input_F
      rw [if_pos h_flag_lo]
    have h_update_self : update (cuccaro_input_F 2 false 0 acc) flagIdx false
                      = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = flagIdx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_F_flag.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    rw [h_update_self]
    -- Now use commute trick at q for M on cuccaro_input_F.
    have h_in_eq2 :
        update (cuccaro_input_F 2 false 0 acc) q false
          = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = q
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx q false
        (cuccaro_input_F 2 false 0 acc)
        h_q_out h_q_ne_one hq_flag
    rw [h_in_eq2] at h_commute
    have h_at_q := congr_fun h_commute q
    rw [FormalRV.Framework.update_eq] at h_at_q
    rw [h_at_q]
    -- Goal: false = cuccaro_input_F 2 false 0 acc q
    exact h_q_val.symm
  push_neg at hq_above
  -- Case q = 2 (carry-in).
  by_cases hq_2 : q = 2
  · subst hq_2
    have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
    have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
    have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 2
        = cuccaro_input_F 2 false 0 acc 2
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    -- Carry-in restored via SQIR theorem.
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
      (tableValue a N 2 k 1) acc flagIdx false
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  -- Case q = 1 (internal flag).
  by_cases hq_1 : q = 1
  · subst hq_1
    have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
    have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
    have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx true) b1Idx true) 1
        = cuccaro_input_F 2 false 0 acc 1
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx true _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N (tableValue a N 2 k 1) flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) 1 = false :=
      ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_input : cuccaro_input_F 2 false 0 acc 1 = false := by
      unfold cuccaro_input_F
      rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_input]
    exact h_clean
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · -- Target bit.
    have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
      true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_target_decode :
        cuccaro_target_val bits 2
            (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Input acc b0Idx b1Idx true true)) = acc := by
      simpa using h_correct
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · -- Read bit.
    have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
      true true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xiv^b — case-1 no-op state_eq on (F, T) input

For non-firing input `b0 = false`, `b1 = true`, the case-1 gate
acts as the identity. The CCX guard is `false AND ¬true = false`,
so the gate behaves as identity. Proof mirrors TT no-op with
substitutions `h_X1_b0 = false` and commute values updated. -/

/-- **Case-1 no-op state_eq on (F, T) input.** -/
theorem toyWindow2Case1Gate_state_eq_FT_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  -- Input read at b1Idx (for the X1 flip).
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]
  -- Post-X1 reads at b0Idx, b1Idx, flagIdx (input has b0=false, b1=true → post-X1 has b1=false).
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b1Idx (!true) b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b1Idx (!true) b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)
                  b1Idx (!true) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  -- For (F, T), CCX1 XOR = F XOR (F AND F) = F. Same no-op structure as TT.
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b1Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b1Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    have h_state_b1 :
        Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)) b1Idx
          = false := by
      rw [Gate.applyNat_CCX]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
      rw [Gate.applyNat_X]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.Framework.update_eq]
      rfl
    set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                    (Gate.applyNat (Gate.X b1Idx)
                      (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true))
    have h_in_eq : update state b1Idx false = state := by
      funext p
      by_cases hp : p = b1Idx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_state_b1.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx false state
        h_b1_out h_b1_ne_one h_b1_ne_flag
    rw [h_in_eq] at h_commute
    have h_at := congr_fun h_commute b1Idx
    rw [FormalRV.Framework.update_eq] at h_at
    rw [h_at]
    rw [FormalRV.Framework.update_eq]
    rfl
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b0Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) b0Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) flagIdx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) flagIdx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    have h_MA_b0 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
          b0Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_b1 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
          b1Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_flag :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true)))
          flagIdx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
      exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_eq]
    rw [h_MA_b0, h_MA_b1, h_MA_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_rhs :
      toyWindow2Case3Input acc b0Idx b1Idx false true q
        = cuccaro_input_F 2 false 0 acc q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · have h_q_ne_one : q ≠ 1 := fun h => by omega
    have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) q
        = cuccaro_input_F 2 false 0 acc q
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
    have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
      cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
    have h_F_flag : (cuccaro_input_F 2 false 0 acc) flagIdx = false := by
      unfold cuccaro_input_F
      rw [if_pos h_flag_lo]
    have h_update_self : update (cuccaro_input_F 2 false 0 acc) flagIdx false
                      = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = flagIdx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_F_flag.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    rw [h_update_self]
    have h_in_eq2 :
        update (cuccaro_input_F 2 false 0 acc) q false
          = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = q
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx q false
        (cuccaro_input_F 2 false 0 acc)
        h_q_out h_q_ne_one hq_flag
    rw [h_in_eq2] at h_commute
    have h_at_q := congr_fun h_commute q
    rw [FormalRV.Framework.update_eq] at h_at_q
    rw [h_at_q]
    exact h_q_val.symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
    have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
    have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 2
        = cuccaro_input_F 2 false 0 acc 2
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
      (tableValue a N 2 k 1) acc flagIdx false
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  by_cases hq_1 : q = 1
  · subst hq_1
    have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
    have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
    have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx true) 1
        = cuccaro_input_F 2 false 0 acc 1
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.and_false, Bool.false_and, Bool.false_xor, Bool.not_true]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx false _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N (tableValue a N 2 k 1) flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) 1 = false :=
      ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_input : cuccaro_input_F 2 false 0 acc 1 = false := by
      unfold cuccaro_input_F
      rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_input]
    exact h_clean
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
      false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_target_decode :
        cuccaro_target_val bits 2
            (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Input acc b0Idx b1Idx false true)) = acc := by
      simpa using h_correct
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
      false true hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xiv^c — case-1 no-op state_eq on (F, F) input

For non-firing input `b0 = false`, `b1 = false`, the case-1 gate
acts as the identity. After X1, b1 flips F → T. The CCX guard is
`false AND (!false) = false AND true = false`, so no fire. -/

/-- **Case-1 no-op state_eq on (F, F) input.** -/
theorem toyWindow2Case1Gate_state_eq_FF_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have h_c_lt_N : tableValue a N 2 k 1 < N := tableValue_lt_N a N 2 k 1 hN_pos
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  have h_F0_b1 :
      update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false b1Idx
        = false := by
    rw [FormalRV.Framework.update_eq]
  have h_X1_b0 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)
                  b1Idx (!false) b0Idx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_X1_b1 :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)
                  b1Idx (!false) b1Idx
        = true := by
    rw [FormalRV.Framework.update_eq]; rfl
  have h_X1_flag :
      update (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)
                  b1Idx (!false) flagIdx
        = false := by
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b1Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b1Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_eq]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
    have h_state_b1 :
        Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)) b1Idx
          = true := by
      rw [Gate.applyNat_CCX]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_ne_flag]
      rw [Gate.applyNat_X]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.Framework.update_eq]
      rfl
    set state := Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                    (Gate.applyNat (Gate.X b1Idx)
                      (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false))
    have h_in_eq : update state b1Idx true = state := by
      funext p
      by_cases hp : p = b1Idx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_state_b1.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx b1Idx true state
        h_b1_out h_b1_ne_one h_b1_ne_flag
    rw [h_in_eq] at h_commute
    have h_at := congr_fun h_commute b1Idx
    rw [FormalRV.Framework.update_eq] at h_at
    rw [h_at]
    rw [FormalRV.Framework.update_eq]
    rfl
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b0Idx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) b0Idx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_eq]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_eq]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) flagIdx
        = (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) flagIdx
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    have h_MA_b0 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)))
          b0Idx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_b1 :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)))
          b1Idx = true := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_eq]
    have h_MA_flag :
        Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N
                         (tableValue a N 2 k 1) flagIdx 1)
          (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.applyNat (Gate.X b1Idx)
              (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false)))
          flagIdx = false := by
      rw [Gate.applyNat_CCX, Gate.applyNat_X]
      rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
      simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
      rw [FormalRV.Framework.update_idem]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
            h_b1_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
      rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
            (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
            h_b0_ne_flag]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
      exact ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_eq]
    rw [h_MA_b0, h_MA_b1, h_MA_flag]
    simp only [Bool.false_and, Bool.false_xor]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b1_ne_flag)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0_ne_flag)]
    unfold cuccaro_input_F
    rw [if_pos h_flag_lo]
  have h_rhs :
      toyWindow2Case3Input acc b0Idx b1Idx false false q
        = cuccaro_input_F 2 false 0 acc q := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  rw [h_rhs]
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · have h_q_ne_one : q ≠ 1 := fun h => by omega
    have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) q
        = cuccaro_input_F 2 false 0 acc q
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ hq_b0]
    have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
      cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
    have h_F_flag : (cuccaro_input_F 2 false 0 acc) flagIdx = false := by
      unfold cuccaro_input_F
      rw [if_pos h_flag_lo]
    have h_update_self : update (cuccaro_input_F 2 false 0 acc) flagIdx false
                      = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = flagIdx
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_F_flag.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    rw [h_update_self]
    have h_in_eq2 :
        update (cuccaro_input_F 2 false 0 acc) q false
          = cuccaro_input_F 2 false 0 acc := by
      funext p
      by_cases hp : p = q
      · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
      · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
    have h_commute :=
      sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        (tableValue a N 2 k 1) flagIdx q false
        (cuccaro_input_F 2 false 0 acc)
        h_q_out h_q_ne_one hq_flag
    rw [h_in_eq2] at h_commute
    have h_at_q := congr_fun h_commute q
    rw [FormalRV.Framework.update_eq] at h_at_q
    rw [h_at_q]
    exact h_q_val.symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    have h_2_ne_b0 : (2 : Nat) ≠ b0Idx := by omega
    have h_2_ne_b1 : (2 : Nat) ≠ b1Idx := by omega
    have h_2_ne_flag : (2 : Nat) ≠ flagIdx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) 2
        = cuccaro_input_F 2 false 0 acc 2
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_2_ne_b0]
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
      (tableValue a N 2 k 1) acc flagIdx false
      hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  by_cases hq_1 : q = 1
  · subst hq_1
    have h_1_ne_flag : (1 : Nat) ≠ flagIdx := Ne.symm h_flag_ne_1
    have h_1_ne_b0 : (1 : Nat) ≠ b0Idx := by omega
    have h_1_ne_b1 : (1 : Nat) ≠ b1Idx := by omega
    unfold toyWindow2Case1Gate toyWindow2Case3Input
    change Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update (update (cuccaro_input_F 2 false 0 acc) b0Idx false) b1Idx false) 1
        = cuccaro_input_F 2 false 0 acc 1
    simp only [Gate.applyNat_seq]
    rw [Gate.applyNat_X]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [Gate.applyNat_CCX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_flag]
    rw [Gate.applyNat_CCX]
    rw [Gate.applyNat_X]
    rw [h_F0_b1, h_X1_b0, h_X1_b1, h_X1_flag]
    simp only [Bool.false_and, Bool.false_xor, Bool.not_false]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1_ne_flag]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_flag]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b1Idx true _ h_b1_out h_b1_ne_one
          h_b1_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b1]
    rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
          (tableValue a N 2 k 1) flagIdx b0Idx false _ h_b0_out h_b0_ne_one
          h_b0_ne_flag]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_1_ne_b0]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N (tableValue a N 2 k 1) flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) 1 = false :=
      ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
        bits N (tableValue a N 2 k 1) acc flagIdx false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_input : cuccaro_input_F 2 false 0 acc 1 = false := by
      unfold cuccaro_input_F
      rw [if_pos (by omega : (1 : Nat) < 2)]
    rw [h_input]
    exact h_clean
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    have h_correct := toyWindow2Case1Gate_correct bits N a k acc flagIdx b0Idx b1Idx
      false false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_target_decode :
        cuccaro_target_val bits 2
            (Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
              (toyWindow2Case3Input acc b0Idx b1Idx false false)) = acc := by
      simpa using h_correct
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    have h_rd := toyWindow2Case1Gate_readVal bits N a k acc flagIdx b0Idx b1Idx
      false false hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt h_rd ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xv — first reusable abstraction: CCX guard-false no-op

The "non-firing case-1 gate is identity" insight reduces to: when the
CCX's AND guard is false, the CCX update at flagIdx is a no-op. This
helper captures that fact in one line and will let case-2/case-3
non-firing proofs reuse it. -/

/-- **CCX guard-false no-op**: If the AND of the two control reads
on `state` is `false`, then applying the CCX at flagIdx is the
identity. The proof is one line via `update_self`. -/
theorem ccx_guard_false_noop
    (b0Idx b1Idx flagIdx : Nat) (state : Nat → Bool)
    (h_guard : (state b0Idx && state b1Idx) = false) :
    Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx) state = state := by
  rw [Gate.applyNat_CCX]
  rw [h_guard]
  simp only [Bool.xor_false]
  exact FormalRV.Framework.update_self state flagIdx

/-- **X-conjugate no-op**: If a gate is the identity on the X-flipped
state at position `q`, then the X-conjugated composition
`X q ∘ gate ∘ X q` is the identity on the original state. This
captures the case-N gate's X-normalization pattern when the inner
CCX-MOD-CCX subgate is a no-op. -/
theorem x_conjugate_noop
    (q : Nat) (gate : Gate) (state : Nat → Bool)
    (h_inner_noop : Gate.applyNat gate (update state q (!state q))
                  = update state q (!state q)) :
    Gate.applyNat (Gate.seq (Gate.X q) (Gate.seq gate (Gate.X q))) state = state := by
  simp only [Gate.applyNat_seq, Gate.applyNat_X]
  rw [h_inner_noop]
  rw [FormalRV.Framework.update_eq]
  simp only [Bool.not_not]
  rw [FormalRV.Framework.update_idem]
  exact FormalRV.Framework.update_self state q

/-- **Mod-add above-layout no-op**: M is identity on `cuccaro_input_F`
at any position `q` above the layout. This captures the most common
above-layout reasoning step in case-N noop proofs. -/
theorem mod_add_above_layout_noop_on_F
    (bits N c acc flagIdx q : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (hq_above : 2 + 2 * bits + 1 ≤ q) (hq_ne_flag : q ≠ flagIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (cuccaro_input_F 2 false 0 acc) q
      = false := by
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_q_out : q < 2 ∨ 2 + 2 * bits + 1 ≤ q := Or.inr hq_above
  have h_q_ne_one : q ≠ 1 := fun h => by omega
  have h_q_val : cuccaro_input_F 2 false 0 acc q = false :=
    cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt
  have h_F_self_q : update (cuccaro_input_F 2 false 0 acc) q false
                  = cuccaro_input_F 2 false 0 acc := by
    funext p
    by_cases hp : p = q
    · subst hp; rw [FormalRV.Framework.update_eq]; exact h_q_val.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  have h_commute :=
    sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
      c flagIdx q false
      (cuccaro_input_F 2 false 0 acc)
      h_q_out h_q_ne_one hq_ne_flag
  rw [h_F_self_q] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Mod-add full state no-op on Case3Input** (control = false branch).

When applied to a `toyWindow2Case3Input acc b0Idx b1Idx b0 b1` state,
the controlled modular-add gate is the FULL-STATE identity (because
the input's flagIdx bit is `false` — the implicit control). This is
the most significant reusable helper for case-N noop proofs: it
captures the entire mod-add subtrace in the non-firing branch and
replaces ~150 lines of inline proof in each case-N noop.

Used in conjunction with `ccx_guard_false_noop` (CCXs) and
`x_conjugate_noop` (X-flips), the case-2/case-3 noop proofs
collapse from ~450 lines to ~150 lines each. -/
theorem mod_add_state_eq_when_control_false_on_Case3Input
    (bits N c acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc : c < N) (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input acc b0Idx b1Idx b0 b1 := by
  funext q
  have h_b0_ne_one : b0Idx ≠ 1 := fun h => by omega
  have h_b1_ne_one : b1Idx ≠ 1 := fun h => by omega
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  have h_flag_allowed : flagIdx < 2 ∨ 2 + 2 * bits + 1 ≤ flagIdx := Or.inl h_flag_lo
  have hacc_lt : acc < 2^bits := Nat.lt_of_lt_of_le hacc hN
  have h_flag_eq_zero : flagIdx = 0 := by omega
  have h_F_flag : cuccaro_input_F 2 false 0 acc flagIdx = false := by
    unfold cuccaro_input_F; rw [if_pos h_flag_lo]
  have h_F_self : update (cuccaro_input_F 2 false 0 acc) flagIdx false
                = cuccaro_input_F 2 false 0 acc := by
    funext p
    by_cases hp : p = flagIdx
    · subst hp; rw [FormalRV.Framework.update_eq]; exact h_F_flag.symm
    · rw [FormalRV.Framework.update_neq _ _ _ _ hp]
  unfold toyWindow2Case3Input
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        c flagIdx b1Idx b1 _ h_b1_out h_b1_ne_one h_b1_ne_flag]
  rw [sqir_style_controlledModAddConst_gate_commute_update_outside_fun bits N
        c flagIdx b0Idx b0 _ h_b0_out h_b0_ne_one h_b0_ne_flag]
  by_cases hq_b1 : q = b1Idx
  · rw [hq_b1]
    rw [FormalRV.Framework.update_eq, FormalRV.Framework.update_eq]
  by_cases hq_b0 : q = b0Idx
  · rw [hq_b0]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq, FormalRV.Framework.update_eq]
  rw [FormalRV.Framework.update_neq _ _ _ _ hq_b1,
      FormalRV.Framework.update_neq _ _ _ _ hq_b0,
      FormalRV.Framework.update_neq _ _ _ _ hq_b1,
      FormalRV.Framework.update_neq _ _ _ _ hq_b0]
  by_cases hq_flag : q = flagIdx
  · rw [hq_flag]
    conv_lhs => rw [← h_F_self]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) flagIdx = false :=
      ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
        bits N c acc flagIdx false
        hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [h_clean]
    exact h_F_flag.symm
  by_cases hq_above : 2 + 2 * bits + 1 ≤ q
  · rw [mod_add_above_layout_noop_on_F bits N c acc flagIdx q
        hbits hN_pos hN hN2 hc hacc h_flag_lo hq_above hq_flag]
    exact (cuccaro_input_F_above_eq_false 2 bits acc q hq_above hacc_lt).symm
  push_neg at hq_above
  by_cases hq_2 : q = 2
  · subst hq_2
    conv_lhs => rw [← h_F_self]
    rw [sqir_style_controlledModAddConst_gate_carry_in_restored bits N
        c acc flagIdx false hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1]
    exact (cuccaro_input_F_at_c_in 2 false 0 acc).symm
  by_cases hq_1 : q = 1
  · subst hq_1
    conv_lhs => rw [← h_F_self]
    have h_clean : Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
        (update (cuccaro_input_F 2 false 0 acc) flagIdx false) 1 = false :=
      ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
        bits N c acc flagIdx false
        hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    rw [h_clean]
    unfold cuccaro_input_F
    rw [if_pos (by omega : (1:Nat) < 2)]
  by_cases hq_0 : q = 0
  · subst hq_0
    exact absurd h_flag_eq_zero.symm hq_flag
  by_cases h_q_odd : q % 2 = 1
  · have hi_lt : (q - 3) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
    rw [hq_eq]
    conv_lhs => rw [← h_F_self]
    have h_clean := ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
      bits N c acc flagIdx false
      hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_target_decode : cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
          (update (cuccaro_input_F 2 false 0 acc) flagIdx false)) = acc := by
      simpa using h_clean
    have h_bit := cuccaro_target_val_eq_implies_bits_match bits 2 acc _ hacc_lt
      h_target_decode ((q - 3) / 2) hi_lt
    rw [h_bit]
    exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc).symm
  · have hi_lt : (q - 4) / 2 < bits := by omega
    have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
    rw [hq_eq]
    conv_lhs => rw [← h_F_self]
    have h_clean := ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
      bits N c acc flagIdx false
      hbits hN_pos hN hN2 hc hacc h_flag_allowed h_flag_ne_1 h_flag_lt_dim
    have h_read_zero : cuccaro_read_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c flagIdx 1)
          (update (cuccaro_input_F 2 false 0 acc) flagIdx false)) = 0 := by
      simpa using h_clean
    have h_zero_lt : (0 : Nat) < 2^bits := Nat.two_pow_pos bits
    have h_bit := cuccaro_read_val_eq_implies_bits_match bits 2 0 _ h_zero_lt
      h_read_zero ((q - 4) / 2) hi_lt
    rw [h_bit, Nat.zero_testBit]
    rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc]
    exact (Nat.zero_testBit _).symm

/-! ## Phase R7d^xiv^d — case-1 unified state equality

Wrapper theorem covering all 4 (b0, b1) inputs via `match` dispatch:
- (true, false) → firing state_eq.
- (true, true), (false, true), (false, false) → no-op state_eq. -/

/-- **Unified case-1 state equality** covering all four (b0, b1)
input shapes. Dispatches to:
- `toyWindow2Case1Gate_state_eq` for `(true, false)` (firing).
- `toyWindow2Case1Gate_state_eq_TT_noop` for `(true, true)`.
- `toyWindow2Case1Gate_state_eq_FT_noop` for `(false, true)`.
- `toyWindow2Case1Gate_state_eq_FF_noop` for `(false, false)`. -/
theorem toyWindow2Case1Gate_state_eq_unified
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc)
          b0Idx b1Idx b0 b1 := by
  match b0, b1 with
  | true, false =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 1) % N)
          b0Idx b1Idx true false
    exact toyWindow2Case1Gate_state_eq bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | true, true =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true
    exact toyWindow2Case1Gate_state_eq_TT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, true =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true
    exact toyWindow2Case1Gate_state_eq_FT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, false =>
    show Gate.applyNat (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
    exact toyWindow2Case1Gate_state_eq_FF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xvi — case-2 TT no-op via reusable helpers

Validation of the R7d^xv abstraction toolkit. The case-2 gate
X-conjugates on b0Idx (rather than b1Idx like case 1). For TT
input, after the b0 X-normalization makes b0 internally false,
the CCX guard is `false ∧ true = false`, so the inner C1-M-C2
sequence is identity, and the outer X-flip restores. This proof
uses ALL FOUR reusable helpers (`ccx_guard_false_noop`,
`mod_add_state_eq_when_control_false_on_Case3Input`) without
needing per-position dispatch. -/

/-- **Case-2 no-op state_eq on (T, T) input** — validation theorem
for the R7d^xv reusable abstraction toolkit. -/
theorem toyWindow2Case2Gate_state_eq_TT_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true := by
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  -- Aux: state b0Idx, b1Idx values at the (false, true) intermediate Case3Input.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false true b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false true b1Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- The X1-flipped state equals Case3Input acc ... false true.
  have h_state_X1 : update (toyWindow2Case3Input acc b0Idx b1Idx true true) b0Idx (!true)
                  = toyWindow2Case3Input acc b0Idx b1Idx false true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rfl
  -- Input b0Idx = true (for X1 read).
  have h_input_b0 : toyWindow2Case3Input acc b0Idx b1Idx true true b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Peel the 5 layers of case-2 gate.
  unfold toyWindow2Case2Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true
  rw [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [h_input_b0]
  rw [h_state_X1]
  -- Now the state going into C1 is Case3Input acc b0Idx b1Idx false true.
  -- Apply ccx_guard_false_noop for C1.
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Apply mod_add_state_eq_when_control_false_on_Case3Input for M.
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 2) acc flagIdx b0Idx b1Idx false true
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Apply ccx_guard_false_noop for C2 (same guard).
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Peel X2 and finish.
  rw [Gate.applyNat_X]
  rw [h_state_b0]
  -- After X2: update Case3Input ... false true) b0Idx (!false) = Case3Input ... true true.
  unfold toyWindow2Case3Input
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rfl

/-- **Case-2 no-op state_eq on (T, F) input** — Case 2 fires only on
(F, T). For input (T, F), the X1 normalization makes b0Idx internally
false, b1Idx remains false. The CCX guard (false ∧ false) is false, so
the inner C1-M-C2 sequence is identity, and the outer X-flip restores. -/
theorem toyWindow2Case2Gate_state_eq_TF_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false := by
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  -- Aux: state b0Idx, b1Idx values at the (false, false) intermediate Case3Input.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false false b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- The X1-flipped state equals Case3Input acc ... false false.
  have h_state_X1 : update (toyWindow2Case3Input acc b0Idx b1Idx true false) b0Idx (!true)
                  = toyWindow2Case3Input acc b0Idx b1Idx false false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rfl
  -- Input b0Idx = true (for X1 read).
  have h_input_b0 : toyWindow2Case3Input acc b0Idx b1Idx true false b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Peel the 5 layers of case-2 gate.
  unfold toyWindow2Case2Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
  rw [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [h_input_b0]
  rw [h_state_X1]
  -- Now the state going into C1 is Case3Input acc b0Idx b1Idx false false.
  -- Apply ccx_guard_false_noop for C1.
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Apply mod_add_state_eq_when_control_false_on_Case3Input for M.
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 2) acc flagIdx b0Idx b1Idx false false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Apply ccx_guard_false_noop for C2 (same guard).
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Peel X2 and finish.
  rw [Gate.applyNat_X]
  rw [h_state_b0]
  -- After X2: update Case3Input ... false false) b0Idx (!false) = Case3Input ... true false.
  unfold toyWindow2Case3Input
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rfl

/-- **Case-2 no-op state_eq on (F, F) input** — Case 2 fires only on
(F, T). For input (F, F), the X1 normalization makes b0Idx internally
true, b1Idx remains false. The CCX guard (true ∧ false) is false, so
the inner C1-M-C2 sequence is identity, and the outer X-flip restores. -/
theorem toyWindow2Case2Gate_state_eq_FF_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false := by
  have h_c_lt_N : tableValue a N 2 k 2 < N := tableValue_lt_N a N 2 k 2 hN_pos
  -- Aux: state b0Idx, b1Idx values at the (true, false) intermediate Case3Input.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx true false b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx true false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- The X1-flipped state equals Case3Input acc ... true false.
  have h_state_X1 : update (toyWindow2Case3Input acc b0Idx b1Idx false false) b0Idx (!false)
                  = toyWindow2Case3Input acc b0Idx b1Idx true false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
    rw [FormalRV.Framework.update_idem]
    rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
    rfl
  -- Input b0Idx = false (for X1 read).
  have h_input_b0 : toyWindow2Case3Input acc b0Idx b1Idx false false b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  -- Peel the 5 layers of case-2 gate.
  unfold toyWindow2Case2Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.X b0Idx)
          (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 2) flagIdx 1)
              (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
  rw [Gate.applyNat_seq]
  rw [Gate.applyNat_X]
  rw [h_input_b0]
  rw [h_state_X1]
  -- Now the state going into C1 is Case3Input acc b0Idx b1Idx true false.
  -- Apply ccx_guard_false_noop for C1.
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Apply mod_add_state_eq_when_control_false_on_Case3Input for M.
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 2) acc flagIdx b0Idx b1Idx true false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Apply ccx_guard_false_noop for C2 (same guard).
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  -- Peel X2 and finish.
  rw [Gate.applyNat_X]
  rw [h_state_b0]
  -- After X2: update Case3Input ... true false) b0Idx (!true) = Case3Input ... false false.
  unfold toyWindow2Case3Input
  rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0_ne_b1]
  rw [FormalRV.Framework.update_idem]
  rw [FormalRV.Framework.update_comm _ _ _ _ _ (Ne.symm h_b0_ne_b1)]
  rfl

/-- **Case-2 unified state_eq** — for arbitrary `(b0, b1)`, dispatches
to the firing theorem (`toyWindow2Case2Gate_state_eq`) when `(!b0) && b1`
holds, and to the appropriate no-op theorem otherwise. -/
theorem toyWindow2Case2Gate_state_eq_unified
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (if (!b0) && b1 then (acc + tableValue a N 2 k 2) % N else acc)
          b0Idx b1Idx b0 b1 := by
  match b0, b1 with
  | true, true =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input acc b0Idx b1Idx true true
    exact toyWindow2Case2Gate_state_eq_TT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | true, false =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
    exact toyWindow2Case2Gate_state_eq_TF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, true =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 2) % N)
          b0Idx b1Idx false true
    exact toyWindow2Case2Gate_state_eq bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, false =>
    show Gate.applyNat (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
    exact toyWindow2Case2Gate_state_eq_FF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xviii — case-3 no-ops via reusable helpers

Case 3 fires only on `(b0=true, b1=true)`. Its gate has the form
`CCX-M-CCX` (no X-normalization), so each no-op proof reduces to
three reusable-helper applications:
- `ccx_guard_false_noop` on the first CCX (guard `b0 && b1 = false`),
- `mod_add_state_eq_when_control_false_on_Case3Input` on the modular
  add (flagIdx still false since CCX did not fire),
- `ccx_guard_false_noop` on the second CCX (same guard).

Each no-op proof is ~35 lines — even shorter than Case-2 no-ops
since Case 3 has no X-conjugation to peel. -/

/-- **Case-3 no-op state_eq on (T, F) input** — Case 3 fires only on
`(T, T)`. For input `(T, F)`, the CCX guard `true ∧ false = false` so
the inner mod-add sees `flagIdx = false`, the whole gate no-ops. -/
theorem toyWindow2Case3Gate_state_eq_TF_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false := by
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  -- State values at input Case3Input ... true false.
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx true false b0Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx true false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  -- Peel the 3 layers of case-3 gate.
  unfold toyWindow2Case3Gate
  -- Convert layout-form mod-add to SQIR form (def-eq).
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 3) acc flagIdx b0Idx b1Idx true false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
        (by rw [h_state_b0, h_state_b1]; rfl)]

/-- **Case-3 no-op state_eq on (F, T) input** — Case 3 fires only on
`(T, T)`. For input `(F, T)`, the CCX guard `false ∧ true = false` so
the whole gate no-ops. -/
theorem toyWindow2Case3Gate_state_eq_FT_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true := by
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false true b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false true b1Idx = true := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  unfold toyWindow2Case3Gate
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 3) acc flagIdx b0Idx b1Idx false true
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
        (by rw [h_state_b0, h_state_b1]; rfl)]

/-- **Case-3 no-op state_eq on (F, F) input** — Case 3 fires only on
`(T, T)`. For input `(F, F)`, the CCX guard `false ∧ false = false`
so the whole gate no-ops. -/
theorem toyWindow2Case3Gate_state_eq_FF_noop
    (bits N a k acc flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false := by
  have h_c_lt_N : tableValue a N 2 k 3 < N := tableValue_lt_N a N 2 k 3 hN_pos
  have h_state_b0 : toyWindow2Case3Input acc b0Idx b1Idx false false b0Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1,
        FormalRV.Framework.update_eq]
  have h_state_b1 : toyWindow2Case3Input acc b0Idx b1Idx false false b1Idx = false := by
    unfold toyWindow2Case3Input
    rw [FormalRV.Framework.update_eq]
  unfold toyWindow2Case3Gate
  change Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
          (Gate.seq
            (sqir_style_controlledModAddConst_gate bits 2 N
              (tableValue a N 2 k 3) flagIdx 1)
            (Gate.CCX b0Idx b1Idx flagIdx)))
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
  rw [Gate.applyNat_seq]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]
  rw [Gate.applyNat_seq]
  rw [mod_add_state_eq_when_control_false_on_Case3Input bits N
        (tableValue a N 2 k 3) acc flagIdx b0Idx b1Idx false false
        hbits hN_pos hN hN2 h_c_lt_N hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  rw [ccx_guard_false_noop b0Idx b1Idx flagIdx
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
        (by rw [h_state_b0, h_state_b1]; rfl)]

/-- **Case-3 unified state_eq** — for arbitrary `(b0, b1)`, dispatches
to the firing theorem (`toyWindow2Case3Gate_state_eq`) when `b0 && b1`
holds, and to the appropriate no-op theorem otherwise. -/
theorem toyWindow2Case3Gate_state_eq_unified
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (if b0 && b1 then (acc + tableValue a N 2 k 3) % N else acc)
          b0Idx b1Idx b0 b1 := by
  match b0, b1 with
  | true, true =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true true)
      = toyWindow2Case3Input ((acc + tableValue a N 2 k 3) % N)
          b0Idx b1Idx true true
    exact toyWindow2Case3Gate_state_eq bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | true, false =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx true false)
      = toyWindow2Case3Input acc b0Idx b1Idx true false
    exact toyWindow2Case3Gate_state_eq_TF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, true =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false true)
      = toyWindow2Case3Input acc b0Idx b1Idx false true
    exact toyWindow2Case3Gate_state_eq_FT_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
  | false, false =>
    show Gate.applyNat (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx false false)
      = toyWindow2Case3Input acc b0Idx b1Idx false false
    exact toyWindow2Case3Gate_state_eq_FF_noop bits N a k acc flagIdx b0Idx b1Idx
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xix — composed selected-add correctness

Assembles the composed `toyWindow2SelectedAddGate` correctness theorem
via the three unified case state_eq theorems landed in R7d^xi^d,
R7d^xvii, and R7d^xviii. -/

/-- **Bridge: target_val on a `Case3Input` reduces to the accumulator**
when the window-bit indices are outside the Cuccaro workspace and the
accumulator fits within the data register. -/
private theorem cuccaro_target_val_Case3Input
    (bits acc : Nat) (b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx)
    (h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx)
    (hacc_lt : acc < 2^bits) :
    cuccaro_target_val bits 2 (toyWindow2Case3Input acc b0Idx b1Idx b0 b1) = acc := by
  unfold toyWindow2Case3Input
  rw [cuccaro_target_val_update_outside_workspace bits 2 b1Idx _ _ h_b1_out]
  rw [cuccaro_target_val_update_outside_workspace bits 2 b0Idx _ _ h_b0_out]
  exact cuccaro_target_val_input bits 2 0 acc false hacc_lt

/-- **R7d^xix — composed selected-add correctness.**

The windowSize=2 selected-add gate `case1 ; case2 ; case3` correctly
implements piecewise modular addition based on the window bits
`(b0, b1)`:
- `(F, F)` (v=0): accumulator unchanged.
- `(T, F)` (v=1): adds `tableValue a N 2 k 1`.
- `(F, T)` (v=2): adds `tableValue a N 2 k 2`.
- `(T, T)` (v=3): adds `tableValue a N 2 k 3`.

Proof is a pure composition of the three unified case state_eq theorems
plus the Case3Input → accumulator bridge. No internal gate machinery
is re-derived. -/
theorem toyWindow2SelectedAddGate_correct
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N
        else if !b0 && b1 then (acc + tableValue a N 2 k 2) % N
        else if b0 && !b1 then (acc + tableValue a N 2 k 1) % N
        else acc := by
  have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
  have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
  unfold toyWindow2SelectedAddGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Apply Case 1 unified.
  rw [toyWindow2Case1Gate_state_eq_unified bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  -- Intermediate accumulator after Case 1.
  set acc1 := if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc with h_acc1_def
  have h_acc1_lt : acc1 < N := by
    rw [h_acc1_def]
    split
    · exact Nat.mod_lt _ hN_pos
    · exact hacc
  -- Apply Case 2 unified at acc1.
  rw [toyWindow2Case2Gate_state_eq_unified bits N a k acc1 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc1_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc2 := if !b0 && b1 then (acc1 + tableValue a N 2 k 2) % N else acc1 with h_acc2_def
  have h_acc2_lt : acc2 < N := by
    rw [h_acc2_def]
    split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc1_lt
  -- Apply Case 3 unified at acc2.
  rw [toyWindow2Case3Gate_state_eq_unified bits N a k acc2 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc2_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc3 := if b0 && b1 then (acc2 + tableValue a N 2 k 3) % N else acc2 with h_acc3_def
  have h_acc3_lt : acc3 < N := by
    rw [h_acc3_def]
    split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc2_lt
  -- Convert cuccaro_target_val (Case3Input acc3 ...) to acc3.
  rw [cuccaro_target_val_Case3Input bits acc3 b0Idx b1Idx b0 b1
        h_b0_out h_b1_out (Nat.lt_of_lt_of_le h_acc3_lt hN)]
  -- Unfold the abbreviations and reduce by case split on (b0, b1).
  rw [h_acc3_def, h_acc2_def, h_acc1_def]
  cases b0 <;> cases b1 <;> simp

/-! ## Phase R7d^xx — spec-layer wrapper

Lifts the selected-add composition correctness theorem
(`toyWindow2SelectedAddGate_correct`) into the windowed arithmetic
spec layer. The wrapper expresses the RHS using the existing
`windowedStepSpec` definition (rather than a piecewise if-then-else),
making the toy gate compatible with downstream `WindowedLookupModMulSpec`
infrastructure. -/

/-- Encode two window bits to a numeric window value `v ∈ [0, 4)`:
`v = b0.toNat + 2 * b1.toNat`. Convention matches the per-case theorems:
- `(F, F)` → 0
- `(T, F)` → 1
- `(F, T)` → 2
- `(T, T)` → 3 -/
def windowBits2_to_v (b0 b1 : Bool) : Nat := b0.toNat + 2 * b1.toNat

/-- **Window-size-2 spec bridge.** `windowedStepSpec` at the encoded
value `windowBits2_to_v b0 b1` is the piecewise modular addition
matching the four `(b0, b1)` cases.

The proof dispatches each `(b0, b1)` to the matching pre-existing
`windowedStepSpec_window2_vN` lemma. -/
theorem windowedStepSpec_window2_bool
    (a N k acc : Nat) (b0 b1 : Bool) (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1)
      = if b0 && b1 then (acc + tableValue a N 2 k 3) % N
        else if !b0 && b1 then (acc + tableValue a N 2 k 2) % N
        else if b0 && !b1 then (acc + tableValue a N 2 k 1) % N
        else acc := by
  cases b0 <;> cases b1
  all_goals simp [windowBits2_to_v, Bool.toNat]
  · exact windowedStepSpec_window2_v0 a N k acc hN_pos hacc
  · exact windowedStepSpec_window2_v2 a N k acc hN_pos
  · exact windowedStepSpec_window2_v1 a N k acc hN_pos
  · exact windowedStepSpec_window2_v3 a N k acc hN_pos

/-- **R7d^xx — spec-form selected-add correctness.**

The composed selected-add gate's target-decode matches `windowedStepSpec`
evaluated at the encoded window value `windowBits2_to_v b0 b1`. This is
the bridge from the explicit composition theorem to the abstract
windowed-arithmetic spec layer. -/
theorem toyWindow2SelectedAddGate_correct_spec
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
      = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) := by
  rw [toyWindow2SelectedAddGate_correct bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  exact (windowedStepSpec_window2_bool a N k acc b0 b1 hN_pos hacc).symm

/-- **`Window2SelectedAddSpec`**: the spec contract for a composed
windowSize=2 selected-add component.

An implementation provides a gate constructor `gate` parameterized by
width and window index, plus a correctness proof that the gate
implements the piecewise modular addition matching `windowedStepSpec`
on all four `(b0, b1)` inputs.

This is the composed analog of `Window2LookupCase3Spec` (which only
covers the v=3 firing case). Once an instance exists, composing across
windows `k = 0 .. numWindows N 2` yields a full windowSize=2 lookup
modular multiplier. -/
structure Window2SelectedAddSpec (a N : Nat) where
  /-- The composed selected-add gate constructor. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Correctness: the gate implements `windowedStepSpec` on the
  encoded window value `windowBits2_to_v b0 b1` for arbitrary
  `(b0, b1) : Bool × Bool`. -/
  selectedAddCorrect :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      cuccaro_target_val bits 2
          (Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
            (toyWindow2Case3Input acc b0Idx b1Idx b0 b1))
        = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1)

/-- **Toy windowSize=2 selected-add spec implementation.**

Wraps the CCX-based `toyWindow2SelectedAddGate` as a
`Window2SelectedAddSpec a N` instance via the R7d^xx wrapper theorem. -/
noncomputable def toyWindow2SelectedAddSpecImpl (a N : Nat) :
    Window2SelectedAddSpec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx
  selectedAddCorrect := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                            hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                            h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                            h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2SelectedAddGate_correct_spec bits N a k acc flagIdx b0Idx b1Idx
      b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xxi — multi-window spec scaffold

Pure spec-level layer for iterating `windowedStepSpec` over multiple
windows. Defines a windowed-bit accessor, an iterated step function,
and the basic unfold/boundedness lemmas needed by the future
multi-window circuit correctness theorem. No circuit-level reasoning
yet — this layer is purely arithmetic. -/

/-- Per-window bit accessor: extracts the window value at window
index `k` from a pair of bit functions `b0 : Nat → Bool` (LSB) and
`b1 : Nat → Bool` (MSB). The window value lives in `[0, 4)`. -/
def windowBits2_at (b0 b1 : Nat → Bool) (k : Nat) : Nat :=
  windowBits2_to_v (b0 k) (b1 k)

/-- The boolean-pair window encoding always fits in `[0, 4)`. -/
theorem windowBits2_to_v_lt_4 (b0 b1 : Bool) :
    windowBits2_to_v b0 b1 < 4 := by
  unfold windowBits2_to_v
  cases b0 <;> cases b1 <;> simp [Bool.toNat]

/-- Multi-window analog: every window value extracted via
`windowBits2_at` is bounded above by `4 = 2^2`. -/
theorem windowBits2_at_lt_4 (b0 b1 : Nat → Bool) (k : Nat) :
    windowBits2_at b0 b1 k < 4 := windowBits2_to_v_lt_4 (b0 k) (b1 k)

/-- **Iterated windowed step** at window size 2: applies
`windowedStepSpec a N 2 k` for `k = 0, …, numWin - 1` starting from
`acc`, with the `k`-th step using window value
`windowBits2_at b0 b1 k`. Recursive on `numWin` for clean induction. -/
def windowedStepSpecIter2
    (a N : Nat) (b0 b1 : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc =>
      windowedStepSpec a N 2 n
        (windowedStepSpecIter2 a N b0 b1 n acc)
        (windowBits2_at b0 b1 n)

/-- Base unfold: 0 windows leaves the accumulator unchanged. -/
@[simp] theorem windowedStepSpecIter2_zero
    (a N acc : Nat) (b0 b1 : Nat → Bool) :
    windowedStepSpecIter2 a N b0 b1 0 acc = acc := rfl

/-- Step unfold: `numWin + 1` windows compose as `numWin` windows
followed by the `numWin`-th selected-add. -/
@[simp] theorem windowedStepSpecIter2_succ
    (a N numWin acc : Nat) (b0 b1 : Nat → Bool) :
    windowedStepSpecIter2 a N b0 b1 (numWin + 1) acc
      = windowedStepSpec a N 2 numWin
          (windowedStepSpecIter2 a N b0 b1 numWin acc)
          (windowBits2_at b0 b1 numWin) := rfl

/-- **Iterated boundedness.** Every intermediate accumulator stays
in `[0, N)`. The base case uses the initial bound `acc < N`; the
inductive case uses `windowedStepSpec_lt_N` (the modular reduction
guarantees output `< N` unconditionally). -/
theorem windowedStepSpecIter2_lt_N
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc < N := by
  induction numWin with
  | zero => exact hacc
  | succ n _ =>
    rw [windowedStepSpecIter2_succ]
    exact windowedStepSpec_lt_N a N 2 n _ _ hN_pos

/-- **Circuit skeleton: multi-window selected-add gate sequence.**

Given a `Window2SelectedAddSpec` implementation, sequences `numWin`
applications of its `gate` constructor over windows `k = 0, …,
numWin - 1`, with `b0Idx k` / `b1Idx k` supplying the per-window
bit positions. Recursion on `numWin` mirrors `windowedStepSpecIter2`.

This is the gate-level analog of `windowedStepSpecIter2`; proving its
correctness theorem (gate output's `cuccaro_target_val` matches
`windowedStepSpecIter2`) is the next major milestone (deferred). -/
noncomputable def windowed2SelectedAddGate
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq (windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx n)
        (impl.gate bits n flagIdx (b0Idx n) (b1Idx n))

/-- Base unfold for the gate skeleton: 0 windows is the identity. -/
@[simp] theorem windowed2SelectedAddGate_zero
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx 0 = Gate.I := rfl

/-- Step unfold for the gate skeleton: `numWin + 1` windows compose
as `numWin` windows followed by the `numWin`-th selected-add. -/
@[simp] theorem windowed2SelectedAddGate_succ
    {a N : Nat} (impl : Window2SelectedAddSpec a N)
    (bits flagIdx numWin : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx (numWin + 1)
      = Gate.seq (windowed2SelectedAddGate impl bits flagIdx b0Idx b1Idx numWin)
                 (impl.gate bits numWin flagIdx (b0Idx numWin) (b1Idx numWin)) :=
  rfl

/-! ## Phase R7d^xxii — full-state selected-add spec

Strengthens the selected-add spec from target-decode (R7d^xx) to
full-state correctness. The composed gate maps a `Case3Input`
state to a `Case3Input` state with the accumulator updated
according to `windowedStepSpec` — preserving the input shape so
the next selected-add gate (at the next window) can chain.

This is the prerequisite for the multi-window circuit correctness
theorem: without preserved state shape, sequential `selectedAdd`
applications can't be composed via the spec interface. -/

/-- **Full-state selected-add correctness.** The composed
windowSize=2 selected-add gate produces a `Case3Input` state with
the accumulator advanced by `windowedStepSpec a N 2 k acc
(windowBits2_to_v b0 b1)`, leaving all other bit positions intact
in the `Case3Input` shape.

Proof mirrors `toyWindow2SelectedAddGate_correct` (R7d^xix) but
stops at the state level — no `cuccaro_target_val` extraction. -/
theorem toyWindow2SelectedAddGate_state_eq_spec
    (bits N a k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2) (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : 2 + 2 * bits + 1 ≤ b0Idx) (h_b1_hi : 2 + 2 * bits + 1 ≤ b1Idx)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx)
    (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
        (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
      = toyWindow2Case3Input
          (windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1))
          b0Idx b1Idx b0 b1 := by
  unfold toyWindow2SelectedAddGate
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Apply Case 1 unified.
  rw [toyWindow2Case1Gate_state_eq_unified bits N a k acc flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc1 := if b0 && !b1 then (acc + tableValue a N 2 k 1) % N else acc
    with h_acc1_def
  have h_acc1_lt : acc1 < N := by
    rw [h_acc1_def]; split
    · exact Nat.mod_lt _ hN_pos
    · exact hacc
  -- Apply Case 2 unified at acc1.
  rw [toyWindow2Case2Gate_state_eq_unified bits N a k acc1 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc1_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc2 := if !b0 && b1 then (acc1 + tableValue a N 2 k 2) % N else acc1
    with h_acc2_def
  have h_acc2_lt : acc2 < N := by
    rw [h_acc2_def]; split
    · exact Nat.mod_lt _ hN_pos
    · exact h_acc1_lt
  -- Apply Case 3 unified at acc2.
  rw [toyWindow2Case3Gate_state_eq_unified bits N a k acc2 flagIdx b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 h_acc2_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
  set acc3 := if b0 && b1 then (acc2 + tableValue a N 2 k 3) % N else acc2
    with h_acc3_def
  -- Show acc3 = windowedStepSpec ... by unfolding + bool-bridge + cases.
  have h_acc3_eq : acc3 = windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) := by
    rw [h_acc3_def, h_acc2_def, h_acc1_def,
        windowedStepSpec_window2_bool a N k acc b0 b1 hN_pos hacc]
    cases b0 <;> cases b1 <;> simp
  rw [h_acc3_eq]

/-- **`Window2SelectedAddStateSpec`**: stronger spec contract for a
composed windowSize=2 selected-add component, exposing the full-state
correctness theorem instead of just target-decode correctness.

The state-level field is required for multi-window composition:
without it, two consecutive selected-add gates can't be chained
through the spec interface (target-decode alone leaves the
intermediate state's shape unknown).

Strictly stronger than `Window2SelectedAddSpec` — instances of
this structure imply `Window2SelectedAddSpec` instances (see
`Window2SelectedAddStateSpec.toSelectedAddSpec`). -/
structure Window2SelectedAddStateSpec (a N : Nat) where
  /-- The composed selected-add gate constructor. -/
  gate : (bits k flagIdx b0Idx b1Idx : Nat) → Gate
  /-- Full-state correctness: the gate transforms a `Case3Input`
  state to a `Case3Input` state with the accumulator updated per
  `windowedStepSpec`. All other bit positions are preserved. -/
  selectedAddStateEq :
    ∀ (bits k acc flagIdx b0Idx b1Idx : Nat) (b0 b1 : Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      2 + 2 * bits + 1 ≤ b0Idx → 2 + 2 * bits + 1 ≤ b1Idx →
      b0Idx ≠ b1Idx → b0Idx ≠ flagIdx → b1Idx ≠ flagIdx →
      Gate.applyNat (gate bits k flagIdx b0Idx b1Idx)
          (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
        = toyWindow2Case3Input
            (windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1))
            b0Idx b1Idx b0 b1

/-- A `Window2SelectedAddStateSpec` instance yields a
`Window2SelectedAddSpec` instance by composing the state-eq theorem
with `cuccaro_target_val_Case3Input`. The conversion is uniform
in the implementation. -/
noncomputable def Window2SelectedAddStateSpec.toSelectedAddSpec
    {a N : Nat} (impl : Window2SelectedAddStateSpec a N) :
    Window2SelectedAddSpec a N where
  gate := impl.gate
  selectedAddCorrect := by
    intro bits k acc flagIdx b0Idx b1Idx b0 b1
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    have h_b0_out : b0Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b0Idx := Or.inr h_b0_hi
    have h_b1_out : b1Idx < 2 ∨ 2 + 2 * bits + 1 ≤ b1Idx := Or.inr h_b1_hi
    have h_step_lt : windowedStepSpec a N 2 k acc (windowBits2_to_v b0 b1) < N :=
      windowedStepSpec_lt_N a N 2 k acc _ hN_pos
    rw [impl.selectedAddStateEq bits k acc flagIdx b0Idx b1Idx b0 b1
          hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag]
    exact cuccaro_target_val_Case3Input bits _ b0Idx b1Idx b0 b1
      h_b0_out h_b1_out (Nat.lt_of_lt_of_le h_step_lt hN)

/-- **Toy windowSize=2 selected-add full-state spec implementation.**

Wraps the CCX-based `toyWindow2SelectedAddGate` as a
`Window2SelectedAddStateSpec a N` instance via
`toyWindow2SelectedAddGate_state_eq_spec`. -/
noncomputable def toyWindow2SelectedAddStateSpecImpl (a N : Nat) :
    Window2SelectedAddStateSpec a N where
  gate := fun bits k flagIdx b0Idx b1Idx =>
            toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx
  selectedAddStateEq := fun bits k acc flagIdx b0Idx b1Idx b0 b1
                            hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                            h_flag_lt_dim h_b0_hi h_b1_hi h_b0_ne_b1
                            h_b0_ne_flag h_b1_ne_flag =>
    toyWindow2SelectedAddGate_state_eq_spec bits N a k acc flagIdx b0Idx b1Idx
      b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag

/-! ## Phase R7d^xxiii — multi-window input encoding

All-windows-at-once input encoding for the windowSize=2 selected-add
pipeline. Installs every window's b0/b1 bits simultaneously over the
Cuccaro accumulator base. Recursive on `numWin` for clean induction;
proves basic readback lemmas (for an arbitrary installed window),
target-extraction (cuccaro_target_val ignores the high window bits),
and workspace preservation (a frame-style lemma for any low-position
query). -/

/-- **Multi-window input encoding.** Installs the b0/b1 bits for
windows `0, …, numWin - 1` on top of a Cuccaro-formatted accumulator
encoding. Recursive on `numWin`. -/
def windowed2Input
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) :
    Nat → (Nat → Bool)
  | 0 => cuccaro_input_F 2 false 0 acc
  | n + 1 =>
      update
        (update (windowed2Input acc b0Idx b1Idx b0 b1 n) (b0Idx n) (b0 n))
        (b1Idx n) (b1 n)

/-- Zero windows: the encoding is just the Cuccaro accumulator base. -/
@[simp] theorem windowed2Input_zero
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) :
    windowed2Input acc b0Idx b1Idx b0 b1 0
      = cuccaro_input_F 2 false 0 acc := rfl

/-- Successor unfold: install window `n`'s bits on top of windows
`0 … n - 1`. -/
@[simp] theorem windowed2Input_succ
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1)
      = update
          (update (windowed2Input acc b0Idx b1Idx b0 b1 n) (b0Idx n) (b0 n))
          (b1Idx n) (b1 n) := rfl

/-- Latest-window readback for `b1`: just the outermost update. -/
theorem windowed2Input_succ_read_b1
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1) (b1Idx n) = b1 n := by
  rw [windowed2Input_succ]
  exact FormalRV.Framework.update_eq _ _ _

/-- Latest-window readback for `b0`: strip the outer `update` at
`b1Idx n` (requires `b0Idx n ≠ b1Idx n`), then read the inner one. -/
theorem windowed2Input_succ_read_b0
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (n : Nat)
    (h_ne : b0Idx n ≠ b1Idx n) :
    windowed2Input acc b0Idx b1Idx b0 b1 (n + 1) (b0Idx n) = b0 n := by
  rw [windowed2Input_succ]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_ne]
  exact FormalRV.Framework.update_eq _ _ _

/-- **General `b0` readback** for any installed window `k < numWin`,
under universal index-disjointness. -/
theorem windowed2Input_read_b0
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_distinct : ∀ i j, i ≠ j → b0Idx i ≠ b0Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b0Idx k) = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k k)]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k n)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_distinct k n hkn)]
      exact ih hk_lt_n

/-- **General `b1` readback** for any installed window `k < numWin`. -/
theorem windowed2Input_read_b1
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b1_distinct : ∀ i j, i ≠ j → b1Idx i ≠ b1Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b1Idx k) = b1 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_distinct k n hkn)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm (h_b0_b1 n k))]
      exact ih hk_lt_n

/-- **Target extraction.** The Cuccaro target decoder ignores all
window bits (they live above the workspace), recovering the input
accumulator. -/
theorem cuccaro_target_val_windowed2Input
    (bits acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (numWin : Nat)
    (hacc_bits : acc < 2^bits)
    (h_hi0 : ∀ k, 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, 2 + 2 * bits + 1 ≤ b1Idx k) :
    cuccaro_target_val bits 2 (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = acc := by
  induction numWin with
  | zero =>
    rw [windowed2Input_zero]
    exact cuccaro_target_val_input bits 2 0 acc false hacc_bits
  | succ n ih =>
    rw [windowed2Input_succ]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b1Idx n) (b1 n) _
          (Or.inr (h_hi1 n))]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b0Idx n) (b0 n) _
          (Or.inr (h_hi0 n))]
    exact ih

/-- **Workspace preservation (frame-style).** At any position `q` in
the Cuccaro workspace (`q < 2 + 2 * bits`), the multi-window encoding
agrees with the base accumulator encoding. Useful for proving that
gates operating only on the workspace + flag + active window bits
preserve `cuccaro_target_val` / `cuccaro_read_val` semantics. -/
theorem windowed2Input_at_low
    (acc bits q : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin : Nat) (h_q_low : q < 2 + 2 * bits + 1)
    (h_hi0 : ∀ k, 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, 2 + 2 * bits + 1 ≤ b1Idx k) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin q
      = cuccaro_input_F 2 false 0 acc q := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ]
    have h_q_ne_b1 : q ≠ b1Idx n := by
      have := h_hi1 n; omega
    have h_q_ne_b0 : q ≠ b0Idx n := by
      have := h_hi0 n; omega
    rw [FormalRV.Framework.update_neq _ _ _ _ h_q_ne_b1]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_q_ne_b0]
    exact ih

/-! ## Phase R7d^xxix-L-1 — q_start-parametric windowed input layout

R7d^xxix-L-DESIGN-LOCK selected Option C2: shift the Cuccaro
workspace above the official data register so that the official data
register `q < bits` is disjoint from the arithmetic accumulator /
workspace.

This section introduces the q_start-parametric counterpart of
`windowed2Input`, bridges it to the old `q_start = 2` layout, and
proves the readback / zero-base / shifted-layout disjointness lemmas
needed by the (forthcoming L-2 / L-3) parametric K-stage.

**Exact accumulator-bit formula (from `cuccaro_input_F`):** the
accumulator's `k`-th bit lives at position `q_start + 2*k + 1`.
(With `q_start = 2`, this gives the old positions `2*k + 3 = 3, 5,
7, ...`; with `q_start = bits`, this gives the shifted positions
`bits + 1, bits + 3, ...`.) -/

/-- **q_start-parametric multi-window input encoding.** Same recursive
structure as `windowed2Input`, but the underlying Cuccaro base allows
an arbitrary `q_start`. The old `windowed2Input` is the
`q_start = 2` specialization (see `windowed2Input_eq_qstart_2`). -/
def windowed2Input_qstart
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) : Nat → (Nat → Bool)
  | 0 => cuccaro_input_F q_start false 0 acc
  | n + 1 =>
      update
        (update
          (windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 n)
          (b0Idx n) (b0 n))
        (b1Idx n) (b1 n)

/-- Zero-window unfold for the q_start-parametric encoding. -/
@[simp] theorem windowed2Input_qstart_zero
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 0
      = cuccaro_input_F q_start false 0 acc := rfl

/-- Successor unfold for the q_start-parametric encoding. -/
@[simp] theorem windowed2Input_qstart_succ
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 (n + 1)
      = update
          (update
            (windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 n)
            (b0Idx n) (b0 n))
          (b1Idx n) (b1 n) := rfl

/-- **Bridge to the old q_start = 2 layout.** The original
`windowed2Input` is the `q_start = 2` specialization of
`windowed2Input_qstart`. Proven by induction on `numWin`, with both
recursive defs unfolding identically. -/
theorem windowed2Input_eq_qstart_2
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin : Nat) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin
      = windowed2Input_qstart 2 acc b0Idx b1Idx b0 b1 numWin := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ, windowed2Input_qstart_succ, ih]

/-- **q_start-parametric base-false at disjoint positions.** If `q`
is not any `b0Idx k` / `b1Idx k` for `k < numWin`, and the
zero-accumulator Cuccaro base reads `false` at `q`, then the full
parametric encoding reads `false` at `q`. Caller supplies the
base-false fact (preserves generality across q_start values).

Mirrors `windowed2Input_zero_at_disjoint` for the q_start-parametric
encoding. -/
private theorem windowed2Input_qstart_zero_at_disjoint
    (q_start : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin q : Nat)
    (h_base : cuccaro_input_F q_start false 0 0 q = false)
    (h_b0_disj : ∀ k, k < numWin → q ≠ b0Idx k)
    (h_b1_disj : ∀ k, k < numWin → q ≠ b1Idx k) :
    windowed2Input_qstart q_start 0 b0Idx b1Idx b0 b1 numWin q = false := by
  induction numWin with
  | zero =>
    rw [windowed2Input_qstart_zero]
    exact h_base
  | succ n ih =>
    rw [windowed2Input_qstart_succ]
    have h_b0_n : q ≠ b0Idx n := h_b0_disj n (Nat.lt_succ_self n)
    have h_b1_n : q ≠ b1Idx n := h_b1_disj n (Nat.lt_succ_self n)
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_n]
    exact ih
      (fun k hk => h_b0_disj k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b1_disj k (Nat.lt_succ_of_lt hk))

/-- **Bounded q_start-parametric b0 readback.** For any installed
window `k < numWin`, the parametric encoding reads back the latest
write at `b0Idx k`. Hypotheses restricted to `< numWin`. -/
theorem windowed2Input_qstart_read_b0_bounded
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 numWin (b0Idx k)
      = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_qstart_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _
            (h_b0_ne_b1 k (Nat.lt_succ_self k))]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0k_ne_b1n : b0Idx k ≠ b1Idx n :=
        h_distinct_b0_b1 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      have h_b0k_ne_b0n : b0Idx k ≠ b0Idx n :=
        h_distinct_b0_b0 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b0n]
      exact ih hk_lt_n
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)

/-- **Bounded q_start-parametric b1 readback.** -/
theorem windowed2Input_qstart_read_b1_bounded
    (q_start acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    windowed2Input_qstart q_start acc b0Idx b1Idx b0 b1 numWin (b1Idx k)
      = b1 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_qstart_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b1k_ne_b1n : b1Idx k ≠ b1Idx n :=
        h_distinct_b1_b1 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      have h_b1k_ne_b0n : b1Idx k ≠ b0Idx n := by
        have := h_distinct_b0_b1 n k (Nat.lt_succ_self n) hk
          (Ne.symm (Nat.ne_of_lt hk_lt_n))
        exact Ne.symm this
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0n]
      exact ih hk_lt_n
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi)
            (Nat.lt_succ_of_lt hj) hij)

/-! ### Shifted-layout disjointness arithmetic

For the shifted Cuccaro layout (q_start = bits), the accumulator
b-bit positions live at `bits + 2*k + 1`. These are strictly above
any official data position `q < bits`, ensuring the disjointness
needed by the (forthcoming) Cuccaro→Data SWAP cascade. -/

/-- **Accumulator b-bit position is at least `bits + 1`.** Direct
arithmetic from `q_start + 2*k + 1` with `q_start = bits`. -/
private theorem shifted_cuccaro_b_pos_ge
    (bits k : Nat) :
    bits + 1 ≤ bits + 2 * k + 1 := by
  omega

/-- **Accumulator b-bit position lies strictly above the data
register.** -/
private theorem shifted_cuccaro_b_above_data
    (bits k : Nat) :
    bits ≤ bits + 2 * k + 1 := by
  omega

/-- **Accumulator b-bit position differs from any data position.**
For the shifted layout (`q_start = bits`), the accumulator b-bit at
position `bits + 2*k + 1` cannot equal a data position `q < bits`. -/
private theorem shifted_cuccaro_b_ne_data
    (bits k q : Nat) (h_q : q < bits) :
    bits + 2 * k + 1 ≠ q := by
  omega

/-- **Data position differs from any accumulator b-bit position.**
Symmetric form of `shifted_cuccaro_b_ne_data`. -/
private theorem data_ne_shifted_cuccaro_b
    (bits k q : Nat) (h_q : q < bits) :
    q ≠ bits + 2 * k + 1 := by
  omega

/-- **Cuccaro→Data SWAP source/destination disjointness** (shifted
layout). The Cuccaro b-bit at `bits + 2*k + 1` (source) and the data
position `bits - 1 - k` (destination) are distinct for any `k`. The
data range `q < bits` is strictly below the accumulator range
`q ≥ bits + 1`. -/
private theorem shifted_swap_src_ne_dst
    (bits k : Nat) (h_k : k < bits) :
    bits + 2 * k + 1 ≠ bits - 1 - k := by
  omega

/-! ### End of R7d^xxix-L-1 q_start-parametric layout

What landed in L-1:
- `windowed2Input_qstart` def + simp unfolds.
- `windowed2Input_eq_qstart_2` bridge to old layout.
- `windowed2Input_qstart_zero_at_disjoint` (private).
- `windowed2Input_qstart_read_b0_bounded` /
  `windowed2Input_qstart_read_b1_bounded` (bounded readbacks).
- Shifted-layout arithmetic (b_pos_ge, b_above_data, b_ne_data,
  data_ne_b, swap_src_ne_dst).

Deferred to L-2 / L-3:
- q_start-parametric selected-add gate + frame lemma.
- K-stage at q_start = bits.
- target-decode for the q_start-parametric layout (not strictly
  needed by L-2; can be deferred indefinitely if not used
  downstream). -/

/-! ## Phase R7d^xxix-L-2′ — q_start-parametric selected-add frame

For Architecture D (Gidney style, see
`GIDNEY_WINDOWED_ARITHMETIC_REVIEW.md`), the selected-add gate must
admit window control bits at positions **below** the Cuccaro
workspace — specifically at data positions `[0, bits)` when the
workspace starts at `q_start = bits`.

This section:
1. Generalizes `sqir_style_controlledModAddConst_gate_commute_update_outside_fun`
   to arbitrary `q_start` and `flagPos`.
2. Defines q_start-parametric versions of the three case gates and
   the composed selected-add gate.
3. Proves the q_start-parametric frame property for the composed
   selected-add gate: it commutes with updates at any position `p`
   that is disjoint from its support (workspace, b0Idx, b1Idx,
   flagIdx).

Critically, the frame disjointness hypothesis allows
`p < q_start` (data positions) as well as
`q_start + 2*bits + 1 ≤ p` (high ancilla). The old q_start = 2
version only allowed `p < 2` (degenerate, just the prefix) plus
high ancilla. -/

/-- **q_start-parametric controlled-mod-add frame lemma.** The
underlying gate `sqir_style_controlledModAddConst_gate bits q_start
N c controlIdx flagPos` commutes with an `update _ updateIdx v`
when `updateIdx` is disjoint from the Cuccaro workspace
(`< q_start` or `≥ q_start + 2*bits + 1`), distinct from `flagPos`,
and distinct from `controlIdx`. -/
private theorem sqir_modAdd_qstart_commute_update_disjoint
    (bits q_start N c controlIdx flagPos updateIdx : Nat) (v : Bool)
    (f : Nat → Bool)
    (hupdate_out :
      updateIdx < q_start ∨ q_start + 2 * bits + 1 ≤ updateIdx)
    (hupdate_ne_flag : updateIdx ≠ flagPos)
    (hupdate_ne_control : updateIdx ≠ controlIdx) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
        (update f updateIdx v)
      = update (Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
          f) updateIdx v := by
  unfold sqir_style_controlledModAddConst_gate
  by_cases hc : c = 0
  · simp [hc, Gate.applyNat_I]
  · simp only [hc, if_false]
    unfold sqir_style_controlledModAddConst_candidate
    simp only [Gate.applyNat_seq]
    rw [sqir_conditionalAddConstGate_commute_update_outside_fun bits q_start c
          controlIdx updateIdx v f hupdate_out hupdate_ne_control]
    rw [sqir_style_compareConst_candidate_commute_update_outside_fun bits q_start N
          flagPos updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_conditionalSubConstGate_commute_update_outside_fun bits q_start N
          flagPos updateIdx v _ hupdate_out hupdate_ne_flag]
    rw [sqir_controlledCompareConst_commute_update_outside_fun bits q_start c
          controlIdx flagPos updateIdx v _
          hupdate_out hupdate_ne_flag hupdate_ne_control]
    rw [Gate.applyNat_CX_commute_update_outside_fun controlIdx flagPos updateIdx v _
          hupdate_ne_control hupdate_ne_flag]

/-- **q_start-parametric case-3 selected-add gate** (binary 11).
Same structure as `toyWindow2Case3Gate` but operating at parametric
`q_start` and `flagPos`. -/
noncomputable def toyWindow2Case3Gate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 3
  Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
    (Gate.seq (sqir_style_controlledModAddConst_gate bits q_start N c flagIdx flagPos)
              (Gate.CCX b0Idx b1Idx flagIdx))

/-- **q_start-parametric case-1 selected-add gate** (binary 01).
X-normalizes b1 before/after the CCX cascade. -/
noncomputable def toyWindow2Case1Gate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 1
  Gate.seq (Gate.X b1Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (sqir_style_controlledModAddConst_gate bits q_start N c flagIdx flagPos)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b1Idx))))

/-- **q_start-parametric case-2 selected-add gate** (binary 10).
X-normalizes b0 before/after the CCX cascade. -/
noncomputable def toyWindow2Case2Gate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  let c := tableValue a N 2 k 2
  Gate.seq (Gate.X b0Idx)
    (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
      (Gate.seq (sqir_style_controlledModAddConst_gate bits q_start N c flagIdx flagPos)
        (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
                  (Gate.X b0Idx))))

/-- **q_start-parametric composed selected-add gate.** Runs the
three nonzero-case gates in sequence. -/
noncomputable def toyWindow2SelectedAddGate_qstart
    (bits q_start N a k : Nat)
    (flagIdx flagPos b0Idx b1Idx : Nat) : Gate :=
  Gate.seq (toyWindow2Case1Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
    (Gate.seq (toyWindow2Case2Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
              (toyWindow2Case3Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx))

/-- **Frame property of a single case gate.** Any `toyWindow2CaseN`
gate (N ∈ {1, 2, 3}) commutes with an `update _ p v` whose position
`p` is disjoint from the Cuccaro workspace, distinct from `b0Idx`,
`b1Idx`, `flagIdx`, and `flagPos`. -/
private theorem toyWindow2Case3Gate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2Case3Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2Case3Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2Case3Gate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx f p v
      hp_ne_b0 hp_ne_b1 hp_ne_flag
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact sqir_modAdd_qstart_commute_update_disjoint bits q_start N
        (tableValue a N 2 k 3) flagIdx flagPos p v g
        hp_disj_workspace hp_ne_flagPos hp_ne_flag
    · intro g
      exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx g p v
        hp_ne_b0 hp_ne_b1 hp_ne_flag

private theorem toyWindow2Case1Gate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2Case1Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2Case1Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2Case1Gate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact Gate.applyNat_X_commute_update_outside_fun b1Idx p v f hp_ne_b1
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx g p v
        hp_ne_b0 hp_ne_b1 hp_ne_flag
    · intro g
      refine applyNat_seq_commute_update _ _ g p v ?_ ?_
      · intro h
        exact sqir_modAdd_qstart_commute_update_disjoint bits q_start N
          (tableValue a N 2 k 1) flagIdx flagPos p v h
          hp_disj_workspace hp_ne_flagPos hp_ne_flag
      · intro h
        refine applyNat_seq_commute_update _ _ h p v ?_ ?_
        · intro i
          exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx i p v
            hp_ne_b0 hp_ne_b1 hp_ne_flag
        · intro i
          exact Gate.applyNat_X_commute_update_outside_fun b1Idx p v i hp_ne_b1

private theorem toyWindow2Case2Gate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2Case2Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2Case2Gate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2Case2Gate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact Gate.applyNat_X_commute_update_outside_fun b0Idx p v f hp_ne_b0
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx g p v
        hp_ne_b0 hp_ne_b1 hp_ne_flag
    · intro g
      refine applyNat_seq_commute_update _ _ g p v ?_ ?_
      · intro h
        exact sqir_modAdd_qstart_commute_update_disjoint bits q_start N
          (tableValue a N 2 k 2) flagIdx flagPos p v h
          hp_disj_workspace hp_ne_flagPos hp_ne_flag
      · intro h
        refine applyNat_seq_commute_update _ _ h p v ?_ ?_
        · intro i
          exact applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx i p v
            hp_ne_b0 hp_ne_b1 hp_ne_flag
        · intro i
          exact Gate.applyNat_X_commute_update_outside_fun b0Idx p v i hp_ne_b0

/-- **PRIMARY L-2′ THEOREM: q_start-parametric selected-add frame.**

The composed `toyWindow2SelectedAddGate_qstart` commutes with any
`update _ p v` where `p` is disjoint from:
- the Cuccaro workspace at `[q_start, q_start + 2*bits + 1)`,
- the case gate's CCX-control positions `b0Idx`, `b1Idx`,
- the CCX-target `flagIdx`,
- the inner mod-add's flag position `flagPos`.

The workspace disjointness is given as a disjunction
(`p < q_start ∨ q_start + 2*bits + 1 ≤ p`), so `p` can be **below**
the workspace (e.g., at official data positions in Architecture D)
as well as above.

This is the architectural-correctness frame property needed by the
Gidney-style two-register pipeline. -/
theorem toyWindow2SelectedAddGate_qstart_commute_update_disjoint
    (bits q_start N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_disj_workspace :
      p < q_start ∨ q_start + 2 * bits + 1 ≤ p)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2SelectedAddGate_qstart bits q_start N a k flagIdx flagPos b0Idx b1Idx)
          s) p v := by
  unfold toyWindow2SelectedAddGate_qstart
  refine applyNat_seq_commute_update _ _ s p v ?_ ?_
  · intro f
    exact toyWindow2Case1Gate_qstart_commute_update_disjoint bits q_start N a k
      flagIdx flagPos b0Idx b1Idx p v f
      hp_disj_workspace hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1
  · intro f
    refine applyNat_seq_commute_update _ _ f p v ?_ ?_
    · intro g
      exact toyWindow2Case2Gate_qstart_commute_update_disjoint bits q_start N a k
        flagIdx flagPos b0Idx b1Idx p v g
        hp_disj_workspace hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1
    · intro g
      exact toyWindow2Case3Gate_qstart_commute_update_disjoint bits q_start N a k
        flagIdx flagPos b0Idx b1Idx p v g
        hp_disj_workspace hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1

/-- **Data-position corollary** for the shifted layout `q_start = bits`.
At any data position `p < bits` distinct from the active window
control positions and flag positions, the selected-add gate
preserves the value at `p`. This is the form directly consumed by
Architecture D's compute step. -/
theorem toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint
    (bits N a k flagIdx flagPos b0Idx b1Idx p : Nat)
    (v : Bool) (s : Nat → Bool)
    (hp_data : p < bits)
    (hp_ne_flag : p ≠ flagIdx)
    (hp_ne_flagPos : p ≠ flagPos)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k flagIdx flagPos b0Idx b1Idx)
        (update s p v)
      = update (Gate.applyNat
          (toyWindow2SelectedAddGate_qstart bits bits N a k flagIdx flagPos b0Idx b1Idx)
          s) p v :=
  toyWindow2SelectedAddGate_qstart_commute_update_disjoint
    bits bits N a k flagIdx flagPos b0Idx b1Idx p v s
    (Or.inl hp_data) hp_ne_flag hp_ne_flagPos hp_ne_b0 hp_ne_b1

/-! ## Phase R7d^xxix-L-3′ — Architecture D state-builder + data preservation

For Gidney-style Architecture D, the input state has:
- official data register at positions `[0, bits)` holding bits of `x`
  (big-endian, matching `encodeDataZeroAnc`);
- shifted Cuccaro workspace at `q_start = bits` holding the
  accumulator `acc`;
- flag position above the workspace (the first free qubit, here
  taken as `bits + 2*bits + 1`).

Window control positions are slice-aliases into the data register:
- `gidneyB0Idx bits k := bits - 1 - 2*k` (bit `2*k` of `x` in
  big-endian).
- `gidneyB1Idx bits k := bits - 1 - (2*k + 1)` (bit `2*k + 1` of `x`).

This phase introduces the Architecture D state-builder
`gidneyComputeInput`, basic readback / disjointness lemmas, and the
**data-preservation theorem** showing the q_start-parametric
selected-add gate preserves all data positions other than the active
window controls.

Full single-window arithmetic correctness on `gidneyComputeInput`
(an actual `acc → (acc + a * windowValue) % N` advance) is deferred
to follow-up sub-ticks; it requires q_start-parametric versions of
the Cuccaro internal helpers (`mod_add_state_eq_when_control_false`,
`mod_add_above_layout_noop_on_F`, etc.) that the existing
`toyWindow2CaseN_state_eq_*` proofs depend on. Those helpers
unfold the Cuccaro adder internals and require careful porting. -/

/-- **Architecture D window-0 control position.** Bit `2*k` of `x`
lives at this position in the big-endian data register. -/
def gidneyB0Idx (bits k : Nat) : Nat := bits - 1 - 2 * k

/-- **Architecture D window-1 control position.** Bit `2*k + 1` of
`x` lives at this position in the big-endian data register. -/
def gidneyB1Idx (bits k : Nat) : Nat := bits - 1 - (2 * k + 1)

/-- **Architecture D flag position.** First free qubit above the
shifted Cuccaro workspace, available as scratch for the case-gate
CCX target. -/
def gidneyFlagPos (bits : Nat) : Nat := bits + 2 * bits + 1

/-- **Architecture D compute input state.** Data positions `[0, bits)`
encode `x` (big-endian, matching `encodeDataZeroAnc`); the shifted
Cuccaro workspace at `q_start = bits` encodes `acc`; positions
outside both regions fall through to the Cuccaro `false` base. -/
def gidneyComputeInput (bits x acc : Nat) : Nat → Bool :=
  fun q =>
    if q < bits then x.testBit (bits - 1 - q)
    else cuccaro_input_F bits false 0 acc q

/-- **Data-position readback.** At any data position `q < bits`, the
state stores `x.testBit (bits - 1 - q)`. -/
theorem gidneyComputeInput_data (bits x acc q : Nat) (hq : q < bits) :
    gidneyComputeInput bits x acc q = x.testBit (bits - 1 - q) := by
  unfold gidneyComputeInput
  rw [if_pos hq]

/-- **Window-0 readback.** At `gidneyB0Idx bits k`, the state holds
bit `2*k` of `x`. -/
theorem gidneyComputeInput_b0 (bits x acc k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyComputeInput bits x acc (gidneyB0Idx bits k) = x.testBit (2 * k) := by
  show gidneyComputeInput bits x acc (bits - 1 - 2 * k) = x.testBit (2 * k)
  have h_lt : bits - 1 - 2 * k < bits := by omega
  rw [gidneyComputeInput_data bits x acc _ h_lt]
  congr 1
  omega

/-- **Window-1 readback.** At `gidneyB1Idx bits k`, the state holds
bit `2*k + 1` of `x`. -/
theorem gidneyComputeInput_b1 (bits x acc k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyComputeInput bits x acc (gidneyB1Idx bits k) = x.testBit (2 * k + 1) := by
  show gidneyComputeInput bits x acc (bits - 1 - (2 * k + 1)) = x.testBit (2 * k + 1)
  have h_lt : bits - 1 - (2 * k + 1) < bits := by omega
  rw [gidneyComputeInput_data bits x acc _ h_lt]
  congr 1
  omega

/-- **Flag position readback (zero).** At `gidneyFlagPos bits`, the
state holds `false` whenever `acc < 2^bits` (so `acc.testBit bits =
false`). The position is `bits + 2*bits + 1` which, relative to the
shifted Cuccaro at `q_start = bits`, sits at offset `2*bits + 1` —
the first odd offset above the workspace, decoding to
`acc.testBit bits`. -/
theorem gidneyComputeInput_at_flagPos (bits x acc : Nat)
    (hbits : 1 ≤ bits) (hacc_lt : acc < 2^bits) :
    gidneyComputeInput bits x acc (gidneyFlagPos bits) = false := by
  unfold gidneyComputeInput gidneyFlagPos
  have h_ge : ¬ bits + 2 * bits + 1 < bits := by omega
  rw [if_neg h_ge]
  unfold cuccaro_input_F
  have h_not_lt : ¬ (bits + 2 * bits + 1 < bits) := by omega
  rw [if_neg h_not_lt]
  have h_idx : bits + 2 * bits + 1 - bits = 2 * bits + 1 := by omega
  rw [h_idx]
  have h_ne_zero : ¬ (2 * bits + 1 = 0) := by omega
  rw [if_neg h_ne_zero]
  have h_odd : (2 * bits + 1) % 2 = 1 := by omega
  rw [if_pos h_odd]
  have h_div : (2 * bits + 1 - 1) / 2 = bits := by omega
  rw [h_div]
  exact Nat.testBit_eq_false_of_lt hacc_lt

/-! ### Shifted-layout arithmetic helpers -/

/-- `gidneyB0Idx k` is a data position when the window fits. -/
private theorem gidneyB0_lt_bits (bits k : Nat) (hwin : 2 * k + 1 < bits) :
    gidneyB0Idx bits k < bits := by
  unfold gidneyB0Idx; omega

/-- `gidneyB1Idx k` is a data position when the window fits. -/
private theorem gidneyB1_lt_bits (bits k : Nat) (hwin : 2 * k + 1 < bits) :
    gidneyB1Idx bits k < bits := by
  unfold gidneyB1Idx; omega

/-- The two window control positions for a single window are
distinct. -/
private theorem gidneyB0_ne_gidneyB1 (bits k : Nat) (hwin : 2 * k + 1 < bits) :
    gidneyB0Idx bits k ≠ gidneyB1Idx bits k := by
  unfold gidneyB0Idx gidneyB1Idx; omega

/-- `gidneyFlagPos` is above the shifted Cuccaro workspace. -/
private theorem gidneyFlag_above_workspace (bits : Nat) :
    bits + 2 * bits + 1 ≤ gidneyFlagPos bits := by
  unfold gidneyFlagPos; omega

/-- Any data position is distinct from `gidneyFlagPos`. -/
private theorem gidneyFlag_ne_data (bits q : Nat) (hq : q < bits) :
    q ≠ gidneyFlagPos bits := by
  unfold gidneyFlagPos; omega

/-- `gidneyFlagPos` is distinct from the window-0 control. -/
private theorem gidneyFlagPos_ne_gidneyB0 (bits k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyFlagPos bits ≠ gidneyB0Idx bits k := by
  unfold gidneyFlagPos gidneyB0Idx; omega

/-- `gidneyFlagPos` is distinct from the window-1 control. -/
private theorem gidneyFlagPos_ne_gidneyB1 (bits k : Nat)
    (hwin : 2 * k + 1 < bits) :
    gidneyFlagPos bits ≠ gidneyB1Idx bits k := by
  unfold gidneyFlagPos gidneyB1Idx; omega

/-! ### State-builder reconstruction lemma

The data-preservation theorem uses the observation that updating a
state at position `p` and then applying the gate is the same as
applying the gate first and then updating at `p`, provided `p` is
disjoint from the gate's support. This is exactly the L-2′ frame
theorem. The state-builder reconstruction shows we can express
`gidneyComputeInput bits x acc` as the underlying `cuccaro_input_F`
base with successive data-position updates — but we don't actually
need this; the direct evaluation at q for the gate's output state
follows from a single application of L-2′. -/

/-- **PRIMARY L-3′ THEOREM: data-position preservation under the
shifted-workspace selected-add gate.**

At any data position `q < bits` other than the active window
controls `gidneyB0Idx bits k` and `gidneyB1Idx bits k`, the gate
preserves the value of `gidneyComputeInput bits x acc q`.

The proof is a single application of the L-2′ data-position frame
theorem (`toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint`)
applied to the difference between the input state and a "zeroed at
q" state. -/
theorem toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint
    (bits N a k acc x q : Nat)
    (hwin : 2 * k + 1 < bits)
    (hq : q < bits)
    (hq_ne_b0 : q ≠ gidneyB0Idx bits k)
    (hq_ne_b1 : q ≠ gidneyB1Idx bits k) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k
          (gidneyFlagPos bits) (gidneyFlagPos bits)
          (gidneyB0Idx bits k) (gidneyB1Idx bits k))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  -- Strategy: express gidneyComputeInput as
  --   update (substateWithQReplaced) q (gidneyComputeInput bits x acc q)
  -- Then apply L-2′ to commute the gate past the outer update, since
  -- q is disjoint from b0Idx, b1Idx, flagPos.
  -- The update commutes through the gate; reading at q gives the
  -- assigned value, which is the original gidneyComputeInput value at q.
  set f := gidneyComputeInput bits x acc with hf_def
  have h_self : update f q (f q) = f := FormalRV.Framework.update_self f q
  have h_qne_flag : q ≠ gidneyFlagPos bits := gidneyFlag_ne_data bits q hq
  have h_commute := toyWindow2SelectedAddGate_qstart_commute_update_data_disjoint
    bits N a k (gidneyFlagPos bits) (gidneyFlagPos bits)
    (gidneyB0Idx bits k) (gidneyB1Idx bits k) q (f q) f
    hq h_qne_flag h_qne_flag hq_ne_b0 hq_ne_b1
  -- h_commute : applyNat gate (update f q (f q)) = update (applyNat gate f) q (f q)
  rw [h_self] at h_commute
  -- h_commute : applyNat gate f = update (applyNat gate f) q (f q)
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Corollary: data-position preservation at non-window positions.**
For data positions `q < bits` that fall OUTSIDE the active window
(`q < gidneyB1Idx bits k ∨ q > gidneyB0Idx bits k`), the gate
preserves the value. Useful when iterating over multi-window
products. -/
theorem toyWindow2SelectedAddGate_qstart_preserves_data_outside_window
    (bits N a k acc x q : Nat)
    (hwin : 2 * k + 1 < bits)
    (hq : q < bits)
    (h_outside : q < bits - 1 - (2 * k + 1) ∨ bits - 1 - 2 * k < q) :
    Gate.applyNat
        (toyWindow2SelectedAddGate_qstart bits bits N a k
          (gidneyFlagPos bits) (gidneyFlagPos bits)
          (gidneyB0Idx bits k) (gidneyB1Idx bits k))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have hq_ne_b0 : q ≠ gidneyB0Idx bits k := by
    unfold gidneyB0Idx
    rcases h_outside with h | h <;> omega
  have hq_ne_b1 : q ≠ gidneyB1Idx bits k := by
    unfold gidneyB1Idx
    rcases h_outside with h | h <;> omega
  exact toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint
    bits N a k acc x q hwin hq hq_ne_b0 hq_ne_b1

/-! ### Status: R7d^xxix-L-3′ partial deliverable

What landed:
- Architecture D layout primitives:
  `gidneyB0Idx`, `gidneyB1Idx`, `gidneyFlagPos`, `gidneyComputeInput`.
- Readback lemmas: `_data`, `_b0`, `_b1`, `_at_flagPos`.
- Shifted-layout arithmetic helpers (B0_lt_bits, B1_lt_bits,
  B0_ne_B1, flag_above_workspace, flag_ne_data, flagPos_ne_b0/b1).
- Primary deliverable: **data-position preservation theorem**
  `toyWindow2SelectedAddGate_qstart_preserves_data_at_disjoint`
  showing all non-active data positions are preserved.
- Outside-window corollary
  `toyWindow2SelectedAddGate_qstart_preserves_data_outside_window`.

What is deferred to follow-up ticks (full single-window arithmetic
correctness):
- q_start-parametric versions of the Cuccaro internal helpers:
  - `mod_add_state_eq_when_control_false_on_qstart_input`.
  - `mod_add_above_layout_noop_on_F` at q_start.
- q_start-parametric per-case state-eq theorems
  (Case1/2/3 FF/FT/TF/TT no-op or fire branches).
- The composed q_start selected-add state-equation theorem
  `toyWindow2SelectedAddGate_qstart_state_eq_on_gidneyComputeInput`.

Why deferred: the existing q_start = 2 state-eq theorems
(`toyWindow2Case3Gate_state_eq_FF_noop`, etc.) span ~200 lines each
because they unfold the Cuccaro adder internals at the specific
positions of the q_start = 2 layout. A clean port to q_start
requires ~6-8 helper lemmas to be ported first, each ~100-200
lines. This is a multi-tick effort that should follow its own
dedicated planning. -/

/-! ## Phase R7d^xxix-L-3.5′ — q_start controlled-mod-add preservation

This phase closes the q_start-parametric **frame-based**
preservation theorem for the controlled mod-add gate
`sqir_style_controlledModAddConst_gate bits q_start N c controlIdx
flagPos`.

**Scope**: positions OUTSIDE the gate's working set are proven
preserved (a strict subset of "full no-op when control is false",
but the workspace/control/flagPos preservation requires the FULL
clean theorem at q_start which is multi-tick effort).

**Why the FULL state preservation is deferred**:
- The q_start = 2 clean theorem
  (`sqir_style_controlledModAddConst_gate_clean`) bakes in
  q_start = 2 AND flagPos = 1 throughout its multi-stage proof
  (deliverables A through G, each ~50-200 lines, in
  `CuccaroSQIRDirtyFlag.lean`).
- The `ControlledModAdd.clean_*` projections used by
  `mod_add_state_eq_when_control_false_on_Case3Input` extract from
  the q_start = 2 clean bundle; they do NOT generalize to q_start =
  bits without a parallel clean theorem.
- Porting clean to parametric q_start requires touching the entire
  `sqir_style_controlledModAddConst_gate_clean` proof chain,
  redoing each deliverable.

**What L-3.5′ achieves**: the FRAME-based preservation gives us
"the gate preserves any state at positions outside the workspace
and outside control/flag positions". This is a clean, useful
result that survives any future clean-theorem port. -/

/-- **q_start frame preservation: gate preserves state at any single
position disjoint from its working set.** Direct consequence of the
L-2′ `sqir_modAdd_qstart_commute_update_disjoint` via
`update_self`. -/
theorem sqir_modAdd_qstart_preserves_at_outside
    (bits q_start N c controlIdx flagPos q : Nat) (s : Nat → Bool)
    (h_q_outside :
      q < q_start ∨ q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos)
    (h_q_ne_control : q ≠ controlIdx) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos) s q
      = s q := by
  have h_self : update s q (s q) = s := FormalRV.Framework.update_self s q
  have h_commute := sqir_modAdd_qstart_commute_update_disjoint
    bits q_start N c controlIdx flagPos q (s q) s
    h_q_outside h_q_ne_flag h_q_ne_control
  rw [h_self] at h_commute
  have h_at_q := congr_fun h_commute q
  rw [FormalRV.Framework.update_eq] at h_at_q
  exact h_at_q

/-- **Above-layout no-op specialization** (matches the prompt's
Step 2 fallback shape). On the zero-accumulator Cuccaro base
`cuccaro_input_F q_start false 0 acc`, at any position above the
workspace + ≠ flagPos, the gate yields `false`. -/
theorem mod_add_above_layout_noop_on_F_qstart
    (bits q_start N c flagPos acc q : Nat)
    (hacc : acc < 2^bits)
    (h_q_above : q_start + 2 * bits + 1 ≤ q)
    (h_q_ne_flag : q ≠ flagPos) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N c flagPos flagPos)
        (cuccaro_input_F q_start false 0 acc) q
      = false := by
  rw [sqir_modAdd_qstart_preserves_at_outside bits q_start N c
        flagPos flagPos q _ (Or.inr h_q_above) h_q_ne_flag h_q_ne_flag]
  exact cuccaro_input_F_above_eq_false q_start bits acc q h_q_above hacc

/-- **Architecture D mod-add preservation at data positions.** For
any data position `q < bits`, the q_start = bits controlled
mod-add gate (with control = flag = gidneyFlagPos) preserves the
value of `gidneyComputeInput bits x acc` at `q`.

This holds because data positions `q < bits = q_start` are below
the shifted workspace, and `gidneyFlagPos = 3*bits + 1 > bits >
q`. -/
theorem sqir_modAdd_qstart_preserves_data_on_gidneyComputeInput
    (bits N c x acc q : Nat)
    (hq : q < bits) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate
          bits bits N c (gidneyFlagPos bits) (gidneyFlagPos bits))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have h_q_outside : q < bits ∨ bits + 2 * bits + 1 ≤ q := Or.inl hq
  have h_q_ne_flag : q ≠ gidneyFlagPos bits := gidneyFlag_ne_data bits q hq
  exact sqir_modAdd_qstart_preserves_at_outside bits bits N c
    (gidneyFlagPos bits) (gidneyFlagPos bits) q _ h_q_outside
    h_q_ne_flag h_q_ne_flag

/-- **Architecture D mod-add preservation above the flag.** For
any position `q > gidneyFlagPos bits`, the q_start = bits
controlled mod-add gate preserves the value of `gidneyComputeInput
bits x acc` at `q`. -/
theorem sqir_modAdd_qstart_preserves_above_flag_on_gidneyComputeInput
    (bits N c x acc q : Nat)
    (h_q_above : gidneyFlagPos bits < q) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate
          bits bits N c (gidneyFlagPos bits) (gidneyFlagPos bits))
        (gidneyComputeInput bits x acc) q
      = gidneyComputeInput bits x acc q := by
  have h_q_workspace_above : bits + 2 * bits + 1 ≤ q := by
    have : bits + 2 * bits + 1 = gidneyFlagPos bits := by unfold gidneyFlagPos; rfl
    omega
  have h_q_outside : q < bits ∨ bits + 2 * bits + 1 ≤ q := Or.inr h_q_workspace_above
  have h_q_ne_flag : q ≠ gidneyFlagPos bits := by
    intro h_eq; rw [h_eq] at h_q_above; exact absurd h_q_above (Nat.lt_irrefl _)
  exact sqir_modAdd_qstart_preserves_at_outside bits bits N c
    (gidneyFlagPos bits) (gidneyFlagPos bits) q _ h_q_outside
    h_q_ne_flag h_q_ne_flag

/-- **c = 0 trivial no-op.** When the constant being added is 0,
the controlled mod-add gate is literally `Gate.I`. -/
theorem sqir_style_controlledModAddConst_gate_qstart_zero_noop
    (bits q_start N controlIdx flagPos : Nat) (s : Nat → Bool) :
    Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits q_start N 0 controlIdx flagPos) s
      = s := by
  unfold sqir_style_controlledModAddConst_gate
  rw [if_pos rfl]
  exact Gate.applyNat_I s

/-! ## Phase R7d^xxix-L-3.6′ — Architecture D control=false target-decode

The L-3.6′ tick ported the control=false target-decode of the
controlled mod-add candidate from q_start = 2 + flagPos = 1 to
parametric q_start + flagPos (see `BQAlgo/CuccaroSQIRDirtyFlag.lean`
for the chain of five ports).

This section specializes the new ported theorem to Architecture D
(q_start = bits, flagPos = gidneyFlagPos bits). The specialization
is the FIRST architectural-correctness theorem for the Gidney-style
layout: it shows that when the control bit is false, the mod-add
gate's target decode equals the original `x`. -/

/-- **Architecture D second ancilla position.** Allocated just above
`gidneyFlagPos bits` so the controlled mod-add can use two distinct
above-workspace positions for its external control and internal
flag. -/
def gidneyFlagPos' (bits : Nat) : Nat := gidneyFlagPos bits + 1

/-- `gidneyFlagPos' bits` is distinct from `gidneyFlagPos bits`. -/
private theorem gidneyFlagPos'_ne_gidneyFlagPos (bits : Nat) :
    gidneyFlagPos' bits ≠ gidneyFlagPos bits := by
  unfold gidneyFlagPos' gidneyFlagPos; omega

/-- `gidneyFlagPos' bits` is also above the shifted workspace. -/
private theorem gidneyFlagPos'_above_workspace (bits : Nat) :
    bits + 2 * bits + 1 ≤ gidneyFlagPos' bits := by
  unfold gidneyFlagPos' gidneyFlagPos; omega

/-- **Architecture D control=false target-decode.** When the
external control at `gidneyFlagPos' bits` is `false`, the controlled
mod-add candidate (with `q_start = bits`, controlIdx = `gidneyFlagPos'
bits`, internal flagPos = `gidneyFlagPos bits`) preserves the
target's decoded value at `x`. -/
theorem sqir_style_controlledModAddConst_candidate_target_decode_control_false_gidney
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_target_val bits bits
        (Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
      = x := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_target_decode_control_false_qstart
    bits bits N c x (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)

/-- **R7d^xxix-L-3.7′ Gidney specialization (workspace bundle,
control=false).**  The Architecture-D controlled mod-add (external
control = `gidneyFlagPos' bits`, internal flagPos = `gidneyFlagPos
bits`) preserves the four workspace conjuncts after applying to the
shifted-workspace `cuccaro_input_F` base with control=false. -/
theorem sqir_style_controlledModAddConst_candidate_workspace_control_false_gidney
    (bits N c x : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N) :
    cuccaro_read_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (bits + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos' bits)
        = false := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_workspace_control_false_qstart
    bits bits N c x (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)

/-- **R7d^xxix-L-3.8′ Gidney specialization (clean bundle,
control=false).**  The Architecture-D controlled mod-add (q_start =
`bits`, internal flagPos = `gidneyFlagPos bits`, external controlIdx =
`gidneyFlagPos' bits`) clean bundle for the control=false branch.

Parametric in `dim` with the three standard dimension hypotheses:
- the shifted Cuccaro workspace fits: `bits + 2 * bits + 1 ≤ dim`;
- `gidneyFlagPos' bits < dim`;
- `gidneyFlagPos bits < dim`.

Trivial wrapper over
`sqir_style_controlledModAddConst_candidate_clean_control_false_qstart`. -/
theorem sqir_style_controlledModAddConst_candidate_clean_control_false_gidney
    (bits N c x dim : Nat)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hc_pos : 0 < c) (hc : c < N) (hx : x < N)
    (h_workspace : bits + 2 * bits + 1 ≤ dim)
    (h_flagPos'_lt_dim : gidneyFlagPos' bits < dim)
    (h_flagPos_lt_dim  : gidneyFlagPos bits  < dim) :
    Gate.WellTyped dim
        (sqir_style_controlledModAddConst_candidate bits bits N c
          (gidneyFlagPos' bits) (gidneyFlagPos bits))
    ∧ cuccaro_target_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = x
    ∧ cuccaro_read_val bits bits
          (Gate.applyNat
            (sqir_style_controlledModAddConst_candidate bits bits N c
              (gidneyFlagPos' bits) (gidneyFlagPos bits))
            (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false))
        = 0
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (bits + 2 * bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos bits)
        = false
    ∧ Gate.applyNat
          (sqir_style_controlledModAddConst_candidate bits bits N c
            (gidneyFlagPos' bits) (gidneyFlagPos bits))
          (update (cuccaro_input_F bits false 0 x) (gidneyFlagPos' bits) false)
          (gidneyFlagPos' bits)
        = false := by
  have h_flagPos'_above : bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    gidneyFlagPos'_above_workspace bits
  have h_flagPos_above : bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    gidneyFlag_above_workspace bits
  have h_ctrl_out :
      gidneyFlagPos' bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos' bits :=
    Or.inr h_flagPos'_above
  have h_flag_out :
      gidneyFlagPos bits < bits ∨ bits + 2 * bits + 1 ≤ gidneyFlagPos bits :=
    Or.inr h_flagPos_above
  exact sqir_style_controlledModAddConst_candidate_clean_control_false_qstart
    bits bits N c x dim (gidneyFlagPos' bits) (gidneyFlagPos bits)
    hbits hN_pos hN hN2 hc_pos hc hx h_ctrl_out h_flag_out
    (gidneyFlagPos'_ne_gidneyFlagPos bits)
    h_workspace h_flagPos'_lt_dim h_flagPos_lt_dim

/-! ### Status: R7d^xxix-L-3.5′ partial deliverable

**Closed** (kernel-clean):
- `sqir_modAdd_qstart_preserves_at_outside` (generic single-position
  frame preservation).
- `mod_add_above_layout_noop_on_F_qstart` (above-layout no-op on
  cuccaro_input_F base, the prompt's Step 2 fallback shape).
- `sqir_modAdd_qstart_preserves_data_on_gidneyComputeInput`
  (Architecture D specialization at data positions).
- `sqir_modAdd_qstart_preserves_above_flag_on_gidneyComputeInput`
  (Architecture D specialization above flag).
- `sqir_style_controlledModAddConst_gate_qstart_zero_noop` (c = 0
  trivial no-op).

**Deferred** (require q_start clean theorem port, multi-tick):
- `sqir_style_controlledModAddConst_gate_qstart_noop_of_control_false`:
  full-state no-op when the control bit is false. Requires the
  q_start-parametric versions of
  `ControlledModAdd.clean_controlPreserved`,
  `ControlledModAdd.clean_flagFalse`,
  `ControlledModAdd.clean_targetDecode` (with control = false),
  and `ControlledModAdd.clean_readZero`. These all factor through
  `sqir_style_controlledModAddConst_gate_clean` which is q_start
  = 2 hard-coded.
- `sqir_style_controlledModAddConst_gate_qstart_noop_on_gidneyComputeInput`
  (the full Architecture-D specialization).
- `toyWindow2SelectedAddGate_qstart_FF_noop_on_gidneyComputeInput`
  (depends on the above).

The deferred theorems are NOT structural — they're proof-engineering
liabilities. The roadmap for porting them is:
1. Port `sqir_style_controlledModAddConst_gate_clean` to parametric
   q_start AND parametric flagPos (the latter being the harder
   change). ~6 subordinate clean lemmas, each ~50-200 lines.
2. Build q_start-parametric `ControlledModAddImpl` instance for
   q_start = bits and the gidneyFlagPos convention.
3. Extract `clean_*` projections.
4. Port `mod_add_state_eq_when_control_false_on_Case3Input` to
   parametric layout.
5. Use to build FF / FT / TF / TT case state_eq theorems for
   `toyWindow2CaseN_qstart`.
6. Compose into full `toyWindow2SelectedAddGate_qstart_state_eq`. -/

/-! ## Phase R7d^xxiv — per-window selected-add frame helper

The frame helper for the toy windowSize=2 selected-add gate. Says that
the gate commutes with an `update _ p v` whenever `p` is "inactive":
above the Cuccaro workspace, distinct from the gate's active window
positions, and distinct from `flagIdx`.

This is the key bridge for proving the full multi-window correctness
theorem `toyWindow2SelectedAddGate_on_windowed2Input` (see the docstring
of that theorem stub below for the proof strategy). -/

/-- **Frame helper for the selected-add gate.**

`toyWindow2SelectedAddGate` at active window positions `(b0Idx, b1Idx,
flagIdx)` commutes with any `update _ p v` where `p` is disjoint from
the gate's support. Specifically:
- `p` is above the Cuccaro workspace (`p ≥ 2 + 2*bits + 1`),
- `p` is not the active b0 / b1 positions,
- `p` is not `flagIdx`.

The proof composes primitive frame lemmas (`Gate.applyNat_X_commute
_update_outside_fun`, `applyNat_CCX_commute_update_disjoint`,
`sqir_style_controlledModAddConst_gate_commute_update_outside_fun`)
through `applyNat_seq_commute_update` per case gate (Case 1, 2, 3), then
chains the three case gates via two more `applyNat_seq_commute_update`. -/
theorem toyWindow2SelectedAddGate_commute_update_inactive
    (bits N a k flagIdx b0Idx b1Idx p : Nat) (v : Bool) (s : Nat → Bool)
    (hp_hi : 2 + 2 * bits + 1 ≤ p)
    (hp_ne_b0 : p ≠ b0Idx)
    (hp_ne_b1 : p ≠ b1Idx)
    (hp_ne_flag : p ≠ flagIdx) :
    Gate.applyNat (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx)
        (update s p v)
      = update
          (Gate.applyNat
            (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx) s)
          p v := by
  have hp_out : p < 2 ∨ 2 + (2 * bits + 1) ≤ p := Or.inr (by omega)
  have hp_ne_one : p ≠ 1 := by omega
  -- Primitive commute proofs (universally quantified over inner state).
  have hX_b0 : ∀ f', Gate.applyNat (Gate.X b0Idx) (update f' p v)
                    = update (Gate.applyNat (Gate.X b0Idx) f') p v :=
    fun f' => Gate.applyNat_X_commute_update_outside_fun b0Idx p v f' hp_ne_b0
  have hX_b1 : ∀ f', Gate.applyNat (Gate.X b1Idx) (update f' p v)
                    = update (Gate.applyNat (Gate.X b1Idx) f') p v :=
    fun f' => Gate.applyNat_X_commute_update_outside_fun b1Idx p v f' hp_ne_b1
  have hCCX : ∀ f', Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx)
                       (update f' p v)
                  = update (Gate.applyNat (Gate.CCX b0Idx b1Idx flagIdx) f') p v :=
    fun f' => applyNat_CCX_commute_update_disjoint b0Idx b1Idx flagIdx f' p v
                hp_ne_b0 hp_ne_b1 hp_ne_flag
  have hM1 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 1) flagIdx 1) f') p v :=
    fun f' => sqir_style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 1) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  have hM2 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 2) flagIdx 1) f') p v :=
    fun f' => sqir_style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 2) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  have hM3 : ∀ f', Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1) (update f' p v)
                  = update (Gate.applyNat
                     (sqir_style_controlledModAddConst_gate bits 2 N
                       (tableValue a N 2 k 3) flagIdx 1) f') p v :=
    fun f' => sqir_style_controlledModAddConst_gate_commute_update_outside_fun
                bits N (tableValue a N 2 k 3) flagIdx p v f'
                hp_out hp_ne_one hp_ne_flag
  -- Case-1 gate commute (5-layer seq X-CCX-M-CCX-X).
  have hCase1 : ∀ f', Gate.applyNat
                        (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.X b1Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 1) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b1Idx)))))
          (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hX_b1
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCCX
              (fun f''' => applyNat_seq_commute_update _ _ f''' p v hM1
                (fun f'''' => applyNat_seq_commute_update _ _ f'''' p v hCCX hX_b1)))
  -- Case-2 gate commute (5-layer seq X-CCX-M-CCX-X).
  have hCase2 : ∀ f', Gate.applyNat
                        (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.X b0Idx)
            (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
              (Gate.seq
                (sqir_style_controlledModAddConst_gate bits 2 N
                  (tableValue a N 2 k 2) flagIdx 1)
                (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx) (Gate.X b0Idx)))))
          (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hX_b0
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCCX
              (fun f''' => applyNat_seq_commute_update _ _ f''' p v hM2
                (fun f'''' => applyNat_seq_commute_update _ _ f'''' p v hCCX hX_b0)))
  -- Case-3 gate commute (3-layer seq CCX-M-CCX).
  have hCase3 : ∀ f', Gate.applyNat
                        (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)
                        (update f' p v)
                    = update (Gate.applyNat
                        (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx) f')
                        p v := by
    intro f'
    show Gate.applyNat (Gate.seq (Gate.CCX b0Idx b1Idx flagIdx)
            (Gate.seq
              (sqir_style_controlledModAddConst_gate bits 2 N
                (tableValue a N 2 k 3) flagIdx 1)
              (Gate.CCX b0Idx b1Idx flagIdx))) (update f' p v) = _
    exact applyNat_seq_commute_update _ _ f' p v hCCX
            (fun f'' => applyNat_seq_commute_update _ _ f'' p v hM3 hCCX)
  -- Compose: toyWindow2SelectedAddGate = Case1Gate ; Case2Gate ; Case3Gate.
  show Gate.applyNat (Gate.seq (toyWindow2Case1Gate bits N a k flagIdx b0Idx b1Idx)
          (Gate.seq (toyWindow2Case2Gate bits N a k flagIdx b0Idx b1Idx)
                    (toyWindow2Case3Gate bits N a k flagIdx b0Idx b1Idx)))
        (update s p v) = _
  exact applyNat_seq_commute_update _ _ s p v hCase1
          (fun f'' => applyNat_seq_commute_update _ _ f'' p v hCase2 hCase3)

/-! ### Documentation: main multi-window theorem strategy

The full main theorem
```
toyWindow2SelectedAddGate_on_windowed2Input : ∀ ... ,
  Gate.applyNat (toyWindow2SelectedAddGate ... k ... (b0Idx k) (b1Idx k))
      (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
    = windowed2Input
        (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
        b0Idx b1Idx b0 b1 numWin
```
is proved by induction on `numWin`. Two cases per step (`numWin = n + 1`):

**Case B (k < n, inactive newest):** The two outermost updates of
`windowed2Input ... (n+1)` are at the inactive positions
`(b0Idx n, b1Idx n)`. By cross-window distinctness, these positions
satisfy the frame helper's "inactive" predicate
(`p ≠ b0Idx k`, `p ≠ b1Idx k`, `p ≠ flagIdx`, `p ≥ 2 + 2*bits + 1`).
Apply `toyWindow2SelectedAddGate_commute_update_inactive` twice to push
the two outer updates outside the gate, then apply the inductive
hypothesis on the inner `windowed2Input ... n`, then re-apply
`windowed2Input_succ` to reconstruct the result.

**Case A (k = n, active newest):** The outer two updates ARE the
active layer `(b0Idx n, b1Idx n) = (b0Idx k, b1Idx k)`. Inside is
`windowed2Input ... n` containing `n` inactive prefix layers. To apply
`toyWindow2SelectedAddGate_state_eq_spec`, we need the inner state to
be `cuccaro_input_F 2 false 0 acc` (i.e., no inactive prefix).
Strategy: inner induction on `n` (the inactive prefix size).
- Inner base `n = 0`: inner state IS `cuccaro_input_F`. State is a
  literal `toyWindow2Case3Input`. Apply spec directly.
- Inner step `n = j + 1`: the inner state has outer layer `(b0Idx j,
  b1Idx j)`. Use `update_comm` (four times) to swap this layer past
  the active `(b0Idx k, b1Idx k)` updates, bringing the inactive layer
  outermost. Use the frame helper to commute the inactive layer through
  the gate. Use inner IH on the stripped state. Then `update_comm` back.

Hypotheses required: cross-window distinctness `b0Idx i ≠ b0Idx j`,
`b1Idx i ≠ b1Idx j`, `b0Idx i ≠ b1Idx j` (for any i, j with i ≠ j),
plus the existing single-window hypotheses. The four `update_comm`
swaps need each pair (`b0Idx k`, `b1Idx k`) × (`b0Idx j`, `b1Idx j`)
to be distinct — which is exactly the cross-window distinctness.

This proof structure is mechanically clear but verbose (~150–200 lines
total). Deferred to a follow-up tick to keep this commit focused on
the reusable frame infrastructure. -/

/-! ## Phase R7d^xxv — per-window selected-add on multi-window input

Closes the per-window theorem `toyWindow2SelectedAddGate_on_windowed2Input`
using the frame helper from R7d^xxiv.

Strategy:
- Auxiliary `toyWindow2SelectedAddGate_active_extended` handles the
  "active gate applied to a Case3Input-like state extended by an
  inactive prefix". Proven by induction on the prefix size with
  `update_comm` swaps + frame helper + IH.
- Main theorem handles arbitrary `numWin` by outer induction:
  - Active newest (k = n): reduce to the auxiliary at m = n, k = n.
  - Inactive newest (k < n): apply frame helper twice + IH on the
    inner `windowed2Input ... n`. -/

/-- **Active-extended auxiliary.** The selected-add gate at fixed
active window index `k` applied to an inactive prefix of size `m`
(with `m ≤ k`) plus the active layer produces the same shape with
the accumulator updated per `windowedStepSpec`.

Proven by induction on `m`. The base case (`m = 0`) is the pure
`Case3Input` shape and applies the spec directly. The inductive case
uses 4 `update_comm` swaps to bring the inactive m-th layer outside
the active layer, applies the frame helper twice to push it past the
gate, then applies the IH on the smaller prefix. -/
private theorem toyWindow2SelectedAddGate_active_extended
    (bits N a acc flagIdx k : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i ≤ k → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i ≤ k → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i ≤ k → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 : ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b1Idx j) :
    ∀ (m : Nat), m ≤ k →
      Gate.applyNat
          (toyWindow2SelectedAddGate bits N a k flagIdx (b0Idx k) (b1Idx k))
          (update (update (windowed2Input acc b0Idx b1Idx b0 b1 m)
                     (b0Idx k) (b0 k)) (b1Idx k) (b1 k))
        = update (update (windowed2Input
            (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
            b0Idx b1Idx b0 b1 m) (b0Idx k) (b0 k)) (b1Idx k) (b1 k) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [windowed2Input_zero, windowed2Input_zero]
    have h_k_le_k : k ≤ k := Nat.le_refl k
    show Gate.applyNat _ (toyWindow2Case3Input acc (b0Idx k) (b1Idx k) (b0 k) (b1 k))
       = toyWindow2Case3Input
           (windowedStepSpec a N 2 k acc (windowBits2_to_v (b0 k) (b1 k)))
           (b0Idx k) (b1Idx k) (b0 k) (b1 k)
    exact toyWindow2SelectedAddGate_state_eq_spec bits N a k acc flagIdx
      (b0Idx k) (b1Idx k) (b0 k) (b1 k)
      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
      (h_hi0 k h_k_le_k) (h_hi1 k h_k_le_k) (h_b0_ne_b1 k h_k_le_k)
      (h_b0_ne_flag k h_k_le_k) (h_b1_ne_flag k h_k_le_k)
  | succ j ih =>
    intro hmk
    have hjk : j ≤ k :=
      Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hmk)
    have hjk_ne : j ≠ k :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hmk)
    have h_k_le_k : k ≤ k := Nat.le_refl k
    have h_b0j_ne_b0k : b0Idx j ≠ b0Idx k :=
      h_distinct_b0_b0 j k hjk h_k_le_k hjk_ne
    have h_b0j_ne_b1k : b0Idx j ≠ b1Idx k :=
      h_distinct_b0_b1 j k hjk h_k_le_k hjk_ne
    have h_b1j_ne_b0k : b1Idx j ≠ b0Idx k :=
      h_distinct_b1_b0 j k hjk h_k_le_k hjk_ne
    have h_b1j_ne_b1k : b1Idx j ≠ b1Idx k :=
      h_distinct_b1_b1 j k hjk h_k_le_k hjk_ne
    have h_b0j_hi : 2 + 2 * bits + 1 ≤ b0Idx j := h_hi0 j hjk
    have h_b1j_hi : 2 + 2 * bits + 1 ≤ b1Idx j := h_hi1 j hjk
    have h_b0j_ne_flag : b0Idx j ≠ flagIdx := h_b0_ne_flag j hjk
    have h_b1j_ne_flag : b1Idx j ≠ flagIdx := h_b1_ne_flag j hjk
    -- Generic swap lemma: 4 update_comm reorderings.
    have swap : ∀ (W : Nat → Bool),
        update (update (update (update W (b0Idx j) (b0 j)) (b1Idx j) (b1 j))
            (b0Idx k) (b0 k)) (b1Idx k) (b1 k)
      = update (update (update (update W (b0Idx k) (b0 k)) (b1Idx k) (b1 k))
            (b0Idx j) (b0 j)) (b1Idx j) (b1 j) := by
      intro W
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1j_ne_b0k]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0j_ne_b0k]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b1j_ne_b1k]
      rw [FormalRV.Framework.update_comm _ _ _ _ _ h_b0j_ne_b1k]
    -- Unfold `windowed2Input ... (j+1)` on both sides via simp on the
    -- @[simp] succ unfold (covers both LHS acc and RHS acc' instances).
    simp only [windowed2Input_succ]
    -- Swap the active layer past the inactive m-th layer (both sides).
    rw [swap (windowed2Input acc b0Idx b1Idx b0 b1 j)]
    rw [swap (windowed2Input
              (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
              b0Idx b1Idx b0 b1 j)]
    -- Push the inactive layer past the gate via frame helper.
    rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
          (b0Idx k) (b1Idx k) (b1Idx j) (b1 j) _
          h_b1j_hi h_b1j_ne_b0k h_b1j_ne_b1k h_b1j_ne_flag]
    rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
          (b0Idx k) (b1Idx k) (b0Idx j) (b0 j) _
          h_b0j_hi h_b0j_ne_b0k h_b0j_ne_b1k h_b0j_ne_flag]
    -- Apply IH on the smaller prefix.
    rw [ih hjk]

/-- **Per-window selected-add correctness on the multi-window
input encoding.** The selected-add gate at active window `k` (with
`k < numWin`) applied to the `windowed2Input` state produces the
same state with the accumulator advanced by `windowedStepSpec` at
the encoded window value.

Proof by induction on `numWin`:
- `k = n` (active newest): reduce to the active-extended auxiliary
  at `m = n`, `k = n`.
- `k < n` (inactive newest): apply the frame helper twice to push
  the two newest inactive updates past the gate, then apply the IH
  on the inner `windowed2Input ... n`, then reassemble. -/
theorem toyWindow2SelectedAddGate_on_windowed2Input
    (bits N a k acc flagIdx numWin : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (hk : k < numWin)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < numWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < numWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < numWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (toyWindow2SelectedAddGate bits N a k flagIdx (b0Idx k) (b1Idx k))
        (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = windowed2Input
          (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
          b0Idx b1Idx b0 b1 numWin := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · -- Active newest case: apply the auxiliary at m = n, k = n.
      subst hkn
      have h_k_le_k : k ≤ k := Nat.le_refl k
      -- Convert bounded hypotheses from i < k+1 to i ≤ k.
      have h_hi0' : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b0Idx i :=
        fun i hi => h_hi0 i (Nat.lt_succ_of_le hi)
      have h_hi1' : ∀ i, i ≤ k → 2 + 2 * bits + 1 ≤ b1Idx i :=
        fun i hi => h_hi1 i (Nat.lt_succ_of_le hi)
      have h_b0_ne_b1' : ∀ i, i ≤ k → b0Idx i ≠ b1Idx i :=
        fun i hi => h_b0_ne_b1 i (Nat.lt_succ_of_le hi)
      have h_b0_ne_flag' : ∀ i, i ≤ k → b0Idx i ≠ flagIdx :=
        fun i hi => h_b0_ne_flag i (Nat.lt_succ_of_le hi)
      have h_b1_ne_flag' : ∀ i, i ≤ k → b1Idx i ≠ flagIdx :=
        fun i hi => h_b1_ne_flag i (Nat.lt_succ_of_le hi)
      have h_distinct_b0_b0' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b0Idx j :=
        fun i j hi hj hij => h_distinct_b0_b0 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      have h_distinct_b0_b1' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b0Idx i ≠ b1Idx j :=
        fun i j hi hj hij => h_distinct_b0_b1 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      have h_distinct_b1_b0' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b0Idx j :=
        fun i j hi hj hij => h_distinct_b1_b0 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      have h_distinct_b1_b1' :
          ∀ i j, i ≤ k → j ≤ k → i ≠ j → b1Idx i ≠ b1Idx j :=
        fun i j hi hj hij => h_distinct_b1_b1 i j
          (Nat.lt_succ_of_le hi) (Nat.lt_succ_of_le hj) hij
      rw [show windowed2Input acc b0Idx b1Idx b0 b1 (k + 1) =
              update (update (windowed2Input acc b0Idx b1Idx b0 b1 k)
                (b0Idx k) (b0 k)) (b1Idx k) (b1 k) from rfl]
      rw [show windowed2Input
              (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
              b0Idx b1Idx b0 b1 (k + 1) =
              update (update (windowed2Input
                  (windowedStepSpec a N 2 k acc (windowBits2_at b0 b1 k))
                  b0Idx b1Idx b0 b1 k)
                (b0Idx k) (b0 k)) (b1Idx k) (b1 k) from rfl]
      exact toyWindow2SelectedAddGate_active_extended bits N a acc flagIdx k
        b0Idx b1Idx b0 b1
        hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_hi0' h_hi1' h_b0_ne_b1' h_b0_ne_flag' h_b1_ne_flag'
        h_distinct_b0_b0' h_distinct_b0_b1' h_distinct_b1_b0' h_distinct_b1_b1'
        k h_k_le_k
    · -- Inactive newest case (k < n): push outer two updates past gate via
      -- frame helper, apply IH on inner prefix.
      have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have hn_lt_succ : n < n + 1 := Nat.lt_succ_self n
      have h_n_ne_k : n ≠ k := fun h => hkn h.symm
      -- Frame helper hypotheses for the n-th window updates.
      have h_b0n_hi : 2 + 2 * bits + 1 ≤ b0Idx n := h_hi0 n hn_lt_succ
      have h_b1n_hi : 2 + 2 * bits + 1 ≤ b1Idx n := h_hi1 n hn_lt_succ
      have h_b0n_ne_b0k : b0Idx n ≠ b0Idx k :=
        h_distinct_b0_b0 n k hn_lt_succ hk h_n_ne_k
      have h_b0n_ne_b1k : b0Idx n ≠ b1Idx k :=
        h_distinct_b0_b1 n k hn_lt_succ hk h_n_ne_k
      have h_b1n_ne_b0k : b1Idx n ≠ b0Idx k :=
        h_distinct_b1_b0 n k hn_lt_succ hk h_n_ne_k
      have h_b1n_ne_b1k : b1Idx n ≠ b1Idx k :=
        h_distinct_b1_b1 n k hn_lt_succ hk h_n_ne_k
      have h_b0n_ne_flag : b0Idx n ≠ flagIdx := h_b0_ne_flag n hn_lt_succ
      have h_b1n_ne_flag : b1Idx n ≠ flagIdx := h_b1_ne_flag n hn_lt_succ
      -- Unfold windowed2Input ... (n+1) on both sides.
      simp only [windowed2Input_succ]
      -- Push outer two updates past gate via frame helper.
      rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
            (b0Idx k) (b1Idx k) (b1Idx n) (b1 n) _
            h_b1n_hi h_b1n_ne_b0k h_b1n_ne_b1k h_b1n_ne_flag]
      rw [toyWindow2SelectedAddGate_commute_update_inactive bits N a k flagIdx
            (b0Idx k) (b1Idx k) (b0Idx n) (b0 n) _
            h_b0n_hi h_b0n_ne_b0k h_b0n_ne_b1k h_b0n_ne_flag]
      -- Restrict hypotheses to numWin = n for IH.
      rw [ih hk_lt_n
            (fun i hi => h_hi0 i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_hi1 i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_b0_ne_b1 i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_b0_ne_flag i (Nat.lt_succ_of_lt hi))
            (fun i hi => h_b1_ne_flag i (Nat.lt_succ_of_lt hi))
            (fun i j hi hj hij =>
              h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
            (fun i j hi hj hij =>
              h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
            (fun i j hi hj hij =>
              h_distinct_b1_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
            (fun i j hi hj hij =>
              h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)]

/-! ## Phase R7d^xxvi — multi-window selected-add fold correctness

Closes the multi-window correctness theorem: the sequence of
`windowed2SelectedAddGate` applications implements the iterated
`windowedStepSpecIter2`.

Strategy: prove a **prefix theorem** with separate parameters `m`
(number of gates applied) and `totalWin` (size of the input window
encoding), then specialize `m = totalWin = numWin`. -/

/-- **Prefix theorem.** Applying the first `m` selected-add gates of
the windowSize=2 toy implementation to a `totalWin`-window input
encoding produces the same input shape with the accumulator advanced
by `windowedStepSpecIter2 ... m acc`.

Proven by induction on `m`. Base case uses `Gate.applyNat_I`. Step
case applies the IH to expose the intermediate accumulator, derives
its `< N` bound via `windowedStepSpecIter2_lt_N`, then applies
`toyWindow2SelectedAddGate_on_windowed2Input` at `k = n` and
reduces via `windowedStepSpecIter2_succ`. -/
theorem toyWindowed2SelectedAddGate_correct_prefix
    (bits N a flagIdx m totalWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (hm_le : m ≤ totalWin)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < totalWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < totalWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < totalWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < totalWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < totalWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < totalWin → j < totalWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
          bits flagIdx b0Idx b1Idx m)
        (windowed2Input acc b0Idx b1Idx b0 b1 totalWin)
      = windowed2Input
          (windowedStepSpecIter2 a N b0 b1 m acc)
          b0Idx b1Idx b0 b1 totalWin := by
  induction m with
  | zero =>
    rw [windowed2SelectedAddGate_zero, windowedStepSpecIter2_zero]
    exact Gate.applyNat_I _
  | succ n ih =>
    have hn_lt : n < totalWin :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hm_le
    have hn_le : n ≤ totalWin := Nat.le_of_lt hn_lt
    rw [windowed2SelectedAddGate_succ, Gate.applyNat_seq, ih hn_le]
    -- After IH: goal is
    --   Gate.applyNat ((toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec.gate
    --                    bits n flagIdx (b0Idx n) (b1Idx n))
    --       (windowed2Input (windowedStepSpecIter2 ... n acc) b0Idx b1Idx b0 b1 totalWin)
    --     = windowed2Input (windowedStepSpecIter2 ... (n+1) acc) b0Idx b1Idx b0 b1 totalWin
    -- The spec's gate is definitionally toyWindow2SelectedAddGate (via the
    -- toSelectedAddSpec conversion and the impl's gate field).
    have hacc_n : windowedStepSpecIter2 a N b0 b1 n acc < N :=
      windowedStepSpecIter2_lt_N a N b0 b1 n acc hN_pos hacc
    show Gate.applyNat
            (toyWindow2SelectedAddGate bits N a n flagIdx (b0Idx n) (b1Idx n))
            (windowed2Input (windowedStepSpecIter2 a N b0 b1 n acc)
              b0Idx b1Idx b0 b1 totalWin)
       = windowed2Input (windowedStepSpecIter2 a N b0 b1 (n + 1) acc)
           b0Idx b1Idx b0 b1 totalWin
    rw [toyWindow2SelectedAddGate_on_windowed2Input bits N a n
          (windowedStepSpecIter2 a N b0 b1 n acc) flagIdx totalWin
          b0Idx b1Idx b0 b1
          hbits hN_pos hN hN2 hacc_n hn_lt h_flag_lo h_flag_ne_1 h_flag_lt_dim
          h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
          h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
    rw [windowedStepSpecIter2_succ]

/-- **R7d^xxvi — toy multi-window selected-add correctness.**

The full `numWin`-window selected-add fold (applying the toy
implementation's selected-add gate at each window index `0, …, numWin
- 1`) on an input of the same window size produces the input shape
with the accumulator advanced by `windowedStepSpecIter2`.

Specialization of the prefix theorem at `m = totalWin = numWin`. -/
theorem toyWindowed2SelectedAddGate_correct
    (bits N a flagIdx numWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < numWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < numWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < numWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
          bits flagIdx b0Idx b1Idx numWin)
        (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = windowed2Input
          (windowedStepSpecIter2 a N b0 b1 numWin acc)
          b0Idx b1Idx b0 b1 numWin :=
  toyWindowed2SelectedAddGate_correct_prefix bits N a flagIdx numWin numWin acc
    b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc (Nat.le_refl numWin)
    h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1

/-! ## Phase R7d^xxvii — arithmetic aggregation

Pure arithmetic stack connecting `windowedStepSpecIter2` to modular
multiplication semantics:
- Stage 1: `windowed2Value` decodes the multiplier value from
  window bits.
- Stage 2: `windowed2TableSum` is the running sum of per-window
  `tableValue`s.
- Stage 3: `windowedStepSpecIter2 ... = (acc + windowed2TableSum ...) % N`.
- Stage 4: `windowed2TableSum ... ≡ a * windowed2Value ... (mod N)`.
- Stage 5: `windowedStepSpecIter2 ... = (acc + a * windowed2Value ...) % N`.
- Stretch: `cuccaro_target_val ∘ Gate.applyNat ... = (acc + a * x) % N`. -/

/-- **Decoded multiplier value.** Sums `windowBits2_at b0 b1 k * 4^k`
over windows `k = 0, …, numWin - 1`. This is the integer encoded by
the per-window bits in the natural window-size-2 binary decoding. -/
def windowed2Value (b0 b1 : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => windowed2Value b0 b1 n + windowBits2_at b0 b1 n * 2^(n * 2)

@[simp] theorem windowed2Value_zero (b0 b1 : Nat → Bool) :
    windowed2Value b0 b1 0 = 0 := rfl

@[simp] theorem windowed2Value_succ (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2Value b0 b1 (n + 1)
      = windowed2Value b0 b1 n + windowBits2_at b0 b1 n * 2^(n * 2) := rfl

/-- **Running sum of per-window `tableValue`s.** Matches the
recursion of `windowedStepSpecIter2`. -/
def windowed2TableSum
    (a N : Nat) (b0 b1 : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      windowed2TableSum a N b0 b1 n + tableValue a N 2 n (windowBits2_at b0 b1 n)

@[simp] theorem windowed2TableSum_zero (a N : Nat) (b0 b1 : Nat → Bool) :
    windowed2TableSum a N b0 b1 0 = 0 := rfl

@[simp] theorem windowed2TableSum_succ
    (a N : Nat) (b0 b1 : Nat → Bool) (n : Nat) :
    windowed2TableSum a N b0 b1 (n + 1)
      = windowed2TableSum a N b0 b1 n
        + tableValue a N 2 n (windowBits2_at b0 b1 n) := rfl

/-- **Stage 3.** The iterated step spec aggregates to the running
table sum modulo N. Requires `acc < N` for the base case (so that
`acc % N = acc`). -/
theorem windowedStepSpecIter2_eq_acc_plus_tableSum_mod
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc
      = (acc + windowed2TableSum a N b0 b1 numWin) % N := by
  induction numWin with
  | zero =>
    rw [windowedStepSpecIter2_zero, windowed2TableSum_zero, Nat.add_zero]
    exact (Nat.mod_eq_of_lt hacc).symm
  | succ n ih =>
    rw [windowedStepSpecIter2_succ]
    show (windowedStepSpecIter2 a N b0 b1 n acc
            + tableValue a N 2 n (windowBits2_at b0 b1 n)) % N
       = (acc + windowed2TableSum a N b0 b1 (n + 1)) % N
    rw [ih, windowed2TableSum_succ]
    -- Goal: ((acc + ws_n) % N + tv) % N
    --     = (acc + (ws_n + tv)) % N
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_assoc]

/-- **Stage 4.** The running table sum is congruent to
`a * windowed2Value` modulo `N`. -/
theorem windowed2TableSum_mod_eq_mul_windowed2Value_mod
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin : Nat) :
    windowed2TableSum a N b0 b1 numWin % N
      = (a * windowed2Value b0 b1 numWin) % N := by
  induction numWin with
  | zero => simp
  | succ n ih =>
    rw [windowed2TableSum_succ, windowed2Value_succ]
    -- LHS: (windowed2TableSum n + tableValue) % N
    -- RHS: (a * (windowed2Value n + v_n * 2^(n*2))) % N
    conv_lhs => rw [Nat.add_mod, ih, ← Nat.add_mod]
    rw [Nat.mul_add]
    -- LHS: (a * windowed2Value n + tableValue) % N
    -- RHS: (a * windowed2Value n + a * (v_n * 2^(n*2))) % N
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    -- Need: tableValue % N = (a * (v_n * 2^(n*2))) % N
    congr 1
    congr 1
    unfold tableValue
    rw [Nat.mod_mod]
    -- Goal: (a * 2^(n*2) * v_n) % N = (a * (v_n * 2^(n*2))) % N
    -- Up to multiplication commutativity / associativity.
    rw [Nat.mul_assoc, Nat.mul_comm (2^(n * 2))]

/-- **Stage 5.** The iterated step spec equals `acc + a * x` modulo
`N`, where `x = windowed2Value b0 b1 numWin` is the multiplier value
decoded from the window bits. -/
theorem windowedStepSpecIter2_eq_mul_mod
    (a N : Nat) (b0 b1 : Nat → Bool) (numWin acc : Nat)
    (hN_pos : 0 < N) (hacc : acc < N) :
    windowedStepSpecIter2 a N b0 b1 numWin acc
      = (acc + a * windowed2Value b0 b1 numWin) % N := by
  rw [windowedStepSpecIter2_eq_acc_plus_tableSum_mod a N b0 b1 numWin acc
        hN_pos hacc]
  conv_lhs => rw [Nat.add_mod, windowed2TableSum_mod_eq_mul_windowed2Value_mod,
                  ← Nat.add_mod]

/-- **Bounded target extraction.** Variant of
`cuccaro_target_val_windowed2Input` where the high-index hypotheses
are bounded by `i < numWin` rather than universal. Required for the
circuit-facing corollary below — the main theorem's hypotheses are
bounded. -/
private theorem cuccaro_target_val_windowed2Input_bounded
    (bits acc : Nat) (b0Idx b1Idx : Nat → Nat)
    (b0 b1 : Nat → Bool) (numWin : Nat)
    (hacc_bits : acc < 2^bits)
    (h_hi0 : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_hi1 : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b1Idx k) :
    cuccaro_target_val bits 2 (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = acc := by
  induction numWin with
  | zero =>
    rw [windowed2Input_zero]
    exact cuccaro_target_val_input bits 2 0 acc false hacc_bits
  | succ n ih =>
    have hn_lt : n < n + 1 := Nat.lt_succ_self n
    rw [windowed2Input_succ]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b1Idx n) (b1 n) _
          (Or.inr (h_hi1 n hn_lt))]
    rw [cuccaro_target_val_update_outside_workspace bits 2 (b0Idx n) (b0 n) _
          (Or.inr (h_hi0 n hn_lt))]
    exact ih
      (fun k hk => h_hi0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_hi1 k (Nat.lt_succ_of_lt hk))

/-- **Circuit-facing corollary.** The full multi-window selected-add
target accumulator implements `(acc + a * x) % N` where `x` is the
window-encoded multiplier. Composes the per-tick R7d^xxvi correctness
with the arithmetic aggregation. -/
theorem toyWindowed2SelectedAddGate_target_mul_correct
    (bits N a flagIdx numWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < numWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < numWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < numWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    cuccaro_target_val bits 2
        (Gate.applyNat
          (windowed2SelectedAddGate
            (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
            bits flagIdx b0Idx b1Idx numWin)
          (windowed2Input acc b0Idx b1Idx b0 b1 numWin))
      = (acc + a * windowed2Value b0 b1 numWin) % N := by
  rw [toyWindowed2SelectedAddGate_correct bits N a flagIdx numWin acc
        b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc
        h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  have h_iter_lt : windowedStepSpecIter2 a N b0 b1 numWin acc < N :=
    windowedStepSpecIter2_lt_N a N b0 b1 numWin acc hN_pos hacc
  have h_iter_lt_pow : windowedStepSpecIter2 a N b0 b1 numWin acc < 2^bits :=
    Nat.lt_of_lt_of_le h_iter_lt hN
  rw [cuccaro_target_val_windowed2Input_bounded bits
        (windowedStepSpecIter2 a N b0 b1 numWin acc)
        b0Idx b1Idx b0 b1 numWin h_iter_lt_pow h_hi0 h_hi1]
  exact windowedStepSpecIter2_eq_mul_mod a N b0 b1 numWin acc hN_pos hacc

/-! ## Phase R7d^xxviii — multi-window multiply-add spec interface

Packages the verified window-size-2 multi-window multiply-add
primitive into a reusable spec record. Defines a stronger state-level
correctness theorem (combining R7d^xxvi's
`toyWindowed2SelectedAddGate_correct` with R7d^xxvii's
`windowedStepSpecIter2_eq_mul_mod`) and provides a concrete toy
implementation.

**Interface inspection summary** (for next-tick wiring):

| Existing interface | Level | Suitable here? |
| --- | --- | --- |
| `Window2SelectedAddSpec` | per-window gate spec | too narrow (single window) |
| `Window2SelectedAddStateSpec` | per-window gate state-eq spec | too narrow (single window) |
| `WindowedLookupModMulSpec` | pure arithmetic, no gate field | doesn't capture circuit-level result |
| `ControlledModAddImpl` | single mod-add gate | wrong abstraction (no window decoding) |
| `ModMulImpl` (SQIRPort) | full QState/BaseUCom | too high-level — Shor oracle, not Gate IR |
| `VerifiedModMulFamily` | full oracle family + QPE wiring | far too high-level |

None of the existing records cleanly captures the **Gate-level
multi-window multiply-add** primitive we've verified. The new
`Window2MulAddSpec` (below) sits between `Window2SelectedAddStateSpec`
(per-window) and `WindowedLookupModMulSpec` (pure arithmetic), and is
the natural composition target for both. -/

/-- **Full-state multiply-add correctness.** Composes
`toyWindowed2SelectedAddGate_correct` (R7d^xxvi) with
`windowedStepSpecIter2_eq_mul_mod` (R7d^xxvii) to give the gate's
output as a `windowed2Input` with the accumulator advanced by
`(acc + a * x) % N`, where `x` is the window-encoded multiplier.

This is the state-level analog of
`toyWindowed2SelectedAddGate_target_mul_correct`. -/
theorem toyWindowed2SelectedAddGate_state_mul_correct
    (bits N a flagIdx numWin acc : Nat)
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_hi0 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i)
    (h_hi1 : ∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i)
    (h_b0_ne_b1 : ∀ i, i < numWin → b0Idx i ≠ b1Idx i)
    (h_b0_ne_flag : ∀ i, i < numWin → b0Idx i ≠ flagIdx)
    (h_b1_ne_flag : ∀ i, i < numWin → b1Idx i ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
          bits flagIdx b0Idx b1Idx numWin)
        (windowed2Input acc b0Idx b1Idx b0 b1 numWin)
      = windowed2Input
          ((acc + a * windowed2Value b0 b1 numWin) % N)
          b0Idx b1Idx b0 b1 numWin := by
  rw [toyWindowed2SelectedAddGate_correct bits N a flagIdx numWin acc
        b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc
        h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  rw [windowedStepSpecIter2_eq_mul_mod a N b0 b1 numWin acc hN_pos hacc]

/-- **`Window2MulAddSpec`**: a spec contract for a Gate-level
windowSize=2 multi-window multiply-add primitive.

An implementation provides:
- `gate`: the composed multi-window gate.
- `input`: the input state encoding (accumulator + window bits).
- `decodeX`: the multiplier decoded from window bits.
- `stateCorrect`: full-state correctness — gate(input(acc)) =
  input((acc + a*x) % N).
- `targetCorrect`: target-decode correctness —
  cuccaro_target_val ∘ gate ∘ input = (acc + a*x) % N.

This is the natural composition target for downstream multi-step
multiplier/exponentiator constructions. -/
structure Window2MulAddSpec (a N : Nat) where
  /-- The composed multi-window multiply-add gate. -/
  gate :
    (bits flagIdx numWin : Nat) →
    (b0Idx b1Idx : Nat → Nat) →
    Gate
  /-- The input state encoding (accumulator + window bits installed). -/
  input :
    (acc : Nat) →
    (b0Idx b1Idx : Nat → Nat) →
    (b0 b1 : Nat → Bool) →
    Nat → (Nat → Bool)
  /-- The multiplier value decoded from the window bits. -/
  decodeX : (b0 b1 : Nat → Bool) → Nat → Nat
  /-- **State-level correctness.** Gate transforms `input(acc)` to
  `input((acc + a * decodeX) % N)`. -/
  stateCorrect :
    ∀ (bits flagIdx numWin acc : Nat)
      (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i) →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ flagIdx) →
      (∀ i, i < numWin → b1Idx i ≠ flagIdx) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) →
      Gate.applyNat (gate bits flagIdx numWin b0Idx b1Idx)
          (input acc b0Idx b1Idx b0 b1 numWin)
        = input ((acc + a * decodeX b0 b1 numWin) % N)
            b0Idx b1Idx b0 b1 numWin
  /-- **Target-decode correctness.** `cuccaro_target_val` extracts
  `(acc + a * decodeX) % N` from the gate's output. -/
  targetCorrect :
    ∀ (bits flagIdx numWin acc : Nat)
      (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool),
      1 ≤ bits → 0 < N → N ≤ 2^bits → 2 * N ≤ 2^bits →
      acc < N →
      flagIdx < 2 → flagIdx ≠ 1 → flagIdx < sqir_modmult_rev_anc bits →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b0Idx i) →
      (∀ i, i < numWin → 2 + 2 * bits + 1 ≤ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ b1Idx i) →
      (∀ i, i < numWin → b0Idx i ≠ flagIdx) →
      (∀ i, i < numWin → b1Idx i ≠ flagIdx) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j) →
      (∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) →
      cuccaro_target_val bits 2
          (Gate.applyNat (gate bits flagIdx numWin b0Idx b1Idx)
            (input acc b0Idx b1Idx b0 b1 numWin))
        = (acc + a * decodeX b0 b1 numWin) % N

/-- **Toy multi-window multiply-add spec implementation.** Wraps the
windowSize=2 CCX-based multi-window selected-add stack as a concrete
`Window2MulAddSpec` instance. -/
noncomputable def toyWindow2MulAddSpecImpl (a N : Nat) :
    Window2MulAddSpec a N where
  gate := fun bits flagIdx numWin b0Idx b1Idx =>
            windowed2SelectedAddGate
              (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
              bits flagIdx b0Idx b1Idx numWin
  input := windowed2Input
  decodeX := windowed2Value
  stateCorrect := fun bits flagIdx numWin acc b0Idx b1Idx b0 b1
                      hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                      h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag
                      h_b1_ne_flag h_distinct_b0_b0 h_distinct_b0_b1
                      h_distinct_b1_b0 h_distinct_b1_b1 =>
    toyWindowed2SelectedAddGate_state_mul_correct bits N a flagIdx numWin acc
      b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
      h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
      h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1
  targetCorrect := fun bits flagIdx numWin acc b0Idx b1Idx b0 b1
                       hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
                       h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag
                       h_b1_ne_flag h_distinct_b0_b0 h_distinct_b0_b1
                       h_distinct_b1_b0 h_distinct_b1_b1 =>
    toyWindowed2SelectedAddGate_target_mul_correct bits N a flagIdx numWin acc
      b0Idx b1Idx b0 b1 hbits hN_pos hN hN2 hacc h_flag_lo h_flag_ne_1
      h_flag_lt_dim h_hi0 h_hi1 h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
      h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1

/-! ## Phase R7d^xxix-B — windowed loader adapter (bit extraction + gate)

First sub-step toward bridging the windowed multiply-add primitive
to the `encodeDataZeroAnc` shape consumed by the existing
`gateMCP_apply_encode` seam (R7d^xxix-A map).

Adds:
- Per-window bit-extraction functions `windowed2_b0_of_x`,
  `windowed2_b1_of_x` (LSB-first decoding of `x`).
- Arithmetic decoding theorem `windowed2Value_of_x_mod`.
- The loader gate `windowedLoadAdapter` (recursive on `numWin`).
- Loader zero/succ unfold simp lemmas.
- The frame property `windowedLoadAdapter_preserves_disjoint` (loader
  preserves any position disjoint from all `b0Idx(k)`, `b1Idx(k)`).

The full apply-to-`encodeDataZeroAnc` theorem (which reads x out of
the data register and writes window bits) is deferred to R7d^xxix-C
because it requires careful big-endian / little-endian bit-position
bookkeeping. -/

/-- The `k`-th LSB-first window-bit decoder for `b0`: returns bit
`2 * k` of `x`. -/
def windowed2_b0_of_x (x : Nat) : Nat → Bool :=
  fun k => x.testBit (2 * k)

/-- The `k`-th LSB-first window-bit decoder for `b1`: returns bit
`2 * k + 1` of `x`. -/
def windowed2_b1_of_x (x : Nat) : Nat → Bool :=
  fun k => x.testBit (2 * k + 1)

/-- Arithmetic helper: `2^(2*k) = 4^k`. -/
private theorem two_pow_two_mul (k : Nat) : 2^(2 * k) = 4^k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, ih]
    rfl

/-- The decoded 2-bit window value at window `k` extracted from `x`. -/
private theorem windowBits2_at_of_x (x k : Nat) :
    windowBits2_at (windowed2_b0_of_x x) (windowed2_b1_of_x x) k
      = (x / 4^k) % 4 := by
  unfold windowBits2_at windowBits2_to_v
    windowed2_b0_of_x windowed2_b1_of_x
  rw [Nat.toNat_testBit, Nat.toNat_testBit]
  -- Goal: x / 2^(2*k) % 2 + 2 * (x / 2^(2*k+1) % 2) = x / 4^k % 4
  have h4k : 2^(2 * k) = 4^k := two_pow_two_mul k
  have h4k1 : 2^(2 * k + 1) = 2 * 4^k := by
    rw [pow_succ, h4k]; ring
  rw [h4k, h4k1]
  -- Goal: x / 4^k % 2 + 2 * (x / (2 * 4^k) % 2) = x / 4^k % 4
  have h_div : x / (2 * 4^k) = (x / 4^k) / 2 := by
    rw [Nat.div_div_eq_div_mul]; congr 1; ring
  rw [h_div]
  -- Goal: y % 2 + 2 * (y / 2 % 2) = y % 4 where y = x / 4^k
  omega

/-- **Arithmetic decoding theorem.** The multi-window value decoded
from `x`'s bits via `windowed2_b0_of_x` / `windowed2_b1_of_x` is
`x mod 2^(2 * numWin)`. When `x < 2^(2 * numWin)`, this equals `x`
itself. -/
theorem windowed2Value_of_x_mod (x numWin : Nat) :
    windowed2Value (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin
      = x % 2^(2 * numWin) := by
  induction numWin with
  | zero =>
    rw [windowed2Value]
    rw [show 2 * 0 = 0 from rfl, pow_zero]
    exact (Nat.mod_one x).symm
  | succ n ih =>
    rw [windowed2Value_succ, ih, windowBits2_at_of_x]
    have h_4n : 2^(2 * n) = 4^n := two_pow_two_mul n
    have h_n2 : 2^(n * 2) = 4^n := by rw [Nat.mul_comm n 2]; exact two_pow_two_mul n
    have h_4n1 : 2^(2 * (n + 1)) = 4^n * 4 := by
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, h_4n]
      norm_num
    rw [h_4n, h_n2, h_4n1, Nat.mod_mul]
    -- Goal: x % 4^n + (x / 4^n) % 4 * 4^n = x % 4^n + 4^n * ((x / 4^n) % 4)
    ring

/-- **Loader gate** (recursive on `numWin`). Installs window `n`'s
b0/b1 bits at positions `b0Idx n`, `b1Idx n` by `CX`-copying from the
big-endian data register positions `bits - 1 - 2*n` and `bits - 2 - 2*n`.

Definition is parameterized by `bits` (data register width) and
`b0Idx`, `b1Idx` (window-bit ancilla position functions). Base case
is `Gate.I`; step case appends two `CX` gates to install the n-th
window's bits. -/
noncomputable def windowedLoadAdapter
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (windowedLoadAdapter bits b0Idx b1Idx n)
        (Gate.seq
          (Gate.CX (bits - 1 - 2 * n) (b0Idx n))
          (Gate.CX (bits - 1 - (2 * n + 1)) (b1Idx n)))

/-- Zero-window loader is the identity. -/
@[simp] theorem windowedLoadAdapter_zero
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowedLoadAdapter bits b0Idx b1Idx 0 = Gate.I := rfl

/-- Successor-window loader appends two `CX` gates to the prefix. -/
@[simp] theorem windowedLoadAdapter_succ
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowedLoadAdapter bits b0Idx b1Idx (n + 1)
      = Gate.seq
          (windowedLoadAdapter bits b0Idx b1Idx n)
          (Gate.seq
            (Gate.CX (bits - 1 - 2 * n) (b0Idx n))
            (Gate.CX (bits - 1 - (2 * n + 1)) (b1Idx n))) := rfl

/-- **Frame property (preserves disjoint positions).** The loader
preserves any position `p` that's not a target of any of its CX gates
(i.e., `p ≠ b0Idx(k)` and `p ≠ b1Idx(k)` for all `k < numWin`).

In particular, this proves the loader preserves all data-register
bits and any ancilla outside the window-bit region. -/
theorem windowedLoadAdapter_preserves_disjoint
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (p : Nat) (numWin : Nat)
    (f : Nat → Bool)
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (windowedLoadAdapter bits b0Idx b1Idx numWin) f p = f p := by
  induction numWin generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [windowedLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_p_ne_b0n : p ≠ b0Idx n := h_p_ne_b0 n (Nat.lt_succ_self n)
    have h_p_ne_b1n : p ≠ b1Idx n := h_p_ne_b1 n (Nat.lt_succ_self n)
    rw [Gate.applyNat_CX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b1n]
    rw [Gate.applyNat_CX]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b0n]
    -- Apply IH on the prefix.
    exact ih f
      (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-! ## Phase R7d^xxix-C — windowed loaded-state encoding

**Critical layout finding**: the windowed selected-add gate's Cuccaro
workspace (positions `[2, 2 + 2*bits + 1]`) OVERLAPS with the
`encodeDataZeroAnc` data register (positions `[0, bits)`) whenever
`bits ≥ 3`. Specifically, positions `[2, bits)` are simultaneously
data-register bits (containing `x`) AND Cuccaro workspace bits
(expected to be `c_in`/`a`/`b` initialization).

**Consequence for the bridge**: a CX-based copy loader leaves `x`'s
bits in the data register (positions `[0, bits)`). When the selected-add
gate then runs, it reads stale `x`-bits as Cuccaro workspace,
corrupting the multiply-add. So copy-based loading CANNOT bridge to
the existing `windowed2SelectedAddGate` correctness.

**The correct bridge** requires a SWAP-based adapter (analogous to the
existing `sqir_encode_to_mult_adapter`) that MOVES `x`'s bits from
data positions to window-bit positions, leaving the data register zero.
This is the natural continuation of the R7d^xxix-D work.

This phase still defines the loaded-state encoding produced by the
current CX loader (with `x` preserved in the data register) so that
the loader's apply theorem can be documented, and provides the readback
lemmas. The bridge to selected-add is deferred to the SWAP loader. -/

/-- **Windowed loaded-state encoding.** The state produced by the
CX-based loader: starts from `encodeDataZeroAnc bits anc x` (data
register holds `x`; ancillas are zero), then installs window bits
`x.testBit (2*k)` at `b0Idx k` and `x.testBit (2*k+1)` at `b1Idx k`
for `k < numWin`. Recursive on `numWin` to match the loader's
recursion structure. -/
def windowed2LoadedInput
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) :
    Nat → (Nat → Bool)
  | 0 => encodeDataZeroAnc bits anc x
  | n + 1 =>
      update
        (update (windowed2LoadedInput bits anc x b0Idx b1Idx n)
          (b0Idx n) (x.testBit (2 * n)))
        (b1Idx n) (x.testBit (2 * n + 1))

/-- Zero-window loaded state is the raw `encodeDataZeroAnc`. -/
@[simp] theorem windowed2LoadedInput_zero
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowed2LoadedInput bits anc x b0Idx b1Idx 0
      = encodeDataZeroAnc bits anc x := rfl

/-- Successor-window loaded state appends two updates installing
the n-th window's bits. -/
@[simp] theorem windowed2LoadedInput_succ
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowed2LoadedInput bits anc x b0Idx b1Idx (n + 1)
      = update
          (update (windowed2LoadedInput bits anc x b0Idx b1Idx n)
            (b0Idx n) (x.testBit (2 * n)))
          (b1Idx n) (x.testBit (2 * n + 1)) := rfl

/-- Latest-window readback for `b1Idx n`: returns
`x.testBit (2 * n + 1)`. -/
theorem windowed2LoadedInput_succ_read_b1
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowed2LoadedInput bits anc x b0Idx b1Idx (n + 1) (b1Idx n)
      = x.testBit (2 * n + 1) := by
  rw [windowed2LoadedInput_succ]
  exact FormalRV.Framework.update_eq _ _ _

/-- Latest-window readback for `b0Idx n`: returns `x.testBit (2 * n)`. -/
theorem windowed2LoadedInput_succ_read_b0
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat)
    (h_ne : b0Idx n ≠ b1Idx n) :
    windowed2LoadedInput bits anc x b0Idx b1Idx (n + 1) (b0Idx n)
      = x.testBit (2 * n) := by
  rw [windowed2LoadedInput_succ]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_ne]
  exact FormalRV.Framework.update_eq _ _ _

/-- **General `b0` readback.** For any window `k < numWin`, the
loaded state at `b0Idx k` returns `x.testBit (2 * k)`. -/
theorem windowed2LoadedInput_read_b0
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_distinct : ∀ i j, i ≠ j → b0Idx i ≠ b0Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2LoadedInput bits anc x b0Idx b1Idx numWin (b0Idx k)
      = x.testBit (2 * k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2LoadedInput_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k k)]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_b1 k n)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_distinct k n hkn)]
      exact ih hk_lt_n

/-- **General `b1` readback.** For any window `k < numWin`, the
loaded state at `b1Idx k` returns `x.testBit (2 * k + 1)`. -/
theorem windowed2LoadedInput_read_b1
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat) (hk : k < numWin)
    (h_b1_distinct : ∀ i j, i ≠ j → b1Idx i ≠ b1Idx j)
    (h_b0_b1 : ∀ i j, b0Idx i ≠ b1Idx j) :
    windowed2LoadedInput bits anc x b0Idx b1Idx numWin (b1Idx k)
      = x.testBit (2 * k + 1) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2LoadedInput_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_distinct k n hkn)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm (h_b0_b1 n k))]
      exact ih hk_lt_n

/-- **Data-position preservation.** At any position `p` distinct from
all window-bit indices `b0Idx(k)`, `b1Idx(k)` (k < numWin), the loaded
state equals the underlying `encodeDataZeroAnc bits anc x`. In
particular, all data-register positions `[0, bits)` are preserved
when window indices are disjoint from data positions. -/
theorem windowed2LoadedInput_at_disjoint
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin p : Nat)
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    windowed2LoadedInput bits anc x b0Idx b1Idx numWin p
      = encodeDataZeroAnc bits anc x p := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2LoadedInput_succ]
    have h_p_ne_b0n : p ≠ b0Idx n := h_p_ne_b0 n (Nat.lt_succ_self n)
    have h_p_ne_b1n : p ≠ b1Idx n := h_p_ne_b1 n (Nat.lt_succ_self n)
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b0n]
    exact ih (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
             (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-! ### Layout conflict: bridge to selected-add NOT YET CLOSED

The selected-add gate's Cuccaro workspace `[2, 2 + 2*bits + 1]`
includes positions `[2, bits)` (when `bits ≥ 3`), which are also
data-register positions in `encodeDataZeroAnc`. After the CX-based
copy loader, those positions still hold `x`'s bits — NOT the
`cuccaro_input_F`-formatted workspace expected by the selected-add.

**This means the simple frame argument fails**:
`Gate.applyNat (selectedAdd) (windowed2LoadedInput ...) ≠
 windowed2LoadedInput ((acc + a*x) % N) ...`
because the selected-add reads stale `x`-bits as `c_in`/`a`/`b`,
producing incorrect output.

**Required for the bridge** (next ticks):
- **R7d^xxix-D**: Build a SWAP-based loader
  `windowedSwapLoadAdapter bits b0Idx b1Idx numWin` that MOVES
  `x`'s bits from `encodeDataZeroAnc` data positions to window-bit
  ancilla positions, leaving the data register zero.
- **R7d^xxix-E**: Prove the SWAP loader's apply theorem:
  `Gate.applyNat (windowedSwapLoadAdapter ...)
   (encodeDataZeroAnc bits anc x)
   = windowed2Input 0 b0Idx b1Idx (windowed2_b0_of_x x)
     (windowed2_b1_of_x x) numWin`.
  The output IS `windowed2Input`-shaped — so the existing selected-add
  correctness (`toyWindowed2SelectedAddGate_state_mul_correct`) chains
  directly.

The current `windowed2LoadedInput` + readback lemmas remain useful as
documentation of what the CX-loader produces, and may be reused as
building blocks for the SWAP loader's invariants. -/

/-! ## Phase R7d^xxix-D — SWAP-based loader construction

Reuses the existing `FormalRV.BQAlgo.qubit_swap` primitive (CX×3)
from `ModularAdder.lean`. The loader sequences per-window SWAPs that
move data bits from `encodeDataZeroAnc` positions to window-bit
ancillas, leaving the data positions cleared (to whatever the
window-bit ancilla initially held — typically 0).

This is the analog of `sqir_encode_to_mult_adapter` /
`reverse_register_swap` but targets the windowed b0Idx/b1Idx ancilla
positions rather than the SQIR multiplier-shifted layout. -/

/-- **SWAP-based loader gate** (recursive on `numWin`). Per window
`n`, performs two `qubit_swap`s:
- swap (data position `bits - 1 - 2*n`) ↔ `b0Idx n`,
- swap (data position `bits - 1 - (2*n + 1)`) ↔ `b1Idx n`.

Source positions follow `encodeDataZeroAnc`'s big-endian convention,
matching the same indexing used by `windowedLoadAdapter` (the
deprecated CX copy loader).

Unlike the CX loader, the data positions are CLEARED after the swap
(they hold whatever the ancilla positions held before, typically 0). -/
noncomputable def windowedSwapLoadAdapter
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (windowedSwapLoadAdapter bits b0Idx b1Idx n)
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * n) (b0Idx n))
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - (2 * n + 1)) (b1Idx n)))

/-- Zero-window SWAP loader is the identity. -/
@[simp] theorem windowedSwapLoadAdapter_zero
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) :
    windowedSwapLoadAdapter bits b0Idx b1Idx 0 = Gate.I := rfl

/-- Successor-window SWAP loader appends two `qubit_swap`s. -/
@[simp] theorem windowedSwapLoadAdapter_succ
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    windowedSwapLoadAdapter bits b0Idx b1Idx (n + 1)
      = Gate.seq
          (windowedSwapLoadAdapter bits b0Idx b1Idx n)
          (Gate.seq
            (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * n) (b0Idx n))
            (FormalRV.BQAlgo.qubit_swap
              (bits - 1 - (2 * n + 1)) (b1Idx n))) := rfl

/-- **Frame property: preserves positions disjoint from all sources
and targets.** The SWAP loader preserves any position `p` that's not
any source data position `bits - 1 - 2*k` / `bits - 1 - (2*k+1)` and
not any target window position `b0Idx(k)` / `b1Idx(k)` for `k < numWin`.

Side conditions `h_swap0_ne`, `h_swap1_ne` ensure each `qubit_swap`'s
two positions are distinct (required by `qubit_swap_correct`). -/
theorem windowedSwapLoadAdapter_preserves_disjoint
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (p : Nat) (numWin : Nat)
    (f : Nat → Bool)
    (h_swap0_ne : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_swap1_ne : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k)
    (h_p_ne_src0 : ∀ k, k < numWin → p ≠ bits - 1 - 2 * k)
    (h_p_ne_src1 : ∀ k, k < numWin → p ≠ bits - 1 - (2 * k + 1))
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) f p
      = f p := by
  induction numWin generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_swap0_n : bits - 1 - 2 * n ≠ b0Idx n :=
      h_swap0_ne n (Nat.lt_succ_self n)
    have h_swap1_n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
      h_swap1_ne n (Nat.lt_succ_self n)
    have h_p_ne_src0n : p ≠ bits - 1 - 2 * n :=
      h_p_ne_src0 n (Nat.lt_succ_self n)
    have h_p_ne_src1n : p ≠ bits - 1 - (2 * n + 1) :=
      h_p_ne_src1 n (Nat.lt_succ_self n)
    have h_p_ne_b0n : p ≠ b0Idx n := h_p_ne_b0 n (Nat.lt_succ_self n)
    have h_p_ne_b1n : p ≠ b1Idx n := h_p_ne_b1 n (Nat.lt_succ_self n)
    -- Outer qubit_swap.
    rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_swap1_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_src1n]
    -- Inner qubit_swap.
    rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_swap0_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_b0n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_p_ne_src0n]
    -- Apply IH on the prefix.
    exact ih f
      (fun k hk => h_swap0_ne k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_swap1_ne k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_src0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_src1 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-! ### Source-index arithmetic helpers (R7d^xxix-E foundations)

Small kernel-clean helpers establishing that data-source positions
`bits - 1 - 2*k` and `bits - 1 - (2*k + 1)` (i) lie within the data
register `[0, bits)` and (ii) differ from any window-bit ancilla
position satisfying `bits ≤ b_idx k`. These are the foundational
arithmetic lemmas the full readback / apply theorem will compose with
`qubit_swap_correct` and `windowedSwapLoadAdapter_preserves_disjoint`. -/

/-- Data source for the b0 bit of window `k` is strictly below `bits`
when `2 * k < bits`. -/
private theorem src0_lt_bits (bits k : Nat) (h : 2 * k < bits) :
    bits - 1 - 2 * k < bits := by omega

/-- Data source for the b1 bit of window `k` is strictly below `bits`
when `2 * k + 1 < bits`. -/
private theorem src1_lt_bits (bits k : Nat) (h : 2 * k + 1 < bits) :
    bits - 1 - (2 * k + 1) < bits := by omega

/-- Data source for window `k`'s b0 bit differs from any
"above-data" ancilla index. -/
private theorem src0_ne_above (bits k b : Nat)
    (h_src : 2 * k < bits) (h_above : bits ≤ b) :
    bits - 1 - 2 * k ≠ b := by omega

/-- Data source for window `k`'s b1 bit differs from any
"above-data" ancilla index. -/
private theorem src1_ne_above (bits k b : Nat)
    (h_src : 2 * k + 1 < bits) (h_above : bits ≤ b) :
    bits - 1 - (2 * k + 1) ≠ b := by omega

/-- The two source positions within a single window differ. -/
private theorem src0_ne_src1 (bits k : Nat)
    (h : 2 * k + 1 < bits) :
    bits - 1 - 2 * k ≠ bits - 1 - (2 * k + 1) := by omega

/-- Boolean bridge: `x.testBit k = decide (x / 2^k % 2 = 1)`. Proved
by case analysis on the Bool value of `testBit`, using
`Nat.toNat_testBit` to bridge to the Nat form. -/
private theorem testBit_eq_decide (x k : Nat) :
    x.testBit k = decide (x / 2^k % 2 = 1) := by
  have h := Nat.toNat_testBit x k
  cases hb : x.testBit k with
  | false =>
    rw [hb] at h
    simp at h
    have h_ne : x / 2^k % 2 ≠ 1 := by omega
    simp [h_ne]
  | true =>
    rw [hb] at h
    simp at h
    have h_eq : x / 2^k % 2 = 1 := h.symm
    simp [h_eq]

/-- **Boolean bridge from `nat_to_funbool` to `Nat.testBit`.**
For any `n, x, i`, the big-endian bit-extractor `nat_to_funbool n x i`
returns `x.testBit (n - 1 - i)`. -/
private theorem nat_to_funbool_eq_testBit
    (n x i : Nat) :
    FormalRV.Framework.nat_to_funbool n x i = x.testBit (n - 1 - i) := by
  unfold FormalRV.Framework.nat_to_funbool
  rw [testBit_eq_decide]

/-- **Latest-window readback for `b1`.** The SWAP loader at
`numWin = n + 1`, applied to `encodeDataZeroAnc`, reads
`x.testBit (2 * n + 1)` at position `b1Idx n`. -/
theorem windowedSwapLoadAdapter_succ_read_b1
    (bits anc n x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_2n1_lt : 2 * n + 1 < bits)
    (h_b0n_above : bits ≤ b0Idx n)
    (h_b1n_above : bits ≤ b1Idx n)
    (h_prefix_b0_above : ∀ k, k < n → bits ≤ b0Idx k)
    (h_prefix_b1_above : ∀ k, k < n → bits ≤ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx (n + 1))
        (encodeDataZeroAnc bits anc x) (b1Idx n)
      = x.testBit (2 * n + 1) := by
  have h_src1n_lt : bits - 1 - (2 * n + 1) < bits := src1_lt_bits bits n h_2n1_lt
  have h_2n_lt : 2 * n < bits := by omega
  have h_src0n_lt : bits - 1 - 2 * n < bits := src0_lt_bits bits n h_2n_lt
  have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
    src0_ne_above bits n _ h_2n_lt h_b0n_above
  have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
    src1_ne_above bits n _ h_2n1_lt h_b1n_above
  have h_b0n_ne_src1n : b0Idx n ≠ bits - 1 - (2 * n + 1) := by omega
  have h_src0n_ne_src1n : bits - 1 - 2 * n ≠ bits - 1 - (2 * n + 1) :=
    src0_ne_src1 bits n h_2n1_lt
  rw [windowedSwapLoadAdapter_succ]
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
  rw [FormalRV.Framework.update_eq]
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_b0n_ne_src1n)]
  rw [FormalRV.Framework.update_neq _ _ _ _ (Ne.symm h_src0n_ne_src1n)]
  -- Apply frame property of prefix loader at src1n
  have h_prefix_swap0_ne : ∀ k, k < n → bits - 1 - 2 * k ≠ b0Idx k :=
    fun k hk => src0_ne_above bits k _ (by omega) (h_prefix_b0_above k hk)
  have h_prefix_swap1_ne : ∀ k, k < n → bits - 1 - (2 * k + 1) ≠ b1Idx k :=
    fun k hk => src1_ne_above bits k _ (by omega) (h_prefix_b1_above k hk)
  have h_src1n_disj_src0_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ bits - 1 - 2 * k :=
    fun k hk => by omega
  have h_src1n_disj_src1_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ bits - 1 - (2 * k + 1) :=
    fun k hk => by omega
  have h_src1n_disj_b0_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ b0Idx k :=
    fun k hk => by
      have := h_prefix_b0_above k hk
      omega
  have h_src1n_disj_b1_prefix :
      ∀ k, k < n → bits - 1 - (2 * n + 1) ≠ b1Idx k :=
    fun k hk => by
      have := h_prefix_b1_above k hk
      omega
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
        (bits - 1 - (2 * n + 1)) n
        (encodeDataZeroAnc bits anc x)
        h_prefix_swap0_ne h_prefix_swap1_ne
        h_src1n_disj_src0_prefix h_src1n_disj_src1_prefix
        h_src1n_disj_b0_prefix h_src1n_disj_b1_prefix]
  rw [encodeDataZeroAnc_data hx h_src1n_lt]
  rw [nat_to_funbool_eq_testBit]
  congr 1
  omega

/-- **Latest-window readback for `b0`.** The SWAP loader at
`numWin = n + 1`, applied to `encodeDataZeroAnc`, reads
`x.testBit (2 * n)` at position `b0Idx n`. -/
theorem windowedSwapLoadAdapter_succ_read_b0
    (bits anc n x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_2n_lt : 2 * n < bits)
    (h_2n1_lt : 2 * n + 1 < bits)
    (h_b0n_above : bits ≤ b0Idx n)
    (h_b1n_above : bits ≤ b1Idx n)
    (h_b0n_ne_b1n : b0Idx n ≠ b1Idx n)
    (h_prefix_b0_above : ∀ k, k < n → bits ≤ b0Idx k)
    (h_prefix_b1_above : ∀ k, k < n → bits ≤ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx (n + 1))
        (encodeDataZeroAnc bits anc x) (b0Idx n)
      = x.testBit (2 * n) := by
  have h_src0n_lt : bits - 1 - 2 * n < bits := src0_lt_bits bits n h_2n_lt
  have h_src1n_lt : bits - 1 - (2 * n + 1) < bits := src1_lt_bits bits n h_2n1_lt
  have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
    src0_ne_above bits n _ h_2n_lt h_b0n_above
  have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
    src1_ne_above bits n _ h_2n1_lt h_b1n_above
  have h_b0n_ne_b1n_swap : b0Idx n ≠ b1Idx n := h_b0n_ne_b1n
  have h_b1n_ne_b0n : b1Idx n ≠ b0Idx n := Ne.symm h_b0n_ne_b1n
  have h_b0n_ne_src1n : b0Idx n ≠ bits - 1 - (2 * n + 1) := by omega
  have h_src1n_ne_b0n : bits - 1 - (2 * n + 1) ≠ b0Idx n := Ne.symm h_b0n_ne_src1n
  rw [windowedSwapLoadAdapter_succ]
  rw [Gate.applyNat_seq, Gate.applyNat_seq]
  -- Outer qubit_swap at (src1n, b1Idx n).
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
  -- update at b1Idx n (≠ b0Idx n).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0n_ne_b1n_swap]
  -- update at src1n (≠ b0Idx n).
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0n_ne_src1n]
  -- Inner qubit_swap at (src0n, b0Idx n).
  rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
  -- update at b0Idx n: use update_eq.
  rw [FormalRV.Framework.update_eq]
  -- Goal: (applyNat prefix encode) src0n = x.testBit (2*n)
  have h_prefix_swap0_ne : ∀ k, k < n → bits - 1 - 2 * k ≠ b0Idx k :=
    fun k hk => src0_ne_above bits k _ (by omega) (h_prefix_b0_above k hk)
  have h_prefix_swap1_ne : ∀ k, k < n → bits - 1 - (2 * k + 1) ≠ b1Idx k :=
    fun k hk => src1_ne_above bits k _ (by omega) (h_prefix_b1_above k hk)
  have h_src0n_disj_src0_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ bits - 1 - 2 * k :=
    fun k hk => by omega
  have h_src0n_disj_src1_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ bits - 1 - (2 * k + 1) :=
    fun k hk => by omega
  have h_src0n_disj_b0_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ b0Idx k :=
    fun k hk => by
      have := h_prefix_b0_above k hk
      omega
  have h_src0n_disj_b1_prefix :
      ∀ k, k < n → bits - 1 - 2 * n ≠ b1Idx k :=
    fun k hk => by
      have := h_prefix_b1_above k hk
      omega
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
        (bits - 1 - 2 * n) n
        (encodeDataZeroAnc bits anc x)
        h_prefix_swap0_ne h_prefix_swap1_ne
        h_src0n_disj_src0_prefix h_src0n_disj_src1_prefix
        h_src0n_disj_b0_prefix h_src0n_disj_b1_prefix]
  rw [encodeDataZeroAnc_data hx h_src0n_lt]
  rw [nat_to_funbool_eq_testBit]
  congr 1
  omega

/-- **General-k readback for `b1`.** For any window `k < numWin`, the
SWAP loader applied to `encodeDataZeroAnc` reads `x.testBit (2*k+1)`
at position `b1Idx k`. Proven by induction on `numWin`.

Uses `h_2numWin_le : 2 * numWin ≤ bits` (rather than the exact-coverage
`2 * numWin = bits`) because the induction hypothesis at `n` requires
`2 * n ≤ bits` (derivable from outer `2 * (n+1) ≤ bits`). -/
theorem windowedSwapLoadAdapter_read_b1
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (b1Idx k)
      = x.testBit (2 * k + 1) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      exact windowedSwapLoadAdapter_succ_read_b1 bits anc k x b0Idx b1Idx hx
        h_2k1_lt
        (h_b0_above k (Nat.lt_succ_self k))
        (h_b1_above k (Nat.lt_succ_self k))
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b1k_above : bits ≤ b1Idx k := h_b1_above k hk
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_b1k_ne_b1n : b1Idx k ≠ b1Idx n :=
        h_distinct_b1_b1 k n hk (Nat.lt_succ_self n) hkn
      have h_b1k_ne_b0n : b1Idx k ≠ b0Idx n :=
        h_distinct_b1_b0 k n hk (Nat.lt_succ_self n) hkn
      have h_b1k_ne_src0n : b1Idx k ≠ bits - 1 - 2 * n := by omega
      have h_b1k_ne_src1n : b1Idx k ≠ bits - 1 - (2 * n + 1) := by omega
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      rw [windowedSwapLoadAdapter_succ]
      rw [Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b1_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **General-k readback for `b0`.** For any window `k < numWin`, the
SWAP loader applied to `encodeDataZeroAnc` reads `x.testBit (2*k)`
at position `b0Idx k`. -/
theorem windowedSwapLoadAdapter_read_b0
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (b0Idx k)
      = x.testBit (2 * k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k_lt : 2 * k < bits := by omega
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      exact windowedSwapLoadAdapter_succ_read_b0 bits anc k x b0Idx b1Idx hx
        h_2k_lt h_2k1_lt
        (h_b0_above k (Nat.lt_succ_self k))
        (h_b1_above k (Nat.lt_succ_self k))
        (h_b0_ne_b1 k (Nat.lt_succ_self k))
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0k_above : bits ≤ b0Idx k := h_b0_above k hk
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_b0k_ne_b0n : b0Idx k ≠ b0Idx n :=
        h_distinct_b0_b0 k n hk (Nat.lt_succ_self n) hkn
      have h_b0k_ne_b1n : b0Idx k ≠ b1Idx n :=
        h_distinct_b0_b1 k n hk (Nat.lt_succ_self n) hkn
      have h_b0k_ne_src0n : b0Idx k ≠ bits - 1 - 2 * n := by omega
      have h_b0k_ne_src1n : b0Idx k ≠ bits - 1 - (2 * n + 1) := by omega
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      rw [windowedSwapLoadAdapter_succ]
      rw [Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **`encodeDataZeroAnc` above-data value.** For any position `q ≥ bits`,
the encoding's value is `false` — either it's in the ancilla range
`[bits, bits + anc)` (use `encodeDataZeroAnc_anc`) or out of range
`[bits + anc, ∞)` (use `encodeDataZeroAnc_oob`). Requires `0 < anc`. -/
private theorem encodeDataZeroAnc_above
    (bits anc x q : Nat) (hx : x < 2^bits) (hq : bits ≤ q) (hanc_pos : 0 < anc) :
    encodeDataZeroAnc bits anc x q = false := by
  by_cases h : q < bits + anc
  · have h_offset : q - bits < anc := by omega
    have h_eq : q = bits + (q - bits) := by omega
    rw [h_eq]
    exact encodeDataZeroAnc_anc hx h_offset
  · push_neg at h
    exact encodeDataZeroAnc_oob hanc_pos h

/-- **Data-clearing at b0 source positions.** For any window
`k < numWin`, the SWAP loader applied to `encodeDataZeroAnc` clears
the data position `bits - 1 - 2 * k` to `false`.

Proven by induction on `numWin`. Latest-window case: the new
`qubit_swap` moves the (initially-zero) window-bit ancilla value
into the data position. Older windows: IH says the position was
already cleared, and the new swaps don't touch this position. -/
theorem windowedSwapLoadAdapter_clears_data_even
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_anc_pos : 0 < anc)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (bits - 1 - 2 * k)
      = false := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k_lt : 2 * k < bits := by omega
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      have h_b0k_above : bits ≤ b0Idx k := h_b0_above k (Nat.lt_succ_self k)
      have h_b1k_above : bits ≤ b1Idx k := h_b1_above k (Nat.lt_succ_self k)
      have h_src0k_ne_b0k : bits - 1 - 2 * k ≠ b0Idx k :=
        src0_ne_above bits k _ h_2k_lt h_b0k_above
      have h_src1k_ne_b1k : bits - 1 - (2 * k + 1) ≠ b1Idx k :=
        src1_ne_above bits k _ h_2k1_lt h_b1k_above
      have h_src0k_ne_src1k : bits - 1 - 2 * k ≠ bits - 1 - (2 * k + 1) :=
        src0_ne_src1 bits k h_2k1_lt
      have h_src0k_ne_b1k : bits - 1 - 2 * k ≠ b1Idx k := by omega
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1k_ne_b1k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b1k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_src1k]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0k_ne_b0k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b0k]
      rw [FormalRV.Framework.update_eq]
      -- Goal: applyNat prefix encode (b0Idx k) = false
      have h_prefix_swap0_ne : ∀ j, j < k → bits - 1 - 2 * j ≠ b0Idx j :=
        fun j hj => src0_ne_above bits j _ (by omega) (h_b0_above j (by omega))
      have h_prefix_swap1_ne : ∀ j, j < k → bits - 1 - (2 * j + 1) ≠ b1Idx j :=
        fun j hj => src1_ne_above bits j _ (by omega) (h_b1_above j (by omega))
      have h_b0k_disj_src0_prefix :
          ∀ j, j < k → b0Idx k ≠ bits - 1 - 2 * j :=
        fun j hj => by
          have := h_b0_above k (Nat.lt_succ_self k); omega
      have h_b0k_disj_src1_prefix :
          ∀ j, j < k → b0Idx k ≠ bits - 1 - (2 * j + 1) :=
        fun j hj => by
          have := h_b0_above k (Nat.lt_succ_self k); omega
      have h_b0k_disj_b0_prefix : ∀ j, j < k → b0Idx k ≠ b0Idx j :=
        fun j hj => h_distinct_b0_b0 k j (Nat.lt_succ_self k) (by omega) (by omega)
      have h_b0k_disj_b1_prefix : ∀ j, j < k → b0Idx k ≠ b1Idx j :=
        fun j hj => h_distinct_b0_b1 k j (Nat.lt_succ_self k) (by omega) (by omega)
      rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
            (b0Idx k) k (encodeDataZeroAnc bits anc x)
            h_prefix_swap0_ne h_prefix_swap1_ne
            h_b0k_disj_src0_prefix h_b0k_disj_src1_prefix
            h_b0k_disj_b0_prefix h_b0k_disj_b1_prefix]
      exact encodeDataZeroAnc_above bits anc x (b0Idx k) hx h_b0k_above h_anc_pos
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_2k_lt : 2 * k < bits := by omega
      have h_src0k_ne_b0n : bits - 1 - 2 * k ≠ b0Idx n := by omega
      have h_src0k_ne_b1n : bits - 1 - 2 * k ≠ b1Idx n := by omega
      have h_src0k_ne_src0n : bits - 1 - 2 * k ≠ bits - 1 - 2 * n := by omega
      have h_src0k_ne_src1n : bits - 1 - 2 * k ≠ bits - 1 - (2 * n + 1) := by omega
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src0k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Data-clearing at b1 source positions.** For any window
`k < numWin`, the SWAP loader applied to `encodeDataZeroAnc` clears
the data position `bits - 1 - (2 * k + 1)` to `false`.

Latest-window case: outer `qubit_swap (src1k) (b1Idx k)` swaps;
inner swap doesn't touch `b1Idx k` (requires `b0Idx k ≠ b1Idx k`).
Older window: outer two swaps don't touch src1k. -/
theorem windowedSwapLoadAdapter_clears_data_odd
    (bits anc x : Nat) (b0Idx b1Idx : Nat → Nat)
    (numWin k : Nat)
    (hx : x < 2^bits)
    (hk : k < numWin)
    (h_anc_pos : 0 < anc)
    (h_2numWin_le : 2 * numWin ≤ bits)
    (h_b0_above : ∀ j, j < numWin → bits ≤ b0Idx j)
    (h_b1_above : ∀ j, j < numWin → bits ≤ b1Idx j)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x) (bits - 1 - (2 * k + 1))
      = false := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst hkn
      have h_2k_lt : 2 * k < bits := by omega
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      have h_b0k_above : bits ≤ b0Idx k := h_b0_above k (Nat.lt_succ_self k)
      have h_b1k_above : bits ≤ b1Idx k := h_b1_above k (Nat.lt_succ_self k)
      have h_b0k_ne_b1k : b0Idx k ≠ b1Idx k := h_b0_ne_b1 k (Nat.lt_succ_self k)
      have h_src1k_ne_b1k : bits - 1 - (2 * k + 1) ≠ b1Idx k :=
        src1_ne_above bits k _ h_2k1_lt h_b1k_above
      have h_src0k_ne_b0k : bits - 1 - 2 * k ≠ b0Idx k :=
        src0_ne_above bits k _ h_2k_lt h_b0k_above
      have h_b1k_ne_src0k : b1Idx k ≠ bits - 1 - 2 * k := by omega
      have h_b1k_ne_b0k : b1Idx k ≠ b0Idx k := Ne.symm h_b0k_ne_b1k
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1k_ne_b1k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_b1k]
      rw [FormalRV.Framework.update_eq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0k_ne_b0k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0k]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_src0k]
      have h_prefix_swap0_ne : ∀ j, j < k → bits - 1 - 2 * j ≠ b0Idx j :=
        fun j hj => src0_ne_above bits j _ (by omega) (h_b0_above j (by omega))
      have h_prefix_swap1_ne : ∀ j, j < k → bits - 1 - (2 * j + 1) ≠ b1Idx j :=
        fun j hj => src1_ne_above bits j _ (by omega) (h_b1_above j (by omega))
      have h_b1k_disj_src0_prefix :
          ∀ j, j < k → b1Idx k ≠ bits - 1 - 2 * j :=
        fun j hj => by
          have := h_b1_above k (Nat.lt_succ_self k); omega
      have h_b1k_disj_src1_prefix :
          ∀ j, j < k → b1Idx k ≠ bits - 1 - (2 * j + 1) :=
        fun j hj => by
          have := h_b1_above k (Nat.lt_succ_self k); omega
      have h_b1k_disj_b0_prefix : ∀ j, j < k → b1Idx k ≠ b0Idx j :=
        fun j hj => h_distinct_b1_b0 k j (Nat.lt_succ_self k) (by omega) (by omega)
      have h_b1k_disj_b1_prefix : ∀ j, j < k → b1Idx k ≠ b1Idx j :=
        fun j hj => h_distinct_b1_b1 k j (Nat.lt_succ_self k) (by omega) (by omega)
      rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx
            (b1Idx k) k (encodeDataZeroAnc bits anc x)
            h_prefix_swap0_ne h_prefix_swap1_ne
            h_b1k_disj_src0_prefix h_b1k_disj_src1_prefix
            h_b1k_disj_b0_prefix h_b1k_disj_b1_prefix]
      exact encodeDataZeroAnc_above bits anc x (b1Idx k) hx h_b1k_above h_anc_pos
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0n_above : bits ≤ b0Idx n := h_b0_above n (Nat.lt_succ_self n)
      have h_b1n_above : bits ≤ b1Idx n := h_b1_above n (Nat.lt_succ_self n)
      have h_2n_lt : 2 * n < bits := by omega
      have h_2n1_lt : 2 * n + 1 < bits := by omega
      have h_src0n_ne_b0n : bits - 1 - 2 * n ≠ b0Idx n :=
        src0_ne_above bits n _ h_2n_lt h_b0n_above
      have h_src1n_ne_b1n : bits - 1 - (2 * n + 1) ≠ b1Idx n :=
        src1_ne_above bits n _ h_2n1_lt h_b1n_above
      have h_2k1_lt : 2 * k + 1 < bits := by omega
      have h_src1k_ne_b0n : bits - 1 - (2 * k + 1) ≠ b0Idx n := by omega
      have h_src1k_ne_b1n : bits - 1 - (2 * k + 1) ≠ b1Idx n := by omega
      have h_src1k_ne_src0n : bits - 1 - (2 * k + 1) ≠ bits - 1 - 2 * n := by omega
      have h_src1k_ne_src1n :
          bits - 1 - (2 * k + 1) ≠ bits - 1 - (2 * n + 1) := by omega
      rw [windowedSwapLoadAdapter_succ, Gate.applyNat_seq, Gate.applyNat_seq]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src1n_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_src1n]
      rw [FormalRV.BQAlgo.qubit_swap_correct _ _ _ h_src0n_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_src1k_ne_src0n]
      exact ih hk_lt_n (by omega)
        (fun j hj => h_b0_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b1_above j (Nat.lt_succ_of_lt hj))
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b1_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Data-position source classification.** Under exact coverage
`2 * numWin = bits`, every data-register position `q < bits`
corresponds to either the even or odd source of some window
`k < numWin`. -/
private theorem data_position_is_source
    (bits numWin q : Nat)
    (h_exact : 2 * numWin = bits)
    (hq : q < bits) :
    (∃ k, k < numWin ∧ q = bits - 1 - 2 * k) ∨
    (∃ k, k < numWin ∧ q = bits - 1 - (2 * k + 1)) := by
  set i := bits - 1 - q with hi_def
  have hi_lt : i < bits := by omega
  rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
  · left
    refine ⟨i / 2, ?_, ?_⟩
    · omega
    · omega
  · right
    refine ⟨i / 2, ?_, ?_⟩
    · omega
    · omega

/-- `cuccaro_input_F 2 false 0 0 q = false` for any `q`. The Cuccaro
input layout with zero carry-in / zero a / zero b is uniformly false:
positions `< 2` return false directly; the c_in slot at i = 0 is
false; alternating a/b positions read `Nat.testBit 0 _ = false`. -/
private theorem cuccaro_input_F_zero_acc_eq_false (q : Nat) :
    cuccaro_input_F 2 false 0 0 q = false := by
  unfold cuccaro_input_F
  split_ifs <;> simp

/-- `windowed2Input 0 ...` is `false` at any position disjoint from
all window-bit indices. The zero-accumulator base is uniformly false
(from `cuccaro_input_F_zero_acc_eq_false`), and the recursive updates
only affect window-target positions. -/
private theorem windowed2Input_zero_at_disjoint
    (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin q : Nat)
    (h_b0_disj : ∀ k, k < numWin → q ≠ b0Idx k)
    (h_b1_disj : ∀ k, k < numWin → q ≠ b1Idx k) :
    windowed2Input 0 b0Idx b1Idx b0 b1 numWin q = false := by
  induction numWin with
  | zero => exact cuccaro_input_F_zero_acc_eq_false q
  | succ n ih =>
    rw [windowed2Input_succ]
    have h_b0_n : q ≠ b0Idx n := h_b0_disj n (Nat.lt_succ_self n)
    have h_b1_n : q ≠ b1Idx n := h_b1_disj n (Nat.lt_succ_self n)
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b1_n]
    rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_n]
    exact ih
      (fun k hk => h_b0_disj k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b1_disj k (Nat.lt_succ_of_lt hk))

/-- Bounded-distinctness variant of `windowed2Input_read_b0`. Same
result but the distinctness hypotheses are restricted to indices
`< numWin`, matching the apply theorem's signature. -/
private theorem windowed2Input_read_b0_bounded
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_b0_ne_b1 : ∀ j, j < numWin → b0Idx j ≠ b1Idx j)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b0Idx k) = b0 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [FormalRV.Framework.update_neq _ _ _ _
            (h_b0_ne_b1 k (Nat.lt_succ_self k))]
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b0k_ne_b1n : b0Idx k ≠ b1Idx n :=
        h_distinct_b0_b1 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      have h_b0k_ne_b0n : b0Idx k ≠ b0Idx n :=
        h_distinct_b0_b0 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b0k_ne_b0n]
      exact ih hk_lt_n
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij =>
          h_distinct_b0_b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- Bounded-distinctness variant of `windowed2Input_read_b1`. -/
private theorem windowed2Input_read_b1_bounded
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool)
    (numWin k : Nat) (hk : k < numWin)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin (b1Idx k) = b1 k := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    rw [windowed2Input_succ]
    by_cases hkn : k = n
    · subst hkn
      exact FormalRV.Framework.update_eq _ _ _
    · have hk_lt_n : k < n :=
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn
      have h_b1k_ne_b1n : b1Idx k ≠ b1Idx n :=
        h_distinct_b1_b1 k n hk (Nat.lt_succ_self n) (Nat.ne_of_lt hk_lt_n)
      have h_b1k_ne_b0n : b1Idx k ≠ b0Idx n := by
        have := h_distinct_b0_b1 n k (Nat.lt_succ_self n) hk
          (Ne.symm (Nat.ne_of_lt hk_lt_n))
        exact Ne.symm this
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b1n]
      rw [FormalRV.Framework.update_neq _ _ _ _ h_b1k_ne_b0n]
      exact ih hk_lt_n
        (fun i j hi hj hij =>
          h_distinct_b0_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij =>
          h_distinct_b1_b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Full SWAP loader apply theorem.** Under exact coverage
`2 * numWin = bits` and above-data + distinctness hypotheses, the
SWAP loader applied to `encodeDataZeroAnc bits anc x` produces
exactly the `windowed2Input 0 ... numWin` state expected by the
verified multi-window selected-add pipeline.

Proven by `funext q` + 4-way case analysis:
- q is a `b0Idx` window target: readback + windowed2Input_read.
- q is a `b1Idx` window target: readback + windowed2Input_read.
- q is a data position (q < bits): clearing + disjoint zero base.
- q is above the data register, not a window target: frame +
  encodeDataZeroAnc_above + disjoint zero base. -/
theorem windowedSwapLoadAdapter_apply_encodeDataZeroAnc
    (bits anc numWin x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_anc_pos : 0 < anc)
    (h_numWin_exact : 2 * numWin = bits)
    (h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (encodeDataZeroAnc bits anc x)
      = windowed2Input 0 b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin := by
  funext q
  have h_2numWin_le : 2 * numWin ≤ bits := by omega
  by_cases hA : ∃ k, k < numWin ∧ q = b0Idx k
  · obtain ⟨k, hk, hq_eq⟩ := hA
    subst hq_eq
    rw [windowedSwapLoadAdapter_read_b0 bits anc x b0Idx b1Idx numWin k hx hk
          h_2numWin_le h_b0_above h_b1_above h_b0_ne_b1
          h_distinct_b0_b0 h_distinct_b0_b1]
    rw [windowed2Input_read_b0_bounded 0 b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin k hk
          h_b0_ne_b1 h_distinct_b0_b0 h_distinct_b0_b1]
    rfl
  · push_neg at hA
    have hA' : ∀ k, k < numWin → q ≠ b0Idx k := fun k hk h => hA k hk h
    by_cases hB : ∃ k, k < numWin ∧ q = b1Idx k
    · obtain ⟨k, hk, hq_eq⟩ := hB
      subst hq_eq
      rw [windowedSwapLoadAdapter_read_b1 bits anc x b0Idx b1Idx numWin k hx hk
            h_2numWin_le h_b0_above h_b1_above
            h_distinct_b1_b0 h_distinct_b1_b1]
      rw [windowed2Input_read_b1_bounded 0 b0Idx b1Idx
            (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin k hk
            h_distinct_b0_b1 h_distinct_b1_b1]
      rfl
    · push_neg at hB
      have hB' : ∀ k, k < numWin → q ≠ b1Idx k := fun k hk h => hB k hk h
      -- RHS: windowed2Input 0 at q (not a target) = false.
      have h_rhs : windowed2Input 0 b0Idx b1Idx
                     (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin q = false :=
        windowed2Input_zero_at_disjoint b0Idx b1Idx _ _ numWin q hA' hB'
      by_cases hq_lt : q < bits
      · -- Case C: q < bits. Classify as even/odd source.
        rcases data_position_is_source bits numWin q h_numWin_exact hq_lt with
          ⟨k, hk, hq_eq⟩ | ⟨k, hk, hq_eq⟩
        · subst hq_eq
          rw [windowedSwapLoadAdapter_clears_data_even bits anc x b0Idx b1Idx
                numWin k hx hk h_anc_pos h_2numWin_le
                h_b0_above h_b1_above h_distinct_b0_b0 h_distinct_b0_b1]
          rw [h_rhs]
        · subst hq_eq
          rw [windowedSwapLoadAdapter_clears_data_odd bits anc x b0Idx b1Idx
                numWin k hx hk h_anc_pos h_2numWin_le
                h_b0_above h_b1_above h_b0_ne_b1
                h_distinct_b1_b0 h_distinct_b1_b1]
          rw [h_rhs]
      · -- Case D: bits ≤ q, not a window target.
        push_neg at hq_lt
        -- LHS via frame property: q disjoint from all sources and targets.
        have h_prefix_swap0_ne : ∀ j, j < numWin → bits - 1 - 2 * j ≠ b0Idx j :=
          fun j hj => src0_ne_above bits j _ (by omega) (h_b0_above j hj)
        have h_prefix_swap1_ne : ∀ j, j < numWin → bits - 1 - (2 * j + 1) ≠ b1Idx j :=
          fun j hj => src1_ne_above bits j _ (by omega) (h_b1_above j hj)
        have h_q_disj_src0 : ∀ j, j < numWin → q ≠ bits - 1 - 2 * j :=
          fun j hj => by omega
        have h_q_disj_src1 : ∀ j, j < numWin → q ≠ bits - 1 - (2 * j + 1) :=
          fun j hj => by omega
        rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx q numWin
              (encodeDataZeroAnc bits anc x)
              h_prefix_swap0_ne h_prefix_swap1_ne
              h_q_disj_src0 h_q_disj_src1 hA' hB']
        rw [encodeDataZeroAnc_above bits anc x q hx hq_lt h_anc_pos]
        rw [h_rhs]

/-! ## Phase R7d^xxix-K — SWAP loader + selected-add composition

Composes the SWAP loader's full apply theorem (R7d^xxix-J) with the
verified multi-window selected-add full-state correctness
(`toyWindowed2SelectedAddGate_state_mul_correct`).

The intermediate output is still in `windowed2Input` layout (the
reverse/output adapter is R7d^xxix-L's scope). -/

/-- **SWAP loader + selected-add composition (raw form).** Applying
the SWAP loader followed by the multi-window selected-add to
`encodeDataZeroAnc` produces the windowed input state with the
accumulator advanced by `a * windowed2Value (b0_of_x x) (b1_of_x x)
numWin` modulo `N`. -/
theorem windowedSwapLoadAdapter_then_selectedAdd_apply
    (bits anc numWin x N a flagIdx : Nat)
    (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_anc_pos : 0 < anc)
    (h_numWin_exact : 2 * numWin = bits)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_b1_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_b0_ne_flag : ∀ k, k < numWin → b0Idx k ≠ flagIdx)
    (h_b1_ne_flag : ∀ k, k < numWin → b1Idx k ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (Gate.seq
          (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
          (windowed2SelectedAddGate
            (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
            bits flagIdx b0Idx b1Idx numWin))
        (encodeDataZeroAnc bits anc x)
      = windowed2Input
          ((0 + a * windowed2Value
              (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin) % N)
          b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin := by
  rw [Gate.applyNat_seq]
  -- Derive bits ≤ b0Idx, bits ≤ b1Idx from the stricter selected-add hypotheses.
  have h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k :=
    fun k hk => by have := h_b0_hi k hk; omega
  have h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k :=
    fun k hk => by have := h_b1_hi k hk; omega
  rw [windowedSwapLoadAdapter_apply_encodeDataZeroAnc bits anc numWin x b0Idx b1Idx
        hx h_anc_pos h_numWin_exact h_b0_above h_b1_above h_b0_ne_b1
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  exact toyWindowed2SelectedAddGate_state_mul_correct bits N a flagIdx numWin 0
    b0Idx b1Idx (windowed2_b0_of_x x) (windowed2_b1_of_x x)
    hbits hN_pos hN hN2 hN_pos
    h_flag_lo h_flag_ne_1 h_flag_lt_dim
    h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
    h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1

/-- **SWAP loader + selected-add composition (cleaned form).** Same
as the raw theorem but with the windowed multiplier value collapsed
to `x % 2^bits` (using `windowed2Value_of_x_mod` and the exact-coverage
hypothesis) and the `0 + ...` simplified away. -/
theorem windowedSwapLoadAdapter_then_selectedAdd_apply_clean
    (bits anc numWin x N a flagIdx : Nat)
    (b0Idx b1Idx : Nat → Nat)
    (hx : x < 2^bits)
    (h_anc_pos : 0 < anc)
    (h_numWin_exact : 2 * numWin = bits)
    (hbits : 1 ≤ bits)
    (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (h_flag_lo : flagIdx < 2)
    (h_flag_ne_1 : flagIdx ≠ 1)
    (h_flag_lt_dim : flagIdx < sqir_modmult_rev_anc bits)
    (h_b0_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b0Idx k)
    (h_b1_hi : ∀ k, k < numWin → 2 + 2 * bits + 1 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_b0_ne_flag : ∀ k, k < numWin → b0Idx k ≠ flagIdx)
    (h_b1_ne_flag : ∀ k, k < numWin → b1Idx k ≠ flagIdx)
    (h_distinct_b0_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 :
      ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat
        (Gate.seq
          (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
          (windowed2SelectedAddGate
            (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
            bits flagIdx b0Idx b1Idx numWin))
        (encodeDataZeroAnc bits anc x)
      = windowed2Input
          ((a * (x % 2^bits)) % N)
          b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin := by
  rw [windowedSwapLoadAdapter_then_selectedAdd_apply bits anc numWin x N a flagIdx
        b0Idx b1Idx hx h_anc_pos h_numWin_exact hbits hN_pos hN hN2
        h_flag_lo h_flag_ne_1 h_flag_lt_dim
        h_b0_hi h_b1_hi h_b0_ne_b1 h_b0_ne_flag h_b1_ne_flag
        h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1]
  rw [windowed2Value_of_x_mod, h_numWin_exact, Nat.zero_add]

/-! ### Status: SWAP loader behavior fully proven (R7d^xxix-J)

The remaining proofs require composing the helpers above with
`encodeDataZeroAnc_data` (data-position value lookup) and a Boolean
identity `nat_to_funbool n x i = x.testBit (n - 1 - i)` (which
itself follows from `Nat.toNat_testBit`).

**R7d^xxix-F (next tick)** should:
1. Prove the per-window readback lemmas:
   - `windowedSwapLoadAdapter_succ_read_b1`: latest-window b1 readback
     returning `x.testBit (2*n + 1)`. ~50-80 lines using
     `qubit_swap_correct` ×2 + `windowedSwapLoadAdapter_preserves_disjoint`
     + `encodeDataZeroAnc_data` + a `nat_to_funbool ↔ testBit` bridge.
   - `windowedSwapLoadAdapter_succ_read_b0`: similar.
   - General-k versions via induction.
2. Prove the data-clearing lemmas at moved positions
   (the swap target was initially 0 from `encodeDataZeroAnc_anc` /
   `encodeDataZeroAnc_oob`, so the source becomes 0 after swap).
3. Compose into the full apply theorem under
   `2 * numWin = bits`:
   ```
   Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
       (encodeDataZeroAnc bits anc x)
     = windowed2Input 0 b0Idx b1Idx
         (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin
   ```
   Proof by `funext q` with case analysis on whether `q` is a
   window target, a moved source, or disjoint.

Estimated 150-250 lines total. The arithmetic helpers landed here
remove a significant fraction of that bookkeeping noise. -/

/-! ## Phase R7d^xiii — composed selected-add: status partial

The composed `toyWindow2SelectedAddGate` correctness theorem requires
**unified case-N state_eq theorems** that cover all four `(b0, b1)`
inputs (not just the firing case). For non-firing inputs, the gate
should act as the identity on `toyWindow2Case3Input acc ... b0 b1`.

The existing state_eq theorems (R7d^x, R7d^xi^d, R7d^xii) only handle
the firing input:
- `toyWindow2Case3Gate_state_eq` for `(b0=true, b1=true)`.
- `toyWindow2Case1Gate_state_eq` for `(b0=true, b1=false)`.
- `toyWindow2Case2Gate_state_eq` for `(b0=false, b1=true)`.

For the composition, each non-firing application produces an
intermediate state. The case-N _correct theorem gives target_val
for general `(b0, b1)`, but the target_val alone does not let the
next case-N _correct apply, since the latter requires the input
to be in `toyWindow2Case3Input` shape. Thus, we need 9 no-op
state_eq lemmas (or equivalently 3 unified case-N state_eq
theorems covering all 4 `(b0, b1)`).

Each no-op state_eq is roughly the size of an existing firing
state_eq (~300 lines). Total for full composition:
- 3 unified case state_eq (each ~600 lines covering 4 (b0,b1)
  values): ~1800 lines.
- Composition theorem proper: ~100 lines.

This exceeds a single tick budget. Deferred to R7d^xiv. The
remainder of this tick documents the gap and verifies that the
existing state_eq theorems remain intact. -/

/-! ### R7d''' status: composition theorem deferred to follow-up tick

**What is verified now**:
* All three case gates (`toyWindow2Case1Gate`, `_Case2Gate`,
  `_Case3Gate`) have proven correctness theorems for their
  respective firing conditions (b0 && !b1, !b0 && b1, b0 && b1).
* The composed gate `toyWindow2SelectedAddGate` is now concretely
  defined as the sequence of the three case gates.
* All four windowSize=2 arithmetic-spec helpers (v=0, v=1, v=2, v=3)
  are landed and rfl/Nat-mod-eq-of-lt-provable.

**What is deferred** (`toyWindow2SelectedAddGate_correct`):
The composed gate's target-decode correctness theorem requires
state-equality proofs for each case gate:

```
theorem toyWindow2CaseV_state_eq :
  Gate.applyNat (caseV_gate ...) (toyWindow2Case3Input acc b0Idx b1Idx b0 b1)
    = toyWindow2Case3Input (newAccV acc b0 b1) b0Idx b1Idx b0 b1
```

where `newAccV` selects the case-fired accumulator update.

These state-equality theorems require funext + per-position case
splits (~60-90 lines per case), analogous to
`sqir_modmult_step_state_eq` (SQIRModMult.lean:1156).  The proof
infrastructure is in place (`cuccaro_target_val_eq_implies_bits_match`,
`cuccaro_read_val_eq_implies_bits_match`, R4b clean conjuncts, the
above-layout commute lemmas, `sqir_style_controlledModAddConst_gate_carry_in_restored`),
but the per-case-per-position bookkeeping is substantial.

Once the three case_state_eq theorems land, the composition theorem
becomes a 4-way `by_cases` on `(b0, b1)` plus straightforward
applications of the case-correctness theorems:

```
theorem toyWindow2SelectedAddGate_correct
    ...
    (v : Nat) (hv : v < 4)
    (h_window : v = ...windowValue from b0, b1...) :
    cuccaro_target_val bits 2
        (Gate.applyNat (toyWindow2SelectedAddGate ...) (Input acc b0 b1))
      = windowedStepSpec a N 2 k acc v
```

* v=0 (b0=F, b1=F): all three case_state_eq give acc' = acc; finish with `windowedStepSpec_window2_v0`.
* v=1 (b0=T, b1=F): case1_state_eq gives acc' = (acc + tv1) % N; cases 2 and 3 don't fire; finish with `windowedStepSpec_window2_v1`.
* v=2 (b0=F, b1=T): case2 fires; finish with `windowedStepSpec_window2_v2`.
* v=3 (b0=T, b1=T): case3 fires; finish with `windowedStepSpec_window2_v3`.

**Next tick**: prove the three `_state_eq` theorems (mirroring
`sqir_modmult_step_state_eq` proof structure), then add the composition
theorem with the 4-way case split above. -/

/-! ## Phase R7d^xxix-L-REVIEW — diagnostic on the reverse-SWAP unloader

The K-state (post selected-add) is:

  windowed2Input ((a * (x % 2^bits)) % N) b0Idx b1Idx
    (windowed2_b0_of_x x) (windowed2_b1_of_x x) numWin

with the following position-by-position content:

* Cuccaro workspace (positions `q < q_start = 2`): false.
* Cuccaro carry-in (position 2): false.
* Cuccaro `b`-bit positions `q_start + 2*k + 1 = 2*k + 3`: bit `k`
  of the accumulator `y := (a * (x % 2^bits)) % N`.
* Cuccaro `a`-bit positions `q_start + 2*k + 2 = 2*k + 4`: false
  (the `a`-register input was 0 because the windowed adder is
  constant-shift modular addition).
* `b0Idx k`, `b1Idx k` (above-workspace window positions):
  `windowed2_b0_of_x x k = x.testBit (2*k)` and
  `windowed2_b1_of_x x k = x.testBit (2*k + 1)`.

The `encodeDataZeroAnc bits anc y` target shape, by contrast, demands:

* Data positions `0..bits-1`: bit `bits-1-i` of `y` at position `i`
  (big-endian decoding via `nat_to_funbool`).
* Ancilla positions `bits..bits+anc-1`: all false.

These two layouts overlap: position `bits-1` is simultaneously
the LSB of the encodeDataZeroAnc shape AND the LSB of the
Cuccaro accumulator (when `bits - 1 = q_start + 1 = 3`, i.e.
`bits = 4`). More generally, the SWAP loader's "data even
position" `bits - 1 - 2*k` is below `q_start = 2` for the highest
windows.

This review proves that a literal inverse-SWAP unloader (applying the
same swaps as the loader in reverse order) restores the **original `x`
window bits** into the data positions and moves the accumulator bits
into the ancilla `b0Idx/b1Idx` positions. That is the wrong direction
for the `encodeDataZeroAnc` shape — it requires `y` at data positions
and `false` at ancilla positions.

The diagnostic theorem below proves this for the simplest non-trivial
case (`numWin = 1`, position `bits - 1`): the inverse-SWAP unloader
produces `windowed2_b0_of_x x 0` at position `bits - 1`, regardless of
the accumulator value `y`. This is sufficient evidence to redesign the
R7d^xxix-L reverse adapter as reversible cleanup rather than reverse
SWAP. -/

/-- **Candidate reverse-SWAP unloader (diagnostic only).** Same swap
operations as `windowedSwapLoadAdapter`, but applied in reverse order:
for `n + 1`, first apply the window-`n` swaps, then recurse on `n`.
Since `qubit_swap` is involutive, applying both loader and unloader
sequentially to disjoint swap positions gives identity. However, the
unloader applied to the post-K state does NOT clean back to
`encodeDataZeroAnc y` — see the diagnostic theorem below. -/
private noncomputable def windowedSwapUnloadAdapterDiag
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * n) (b0Idx n))
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - (2 * n + 1)) (b1Idx n)))
        (windowedSwapUnloadAdapterDiag bits b0Idx b1Idx n)

/-- **DIAGNOSTIC — reverse-SWAP unloader pulls `x` bit back into data
position.** For `numWin = 1`, applying the candidate reverse-SWAP
unloader to the post-K windowed input state (with arbitrary accumulator
`y`) gives at the data position `bits - 1` the original `x` bit
`windowed2_b0_of_x x 0 = x.testBit 0`, NOT a bit of the accumulator
`y`. The accumulator's bit 0 (which was at position `bits - 1` in the
specific case `bits = 4` since `q_start + 1 = 3`) is lost — it gets
moved to position `b0Idx 0` (the ancilla position that
`encodeDataZeroAnc` requires to be false).

This shows the inverse-SWAP approach is INVALID for projecting back to
the `encodeDataZeroAnc y` shape required by `gateMCP_apply_encode`. -/
private theorem unloadDiag_data_msb_reads_old_x_at_numWin_1
    (bits y x : Nat) (b0Idx b1Idx : Nat → Nat)
    (hbits : 2 ≤ bits)
    (h_b0_above : bits ≤ b0Idx 0)
    (h_b1_above : bits ≤ b1Idx 0)
    (h_b0_ne_b1 : b0Idx 0 ≠ b1Idx 0) :
    Gate.applyNat (windowedSwapUnloadAdapterDiag bits b0Idx b1Idx 1)
        (windowed2Input y b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) 1)
        (bits - 1)
      = windowed2_b0_of_x x 0 := by
  -- Unfold unload at numWin = 1 and compute through the SWAP applies.
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - 2 * 0) (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap (bits - 1 - (2 * 0 + 1)) (b1Idx 0)))
        (windowedSwapUnloadAdapterDiag bits b0Idx b1Idx 0))
      _ (bits - 1) = _
  -- Normalize indices.
  have hidx0 : bits - 1 - 2 * 0 = bits - 1 := by omega
  have hidx1 : bits - 1 - (2 * 0 + 1) = bits - 2 := by omega
  rw [hidx0, hidx1]
  -- Unfold the recursion base.
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (bits - 1) (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap (bits - 2) (b1Idx 0)))
        Gate.I)
      _ (bits - 1) = _
  -- Apply Gate.applyNat_seq three times.
  simp only [Gate.applyNat_seq, Gate.applyNat_I]
  -- Now we have:
  --   applyNat (swap (bits-2) (b1Idx 0))
  --     (applyNat (swap (bits-1) (b0Idx 0)) s) (bits - 1)
  -- where s is the windowed2Input state.
  -- Disjointness facts:
  have h_b0_ne_msb : b0Idx 0 ≠ bits - 1 := by omega
  have h_b1_ne_msb : b1Idx 0 ≠ bits - 1 := by omega
  have h_msb_ne_msb2 : bits - 1 ≠ bits - 2 := by omega
  have h_msb_ne_b0 : bits - 1 ≠ b0Idx 0 := fun h => h_b0_ne_msb h.symm
  have h_msb_ne_b1 : bits - 1 ≠ b1Idx 0 := fun h => h_b1_ne_msb h.symm
  have h_msb2_ne_b1 : bits - 2 ≠ b1Idx 0 := by omega
  -- Step 1: rewrite the inner swap.
  rw [FormalRV.BQAlgo.qubit_swap_correct (bits - 1) (b0Idx 0) _ h_msb_ne_b0]
  -- Step 2: rewrite the outer swap.
  rw [FormalRV.BQAlgo.qubit_swap_correct (bits - 2) (b1Idx 0) _ h_msb2_ne_b1]
  -- Read at position bits - 1.
  -- The outermost update is at b1Idx 0; skip via h_msb_ne_b1.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_msb_ne_b1]
  -- The middle update is at (bits - 2); skip via h_msb_ne_msb2.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_msb_ne_msb2]
  -- The next update is at b0Idx 0; skip via h_msb_ne_b0.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_msb_ne_b0]
  -- The innermost update is at (bits - 1); take its assigned value
  -- which is s (b0Idx 0).
  rw [FormalRV.Framework.update_eq _ _ _]
  -- Now reduce the windowed2Input read at b0Idx 0.
  rw [windowed2Input_succ_read_b0 y b0Idx b1Idx
        (windowed2_b0_of_x x) (windowed2_b1_of_x x) 0 h_b0_ne_b1]

/-- **DIAGNOSTIC corollary — accumulator bit lost.** The inverse-SWAP
unloader on the post-K state places the accumulator's LSB at position
`b0Idx 0` (an ancilla position required to be false in
`encodeDataZeroAnc` form). This is the symmetric witness: the data
position is wrong AND the ancilla position is dirty. Stated for
`numWin = 1` and the specific case `bits = 4` where the accumulator
bit 0 lives at position `bits - 1 = 3`. -/
private theorem unloadDiag_ancilla_receives_acc_at_numWin_1_bits_4
    (y x : Nat) (b0Idx b1Idx : Nat → Nat)
    (h_b0_above : 4 ≤ b0Idx 0)
    (h_b1_above : 4 ≤ b1Idx 0)
    (h_b0_ne_b1 : b0Idx 0 ≠ b1Idx 0) :
    Gate.applyNat (windowedSwapUnloadAdapterDiag 4 b0Idx b1Idx 1)
        (windowed2Input y b0Idx b1Idx
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) 1)
        (b0Idx 0)
      = y.testBit 0 := by
  -- Unfold unload at numWin = 1 with bits = 4.
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap (4 - 1 - 2 * 0) (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap (4 - 1 - (2 * 0 + 1)) (b1Idx 0)))
        (windowedSwapUnloadAdapterDiag 4 b0Idx b1Idx 0))
      _ (b0Idx 0) = _
  -- Normalize indices: bits - 1 = 3, bits - 2 = 2.
  have hidx0 : (4 : Nat) - 1 - 2 * 0 = 3 := by decide
  have hidx1 : (4 : Nat) - 1 - (2 * 0 + 1) = 2 := by decide
  rw [hidx0, hidx1]
  show Gate.applyNat
      (Gate.seq
        (Gate.seq
          (FormalRV.BQAlgo.qubit_swap 3 (b0Idx 0))
          (FormalRV.BQAlgo.qubit_swap 2 (b1Idx 0)))
        Gate.I)
      _ (b0Idx 0) = _
  simp only [Gate.applyNat_seq, Gate.applyNat_I]
  have h_3_ne_b0 : (3 : Nat) ≠ b0Idx 0 := by omega
  have h_2_ne_b1 : (2 : Nat) ≠ b1Idx 0 := by omega
  have h_b0_ne_3 : b0Idx 0 ≠ 3 := fun h => h_3_ne_b0 h.symm
  have h_b0_ne_2 : b0Idx 0 ≠ 2 := by omega
  have h_b0_ne_b1' : b0Idx 0 ≠ b1Idx 0 := h_b0_ne_b1
  -- Step 1: rewrite the inner swap (3 ↔ b0Idx 0).
  rw [FormalRV.BQAlgo.qubit_swap_correct 3 (b0Idx 0) _ h_3_ne_b0]
  -- Step 2: rewrite the outer swap (2 ↔ b1Idx 0).
  rw [FormalRV.BQAlgo.qubit_swap_correct 2 (b1Idx 0) _ h_2_ne_b1]
  -- Read at position b0Idx 0:
  -- Outermost update at b1Idx 0; skip via h_b0_ne_b1.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_b1']
  -- Next update at 2; skip via h_b0_ne_2.
  rw [FormalRV.Framework.update_neq _ _ _ _ h_b0_ne_2]
  -- Next update at b0Idx 0; take its value via update_eq.
  rw [FormalRV.Framework.update_eq _ _ _]
  -- Now the value is s (bits - 1) where the original swap read it from
  -- position bits - 1 = 3 in s.
  -- s at position 3: cuccaro accumulator bit 0 since
  --   q_start = 2, q - q_start = 1, b.testBit 0 = y.testBit 0.
  -- We use windowed2Input_succ to strip the two ancilla updates,
  -- then cuccaro_input_F_at_b for the accumulator readout.
  -- The state is windowed2Input y b0Idx b1Idx ... 1, expand:
  rw [windowed2Input_succ]
  -- Outer update at b1Idx 0 ≠ 3.
  have h_3_ne_b1 : (3 : Nat) ≠ b1Idx 0 := by omega
  rw [FormalRV.Framework.update_neq _ _ _ _ h_3_ne_b1]
  rw [FormalRV.Framework.update_neq _ _ _ _ h_3_ne_b0]
  -- Inner: windowed2Input y _ _ _ _ 0 = cuccaro_input_F 2 false 0 y.
  rw [windowed2Input_zero]
  -- cuccaro_input_F 2 false 0 y 3 = y.testBit 0 since 3 = q_start + 2*0 + 1.
  have h_b : cuccaro_input_F 2 false 0 y 3 = y.testBit 0 := by
    rw [show (3 : Nat) = 2 + 2 * 0 + 1 from by rfl]
    exact cuccaro_input_F_at_b 2 0 false 0 y
  exact h_b

/-! ## Phase R7d^xxix-L-DESIGN-LOCK — overlap diagnostics for the
naive cuccaroBitsToDataSwap proposal

After R7d^xxix-L-REVIEW showed the reverse-SWAP unloader is invalid,
the proposed next architecture was Option C: K-stage + a separate
"Cuccaro→Data SWAP" cascade swapping accumulator bits at Cuccaro
b-bit positions `2*n + 3` into official data positions `bits - 1 - n`.

This section proves the proposed independent SWAP cascade is ALSO
invalid in its naive form — the source-position set
`{2*n + 3 : n < bits}` and destination-position set
`{bits - 1 - n : n < bits}` are NOT disjoint, so a sequential
independent SWAP cascade would either (a) include `qubit_swap p p`
calls (violating the well-typed precondition `a ≠ b`) or (b) overwrite
earlier swaps' outputs.

The key facts: at `bits = 4`, the very first swap `qubit_swap 3 3` is
malformed; at `bits = 10`, there are multiple cross-index overlaps. -/

/-- Cuccaro b-bit (accumulator) position for window index `n`. -/
private def cuccaroBPos (n : Nat) : Nat := 2 * n + 3

/-- Official `encodeDataZeroAnc` data position for window index `n`
(under the `bits - 1 - n` big-endian mapping). -/
private def dataPos (bits n : Nat) : Nat := bits - 1 - n

/-- **Coincidence characterization (key arithmetic fact).** The
Cuccaro accumulator's `n`-th b-bit position coincides with the official
data register's `n`-th big-endian position exactly when `bits = 3*n + 4`.
Proof: `omega` on the Nat subtractions. -/
private theorem cuccaroBPos_dataPos_eq_iff (bits n : Nat) :
    cuccaroBPos n = dataPos bits n ↔ bits = 3 * n + 4 := by
  unfold cuccaroBPos dataPos
  omega

/-- **`bits = 4` diagnostic.** At the smallest interesting width
(`bits = 4`, satisfying `2 * numWin = bits` with `numWin = 2`), the
window-0 source `cuccaroBPos 0 = 3` and window-0 destination
`dataPos 4 0 = 3` are EQUAL. A `qubit_swap 3 3` is malformed because
`qubit_swap_correct` requires `a ≠ b`. -/
private theorem cuccaroBitsToDataSwap_invalid_at_bits_4 :
    cuccaroBPos 0 = dataPos 4 0 := by
  rfl

/-- **`bits = 10` cross-index overlap diagnostic.** Even when window-0
source and destination are distinct (e.g., for `bits = 10`,
`cuccaroBPos 0 = 3` vs `dataPos 10 0 = 9`), other window indices
create cross-collisions: window-1 source coincides with window-4
destination, and window-2 source coincides with window-2 destination
(the diagonal case `bits = 3*n + 4` at `n = 2`, `bits = 10`).
A naive sequential cascade would produce either malformed swaps or
incorrect overwrites. -/
private theorem cuccaroBitsToDataSwap_overlap_bits10 :
    cuccaroBPos 1 = dataPos 10 4 ∧
    cuccaroBPos 2 = dataPos 10 2 := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- **Verdict: Cuccaro accumulator positions overlap data positions in
general.** The set `{cuccaroBPos n : n < bits}` (positions
`{3, 5, 7, …, 2*bits + 1}`) and the set `{dataPos bits n : n < bits}`
(positions `{0, 1, 2, …, bits - 1}`) share all odd integers in
`[3, bits - 1]` — i.e., for every `bits ≥ 4`, there is at least one
shared position.

Specifically, for `bits = 4`: shared = `{3}`; for `bits = 6`: shared
= `{3, 5}`; for `bits = 10`: shared = `{3, 5, 7, 9}`.

The "Cuccaro→Data SWAP" cascade therefore cannot be specified as a
naive sequence of independent SWAPs. The fix requires either:
- a permutation network (multiple non-independent swap chains), or
- shifting the Cuccaro workspace ABOVE the official data register
  (Option C2 in the design note). -/
private theorem cuccaroBPos_in_data_range (n bits : Nat)
    (h : 2 * n + 3 < bits) :
    cuccaroBPos n < bits := by
  unfold cuccaroBPos
  omega

end Windowed

/-! ## Compatibility note

The following names from the old API remain available (now deprecated):
- `FormalRV.SQIRPort.Shor_correct`
- `FormalRV.SQIRPort.f_modmult_circuit`
- `FormalRV.SQIRPort.f_modmult_circuit_MMI`
- `FormalRV.SQIRPort.f_modmult_circuit_uc_well_typed`

Each is marked `@[deprecated VerifiedShor.correct]` (or the
corresponding constructive verified replacement).  See
`Shor.lean:4570-4716` for the deprecation site. -/

end VerifiedShor
