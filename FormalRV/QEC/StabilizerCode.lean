/-
  FormalRV.QEC.StabilizerCode — ARBITRARY stabilizer codes, beyond CSS.

  ## Why this exists (refactor goal 4, John 2026-06-10)

  "Allow the user to define arbitrary QEC codes under the stabilizer
  framework, while also providing shorthand helper frameworks for well-known
  codes."  Until this file the only code structure was `CSSCode` (a pair of
  GF(2) check matrices — X-type and Z-type rows only).  A general stabilizer
  code is just a list of PHASED Pauli check generators over `n` qubits; its
  validity (uniform length + pairwise commutation) is precisely
  `StabilizerState.valid`, so every general code plugs directly into the
  existing Gottesman PPM machinery (`apply_PPM_pos/neg`,
  `SurgeryCorrect.measureChecks`, `LogicalMeasurementGeneral`).

  Contents:
    * `StabilizerCode`        — n qubits + arbitrary Pauli check list;
    * `StabilizerCode.valid`  — decidable well-formedness;
    * `CSSCode.toStabilizerCode` + the theorem that every well-shaped CSS
      code with the CSS condition is a valid stabilizer code (riding on
      `syndrome_circuit_implements_code`);
    * `isCSSShaped`           — decidable "is this code expressible in the
      CSS fragment?";
    * `code513`               — the [[5,1,3]] perfect code, the canonical
      NON-CSS stabilizer code, validity by kernel `decide`, non-CSS-ness
      pinned by theorem.

  Shorthand families (surface / hypergraph-product / bivariate-bicycle /
  lifted-product) remain in `FrontendAlgebraic.lean` — they are CSS by
  construction and embed here via `toStabilizerCode`.  Syndrome-extraction
  circuit compilation (`Circuit/SyndromeExtraction.lean`) currently covers
  the CSS fragment (X/Z-basis check blocks); general-Pauli extraction blocks
  need basis-change gates in the IR — documented residue.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.CSSCode
import FormalRV.QEC.Logical

namespace FormalRV.QEC

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp

/-- An arbitrary stabilizer code: `n` qubits and a list of phased Pauli
    check generators. -/
structure StabilizerCode where
  n      : Nat
  checks : List PauliString
  deriving DecidableEq, Repr, Inhabited

namespace StabilizerCode

/-- Structural validity: every check has length `n` and all checks pairwise
    commute — exactly `StabilizerState.valid`, so a valid code's check list
    IS a measurable stabilizer state.  NOT checked (documented residue, as
    for CSS `derivedK`): sign-consistency (a generator set like `{+Z, −Z}`
    whose group contains `−I` passes) and generator independence. -/
def valid (c : StabilizerCode) : Bool :=
  StabilizerState.valid c.checks c.n

/-- A check usable in the CSS fragment: X/I-only or Z/I-only. -/
def checkIsXType (g : PauliString) : Bool :=
  g.ops.all (fun p => p == Pauli.X || p == Pauli.I)

def checkIsZType (g : PauliString) : Bool :=
  g.ops.all (fun p => p == Pauli.Z || p == Pauli.I)

/-- Decidable: the code is expressible in the CSS fragment (every check is
    X-type or Z-type).  Classifies by Pauli letters only, i.e. up to sign —
    phases are ignored, while `CSSCode.toStabilizers` always emits
    `Phase.plus` checks. -/
def isCSSShaped (c : StabilizerCode) : Bool :=
  c.checks.all (fun g => checkIsXType g || checkIsZType g)

end StabilizerCode

/-! ## CSS codes embed -/

/-- Every CSS code is a stabilizer code via its lowered check list. -/
def CSSCode.toStabilizerCode (c : CSSCode) : StabilizerCode :=
  ⟨c.n, c.toStabilizers⟩

/-- A well-shaped CSS code satisfying the CSS condition embeds as a VALID
    stabilizer code (the `syndrome_circuit_implements_code` bridge). -/
theorem CSSCode.toStabilizerCode_valid (c : CSSCode)
    (hws : c.well_shaped = true) (hcss : c.css_condition = true) :
    c.toStabilizerCode.valid = true :=
  (CSSCode.syndrome_circuit_implements_code c hws).mpr hcss

/-- The CSS embedding is CSS-shaped (sanity, on the Steane [[7,1,3]] code). -/
example : (CSSCode.toStabilizerCode steaneCSS).isCSSShaped = true := by
  decide

/-! ## The [[5,1,3]] perfect code — genuinely non-CSS -/

/-- The five-qubit code: stabilizers `XZZXI, IXZZX, XIXZZ, ZXIXZ` (cyclic
    shifts of `XZZXI`), the smallest distance-3 code, and NOT a CSS code. -/
def code513 : StabilizerCode :=
  ⟨5,
   [⟨Phase.plus, [Pauli.X, Pauli.Z, Pauli.Z, Pauli.X, Pauli.I]⟩,
    ⟨Phase.plus, [Pauli.I, Pauli.X, Pauli.Z, Pauli.Z, Pauli.X]⟩,
    ⟨Phase.plus, [Pauli.X, Pauli.I, Pauli.X, Pauli.Z, Pauli.Z]⟩,
    ⟨Phase.plus, [Pauli.Z, Pauli.X, Pauli.I, Pauli.X, Pauli.Z]⟩]⟩

/-- The [[5,1,3]] code is a valid stabilizer code (4 commuting length-5
    generators) — kernel `decide`, no native evaluation. -/
theorem code513_valid : code513.valid = true := by decide

/-- The [[5,1,3]] code is NOT CSS-shaped: its first check `XZZXI` mixes X
    and Z — the user-defined-code framework genuinely exceeds `CSSCode`. -/
theorem code513_not_css : code513.isCSSShaped = false := by decide

/-- Derived: 5 − 4 independent checks = 1 logical qubit (the checks are
    independent; here we pin only the generator count — rank-based `k`
    derivation for general Pauli checks via the symplectic GF(2) form is a
    documented residue, as for CSS `derivedK`). -/
theorem code513_check_count : code513.checks.length = 4 := by decide

end FormalRV.QEC
