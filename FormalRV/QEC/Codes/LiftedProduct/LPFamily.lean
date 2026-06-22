/-
  FormalRV.QEC.Codes.LiftedProduct.LPFamily — lifted-product codes
  LP(A, A†) over F₂[x]/(xˡ+1) with ARBITRARY lift size and seed.

  The generator `code l A rA nA` is total: ANY circulant size `l` and ANY
  `rA × nA` polynomial seed matrix `A` (entries = exponent supports) yield
  the `[[(rA² + nA²)·l, ·, ·]]` LP check matrices, stabilizer list, compiled
  extraction circuit, and Stim text.  The compiled-circuit semantics theorem
  holds for EVERY parameter choice, conditional only on the decidable shape
  check.  For this family the shape hypothesis is ALREADY closed
  parametrically: `Algebraic.liftedProduct_well_shaped` (`LPCssCondition`),
  which is how `lp16/lp20/lp24` (2610–5278 columns) get well-shapedness
  without any `decide` at scale; the ∀-parameter `css_condition` is the
  documented open `LPCssCondition` §9 programme.

  No `sorry`; no project axioms (kernel `decide` throughout this file).
-/

import FormalRV.QEC.Codes.LiftedProduct.LPChain

set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.LP

open FormalRV.QEC FormalRV.QEC.Circuit FormalRV.QEC.Algebraic
open FormalRV.Framework.LDPC FormalRV.Framework.PauliSem

/-! ## The arbitrary-parameter generator and its review artifacts -/

/-- The lifted product LP(A, A†) for ARBITRARY lift size `l` and `rA × nA`
    polynomial seed `A` (entries are exponent-support lists in
    F₂[x]/(xˡ+1)). -/
abbrev code (l : Nat) (A : List (List Circ)) (rA nA : Nat) : FormalRV.QEC.CSSCode :=
  liftedProduct l A rA nA

abbrev checkMatrixX (l : Nat) (A : List (List Circ)) (rA nA : Nat) : BoolMat :=
  (code l A rA nA).hx
abbrev checkMatrixZ (l : Nat) (A : List (List Circ)) (rA nA : Nat) : BoolMat :=
  (code l A rA nA).hz

/-- The detailed stabilizer generators for ANY parameters. -/
abbrev stabilizers (l : Nat) (A : List (List Circ)) (rA nA : Nat) : List PauliString :=
  (code l A rA nA).toStabilizers

/-- The compiled extraction round for ANY parameters. -/
abbrev extractionRound (l : Nat) (A : List (List Circ)) (rA nA : Nat) : Round :=
  FormalRV.QEC.CSSCode.extractionRound (code l A rA nA)

/-- Its Stim text. -/
abbrev extractionStim (l : Nat) (A : List (List Circ)) (rA nA : Nat) : String :=
  toStim (Round.ops (extractionRound l A rA nA))

/-- `n = (rA² + nA²)·l` for every parameter choice (definitional). -/
theorem code_n (l : Nat) (A : List (List Circ)) (rA nA : Nat) :
    (code l A rA nA).n = (rA * rA + nA * nA) * l := rfl

/-! ## Semantics for EVERY parameter choice -/

theorem family_extraction_measures (l : Nat) (A : List (List Circ)) (rA nA : Nat)
    (h : (code l A rA nA).well_shaped = true) :
    Round.measuredDataObs
        ((code l A rA nA).n + (code l A rA nA).hx.length
          + (code l A rA nA).hz.length)
        (code l A rA nA).n (extractionRound l A rA nA)
      = (code l A rA nA).toStabilizers :=
  extractionRound_measures_code (code l A rA nA) h

/-! ## A second parameter set (genuine arbitrariness) -/

/-- A different LP member: lift size 5, seed `A = [x⁰, x²]` — `[[25, ·, ·]]`. -/
def lp25 : FormalRV.QEC.CSSCode := code 5 [[[0], [2]]] 1 2

theorem lp25_n : lp25.n = 25 := by decide
theorem lp25_valid : lp25.valid = true := by decide

theorem lp25_extraction_measures :
    Round.measuredDataObs
        (lp25.n + lp25.hx.length + lp25.hz.length)
        lp25.n (FormalRV.QEC.CSSCode.extractionRound lp25)
      = lp25.toStabilizers :=
  extractionRound_measures_code lp25 (by decide)

end FormalRV.QEC.Codes.LP
