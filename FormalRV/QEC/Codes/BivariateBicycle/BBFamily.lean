/-
  FormalRV.QEC.Codes.BivariateBicycle.BBFamily — bivariate-bicycle codes
  with ARBITRARY block parameters and polynomials.

  The generator `code l m a b` is total: ANY `l, m` and ANY exponent-support
  lists `a, b` (the monomials of the two bivariate polynomials A, B) yield
  the `[[2·l·m, ·, ·]]` BB check matrices `hx = [A|B]`, `hz = [Bᵀ|Aᵀ]`, the
  stabilizer list, the compiled extraction circuit, and Stim text.  The
  compiled-circuit semantics theorem holds for EVERY parameter choice,
  conditional only on the decidable shape check — discharged below for two
  different parameter sets.  (`Instances.bb18` is the paper-scale
  `[[248,10,18]]` member.)

  No `sorry`; no project axioms (kernel `decide` throughout this file).
-/

import FormalRV.QEC.Codes.BivariateBicycle.BBChain

set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.BB

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC FormalRV.Framework.PauliSem

/-! ## The arbitrary-parameter generator and its review artifacts -/

/-- The bivariate-bicycle code for ARBITRARY `l, m` and polynomial supports
    `a, b` (lists of `(i, j)` monomial exponents). -/
abbrev code (l m : Nat) (a b : List (Nat × Nat)) : FormalRV.QEC.CSSCode :=
  FormalRV.QEC.Algebraic.bivariateBicycle l m a b

abbrev checkMatrixX (l m : Nat) (a b : List (Nat × Nat)) : BoolMat := (code l m a b).hx
abbrev checkMatrixZ (l m : Nat) (a b : List (Nat × Nat)) : BoolMat := (code l m a b).hz

/-- The detailed stabilizer generators for ANY parameters. -/
abbrev stabilizers (l m : Nat) (a b : List (Nat × Nat)) : List PauliString :=
  (code l m a b).toStabilizers

/-- The compiled extraction round for ANY parameters. -/
abbrev extractionRound (l m : Nat) (a b : List (Nat × Nat)) : Round :=
  FormalRV.QEC.CSSCode.extractionRound (code l m a b)

/-- Its Stim text. -/
abbrev extractionStim (l m : Nat) (a b : List (Nat × Nat)) : String :=
  toStim (Round.ops (extractionRound l m a b))

/-- `n = 2·l·m` for every parameter choice (definitional). -/
theorem code_n (l m : Nat) (a b : List (Nat × Nat)) :
    (code l m a b).n = 2 * l * m := rfl

/-! ## Semantics for EVERY parameter choice -/

theorem family_extraction_measures (l m : Nat) (a b : List (Nat × Nat))
    (h : (code l m a b).well_shaped = true) :
    Round.measuredDataObs
        ((code l m a b).n + (code l m a b).hx.length + (code l m a b).hz.length)
        (code l m a b).n (extractionRound l m a b)
      = (code l m a b).toStabilizers :=
  extractionRound_measures_code (code l m a b) h

/-! ## A second parameter set (genuine arbitrariness) -/

/-- A different BB member: `l = 4, m = 2`, `A = 1 + x`, `B = 1 + y` —
    `[[16, ·, ·]]`. -/
def bb16 : FormalRV.QEC.CSSCode := code 4 2 [(0, 0), (1, 0)] [(0, 0), (0, 1)]

theorem bb16_n : bb16.n = 16 := by decide
theorem bb16_valid : bb16.valid = true := by decide

theorem bb16_extraction_measures :
    Round.measuredDataObs
        (bb16.n + bb16.hx.length + bb16.hz.length)
        bb16.n (FormalRV.QEC.CSSCode.extractionRound bb16)
      = bb16.toStabilizers :=
  extractionRound_measures_code bb16 (by decide)

end FormalRV.QEC.Codes.BB
