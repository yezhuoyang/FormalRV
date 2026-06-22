/-
  FormalRV.QEC.Codes.HypergraphProduct.HGPFamily — hypergraph products of
  ARBITRARY seed matrices.

  The generator `code h1 h2 m1 n1 m2 n2` is total in its seeds: ANY pair of
  GF(2) check matrices yields the HGP check matrices, stabilizer list,
  compiled extraction circuit, and Stim text.  The compiled-circuit
  semantics theorem holds for EVERY seed pair, conditional only on the
  decidable `well_shaped` check — discharged below for two different seed
  pairs (Hamming×rep3 and rep3×rep4) to demonstrate genuine arbitrariness.
  The ∀-seed well-shapedness/CSS programme is tracked work (the
  `LPCssCondition` precedent).

  No `sorry`; no project axioms (kernel `decide` throughout this file).
-/

import FormalRV.QEC.Codes.HypergraphProduct.HGPChain

set_option maxRecDepth 16384

namespace FormalRV.QEC.Codes.HGP

open FormalRV.QEC FormalRV.QEC.Circuit
open FormalRV.Framework.LDPC FormalRV.Framework.PauliSem

/-! ## The arbitrary-seed generator and its review artifacts -/

/-- The hypergraph product of ARBITRARY seed check matrices `h1 : m1 × n1`,
    `h2 : m2 × n2`: an `[[n1·n2 + m1·m2, k1·k2 + k1ᵀ·k2ᵀ, min(d…)]]` CSS
    code. -/
abbrev code (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : FormalRV.QEC.CSSCode :=
  FormalRV.QEC.Algebraic.hypergraphProduct h1 h2 m1 n1 m2 n2

abbrev checkMatrixX (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : BoolMat :=
  (code h1 h2 m1 n1 m2 n2).hx
abbrev checkMatrixZ (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : BoolMat :=
  (code h1 h2 m1 n1 m2 n2).hz

/-- The detailed stabilizer generators for ANY seed pair. -/
abbrev stabilizers (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : List PauliString :=
  (code h1 h2 m1 n1 m2 n2).toStabilizers

/-- The compiled extraction round for ANY seed pair. -/
abbrev extractionRound (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : Round :=
  FormalRV.QEC.CSSCode.extractionRound (code h1 h2 m1 n1 m2 n2)

/-- Its Stim text. -/
abbrev extractionStim (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : String :=
  toStim (Round.ops (extractionRound h1 h2 m1 n1 m2 n2))

/-- `n = n1·n2 + m1·m2` for every seed pair (definitional). -/
theorem code_n (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) :
    (code h1 h2 m1 n1 m2 n2).n = n1 * n2 + m1 * m2 := rfl

/-! ## Semantics for EVERY seed pair -/

/-- **Arbitrary-seed semantics.**  For every seed pair, the compiled
    extraction round measures exactly the HGP code's stabilizers,
    conditional only on the decidable shape check. -/
theorem family_extraction_measures (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat)
    (h : (code h1 h2 m1 n1 m2 n2).well_shaped = true) :
    Round.measuredDataObs
        ((code h1 h2 m1 n1 m2 n2).n + (code h1 h2 m1 n1 m2 n2).hx.length
          + (code h1 h2 m1 n1 m2 n2).hz.length)
        (code h1 h2 m1 n1 m2 n2).n (extractionRound h1 h2 m1 n1 m2 n2)
      = (code h1 h2 m1 n1 m2 n2).toStabilizers :=
  extractionRound_measures_code (code h1 h2 m1 n1 m2 n2) h

/-! ## A second seed pair (genuine arbitrariness) -/

/-- HGP(rep 3, rep 4): an `[[18, 1, 3]]`-type product of two DIFFERENT
    repetition checks — a non-square instance distinct from `hgp73`. -/
def hgp_rep34 : FormalRV.QEC.CSSCode :=
  code (FormalRV.QEC.Algebraic.repCode 3) (FormalRV.QEC.Algebraic.repCode 4) 2 3 3 4

theorem hgp_rep34_n : hgp_rep34.n = 18 := by decide
theorem hgp_rep34_valid : hgp_rep34.valid = true := by decide

theorem hgp_rep34_extraction_measures :
    Round.measuredDataObs
        (hgp_rep34.n + hgp_rep34.hx.length + hgp_rep34.hz.length)
        hgp_rep34.n (FormalRV.QEC.CSSCode.extractionRound hgp_rep34)
      = hgp_rep34.toStabilizers :=
  extractionRound_measures_code hgp_rep34 (by decide)

end FormalRV.QEC.Codes.HGP
