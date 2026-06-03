/-
  FormalRV.Corpus.ShorPPMUnitaryReduction — turn the "unitary ∧ Boolean-PPM" CONJUNCTION
  into a REDUCTION for the Clifford fragment (closing seam 6).

  The audit's seam 6: `shor_succeeds_with_ppm_realized_modmult` and
  `surface_shor_ppm_physically_realized` are CONJUNCTIONS (unitary success ∧ Boolean PPM
  run) at shared parameters — "a conjunction, NOT a reduction" — with no theorem proving
  the Boolean PPM program EQUALS the unitary's action.

  Here we prove exactly that equality for the Clifford (I/X/CX) fragment — the fragment
  that the modular-multiplier circuit is built from, apart from the CCX/Toffoli gates
  (whose magic-state realisation is seam 5).  Composing two existing pieces:

    • `magicBasisPPMReflects_ICX` : running the compiled PPM program of an ICX gate forces
      the magic-basis gate relation (`PPMReflectsGateRel`);
    • `magicBasisPPMGateRel_imp_applyNat` : that gate relation forces
      `σ'.bits = Gate.applyNat g s.bits`.

  Their composition is a genuine REDUCTION: from a computational-basis input, the Boolean
  PPM RUN of the compiled Clifford circuit yields EXACTLY `Gate.applyNat g f` — the
  unitary's computational-basis (permutation) action.  Not a conjunction at shared
  parameters: an EQUALITY between the two semantic levels.

  Residue (honest): `Gate.applyNat` is the gate's classical-basis permutation; that this
  permutation equals the SQIR `uc_eval` unitary on basis states is the Gottesman–Knill /
  Heisenberg–Schrödinger faithfulness (delimited).  And the non-Clifford CCX needs a magic
  state — seam 5.  But for the Clifford fragment the conjunction is now a reduction.

  No `sorry`, no `axiom`.
-/

import FormalRV.PPM.CircuitToPPMMagicFactory

namespace FormalRV.Corpus.ShorPPMUnitaryReduction

open FormalRV.Framework
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMInterface
open FormalRV.Framework.CircuitToPPMSemanticBridge
open FormalRV.BQAlgo

/-! ## §1. The reduction: Boolean PPM run = unitary basis action (Clifford fragment) -/

/-- **REDUCTION (Clifford fragment).**  For any Clifford `I/X/CX/seq` gate `g`, running the
    COMPILED PPM PROGRAM `compileArithmeticGateToPPM g` from the encoded computational-basis
    input `f` lands in a state whose bits are EXACTLY `Gate.applyNat g f` — the unitary's
    basis-permutation action.  This is an EQUALITY between the Boolean-PPM run and the
    gate's basis action — not a conjunction at shared parameters. -/
theorem ppm_clifford_run_eq_applyNat
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) (f : Nat → Bool)
    (σ' : MagicBasisPPMState)
    (hrun : PPMProgramRel (magicBasisPPMSemanticsModel F) (compileArithmeticGateToPPM g)
              (magicBasisEncodeBits F f) σ') :
    σ'.bits = Gate.applyNat g f :=
  magicBasisPPMGateRel_imp_applyNat g (magicBasisEncodeBits F f) σ'
    (magicBasisPPMReflects_ICX F g hICX (magicBasisEncodeBits F f) σ' hrun)

/-- The reduction at the OBSERVATION level: the Boolean PPM run observes exactly the
    `Gate.applyNat g f` bit-state (and never fails) — the full refinement, for the
    Clifford fragment, as an equality of observed bit-states. -/
theorem ppm_clifford_observes_applyNat
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) (f : Nat → Bool)
    (σ' : MagicBasisPPMState)
    (hrun : PPMProgramRel (magicBasisPPMSemanticsModel F) (compileArithmeticGateToPPM g)
              (magicBasisEncodeBits F f) σ') :
    magicBasisObservesBits F σ' (Gate.applyNat g f) :=
  ⟨ppm_clifford_run_eq_applyNat F g hICX f σ' hrun,
   magicBasisPPMGateRel_preserves_failed g (magicBasisEncodeBits F f) σ'
     (magicBasisPPMReflects_ICX F g hICX (magicBasisEncodeBits F f) σ' hrun)⟩

/-! ## §2. Determinism: the Boolean PPM run is FUNCTION of the input (a reduction, not a
    relation) -/

/-- The Boolean PPM run of a Clifford circuit is DETERMINISTIC in the input bits: any two
    runs from the same encoded input land in states with identical bits.  (Two relational
    outputs are forced equal because both equal `Gate.applyNat g f`.)  This is what makes
    "the Boolean PPM run" a well-defined function of the input — the hallmark of a genuine
    reduction. -/
theorem ppm_clifford_run_deterministic
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) (f : Nat → Bool)
    (σ₁ σ₂ : MagicBasisPPMState)
    (h1 : PPMProgramRel (magicBasisPPMSemanticsModel F) (compileArithmeticGateToPPM g)
            (magicBasisEncodeBits F f) σ₁)
    (h2 : PPMProgramRel (magicBasisPPMSemanticsModel F) (compileArithmeticGateToPPM g)
            (magicBasisEncodeBits F f) σ₂) :
    σ₁.bits = σ₂.bits := by
  rw [ppm_clifford_run_eq_applyNat F g hICX f σ₁ h1,
      ppm_clifford_run_eq_applyNat F g hICX f σ₂ h2]

/-! ## §3. Headline -/

/-- **Seam 6 (Clifford fragment): the conjunction is now a reduction.**  For every Clifford
    `I/X/CX/seq` gate, the Boolean PPM program run from a basis input is provably EQUAL to
    the unitary's basis-permutation action `Gate.applyNat`, and is a deterministic function
    of the input.  The two semantic levels are connected by an equality, not merely
    conjoined.  (CCX/Toffoli needs a magic state — seam 5; `applyNat`↔`uc_eval` basis
    faithfulness is the delimited Gottesman–Knill residue.) -/
theorem clifford_ppm_is_a_reduction
    (F : TFactoryContract) (g : Gate) (hICX : isICXGate g = true) (f : Nat → Bool) :
    (∀ σ', PPMProgramRel (magicBasisPPMSemanticsModel F) (compileArithmeticGateToPPM g)
              (magicBasisEncodeBits F f) σ' → σ'.bits = Gate.applyNat g f) :=
  fun σ' hrun => ppm_clifford_run_eq_applyNat F g hICX f σ' hrun

end FormalRV.Corpus.ShorPPMUnitaryReduction
