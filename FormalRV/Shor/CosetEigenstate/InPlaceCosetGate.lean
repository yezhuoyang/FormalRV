/-
  FormalRV.Shor.CosetEigenstate.InPlaceCosetGate — SUB-LEMMA 1 of the in-place phase:
  the LITERAL in-place reduced-lookup coset multiplier GATE.
  ════════════════════════════════════════════════════════════════════════════

  The in-place phase (see `InPlaceCosetSpec`, tag `coset-shor-scaffold-complete`) builds
  a concrete oracle satisfying `inplaceReducedLookupCosetMul_shift`.  THIS file is
  checkpoint 1: define the literal gate and make the register/bad-set reindexing
  obligations EXPLICIT.  No Shor-level lemma is proven here, and no abstract
  permutation/`workMat` is introduced — only the gate term, its well-typedness, the
  (proven) register-dimension identity, and the precisely-stated open obligations for
  checkpoints 2–4.

  THE CONSTRUCTION (the standard out-of-place → in-place trick, `InPlace.inPlaceMul`):

      inplaceCosetGate = mulFwd(a) ; accYSwap ; reverse(mulFwd(a⁻¹))

         |z⟩|0⟩  --fwd(a)-->  |z⟩|a·z⟩  --swap-->  |a·z⟩|z⟩  --rev fwd(a⁻¹)-->  |a·z⟩|0⟩

    * `mulFwd(c) = cosetModMulCircuitOf cuccaroAdder w bits N c numWin` — the VERIFIED
      out-of-place reduced-lookup coset multiplier (multiplies the y-register coset into
      the accumulator), at constant `c`.
    * `accYSwap cuccaroAdder w bits` — the proven acc↔y register swap
      (`augendIdx (1+2w)` ↔ `1+2w + span bits + i`).
    * `reverse (mulFwd(a⁻¹))` — `Gate.reverse` of the `a⁻¹`-forward multiplier; per
      `InPlace.inPlaceMul_correct` the un-compute leg is discharged by PURE reversibility
      (`applyNat_reverse_cancel`), isolating ALL arithmetic into a single `hchain`
      (checkpoint 2/3, stated below as `inplaceCosetGate_hchain`).

  `a⁻¹` (`aInv`) is a free `Nat` parameter here (the modular inverse with
  `(a*aInv)%N = 1`, `aInv < N`, exists by `CosetModArith.cosetModInv_exists` under
  `Coprime a N`); its arithmetic role is a correctness hypothesis, NOT part of the
  gate definition.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate
import FormalRV.Shor.CosetEigenstate.InPlace
import FormalRV.Shor.CosetEigenstate.GatePerm
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Shor.CosetEigenstate.InPlaceCosetGate

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit (accYSwap)
open FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate
  (cosetModMulCircuitOf cosetDim cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim)
open FormalRV.Shor.CosetEigenstate.InPlace (inPlaceMul)
open FormalRV.Shor.CosetEigenstate.GatePerm (reverse_wellTyped)
open FormalRV.BQAlgo.WindowedModNShor (accYSwap_cuccaro_wellTyped)

/-! ## §1. The literal gate. -/

/-- **The literal in-place reduced-lookup coset multiplier gate** (checkpoint 1).
    `mulFwd(a) ; accYSwap ; reverse(mulFwd(a⁻¹))`, defeq to
    `Gate.seq (cosetModMulCircuitOf … a) (Gate.seq (accYSwap …) (Gate.reverse (cosetModMulCircuitOf … aInv)))`.
    Lives on `cosetDim w bits` qubits (the swap is internal; `reverse` preserves indices). -/
def inplaceCosetGate (w bits N a aInv numWin : Nat) : Gate :=
  inPlaceMul
    (cosetModMulCircuitOf cuccaroAdder w bits N a    numWin)
    (accYSwap cuccaroAdder w bits)
    (cosetModMulCircuitOf cuccaroAdder w bits N aInv numWin)

/-- **Definitional unfolding (machine-checked direction guard).**  `InPlace.inPlaceMul`
    applies `Gate.reverse` to its THIRD argument, so the un-compute leg of
    `inplaceCosetGate` is literally `Gate.reverse (mulFwd aInv)` — the SUBTRACTING
    `a⁻¹`-multiply that clears the scratch — NOT a forward `mulFwd aInv`.  This `rfl`
    confirms the direction the prose claims (closing the naming ambiguity: the third arg
    is reversed by the combinator, not pre-reversed). -/
theorem inplaceCosetGate_unfold (w bits N a aInv numWin : Nat) :
    inplaceCosetGate w bits N a aInv numWin
      = Gate.seq (cosetModMulCircuitOf cuccaroAdder w bits N a numWin)
          (Gate.seq (accYSwap cuccaroAdder w bits)
            (GateReversible.Gate.reverse
              (cosetModMulCircuitOf cuccaroAdder w bits N aInv numWin))) :=
  rfl

/-! ## §2. Well-typedness (the only proof discharged at checkpoint 1). -/

/-- **The in-place coset gate is well-typed at its own dimension** `cosetDim w bits`.
    Each of the three legs is well-typed at `cosetDim`: the two forward multipliers by
    `cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim`, the swap by
    `accYSwap_cuccaro_wellTyped` (its budget `1+2w+(2bits+1)+bits = cosetDim` holds with
    equality), and the un-compute leg by `reverse_wellTyped` of the `aInv` forward gate. -/
theorem inplaceCosetGate_cuccaro_wellTyped (w bits N a aInv numWin : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (cosetDim w bits) (inplaceCosetGate w bits N a aInv numWin) := by
  unfold inplaceCosetGate inPlaceMul
  refine ⟨cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim w bits N a numWin hw hbits,
    accYSwap_cuccaro_wellTyped w bits (cosetDim w bits) (by unfold cosetDim; omega),
    reverse_wellTyped (cosetModMulCircuitOf cuccaroAdder w bits N aInv numWin)
      (cosetDim w bits)
      (cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim w bits N aInv numWin hw hbits)⟩

/-! ## §3. The register-dimension identity — the Nat core of reindexing OBLIGATION (a). -/

/-- The scratch (ancilla) budget of the in-place coset gate on the Shor work register:
    the lookup zone + the cuccaro accumulator/addend/carry block, i.e. everything except
    the `bits`-wide residue (y-) register that is the in-place input=output. -/
def cosetAnc (w bits : Nat) : Nat := 2 + 2 * w + 2 * bits

/-- **OBLIGATION (a) [PROVEN, Nat core].**  The Shor work register `n + anc` with
    `n = bits` (residue, input=output) and `anc = cosetAnc w bits` (scratch) IS the gate's
    register `cosetDim w bits`.  The carried `Fin (2^(bits + cosetAnc w bits)) ≃
    Fin (2^(cosetDim w bits))` reindex (and the `BaseUCom` transport of
    `Gate.toUCom (cosetDim w bits) (inplaceCosetGate …)` to dim `bits + cosetAnc w bits`)
    follow from this equation by `congrArg`. -/
theorem cosetWork_dim_eq (w bits : Nat) : bits + cosetAnc w bits = cosetDim w bits := by
  unfold cosetAnc cosetDim; omega

/-! ## §4. The arithmetic-heart OBLIGATION — the basis round-trip (checkpoints 2–3).

    `InPlace.inPlaceMul_correct` reduces the gate's basis action to ONE round-trip
    hypothesis: `swap ∘ mulFwd(a)` carries the input encoding `s0` to exactly what
    `mulFwd(a⁻¹)` produces from the output encoding `sFinal`; the un-compute is then pure
    reversibility.  This Prop names that hypothesis for THIS gate — discharging it (for
    `s0`/`sFinal` the canonical residue encodings, off the wrap boundary) is checkpoints
    2–3, and yields `applyNat (inplaceCosetGate …) s0 = sFinal`. -/
def inplaceCosetGate_hchain (w bits N a aInv numWin : Nat) (s0 sFinal : Nat → Bool) : Prop :=
  Gate.applyNat (accYSwap cuccaroAdder w bits)
      (Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N a numWin) s0)
    = Gate.applyNat (cosetModMulCircuitOf cuccaroAdder w bits N aInv numWin) sFinal

/-! ## §5. The remaining OBLIGATIONS, stated explicitly (checkpoints 2–4).

  These are the precise targets the next checkpoints must discharge.  They are NOT
  proven here, and nothing in the verified scaffold depends on them (grep-confirmed:
  `inplaceReducedLookupCosetMul_shift` has no consumers).  Stated so that the
  register/bad-set reindexing cannot silently change underneath the proof.

  ── OBLIGATION (b) — bad-set reindex `B (work register) ↔ wrap boundary` ─────────────
    The spec's bad set `B : Finset (Fin (2^(bits + cosetAnc w bits)))` is the image,
    under the OBLIGATION-(a) reindex `Fin (2^(bits+cosetAnc w bits)) ≃ Fin (2^cosetDim)`,
    of the multiplier-local wrap-boundary set of
    `ReducedLookupCosetShift.reducedLookupWindowedMul_embedAgreeOff_local` (the runway
    overflow, mass `≤ numWin/2^cm`).  REQUIREMENT (the user's caution): `B` must be
    PHASE-INDEPENDENT — it may depend on the gate `(w,bits,N,a,numWin)` but NOT on any
    control outcome / phase branch.  The forward leg's set lives on the ACCUMULATOR
    factor `Fin (2^bits)`; the in-place result's `B` lives on the residue (y-) factor —
    the swap moves the runway, so the `B ↔ wrap` correspondence must be proven through
    `accYSwap`, NOT assumed equal.

  ── OBLIGATION (c) — value-encoding `cosetState z ↔ residue-register encoding` ───────
    The spec asserts `uc_eval (Gate.toUCom (cosetDim w bits) (inplaceCosetGate …))
    (cosetState (2^(bits+cosetAnc)) N cm z) = cosetState … ((a*z)%N)` off `B`.  At the
    basis level this is `inplaceCosetGate_hchain` with `s0`/`sFinal` the canonical coset
    encodings of `z` / `(a*z)%N` (residue = y-register, scratch clean — the
    `ModNMulReady`/`MulReady` contract); lifting the basis action to the `cosetState`
    superposition and through `Gate.toUCom`'s `uc_eval` is checkpoint 4 (the
    branchOfE-control-form → in-place row-action conversion + the accumulator-dim →
    work-dim transport via OBLIGATION (a)).

  ── THE TARGET (what checkpoints 2–4 assemble) ──────────────────────────────────────
    `inplaceReducedLookupCosetMul_shift bits (cosetAnc w bits) N cm a numWin
        (cosetWork_dim_eq w bits ▸ Gate.toUCom (cosetDim w bits) (inplaceCosetGate w bits N a aInv numWin))`
    i.e. the in-place gate, lifted to a `BaseUCom` and transported to the work dimension,
    satisfies the frozen interface — which then feeds `ControlOracleLift` and the
    (deferred) lemma-5 glue.
-/

end FormalRV.Shor.CosetEigenstate.InPlaceCosetGate
