/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetGate — SUB-LEMMA 1 of the in-place phase:
  the LITERAL in-place reduced-lookup coset multiplier GATE.
  ════════════════════════════════════════════════════════════════════════════

  The in-place phase (see `InPlaceCosetSpec`, tag `coset-shor-scaffold-complete`) builds
  a concrete oracle satisfying `inplaceReducedLookupCosetMul_shift`.  THIS file is
  checkpoint 1: define the literal gate and make the register/bad-set reindexing
  obligations EXPLICIT.

  IDIOM (review decision 2026-06-15): the un-compute leg is a SECOND FORWARD multiply by
  `(N − aInv)`, NOT `Gate.reverse(mulFwd aInv)`.  This is the EXACT idiom of the repo's
  one PROVEN in-place multiplier `windowedModNMulInPlace`/`_correct`
  (FormalRV/Arithmetic/Windowed/WindowedModNInPlace.lean), so checkpoint 3 clones that
  verified basis proof at the coset level (cancellation by `mod_inv_cancel_identity`:
  `(y + (N − aInv)·(a·y % N)) % N = 0`).  Gidney's source idiom is `OOPmul(a) ; SWAP ;
  OOPmul(−a⁻¹)`.

  THE CONSTRUCTION (the standard out-of-place → in-place trick):

      inplaceCosetGate = mulFwd(a) ; accYSwap ; mulFwd(N − aInv)

         |z⟩|0⟩  --fwd(a)-->  |z⟩|a·z⟩  --swap-->  |a·z⟩|z⟩  --fwd(N−aInv)-->  |a·z⟩|0⟩

    * `mulFwd(c) = cosetModMulCircuitOf cuccaroAdder w bits N c numWin` — the VERIFIED
      out-of-place reduced-lookup coset multiplier (multiplies the y-register coset into
      the accumulator), at constant `c`.
    * `accYSwap cuccaroAdder w bits` — the proven acc↔y register swap
      (`augendIdx (1+2w)` ↔ `1+2w + span bits + i`), moving the post-`mulFwd(a)`
      accumulator into the y-register.
    * `mulFwd(N − aInv)` — the second forward multiply, reading the swapped y-register and
      clearing the accumulator (now holding the old `y`) to the coset of `0`.

  `aInv` (the modular inverse, `(a*aInv)%N = 1`, `aInv < N`, exists by
  `CosetModArith.cosetModInv_exists` under `Coprime a N`) is a free `Nat` parameter; the
  uncompute leg uses the additive-complement constant `N − aInv`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Def.ReducedLookupCosetGate
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetGate

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit (accYSwap)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
  (cosetModMulCircuitOf cosetDim cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim)
open FormalRV.BQAlgo.WindowedModNShor (accYSwap_cuccaro_wellTyped)

/-! ## §1. The literal gate. -/

/-- **The literal in-place reduced-lookup coset multiplier gate** (checkpoint 1).
    `mulFwd(a) ; accYSwap ; mulFwd(N − aInv)`, the coset analogue of the proven
    `windowedModNMulInPlace`.  Lives on `cosetDim w bits` qubits (the swap is internal). -/
def inplaceCosetGate (w bits N a aInv numWin : Nat) : Gate :=
  Gate.seq
    (Gate.seq (cosetModMulCircuitOf cuccaroAdder w bits N a numWin)
              (accYSwap cuccaroAdder w bits))
    (cosetModMulCircuitOf cuccaroAdder w bits N (N - aInv) numWin)

/-- **Structure guard (machine-checked, `rfl`).**  The gate is literally
    `(mulFwd(a) ; accYSwap) ; mulFwd(N − aInv)` — the un-compute leg is a FORWARD multiply
    by the additive-complement constant `N − aInv` (matching the proven
    `windowedModNMulInPlace`), NOT a `Gate.reverse`.  Confirms the idiom in code, and names
    the explicit three-leg structure for rewriting in checkpoint 3. -/
theorem inplaceCosetGate_unfold (w bits N a aInv numWin : Nat) :
    inplaceCosetGate w bits N a aInv numWin
      = Gate.seq
          (Gate.seq (cosetModMulCircuitOf cuccaroAdder w bits N a numWin)
                    (accYSwap cuccaroAdder w bits))
          (cosetModMulCircuitOf cuccaroAdder w bits N (N - aInv) numWin) :=
  rfl

/-! ## §2. Well-typedness (the only proof discharged at checkpoint 1). -/

/-- **The in-place coset gate is well-typed at its own dimension** `cosetDim w bits`.
    All three legs are well-typed at `cosetDim`: the two forward multipliers by
    `cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim` (at constants `a` and `N − aInv`),
    the swap by `accYSwap_cuccaro_wellTyped` (its budget `1+2w+(2bits+1)+bits = cosetDim`
    holds with equality). -/
theorem inplaceCosetGate_cuccaro_wellTyped (w bits N a aInv numWin : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (cosetDim w bits) (inplaceCosetGate w bits N a aInv numWin) := by
  unfold inplaceCosetGate
  exact ⟨⟨cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim w bits N a numWin hw hbits,
          accYSwap_cuccaro_wellTyped w bits (cosetDim w bits) (by unfold cosetDim; omega)⟩,
         cosetModMulCircuitOf_cuccaro_wellTyped_cosetDim w bits N (N - aInv) numWin hw hbits⟩

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

/-! ## §4. The clearing mechanism (checkpoint 3 — clone of the proven template).

    Checkpoint 3 follows `windowedModNMulInPlace_correct` (WindowedModNInPlace.lean:224)
    at the coset level, via `Gate.applyNat`-level bookkeeping lifted with
    `uc_eval_eq_permState`:
      1. `mulFwd(a)` advances the accumulator to the coset of `a·y` (checkpoint 2,
         `InPlaceCosetForward.inplaceCosetGate_forward_state`); y stays plain.
      2. `accYSwap` exchanges accumulator ↔ y-register (`accYSwap_apply`): accumulator ←
         plain `y`, y-register ← coset of `a·y`.
      3. `mulFwd(N − aInv)` reads the swapped y-register and clears the accumulator to the
         coset of `0` by `mod_inv_cancel_identity`: `(y + (N − aInv)·(a·y % N)) % N = 0`
         (runway terms `k·N` vanish mod `N`).
    HONEST DEVIATION: the in-place bad set is the forward-wrap ∪ reverse-wrap (two window
    symmetric differences); the swap contributes 0 (`normSqDist_perm_invariant`).  The
    total Born-mass bound DOUBLES to `≤ 2·numWin/2^cm` (the spec's `numWin/2^cm` constant
    is relaxed accordingly downstream — a constant, no structural change).
-/

/-! ## §5. The remaining OBLIGATIONS, stated explicitly (checkpoints 3–4).

  These are the precise targets the next checkpoints must discharge.  They are NOT
  proven here, and nothing in the verified scaffold depends on them (grep-confirmed:
  `inplaceReducedLookupCosetMul_shift` has no consumers).  Stated so that the
  register/bad-set reindexing cannot silently change underneath the proof.

  ── OBLIGATION (b) — bad-set reindex `B (work register) ↔ wrap boundary` ─────────────
    The spec's bad set `B : Finset (Fin (2^(bits + cosetAnc w bits)))` is the image,
    under the OBLIGATION-(a) reindex `Fin (2^(bits+cosetAnc w bits)) ≃ Fin (2^cosetDim)`,
    of the forward-wrap ∪ reverse-wrap boundary (each leg's mass `≤ numWin/2^cm` by
    `ReducedLookupCosetShift.reducedLookupWindowedMul_embedAgreeOff_local`, summing to
    `≤ 2·numWin/2^cm`).  REQUIREMENT (the user's caution): `B` must be PHASE-INDEPENDENT —
    it may depend on the gate `(w,bits,N,a,numWin)` but NOT on any control outcome / phase
    branch.  The forward leg's set lives on the ACCUMULATOR factor `Fin (2^bits)`; the
    in-place result's `B` lives on the residue (y-) factor — the swap moves the runway, so
    the `B ↔ wrap` correspondence must be proven THROUGH `accYSwap`, NOT assumed equal.

  ── OBLIGATION (c) — value-encoding `cosetState z ↔ residue-register encoding` ───────
    The spec asserts `uc_eval (Gate.toUCom (cosetDim w bits) (inplaceCosetGate …))
    (cosetState (2^(bits+cosetAnc)) N cm z) = cosetState … ((a*z)%N)` off `B`.  At the
    basis level this is the §4 three-step clone (`mulFwd(a)`; `accYSwap`; `mulFwd(N−aInv)`)
    with `z` the residue in the y-register and clean scratch (the `ModNMulReady`/`MulReady`
    contract); lifting the basis action to the `cosetState` superposition and through
    `Gate.toUCom`'s `uc_eval` is checkpoint 4 (the branchOfE-control-form → in-place
    row-action conversion + the accumulator-dim → work-dim transport via OBLIGATION (a)).

  ── THE TARGET (what checkpoints 3–4 assemble) ──────────────────────────────────────
    `inplaceReducedLookupCosetMul_shift bits (cosetAnc w bits) N cm a (2*numWin)
        (cosetWork_dim_eq w bits ▸ Gate.toUCom (cosetDim w bits) (inplaceCosetGate w bits N a aInv numWin))`
    i.e. the in-place gate, lifted to a `BaseUCom` and transported to the work dimension,
    satisfies the frozen interface (with the doubled mass budget) — which then feeds
    `ControlOracleLift` and the (deferred) lemma-5 glue.
-/

end FormalRV.Shor.GidneyInPlace.InPlaceCosetGate
