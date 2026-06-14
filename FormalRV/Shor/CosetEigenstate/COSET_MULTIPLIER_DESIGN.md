# Design note — the runway-preserving coset modular multiplier (Gidney's real construction)

**Purpose.** Resolve, on paper before any circuit code, how Gidney–Ekerå-2021's coset
modular multiplier preserves the runway *cheaply*, what its exact net action and per-step
deviation are, and which spec the circuit must target. This was prompted by two prior
results:

- **Audit (`CosetScalingAudit`, OPTION B, proven):** the literal `v ↦ c·v` map (the repo's
  `cosetMulGate` = `windowedMulInPlace`) coarsens the runway `N → cN`; overlap with the
  canonical coset is only `~M/c`. So it is the **wrong** oracle.
- **Spec + eigenstate (`RunwayMul`, `RunwayCosetEigenstate`, proven):** the *residue*
  multiplier `runwayMul c N v = (c·(v%N) mod N) + (v/N)·N` has an **exact** coset orbit-shift
  `cosetState(k) → cosetState(ck mod N)`, hence an exact coset eigenstate (eigenvalue `ζ⁻¹`).

The open question was: *is there a CHEAP circuit realizing `runwayMul`'s residue action, given
that cheap combined-register arithmetic seems to give the bad whole-value multiply?*

---

## 1. The coset representation and the cheap modular ADD

A residue `x mod N` is stored as `x + r·N` for a runway index `r ∈ [0, 2^c)` (register width
`bits = ⌈log₂N⌉ + c`, with `2^c·N ≤ 2^bits`). The quantum work register holds the **uniform**
coset superposition `cosetState = (1/√M) ∑_{r<M} |x + rN⟩` (`M = 2^m`, `m ≤ c`).

**Cheap modular add (no conditional subtraction).** To add `c < N` to a coset rep, just add
`c` (a *plain* adder, mod `2^bits`):
```
(x + rN) + c  =  (x+c) + rN  =  { (x+c) + rN              if x+c < N
                                { (x+c−N) + (r+1)N         if x+c ≥ N    (residue (x+c)%N, runway r+1)
```
So **plain addition automatically performs modular addition** in the coset rep — the runway
absorbs the overflow, incrementing by at most 1. This is exactly
`PhysCosetFold.physCoset_windowed_fold` / `CosetEmbedStep` (plain `cuccaro_addConstGate`
shifts the coset; the boundary mass is the deviation).

---

## 2. The coset modular MULTIPLY — and the one fix vs the repo's gate

Modular multiply `x ↦ (a·x) mod N` is a **windowed multiply-accumulate** into a fresh
accumulator (in coset rep), using the cheap coset adds of §1. Split the multiplicand into
`numWin` windows; for window `i` with value `Xᵢ`, add the **lookup** `L(i, Xᵢ)` to the
accumulator.

**THE FIX (the whole resolution).** The lookup table must store **reduced** constants:
```
L(i, w) = (a · w · 2^{w·i}) mod N        (each L < N)        ← CORRECT (coset modular)
L(i, w) =  a · w · 2^{w·i}               (mod 2^bits)        ← the repo's windowedMulInPlace = WRONG
```
With **reduced** lookups, every added value is `< N`, so:

- **Net residue is exact `a·x mod N`, independent of the input runway.** The accumulator
  value is `∑ᵢ L(i, Xᵢ) ≡ ∑ᵢ a·Xᵢ·2^{wi} = a·X = a·(x + rN) ≡ a·x  (mod N)` — the input runway
  `rN ≡ 0 (mod N)` is *forgotten*. (This is why reading the full coset value's windows is
  harmless: the runway contributes 0 mod N.)
- **The output runway is fresh and BOUNDED.** The accumulator value is `∑ᵢ L(i,Xᵢ) < numWin·N`,
  so `= (a·x mod N) + q·N` with `q = ⌊∑L / N⌋ ≤ numWin`. The runway grew by `≤ numWin`, NOT
  scaled by `a`.

With **non-reduced** lookups (the repo's gate) the added values are `~2^bits`, the runway is
multiplied by `a` (`N → cN`), and OPTION B's sparse overlap results. **The bug is purely the
unreduced lookup table; the fix is one classical change — reduce the table constants mod `N`.**

The in-place multiply is then the usual `out-of-place (reduced-lookup windowed) ; swap ;
uncompute`, so the work register goes `cosetState(x) ↦ cosetState((a·x) mod N)` with a fresh
runway shifted by `≤ numWin`.

---

## 3. Net action, deviation, and the spec to target

**State-level action (the right abstraction):** on the *uniform* coset superposition,
```
cosetState(k)  ↦  cosetState((a·k) mod N)        (uniform runway ↦ uniform runway)
```
which is **exactly `RunwayMul.runwayMul_cosetState_shift`**. The runway is *refreshed* (not
literally `j`-preserved), but the uniform coset state is preserved, so the state abstraction is
correct — `runwayMul`'s value map `k+jN ↦ (ck mod N)+jN` is one realization; the circuit's
refresh gives the *same* `cosetState` orbit-shift.

**Per-multiply deviation `ε`:** the output `cosetState(runningSum)` has runway shifted by the
growth `q ≤ numWin`, so it agrees with the ideal uniform `cosetState((a·x) mod N)` **off the
`≤ q` boundary representatives** — Born mass `≤ numWin/2^m` per side. This is **exactly
`CosetFoldWindowed.cosetState_windowedMul_embed_off`** (already proven), with `cosetWindowConst`
= the reduced lookup constants and `idealAcc = (a·x)%N`. So the abstract per-multiply coset
modular multiply is *already formalized*; only the CIRCUIT (the reduced-lookup gate) is missing.

**Confirmation that the spec is right:** `runwayMul` (residue `a·x mod N`) is the correct
residue action; `runwayMul_cosetState_shift` is the correct state action; `RunwayCosetEigenstate`
gives the exact eigenstate on the residue orbit `a^t mod N`. The runway refresh + bounded growth
is the `ε`, handled by the existing wrap-accumulation engine (`CosetWrapAccumulation`).

---

## 4. The circuit to build (actionable)

**Target gate:** a windowed multiply-in-place built from **plain `cuccaro` adds** with a
**mod-`N`-reduced** lookup table — i.e. `windowedMulInPlace` but with the per-window constants
reduced mod `N`.

**Reuse:**
- the Cuccaro adder + `cuccaro_addConstGate` value/structured-output lemmas (already built;
  `physCoset_windowed_fold` shows the per-add coset shift);
- the windowed-step framework (`WindowedCircuit`/`WindowedInPlace`, the fold + step invariant);
- **the abstract deviation is done**: `CosetFoldWindowed.cosetState_windowedMul_embed_off`
  (`≤ numWin/2^m` per side) — the circuit just needs to *realize* its `cosetWindowConst`.

**The genuinely new piece:** a windowed multiplier variant whose lookup constants are
`(a · window · 2^{w·i}) mod N` (reduced), and the value-correctness lemma
`runwayMulGate_cosetState : cosetState(k) → cosetState((a·k) mod N)` off the `numWin/2^m` wrap —
i.e. discharging `runwayMul_cosetState_shift`'s hypothesis for the concrete gate, then the
`σ`-permutation/`permState` bridge.

**Target spec (the contract to prove for the gate `G`):**
```
cosetState(k)  ─uc_eval(toUCom G)─→  cosetState((a·k) mod N)      off a wrap set of mass ≤ numWin/2^m
```
which feeds `runwayMul_cosetState_shift` → `RunwayCosetEigenstate` → (engines) → the bound. NO
fully-exact modular reduction is needed in the circuit; the runway makes it cheap.

---

## 5. Verdict

- **Tension resolved.** A cheap runway-preserving coset modular multiplier DOES exist: windowed
  plain adds with **mod-`N`-reduced lookup constants**. The repo's `cosetMulGate` fails *only*
  because its lookups are unreduced (mod `2^bits`); reducing them mod `N` fixes the runway
  scaling. The net residue action is exactly `a·x mod N` (input runway forgotten, output runway
  bounded by `numWin`), matching `runwayMul`; the deviation is the already-proven `numWin/2^m`
  boundary mass.
- **Most of the formalization is already done** (`CosetFoldWindowed` = the abstract per-multiply
  deviation; `RunwayMul`/`RunwayCosetEigenstate` = the exact shift + eigenstate; the engines +
  capstone). The remaining build is the **reduced-lookup windowed multiplier gate** + its
  `cosetState(k) → cosetState(ak mod N)` value-correctness (off `numWin/2^m`), which then
  discharges `runwayMul_cosetState_shift` for the concrete circuit.

**Honesty note.** §1–§3's arithmetic (reduced lookups ⇒ residue `a·x mod N` + bounded runway;
unreduced ⇒ scaling) is solid and matches the proven `CosetScalingAudit` / `CosetFoldWindowed`.
The "refresh vs preserve" runway detail and the exact GE2021 windowing layout are reconstructed
from coset-rep principles; the circuit build should re-confirm them against the concrete
`WindowedCircuit` register layout.

---

## 6. The reduced-lookup gate — built; what is proven and the remaining QState lift

The reduced-lookup coset gate `cosetModMulCircuitOf` is **built** (`ReducedLookupCosetGate.lean`),
as a variant of the windowed multiplier with the mod-`N`-reduced table `tableValue a N w`.
The windowed value proof was made **table-generic** to support it:

- `ReducedLookupCosetGate.lean` — `reducedWindowStepOf`/`reducedWindowedMulOf`/`cosetModMulCircuitOf`
  (+ WellTyped). `cosetModMulCircuitOf` is DEFINITIONALLY `windowedMulTOf … (tableValue a N w) …`.
- `WindowedCircuit.lean` — `windowStepTOf`/`windowedMulTOf`/`windowedMulCircuitTOf` (table free).
- `WindowedCircuitCorrect.lean` — `stepInv_stepT`/`stepInv_foldT` (advance by `Tfam j (windowⱼ y)`);
  the hard-wired `stepInv_step`/`stepInv_fold` are byte-identical DEFEQ wrappers.
- `WindowedInPlace.lean` — `stepInv_foldT_acc`/`windowedMulCircuitTOf_correct_acc` (start-
  ACCUMULATOR-agnostic, table-generic). **This is the Boolean substrate for the QState lift.**
- `ReducedLookupCosetValue.lean` — **Boolean value PROVEN**: `reducedCosetMul_decodeAcc_cuccaro`
  (`decodeAcc = (∑ₖ tableValue a N w k (windowₖ y)) mod 2^bits`); `reducedCosetMul_residue`
  (`… mod N = (a·y) mod N`, input runway forgotten); `idealAcc_eq_sum_mod`; combined
  `reducedCosetMul_decodeAcc_residue_cuccaro` under the runway-fit `fold < 2^bits`.

**The remaining piece (the QState lift, LARGE):** discharge `CosetTableSum.cosetOutOfPlace_hfwd`'s
`hfac_act` for this concrete gate — i.e. the gate's per-control-branch **QState data substate**
(`branchOf h s_act b`, `ControlledLift.lean:51`) equals `β b · actualAcc (full/m) N m 0
(cosetWindowConst a N w (xval b)) numWin` (`CosetMul.actualAcc`, the `shiftState` coset fold).
Feeding `hfac_act` + the easy `hfac_idl` (ideal `cosetState((a·x) mod N)`) into
`cosetOutOfPlace_hfwd` yields the deviation `normSqDist ≤ numWin·(2/2^m)` — the
`cosetState(k) → cosetState((a·k) mod N)` shift off the wrap.  This is the FIRST lookup-controlled
`uc_eval` coset theorem in the repo (existing coset `uc_eval` results — `uc_eval_cuccaro_physCoset`,
`physCoset_windowed_fold` — are for FIXED constants, not lookup-controlled adds, so they do not
transfer mechanically).  Precise lemma chain (substrate now ready):

1. **Per-pass QState coset action** (the core).  Lift the Boolean post-state to the column vector:
   `uc_eval(toUCom (cosetModMulCircuitOf …)) · |mulInputAccOf(acc₀=z, y=x)⟩ =
    |mulInputAccOf(acc₀=(z + ∑ₖ tableValue a N w k (windowₖ x)) mod 2^bits, y=x)⟩`, via
   (1a) `StepInv`-output = `mulInputAccOf(new acc)` (Boolean extensionality from `stepInv_foldT_acc`'s
   F/D/C/V conjuncts), (1b) `UCEvalBridge.uc_eval_basis_agree` (gate on basis = basis permutation,
   `gateToPerm` from `applyNat`) + `cosetModMulCircuitOf_cuccaro_wellTyped`.
2. **Coset superposition / shiftState** (MEDIUM).  Sum (1) over the accumulator runway `{z₀+jN}`;
   under the runway-fit (no `2^bits` wrap) this is `shiftState (∑ tableValue)`, hence by
   `actualAcc_eq_cosetState_runningSum` equals `actualAcc … (cosetWindowConst a N w x) numWin`.
3. **`branchOf` factorization** (MEDIUM — the crux design).  Relate the flat gate layout
   (`mulInputAccOf`: ctrl@0, addr@1.., accumulator@augendIdx, y@yBase, interleaved) to the
   `jointIdx h x y` control×data tensor: the `y`/multiplier register is the preserved control factor
   `Fin m_dim` (read by `copyWindow`, restored), the accumulator is the data factor `Fin (full/m)=2^bits`.
   This is the `phaseMarginal_relabel_invariant`/E_phys layout-bridge applied to the accumulator.
4. **`hfac_act` assembly** (SMALL): combine 2+3 → `hfac_act` → `cosetOutOfPlace_hfwd` → deviation.

The gate is OUT-OF-PLACE (fresh accumulator at `augendIdx`, `y` restored); no in-place SWAP is in
`cosetModMulCircuitOf`, so `actualAcc` acts on the accumulator factor and `y` is a classical control.
The runway-fit `hfit` (Boolean `fold < 2^bits`, already a hypothesis in
`reducedCosetMul_decodeAcc_residue_cuccaro`) is the shadow of the bounded runway growth.
