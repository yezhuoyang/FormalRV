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
