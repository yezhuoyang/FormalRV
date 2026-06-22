# Verified Lattice-Surgery Compiler for Fault-Tolerant Shor

A complete, machine-checked compile-and-compose pipeline that turns a routed
Pauli-based measurement program (the lowered Shor arithmetic) into ONE verified
surface-code lattice-surgery spacetime diagram, on the Gidney–Ekerå 20-million-qubit
machine.

Every theorem below is **axiom-clean** — `propext` + `Quot.sound` for the general
(structural) theorems, plus small per-instance `native_decide` reflection axioms for
the concrete gadgets. No `sorry`, no hand-declared axioms. The full `FormalRV.QEC`
umbrella builds green.

> **One-line summary.** Prove each gadget once → a general weld theorem composes any
> two → a chain corollary composes a list → a frame tracker derives the surfaces →
> a dispatch selects gadgets → the whole circuit is verified, semantically, at
> per-distinct-gadget cost.

---

## The pipeline

```
routed PPM program (List PlacedGadget, in program order)
   │
   ▼  SCHEDULE        ASAP greedy, disjoint-qubit time layers (parallelism)
   │                  Threader.lean        — scheduleLayers
   ▼  ROUTE           weight-k Z̄ at any distance → long-range merge;
   │                  mixed/Y → Clifford-promoted gadget
   │                  Routing.lean, Dispatch.lean — lrMergeMulti, dispatchLaS
   ▼  FRAME-TRACK     global flow frame = component joint-Z + per-qubit X;
   │                  per-layer surfCombine maps (handles EVOLVING frames)
   │                  FrameTracker.lean, Compiler.lean — frameFlows, layerMap
   ▼  EMIT            layer LaSre + surface + ports, at global columns
   │                  Compiler.lean — emitLaS', emitSurf'
   ▼  PAD             unify footprint (height/J) for mixed+pure programs
   │                  Routing.lean, CliffordFrame.lean — lrMergeMultiH
   ▼  WELD + CERTIFY  chainOK (per-gadget+interface) → weldChain_LaSCorrectFull
   │                  ChainComposition.lean — the BRIDGE
   ▼
one verified LaSCorrectFull diagram realizing the program's measurement sequence
```

---

## The proof spine (bottom-up)

### 1. The general weld-composition theorem — `WeldComposition.lean`
The keystone. `funcCubeOK`/`validCube` at a cube read only that cube + its lower
neighbours, so a weld agrees with `A` below the seam and (shifted) `B` above; only the
two interface layers are new.

| theorem | statement |
|---|---|
| `funcCubeOK_lower` / `_upper` | per-cube congruence with `A` / shifted `B` |
| `weldK_funcOK` | `A.funcOK ∧ B.funcOK ∧ weldInterfaceOK → (weldK A B).funcOK` |
| `weldK_valid` | same for structural validity |
| **`weldK_LaSCorrectFull`** | + ports ⇒ the welded diagram is `LaSCorrectFull` |

Proven by structural reasoning — **no `native_decide` on the whole grid.** This is what
makes composition scale.

### 2. The chain induction corollary — `ChainComposition.lean`
Lifts the single-step weld to a whole list by induction.

| theorem | statement |
|---|---|
| `chainOK` | recursive checker: each gadget's `valid`+`funcOK` + each weld's interface |
| `chainOK_sound` | `chainOK → (weldChain …)` is `valid`+`funcOK` |
| **`weldChain_LaSCorrectFull`** | + ports ⇒ the whole chain is `LaSCorrectFull` — **THE BRIDGE** |
| `shorBlock_correct` | a real `M_{Z₁Z₂};idle;M_{Z₁Z₂}` block, certified |

### 3. The weld algebra — `Weld.lean`, `FaithfulMixedMerge.lean`, `ConjugationWeld.lean`
`weldK` (sequential), `weldI` (parallel), `surfCombine`/`weldSurfP` (flow products),
`rotSurf` (H-rotation re-index); `weld2`/`weld3` package them. Verified primitives:
`memWeld_fully_correct`, `parIdle_fully_correct`, `hhWeld_is_identity`,
`faithfulMixedMerge_fully_correct` (the mixed merge `H₁·Zmerge·H₁` = `M_{X₁Z₂}`),
`yReadWeld_correct` (the `S`-conjugated `M_Y`).

---

## The gadget catalog (each proven once)

| gadget | file | measures | proof |
|---|---|---|---|
| `lrMergeMulti cols` | `Routing.lean` | joint `Z̄` over `cols`, any weight/distance | `lrMM_w2/w3/w4` |
| `lrMergeMultiH cols h` | `Routing.lean` | same, height-padded (for mixed footprint) | `lrMMH_h9` |
| `mixLaS` | `FaithfulMixedMerge.lean` | `X̄₁Z̄₂` (Clifford-promoted) | `faithfulMixedMerge_fully_correct` |
| `yReadLaS` | `ConjugationWeld.lean` | `Ȳ` (`S`-conjugated) | `yReadWeld_correct` |
| H, S, CNOT, CZ, CCZ | `*FromLaSsynth.lean` | the Clifford/`T` gates | `*_fully_correct` |

A single `lrMergeMulti` subsumes every pure-`Z` merge — `lrMergeMultiH cols 1` *is* the
adjacent `mergeZLaS`; `d>1` routes through free channel columns.

---

## The compiler (`LogicalLayout/`)

- **`Threader.lean`** — `scheduleLayers` (ASAP parallel: adder 180 gadgets → 55 layers,
  every layer disjoint), `factoryColumns` (GE2021 T-factory reservation, kept
  physical-only), `buildLayerLaS` (`allLayersWellFormed adderPPM`).
- **`FrameTracker.lean`** — the stabilizer-frame tracker. Through Z-merges `X̄_q` passes
  straight but a lone `Z̄_q` can't, so the global Z-frame is **one joint-Z per
  merge-graph component**. `evo_correct`: the evolving-frame `Z̄₀Z̄₁;Z̄₁Z̄₂` is certified.
- **`Compiler.lean`** — the integrated pipeline. `block_correct` (long-range +
  frame-evolution + parallel-idle), `wblock_correct` (mixed weights via `lrMergeMulti`).
- **`CliffordFrame.lean`** — `mixChain_correct` (mixed merges compose), `fullChain_correct`
  (a **mixed + pure** block, unified footprint, end to end).
- **`Dispatch.lean`** — `routeClass` (classify a measurement) + `dispatchLaS` →
  `dispatch_*_verified` (every branch lands on a verified gadget, by construction).

---

## The scalable proof architecture — `Bridge.lean`

A circuit's proof is **not** one giant `native_decide`. It factors:

1. **Per-distinct-gadget certificates**, proven once — `cert_zm_func`, `cert_zm_valid`.
2. **Factored `chainOK`** — `zmProg_chainOK` discharges *both* occurrences' interior
   via the *one* certificate (`simp [chainOK]` then `simp [certs]`); only the two
   interface layers go to `native_decide`.
3. **The general bridge** — `weldChain_LaSCorrectFull` (proven once) lifts to the whole.

`zmProg_correct`'s axiom footprint *contains* the certificates plus a *smaller*
interface check — the factoring is verified, not asserted. **Cost = O(distinct gadgets)
+ O(interfaces), not O(total gadgets)** — and each interface is now O(1) in the chain
length (`weldInterfaceOK2`/`weldInterfaceValidOK2` iterate only the two layers
`{kA-1, kA}` over the known constant width, never the chain-growing grid), so the whole
factored proof is **genuinely O(N)**.

### Semantic correctness rides along
The chain's spec `paulis` IS the program's measurement sequence (flow 0 of each gadget
= the demanded Pauli, pinned to the surface by `portsOK`). So `LaSCorrectFull` *against
that spec* states the lattice surgery **measures exactly the program's measurements**
(`zmProg_measures_Z0Z1`; the basis is physically anchored by `ColorEnforcing.lean`, the
qubit/order faithfulness by `ComposedSemantic.lean`). Structural + semantic, one bridge.

---

## Honest scope

**Done & verified** — every fundamental compile-and-compose challenge: general weld
composition, chain induction, parallel scheduling, T-factory reservation, evolving
stabilizer-frame tracking, long-range routing (any pure-Z weight/distance),
Clifford-frame (mixed/Y), footprint padding (mixed+pure unified), auto-dispatch, and a
scalable factored *semantic* proof.

Asymptotic linearity is now **closed**: the `gridCubes`-filtering `weldInterfaceOK`
(O(N²)) is replaced by the 2-layer-only, width-parameterized `weldInterfaceOK2`
(O(N) — soundness via `weldInterfaceOK_of_2`, `chainOK_sound` updated). `mixLaS` is
generalized to arbitrary mixed-merge positions (`mixGenLaS`), and the full lowered
adder/modexp corpus runs through the dispatch with honest resource counts
(`CompileReport.lean`).

**Remaining — scale & tightening, not theory:** the verified corpus is small (2-bit
adder, `shorModExp 1 3 2`) — RSA-2048-scale runs are future work; and spacetime counts
use a uniform `h=9`/`wj=2` footprint (a per-layer-height compiler would be tighter). Each
reduces to *reusing* the verified pieces above — which is exactly the point of the bridge
architecture.
