# Runway-based coset modular multiplier — modular build design

Faithful low-deviation coset multiplier built on the verified oblivious-carry-runway
adder (`ObliviousRunwayAdder/`), carrying the real `totalDeviation = 41/536870912`
into the basis-generic eigenstate engine and the coset Shor bound.

## Decision: Option (b) — new runway-windowed fold (NOT a runway `Adder` instance)

The runway adder violates the `Adder` interface in three load-bearing ways:
1. No single-register `mod 2^bits` sum — its value is `contiguousDecode` over `k`
   segments at place value `2^(m·gSep)`, not `decodeReg augendIdx bits`.
2. Runways are *deliberately un-restored* deferred carries (`IterReady`, not
   `kClean`, is preserved) — so a runway add is not an `Adder`-contract add.
3. `windowedMulOf` does one width-`bits` add per window; the runway does `k`
   width-`gSep` disjoint Cuccaro adds. A runway `Adder` would need non-linear
   `augendIdx` + an `ancClean` false after every add — unsatisfiable.

So we write a thin NEW fold, reusing `copyWindow`/`lookupReadAt` unchanged and
`runwayAddK` for the add, residue tables `T_j[v] = (c·(2^w)^j·v) mod N` (every
add `< N` ⇒ accumulator stays a bounded coset rep via `noWrap_of_padding` +
`cosetAdd_correct`), correctness from `runwayAddK_iter_contiguous_clean` (t=1).

## Ordered modules (each kernel-clean independently)

| # | module | reuse | new obligation |
|---|---|---|---|
| M1 | RunwayLayout: dims, `runwayAugendIdx`/`runwayAddendIdx`, `mulInputRunway`, `runwayWindowStep`, `runwayLookupAdd`, `runwayWindowedMul` (defs) | `copyWindow`, `lookupReadAt`, `runwayAddK`, `runwayAddK_wellTyped` | defs + WellTyped |
| M2 | NoOverflow: per-segment no-overflow from global padding | `noWrap_of_padding`, `runwayAddK_advance_genuine` | R4 glue |
| M3 | StepCorrect: one window-step adds `T_j[y_j]`, returns clean | `runwayAddK_iter_contiguous_clean` (t=1) | R1 cross-window chaining |
| M4 | MulCorrect: fold leaves `Σ_j T_j[y_j]` = coset rep of `c·y mod N` | M3, `cosetAdd_correct` | induction on numWin |
| M5 | DecodeBridge: contiguous read = linear `decodeAccOf` under no-wrap | `decodeAccOf`, `windowedCosetMul_correct` | R2 bridge |
| M6 | CarryRunwayWitness: discharge `ObliviousCarryRunway` | `ObliviousCarryRunway`, toffoli-padded | R5 count + computes_same_coset |
| M7 | Deviation: runway deviation = `totalDeviation` | `totalWrapFracD_eq_totalDeviation`, `faithful_total_deviation_le` | verbatim instantiation |
| M8 | Family: `runwayMulFamily : Nat → BaseUCom` + `runwayMulFamily_shift` | `cosetMulFamily`/`cosetMulFamily_perm`, `oddLift`, M4 | shift (mirror cosetMulFamily_perm) |
| M9 | Eigenstate: `runwayOrbitBasis`, instantiate `fourierEigenstate_eigen_lsb` | `fourierEigenstate_eigen_lsb`, `modmult_eigenstate_combined_eigen_lsb` template, `a_pow_mod_periodic_in_n` | one-liner + M8 glue |
| M10 | QPE: `qpe_var_lsb_on_eigenfamily_initial` | the engine + `|1⟩` decomposition | supply h_eig=M9, h_decomp |
| M11 | ShorBound: `CosetMarginalRelabel` (ε=totalDeviationR) → `coset_shor_succeeds_marginal` | bound + keystone `prob_partial_meas_basis_dataPerm_offBad`, M7 | σ, badY, agree, wrap weights |
| M12 (deferred) | InPlace: `runwayAccYSwap` + in-place modexp | `windowedModNMulInPlace` shape | R3 runway swap+uncompute |

Risks: R1 (cross-window clean chaining — main new proof), R2 (contiguous↔linear
decode bridge — second hardest), R3 (in-place swap, deferred, off the
single-multiply→Shor path), R4/R5 (low, arithmetic/count glue).
