# Audit · xu-2024 — constant-overhead FTQC, 24 ms cycle (arXiv:2308.08648)

**Headline:** constant-overhead fault-tolerant quantum computation on reconfigurable atom arrays;
~24 ms QEC cycle. This is the architecture the neutral-atom demo (`Example/neutral_atom/`) realizes.

**Honest status:** parameter-tuple binding + the 24,000× cycle-time **outlier** cross-check (the only
non-1µs hardware in the corpus). The constant-overhead claim itself is OPEN.

## Per-layer ledger  (✅ verify-clean · ➗ arithmetic · ⬜ GAP/recorded)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded — **24 ms cycle** (the corpus outlier), 1e-3 error |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ⬜ GAP |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared success bound |
| L2 / L3 | `L2_Arithmetic.lean` / `L3_PPM.lean` | ⬜ GAP |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ⬜ recorded LP code [[544,80,12]] |
| Verifier | [`Verifier.lean`](Verifier.lean) | ➗ 24,000× cycle-time outlier cross-check; constant-overhead claim OPEN |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level via the general emitters (small reps; the L4 line displays a real bivariate-bicycle LP-family code `[[72,12,6]]` standing in for Xu2024's `[[544,80,12]]`) |

## STILL UNSOLVED
- code-distance verification from the parity matrices; the subthreshold logical-error ansatz;
  end-to-end circuit-depth / FT integration; the neutral-atom syndrome-extraction physical model.
