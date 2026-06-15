# Audit · cain-xu-2026 — RSA-2048 on a lifted-product qLDPC stack (arXiv:2603.28627)

**Headline claim:** RSA-2048 in ~10,000 physical qubits, in ~1 week (with parallelisation).

Per-paper audit folder, uniform structure (Hardware · SystemZones · L1_Algorithm · L2_Arithmetic ·
L3_PPM · L4_Code · Verifier · Codegen), all in ONE flat namespace `FormalRV.Audit.CainXu2026`.
This folder follows the framework **rigorously** — semantic correctness first, resource next —
and the [`Verifier.lean`](Verifier.lean) gate runs `#verify_clean` on every theorem marked ✅, so a
`sorry`/native axiom would **fail the build**. Nothing here is "a counted number claimed as a proof":
the ➗ rows are explicitly arithmetic-only, and the open problems are named under GAP.

## Settings a reader should check match the paper
- LP memory `lp_20^{3,7} = [[4350,1224,20]]` (k DERIVED from the parity matrices), bb18 `[[248,10,18]]`
- per-Toffoli τ_s: adder 25, ctl-adder 15, lookup 71; operation-zone ancilla `N_𝒜 = 894`; factory ≈ 2565
- hardware: physical error 1e-3, cycle 1 µs (neutral-atom baseline)

## Per-layer ledger  (✅ verify-clean semantic · ➗ arithmetic-only `decide`/`native_decide` · ⬜ GAP)

| Layer | File | Status |
|---|---|---|
| Hardware | [`Hardware.lean`](Hardware.lean) | recorded (1e-3, 1 µs) |
| System zones | [`SystemZones.lean`](SystemZones.lean) | ✅ all SysLayer invariants hold; ✅ the full ~10⁹-PPM modexp schedule is system-correct (induction) |
| L1 algorithm | [`L1_Algorithm.lean`](L1_Algorithm.lean) | ✅ shared N-parametric success bound `≥ κ/(log₂N)⁴` |
| L2 arithmetic | [`L2_Arithmetic.lean`](L2_Arithmetic.lean) | ✅ Eqs E3/E4 (exact identities); ➗ E9 (22,720 τ_s, `decide`) |
| L3 PPM | [`L3_PPM.lean`](L3_PPM.lean) | ✅ each PPM is a correct logical measurement; ✅ the whole modexp PRESERVES the code (induction, scale-free) |
| L4 code | [`L4_Code.lean`](L4_Code.lean) | ✅ structurally-verified LP-code surgery gadget; ➗ k=10/1224 DERIVED from matrices (`native_decide`) |
| Verifier | [`Verifier.lean`](Verifier.lean) | ✅ verified resource UPPER BOUND + ✅ lower-≤-upper SOUNDNESS |
| Codegen | [`Codegen.lean`](Codegen.lean) | emits the ACTUAL construction at each level via the general emitters (small reps; cain-xu's real bb18/lp20 codes noted in comments) |

## Our approach
Semantic core: a naive modexp = a sequence of logical-Z PPMs PRESERVES every stabilizer of the real
[[18,2,d]] BB code, proved by **induction** (so it holds at the full ~10⁹-PPM scale without
enumeration); a lattice-surgery gadget on the LP family implements a genuine logical measurement.
Resource: that semantic correctness makes the naive cost a genuine **upper bound**, and at lp_20's
DERIVED parameters ([[4350,1224,20]]) that bound is **7,809 qubits / ~1.3×10¹³ µs** — but those two
figures are ➗ `decide` ARITHMETIC on the 4350-qubit parameters, *not* a semantic proof on the
4350-qubit object; the induction code-preservation proof above is on the 18-qubit BB code. The
headline `qianxu_verified_upper_bound` bundles both (the 18-qubit semantic fact + the arithmetic
figures) under one `#verify_clean`. A structural **lower bound** (incompressible memory; critical-path
Toffoli depth) is proved ≤ it. The paper's ~10⁴ qubits / ~1 week sits **between** the two verified bounds.

## GAP we determined / STILL UNSOLVED
- the ~4,961-qubit gap = **factory-sharing / multi-block packing** (claimed, NOT constructed);
- the ~1000× time gap = the **parallelisation trick** (only the naive sequential schedule is proven);
- the LP **distance d** is an input (not derived from the lifted-product formula);
- the full RSA-scale GB/LP **parity matrices** are externally sourced; k at 1620/4350 columns uses the
  homological formula (out of brute-rank reach);
- **magic-state distillation** correctness/yield is assumed (supply ≥ demand is checked, distillation isn't);
- the **decoder algorithm** is unspecified (only its reaction-time budget is checked).
