# Counting consistency/cheating audit — 2026-06-03

Adversarial audit (4 parallel auditors + synthesis) of every gate-counting theorem in
`FormalRV/`, triggered by the user's demand: "no inconsistency/cheating in any counting."

## Verdict: one real headline problem (now fixed) + a hygiene item (now fixed)

### Problem 1 (CENTRAL) — headline number was on the wrong term. FIXED.

The RSA-2048 headline `137,438,953,472` (`16·n³`) was counted on `shorModExp`, a chain of
**out-of-place** `sqir_modmult_const_gate`s. That term is:
- **not** the verified Shor oracle (which is the **in-place** `sqir_modmult_MCP_gate`, via
  `f_modmult_circuit_verified_bits`), and
- **not even a valid mod-exp circuit** — out-of-place multipliers write into a fresh
  accumulator with no feedback, so a chain of them cannot exponentiate.

The repo's own verified-oracle chain (`shorModExpVerified`, in-place MCP) gives
`274,877,906,944` (`32·n³`) = exactly 2× (the in-place forward+uncompute factor). So the
advertised figure **understated the verified-oracle arithmetic cost by 2×** and was attached
to a semantically-invalid term.

**Fix:**
- Renamed `shor2048_CCZMagic_exact` → `shor2048_CCZMagic_outOfPlaceModel`; docstring now says
  it is a counting model, not the verified circuit, and points to the verified number.
- `shor2048_CCZMagic_verified = 274,877,906,944` is now the labeled headline.
- Both chains relabeled **count-only / SCAFFOLDED**: neither has a proof it computes
  `a^x mod N` (the verified mod-exp semantics lives in
  `Shor_correct_verified_no_modmult_axioms` via `controlled_powers`, a BaseUCom term with no
  bridge to these Gate chains). The `2·bits` exponent multiplicity is flagged structural.

### Problem 2 (hygiene) — `native_decide` (compiler-trust). FIXED 16→1.

16 `native_decide` (adds `Lean.ofReduceBool`) in toy-architecture files (not headline
resource counts): 11 in `GE2021PPMSysInv.lean` (zone/site/syscall/qubit counts of a tiny
toy block), 2 tactic uses in `CircuitToPPMInterface/Part5.lean` (toy trace-match), 3 in
comments. Switched 15 to kernel `decide`; 1 (the heaviest toy trace-match,
`toySurgeryComposedSchedule_trace_matches`) genuinely fails `decide` and is kept with a
disclosing comment.

## What the audit certified CLEAN (no change needed)

- Gate-level counters `tcount/gcount/depth`; bridge `tcount = 7·toffCount`,
  `gcount = numX+numCX+numCCX` (induction, kernel-clean), consistent with the `BaseUCom.CCX`
  7-T Toffoli decomposition.
- The `CCX → [H,CCZ,H]` PPM mapping giving `numCCZMagic = toffCount`, `numMeas = 3·toffCount`.
- The Gidney **adder** end-to-end (`verified_adder_end_to_end`): semantics + cost on ONE term.
- The single **modmult** end-to-end (`verified_MCP_oracle_end_to_end`): MultiplyCircuitProperty
  + exactly `16·bits²` magic states on the verified oracle term.
- Per-step exact counts `56·bits²` (const) / `112·bits²` (MCP) under valid-Shor-base
  hypotheses, with the number-theory non-vanishing lemma proved.
- All literals reconcile arithmetically (56/7=8, 112/7=16, `16·2048³=137438953472`,
  `32·2048³=274877906944`, `4096·33554432=137438953472`, 3× measurements).

## QASM justification (separate, same day)

`scripts/EmitQASM.lean` emits the actual verified circuits to `PyCircuits/qasm/`;
`PyCircuits/verified_circuit_qasm_count.py` confirms in Qiskit (6/6) that the emitted
circuits' gate counts equal the Lean numbers (const 8·bits²/56·bits², MCP 16·bits²/112·bits²,
MCP = 2× const), with `tcount = 7·numCCX` proved in `Core/GateQASM.lean`.

## Controlled-overhead count — NOW CLOSED (was previously flagged "ill-posed")

`FormalRV/Shor/ControlledModExpCount.lean` (axiom-clean) actually counts
`controlled_powers (verified oracle)` — the exact verified Shor mod-exp INCLUDING control.
The earlier "ill-posed" was only about collapsing the result to a single *magic-state* number
(the generic `control` emits `π/8` rotations, so that collapse needs per-rotation synthesis);
the GATE COUNT is angle-independent and proved:

- **Generic control overhead** (any circuit `c`):
  `ucApp2 (control q c) = 2·ucApp1 c + 6·ucApp2 c` (CNOTs),
  `ucApp1 (control q c) = 4·ucApp1 c + 9·ucApp2 c + ucApp3 c` (rotations).
- **`Gate → BaseUCom` counts**: `ucApp2 (toUCom g) = numCX g + 6·numCCX g`,
  `ucApp1 (toUCom g) = numI g + numX g + 9·numCCX g`.
- **Per controlled oracle** (`ucApp2/1_control_toUCom`): fully determined by
  `(gNumI, numX, numCX, numCCX)`.  At bits=2 (N=15,a=7,ainv=13): EXACTLY **4710 CNOTs +
  7764 rotations** per controlled oracle (`#eval`).
- **Whole algorithm**: `controlled_powers = npar (control i (f i))`, so the total is the sum
  over the `m` exponent steps (`ucApp2_npar` / `ucApp1_npar`; the `+1` in `ucApp1_npar` is the
  base `SKIP` identity rotation).
- **QASM justification** (`controlled_overhead_qasm_check.py`, 3/3): the decomposed-Toffoli
  CNOT count of the emitted oracle = `numCX + 6·numCCX` (MCP: 552 = 168 + 6·64), confirming the
  formula's input against the real circuit.

## Honest residue (flagged, not faked)

- No full mod-exp **semantic** correctness for the Gate counting chains (count-only). The
  verified *algorithm* semantics IS proved (`Shor_correct_verified_no_modmult_axioms`,
  axiom-clean) on the BaseUCom `controlled_powers` term; the bridge to the Gate counting chains
  is not built.
- The controlled mod-exp's count is given as (CNOTs, rotations) — both exact.  Collapsing the
  rotations to a single *magic-state* number still needs per-rotation Clifford+T synthesis
  (the rotations are mixed `π/4`, `π/8`, … angles); that synthesis layer is the one remaining
  honest residual, and its size is now exactly bounded by the proved rotation count.
