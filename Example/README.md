# Worked example — the 2-bit Cuccaro adder, end to end

Full detail at **every layer** for the smallest non-trivial circuit, so you can inspect each
step and **verify it yourself** — and re-run the resource verification on **your own hardware**.

> **The source of truth is [`Adder2EndToEnd.lean`](Adder2EndToEnd.lean)** in this folder.
> ```bash
> lake env lean --run Example/Adder2EndToEnd.lean
> ```
> Running it **type-checks every theorem** below (including `schedule_fits` — a machine-checked
> proof that the surgery schedule fits the architecture) and prints the resource table. **Edit the
> `EDIT HERE` block (zones, decoder width, parallelism, reaction latency), re-run, and you get a new
> machine-checked verdict + new verified bounds.** If your hardware can't host the schedule, the
> proof is *rejected* — that's the verification.

Everything below is the **actual emitted output** of the real compilers — not hand-typed.

---

## L1 / L2 — the verified logical circuit

`cuccaro_n_bit_adder_full 2 0`, proven by **`cuccaro_n_bit_adder_full_correct`** (target register
`:= a + b mod 4`, read register restored, carry preserved) — a *theorem*, not a test. 5 qubits.

## L2 → OpenQASM ([`adder2.qasm`](adder2.qasm)) — Qiskit re-verifies the counts

`Core/GateQASM.toQASM` emits the full circuit; `5` qubits, `8·cx + 4·ccx`, `tcount 28`.
`python PyCircuits/verified_circuit_qasm_count.py` reloads it in Qiskit and confirms the gate
counts equal the Lean-proved numbers.

```qasm
OPENQASM 2.0; include "qelib1.inc"; qreg q[5];
cx q[2],q[1]; cx q[2],q[0]; ccx q[0],q[1],q[2];      // MAJ bit 0
cx q[4],q[3]; cx q[4],q[2]; ccx q[2],q[3],q[4];      // MAJ bit 1
ccx q[2],q[3],q[4]; cx q[4],q[2]; cx q[2],q[3];      // UMA bit 1
ccx q[0],q[1],q[2]; cx q[2],q[0]; cx q[0],q[1];      // UMA bit 0
```

## L3 → PPM ([`adder2_ppm.txt`](adder2_ppm.txt)) — the real `compileArithmeticGateToPPM`

28 commands. Each `cx` → joint `ZZ` measurement + Pauli-frame update; each `ccx` → inject a
`|C̄CZ̄⟩` magic state + joint `ZZZ` measurement + frame update:

```
M Z 2,1 · F 1            M Z 2,0 · F 0            T 2 · M Z 0,1,2 · F 2     # MAJ bit 0
M Z 4,3 · F 3            M Z 4,2 · F 2            T 4 · M Z 2,3,4 · F 4     # MAJ bit 1
T 4 · M Z 2,3,4 · F 4    M Z 4,2 · F 2            M Z 2,3 · F 3            # UMA bit 1
T 2 · M Z 0,1,2 · F 2    M Z 2,0 · F 0            M Z 0,1 · F 1            # UMA bit 0
```

→ **4 `|C̄CZ̄⟩` magic states** (one per Toffoli) and **12 joint logical measurements**
(`numCX + numCCX = 8 + 4`).

## System — the hardware architecture (zoned), editable

| Zone | Sites | Role |
|---|---|---|
| **Data** | `[0, 100)` — 100 patches | computation / register qubits |
| **Ancilla** | `[100, 200)` — 100 patches | surgery routing ancillae |
| **Factory** | `[200, 300)` — 100 patches | magic-state (`\|C̄CZ̄⟩`) factories |
| **Routing** | `[300, 400)` — 100 patches | bus / transit |

Operation-capacity model (`adder_demo_opCap`): **Gate2q ‖ = 1** (single-laser hardware),
measure / decode / feedback ‖ = 4 each, gate1q ‖ = 4, magic-req / fresh-ancilla / transit ‖ = 100.
Timing: `t_react = 10 µs`, window `= 1000 µs`. **All of these are the `EDIT HERE` knobs.**

## System — the full schedule ([`adder2_full_schedule.txt`](adder2_full_schedule.txt), 192 SysCalls)

The 12 PPM measurements lower to 12 surgery merge blocks (3 syndrome rounds each), scheduled onto
the zones with explicit `begin..end` µs. Excerpt (one merge block):

```
FRESHANC 1 0 1        # allocate a fresh ancilla patch in zone 1 (Ancilla)
GATE2Q 0 100 1 2      # merge data-site 0 with ancilla-site 100   (one syndrome round)
GATE2Q 50 100 2 3     # merge data-site 50 with ancilla-site 100
MEAS 100 3 4          # measure the ancilla (the joint-parity readout)
DECODE 0 4 5          # decode the syndrome
... (× 12 blocks, then PauliFrameUpdate)
```

This schedule is **proven** to satisfy *every* strict system invariant on the architecture above —
operation-capacity, feedback-after-decode, slot-capacity, ancilla-freshness — by
**`schedule_fits`** (`= all_invariants_strict_with_slot_capacity_and_freshness_ok … = true`,
`native_decide`).

## L4 → lattice surgery ([certificate](adder2_ls_certificate.txt))

`python PyCircuits/ls_compile.py PyCircuits/qasm/adder2.qasm` auto-compiles the circuit to a
conflict-free surface-code space-time layout with a **certificate** (the trusted artifact) and a
ray-traced render:

<p align="center"><img src="../docs/diagrams/ls_adder2_blender.png" width="460" alt="2-bit adder, surface-code lattice surgery, ray-traced"></p>

```
qubits 5 · depth 11 · two_qubit_merges 8 · magic_injections 4 · conflict_free True · spacetime_volume 60
```

## Final verified resource — on the default architecture

| Layer | Resource | Value | Verified by |
|---|---|---:|---|
| L2 logical | qubits / Toffolis / CX / T-count | 5 / 4 / 8 / 28 | `cuccaro_n_bit_adder_full_correct` + `Core/GateQASM` (Qiskit) |
| L3 PPM | `\|C̄CZ̄⟩` magic states | 4 | `compileArithmeticGateToPPM` |
| L3 PPM | joint logical measurements | 12 | `compileArithmeticGateToPPM` |
| System | SysCalls / merges / **wall-clock** | 192 / 72 / **192 µs** | `scheduleWallclockUs` (foldl over the schedule) |
| System | **schedule fits architecture** | ✓ | **`schedule_fits`** (all strict invariants) |
| System | **wall-clock lower bound** | **≥ 72 µs** | `gate2q_capacity_lower_bound_us` (⌈72 Gate2q / 1‖⌉ · 1 µs) |
| L4 surgery | conflict-free layout, volume | ✓ / 60 | `ls_compile` certificate |

## Re-run on YOUR hardware

Open [`Adder2EndToEnd.lean`](Adder2EndToEnd.lean), change the `EDIT HERE` block — e.g. a wider
decoder bank (`maxMeasParallel`), more Gate2q parallelism (`maxGate2qParallel`), a different
reaction latency (`tReactUs`), or resized zones (`myArch`) — and re-run
`lake env lean --run Example/Adder2EndToEnd.lean`. You get a fresh machine-checked verdict
(`schedule_fits` passes ⇒ feasible; rejected ⇒ infeasible) and a fresh verified wall-clock lower
bound. Nothing here is trusted on our word — the proofs are re-checked every run.
