# Lattice surgery on a NEUTRAL-ATOM system — distance-3 surface-code XX-merge via ZAC

The *same* verified QEC operation as the superconducting story — but compiled to **moving atoms**.
We take FormalRV's verified **distance-3 two-patch surface-code XX-merge** (`surface3_xx_merge`,
joint X̄₁X̄₂ of two `[[13,1,3]]` patches), emit its **physical syndrome circuit**, and compile it
onto a **neutral-atom zoned architecture** with [**ZAC**](https://github.com/UCLA-VAST/ZAC) (Lin,
Tan & Cong, *Reuse-aware compilation for zoned neutral-atom architectures*, HPCA 2025). The output
is an **atom-movement schedule** + a **GIF** of the atoms physically implementing the merge.

> **The QEC framework is identical to superconducting** — same surface code, same parity checks,
> same *verified* logical merge (`surface3_xx_merge_verifies` / `surface3_xx_merge_implements_logical`
> in FormalRV). What changes is only the **physical realization**: instead of fixed couplers, the
> atoms are **picked up by an AOD and moved into an entanglement zone** for a Rydberg `CZ`, then
> moved back. That movement is exactly what the GIF shows.

<p align="center"><img src="surface3_xx_merge_neutral_atom.gif" width="520" alt="neutral-atom movement implementing one syndrome-check step of the d=3 surface-code XX-merge"></p>

*(One syndrome-check merge step: an ancilla atom is transported from the storage zone into the
entanglement zone, does Rydberg `CZ` with its data neighbours, and returns. The full merge is 13
such Rydberg stages — too long to GIF, so this shows the elementary move.)*

## Pipeline

```
FormalRV verified gadget        surface3_xx_merge  (joint X̄₁X̄₂, two [[13,1,3]] patches)
  └─ scripts/EmitSurgeryStim.lean ─►  surface3_xx_merge.stim   (physical syndrome circuit:
                                       14 X-checks RX/CX/MX + 12 Z-checks R/CX/M, 53 qubits, 88 CX)
       └─ stim_to_qasm.py ─────────►  surface3_xx_merge.qasm   (unitary entangling skeleton; Qiskit
                                       transpiles to 88 CZ + 204 U3 — exactly ZAC's gate set)
            └─ run_zac_surgery.py ──►  ZAC compile on surface3_surgery_arch.json
                                       ─►  ZAIR atom-movement schedule (+ GIF)
```

## The architecture (exact) — [`surface3_surgery_arch.json`](surface3_surgery_arch.json)

Sized precisely for the 53 atoms of this merge (`26` data + `1` surgery ancilla + `26` syndrome
ancillas). Distances in µm, durations in µs:

| Component | Setting |
|---|---|
| **Storage / memory zone** | one SLM, `6 × 10 = 60` sites, `3 µm` pitch → `30 × 18 µm` (holds all 53 atoms) |
| **Entanglement zone** | two interleaved SLMs, `6 × 10`, `12 × 10 µm` pitch, at `y = 28 µm`; Rydberg `CZ` happens here |
| **Mover** | 1 AOD array (`6 × 10`, `2 µm` pitch) |
| **Durations** | Rydberg `CZ` `0.36 µs`, 1-qubit `0.5 µs`, atom transfer `15 µs` |
| **Fidelities** | 2-qubit `0.995`, 1-qubit `0.9997`, transfer `0.999`; `T = 1.5 s` |

## Compiled resource (full merge, ZAC verifier passes)

`python run_zac_surgery.py all`:

| Metric | Value |
|---|---:|
| atoms | 53 |
| entangling `CZ` gates | 88 |
| Rydberg (parallel-CZ) stages | 13 |
| ZAIR atom-movement instructions | 178 |
| schedule runtime | 22 372 µs (≈ 22.4 ms) |
| ZAC gate-scheduling + placement verification | ✓ pass |

## Reproduce

```bash
# 1. emit the verified merge's physical circuit (from FormalRV)
lake env lean --run scripts/EmitSurgeryStim.lean        # -> Example/neutral_atom/surface3_xx_merge.stim
# 2. convert to ZAC's unitary QASM
cd Example/neutral_atom && python stim_to_qasm.py surface3_xx_merge.stim surface3_xx_merge.qasm
# 3a. compile the FULL merge + print the resource table (needs ZAC at ../../../VerifyShor/ZAC + qiskit)
python run_zac_surgery.py all
# 3b. render the movement GIF for the first N CZ (default 4 = one syndrome-check step)
python run_zac_surgery.py 4
```

## Honest scope

- **ZAC is a circuit → atom-movement router, not a QEC encoder.** The surface-code + lattice-surgery
  structure lives in the *input circuit we emit from the FormalRV-verified gadget*; ZAC realizes
  those physical gates as atom moves + Rydberg `CZ`s and verifies the movement schedule (no atom
  collisions, valid placement) — it does not re-derive the code.
- The QASM is the merge's **unitary entangling skeleton** (the 88 `CZ`). The prep/measure SPAM
  (`RX`/`MX`/`R`/`M`) is done in place / a readout zone and is dropped for the unitary route — it
  doesn't change the atom-movement pattern.
- The GIF renders one syndrome-check step (4 `CZ`) for size; the *full* merge (13 Rydberg stages,
  178 instructions) is compiled + verified by `run_zac_surgery.py all`.
- The **logical correctness** of the merge (that it measures X̄₁X̄₂) is the FormalRV theorem, not
  ZAC's concern. ZAC + FormalRV are complementary: FormalRV proves *what* the surgery does; ZAC
  shows *how* a neutral-atom machine physically does it.
