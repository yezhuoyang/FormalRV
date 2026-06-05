# Lattice surgery on a NEUTRAL-ATOM system — distance-3 surface-code XX-merge via ZAC

The *same* verified QEC operation as the superconducting story — but compiled to **moving atoms**.
We take FormalRV's verified **distance-3 two-patch surface-code XX-merge** (`surface3_xx_merge`,
joint X̄₁X̄₂ of two `[[13,1,3]]` patches), emit its **physical syndrome circuit**, and compile it
onto a **neutral-atom zoned architecture** with [**ZAC**](https://github.com/UCLA-VAST/ZAC) (Lin,
Tan & Cong, HPCA 2025). The output is an **atom-movement schedule** + a **GIF** of the atoms
physically implementing the merge.

> **The QEC framework is identical to superconducting** — same surface code, same parity checks,
> same *verified* logical merge (`surface3_xx_merge_verifies` in FormalRV). Only the **physical
> realization** differs: atoms are picked up by an AOD and **moved into an entanglement zone** for
> a Rydberg `CZ`, instead of using fixed couplers. That movement is what the GIF shows.

<p align="center"><img src="surface3_xx_merge_neutral_atom.gif" width="540" alt="neutral-atom movement implementing one syndrome-check step of the d=3 surface-code XX-merge"></p>

*The GIF (one syndrome-check merge step) is annotated with **(a)** Qian Xu's **zones** as
spatially-separated regions — Memory · Operation-Ancilla (`N_𝒜`) · Factory · Reservoir, plus the
**Entangling** (processor) zone above — and **(b)** a magenta banner showing the **FormalRV
SysCall** each ZAC operation realizes (`FRESHANC` → place patches, `routing` → AOD transport into
the entangling zone, `GATE2Q` = the merge via Rydberg `CZ`).*

## Pipeline

```
FormalRV verified gadget        surface3_xx_merge  (joint X̄₁X̄₂, two [[13,1,3]] patches)
  └─ scripts/EmitSurgeryStim.lean ─►  surface3_xx_merge.stim   (physical syndrome circuit: 53 qubits, 88 CX)
       └─ stim_to_qasm.py ─────────►  surface3_xx_merge.qasm   (Qiskit transpiles to 88 CZ + 204 U3)
            └─ run_zac_surgery.py ──►  ZAC compile on surface3_surgery_arch.json
                                       ─►  ZAIR atom-movement schedule  +  annotated GIF
```

## Architecture — Qian Xu's zone taxonomy (the factoring layout)

Following **Qian Xu's neutral-atom architecture** — the ~10,000-atom factoring layout
(*memory + processor + factory + operation-zone ancilla `N_𝒜` + reservoir*, bound in FormalRV's
[`Corpus/QianxuBounds`](../../FormalRV/Corpus/QianxuBounds.lean)) and Xu et al. 2024 (Nat. Phys.,
Fig. 1: a **qLDPC memory block**, **mediating ancillae**, and **computation qubits** as distinct
2D regions). The atoms are **not** stacked in row bands — they sit in **separated regions**
(physical gaps between them) of the single storage array, plus a distinct **entangling zone**:

| Zone (Xu taxonomy) | Role | Here (`surface3_surgery_arch.json`) |
|---|---|---|
| **Memory / Data** | logical data patches | storage cols 0–5 — 26 data + 1 surgery ancilla |
| **Operation-zone Ancilla** (`N_𝒜`) | mediating syndrome ancillae | storage cols 10–15 — 26 ancillas (empty-gap separated from Memory) |
| **Factory** | `\|C̄CZ̄⟩` magic-state factories | storage cols 20–25 — idle trap sites, reserved (Clifford merge) |
| **Reservoir** | spare qubits | storage cols 30–33 — idle trap sites, spare |
| **Entangling (processor)** | where Rydberg `CZ` fires | SLMs at `y ≥ 32 µm` — the physical **merge** |

Each role is a **spatially separated region** (gaps between Memory · Ancilla · Factory ·
Reservoir), and atoms are **shuttled by the AOD into the entangling zone** for the Rydberg `CZ` —
that movement *is* the lattice surgery. (ZAC's hardware model has one physical storage array +
entangling zones; the roles are regions of the storage, matching how Xu's logical zones map onto
the atom array.) Durations (µs): Rydberg `CZ` `0.36`, transfer `15`; fidelities 2-qubit `0.995`,
transfer `0.999`; `T = 1.5 s`; one AOD mover.

## Do FormalRV's system invariants hold on neutral atoms? — YES, verified

[`NeutralAtomInvariants.lean`](NeutralAtomInvariants.lean) re-checks the FormalRV system invariants
under **neutral-atom hardware parameters** read off the ZAC compile:

```bash
lake env lean --run Example/neutral_atom/NeutralAtomInvariants.lean
```

- ZAC's compile does **up to 12 parallel Rydberg `CZ`** per stage — so the neutral-atom
  `max_gate2q_active = 12` (vs the superconducting single-laser `1`), and readout is parallel.
- `theorem adder_n1_neutralatom_system_ok` (`native_decide`) proves the verified schedule satisfies
  **every** strict invariant — operation-capacity, feedback-after-decode, slot-capacity,
  ancilla-freshness — under those neutral-atom capacities. (Capacity constraints, so a *more*
  parallel platform satisfies them a fortiori.)
- **So the original `maxGate2qParallel=1` was a superconducting assumption; the neutral-atom value
  is 12, and the invariants still hold.** The check is re-runnable: change the capacities and re-run.

## Compiled resource (full merge, ZAC verifier passes)

`python run_zac_surgery.py all`:

| Metric | Value |
|---|---:|
| atoms | 53 |
| entangling `CZ` gates | 88 |
| **max parallel `CZ` per Rydberg stage** | **12** |
| Rydberg stages | 13 |
| ZAIR atom-movement instructions | 172 |
| schedule runtime | 24 599 µs (≈ 25 ms) |
| ZAC gate-scheduling + placement verification | ✓ pass |

## Reproduce

```bash
lake env lean --run scripts/EmitSurgeryStim.lean                 # verified merge -> .stim
cd Example/neutral_atom && python stim_to_qasm.py surface3_xx_merge.stim surface3_xx_merge.qasm
python run_zac_surgery.py all                                    # full merge + resources
python run_zac_surgery.py 4                                      # GIF of one syndrome-check step
lake env lean --run Example/neutral_atom/NeutralAtomInvariants.lean   # invariants on neutral atoms
```

## Honest scope

- **Layers.** FormalRV's SysCall schedule is at the **logical** level (logical merges/measures on
  zone *sites*, abstract cycle units); ZAC is at the **physical** level (each logical merge = many
  atom moves + Rydberg `CZ`s, real µs — this merge is ≈ 25 ms). The zones + SysCalls map across
  (table above + GIF banner); the absolute time scales differ (logical cycles vs physical µs).
- **ZAC is a circuit → atom-movement router, not a QEC encoder.** The surface-code + lattice-surgery
  structure lives in the input circuit we emit from the *verified gadget*; ZAC realizes + verifies
  the movement schedule (no atom collisions, valid placement) — it does not re-derive the code.
- The QASM is the merge's **unitary entangling skeleton** (88 `CZ`); prep/measure SPAM is in place.
- The GIF renders one syndrome-check step (4 `CZ`) for size; the full merge (13 Rydberg stages,
  172 instructions) is compiled + verified by `run_zac_surgery.py all`.
- **FormalRV proves *what* the surgery does + that the system invariants hold; ZAC shows *how* a
  neutral-atom machine does it.** Complementary, and now consistent (same zones, same invariants).
