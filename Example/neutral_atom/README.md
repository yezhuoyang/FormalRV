# The 2-bit Cuccaro adder at distance-3 surface-code lattice surgery — on NEUTRAL ATOMS (ZAC)

The **same 2-bit Cuccaro adder** verified in [`../Adder2EndToEnd.lean`](../Adder2EndToEnd.lean),
realized as **distance-3 surface-code lattice surgery** with the **FULL merged-code syndrome for
every merge**, and compiled onto a **neutral-atom zoned architecture** with
[**ZAC**](https://github.com/UCLA-VAST/ZAC) (Lin, Tan & Cong, HPCA 2025). Each of the adder's 5
logical qubits is a surface-code `[[13,1,3]]` patch (`surfaceHGP 3`, verified in FormalRV); each of
its 12 joint Pauli-`Z` measurements is the **complete verified merged-code syndrome circuit**
(`surface3_zz_merge`, 88 CX / `surface3_zzz_merge`, 131 CX), and each Toffoli consumes a `|C̄CZ̄⟩`
from a **factory**. The GIF shows the atoms physically moving to do it.

> Same QEC framework as superconducting — same surface code, same parity checks, same verified
> logical operations. Only the **physical realization** differs: atoms are shuttled by an AOD into
> an entangling zone for the Rydberg `CZ`s, instead of fixed couplers.

<p align="center"><img src="surface3_adder2_d3_neutral_atom.gif" width="560" alt="neutral-atom movement implementing the 2-bit adder's full d=3 surface-code lattice surgery"></p>

*Qian Xu's zones: **MEMORY** (the 5 d=3 patches = 65 data atoms, 5 patch-rows), **ANCILLA** (the
reused surgery+syndrome ancilla pool, `N_𝒜`), **FACTORY** (the 4 `|C̄CZ̄⟩` magic atoms — one per
Toffoli), **RES**ervoir. Atoms shuttle up into the **ENTANGLING** zone for the Rydberg `CZ`s; the
magenta banner shows the **FormalRV SysCall** each ZAC op realizes.*

## Pipeline

```
FormalRV verified 2-bit Cuccaro adder        cuccaro_n_bit_adder_full 2 0  (5 logical qubits)
  ├─ scripts/EmitSurgeryStim.lean ─────────►  surface3_zz_merge.stim (88 CX) , surface3_zzz_merge.stim
  │                                            (131 CX) — the verified FULL merged-code syndromes
  └─ scripts/EmitAdder2Example.lean ───────►  adder2_ppm.txt   (12 joint-Z measurements + 4 magic-T)
       └─ gen_adder2_d3_full_qasm.py ──────►  surface3_adder2_d3_full.qasm   (each PPM merge = the
                                              FULL zz/zzz syndrome remapped onto the 5 shared
                                              patches; 108 atoms, 1232 CX)
            └─ run_zac_surgery.py ─────────►  ZAC compile + atom-movement GIF
```

## Architecture — Qian Xu zone taxonomy ([`surface3_surgery_arch.json`](surface3_surgery_arch.json))

| Zone | Role | Here |
|---|---|---|
| **Memory** | logical data patches | 65 atoms = **5 × `[[13,1,3]]`** surface-code patches |
| **Operation Ancilla** (`N_𝒜`) | surgery + syndrome ancillae | **39 atoms, reused** across all 12 merges |
| **Factory** | `\|C̄CZ̄⟩` magic-state factory | **4 atoms — USED** (one per Toffoli) |
| **Reservoir** | spare | idle trap sites |
| **Entangling (processor)** | Rydberg `CZ` fires here | the full merges + magic injections |

## Compiled resource (ZAC verifier passes) — `python run_zac_surgery.py all`

| Metric | Value |
|---|---:|
| logical qubits / surface-code patches | 5 |
| physical atoms | **108** (65 data + 39 reused ancillae + 4 magic) |
| entangling `CZ` (full merged-code syndromes) | **1232** (8 × 88 + 4 × 131 + 4 magic) |
| Rydberg stages (max parallel `CZ`) | 95 (≤ 20) |
| ZAIR atom-movement instructions | **1889** |
| schedule runtime | 316 906 µs (≈ 317 ms) |
| ZAC gate-scheduling + placement verification | ✓ pass |

## Do FormalRV's system invariants hold on neutral atoms? — YES

[`NeutralAtomInvariants.lean`](NeutralAtomInvariants.lean) (`native_decide`) proves the verified
schedule satisfies every strict system invariant under neutral-atom capacities (`max_gate2q_active`
set to the platform's Rydberg parallelism, vs the superconducting single-laser `1`).

## Reproduce

```bash
lake env lean --run scripts/EmitSurgeryStim.lean              # verified zz/zzz full merge templates
lake env lean --run scripts/EmitAdder2Example.lean            # adder -> PPM
cd Example/neutral_atom
python gen_adder2_d3_full_qasm.py                             # FULL merges, 5 shared patches -> QASM
python run_zac_surgery.py all                                 # full adder surgery + resources
python run_zac_surgery.py 12                                  # GIF (first full merge)
lake env lean --run NeutralAtomInvariants.lean                # invariants on neutral atoms
```

## Honest scope

- **Full merged-code syndrome.** Each of the 12 merges is the *complete* verified merged-code
  stabilizer circuit (`surface3_zz_merge` / `surface3_zzz_merge` from
  [`Corpus/SurgeryDemoCNOT`](../../FormalRV/Corpus/SurgeryDemoCNOT.lean) +
  [`SurgeryDemoMerge`](../../FormalRV/Corpus/SurgeryDemoMerge.lean)), remapped onto the 5 shared
  `[[13,1,3]]` patches — not a simplified joint-`Z̄` readout. (A lighter
  one-ancilla-coupling-per-merge variant is in `gen_adder2_d3_qasm.py`.)
- **Ancilla reuse.** The surgery+syndrome ancillae are reused across the 12 merges (they are
  measured + reset between merges; ZAC ignores measurement and routes the unitary part, so the same
  atoms serve every merge — that reset is the implied SPAM, hence 39 ancillae, not 12 × 39).
- **ZAC routes the circuit**; the surface-code + lattice-surgery structure is in the verified input.
- **Layers/units.** FormalRV is logical (cycles); ZAC is physical (≈ 317 ms, transport-dominated).
- **FormalRV proves *what* the adder does + that the invariants hold; ZAC shows *how* a
  neutral-atom machine does it.**
