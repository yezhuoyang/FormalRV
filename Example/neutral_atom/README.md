# The 2-bit Cuccaro adder at distance-3 surface-code lattice surgery — on NEUTRAL ATOMS (ZAC)

The **same 2-bit Cuccaro adder** verified in [`../Adder2EndToEnd.lean`](../Adder2EndToEnd.lean),
now realized as **distance-3 surface-code lattice surgery** and compiled onto a **neutral-atom
zoned architecture** with [**ZAC**](https://github.com/UCLA-VAST/ZAC) (Lin, Tan & Cong, HPCA 2025).
Each of the adder's 5 logical qubits becomes a surface-code `[[13,1,3]]` patch (`surfaceHGP 3`,
verified in FormalRV); its lattice surgery is the adder's PPM program — each joint Pauli-`Z`
measurement is a **merge**, each Toffoli consumes a `|C̄CZ̄⟩` from a **factory**. The GIF shows the
atoms physically moving to do it.

> Same QEC framework as superconducting — same surface code, same parity checks, same verified
> logical operations. Only the **physical realization** differs: atoms are shuttled by an AOD into
> an entangling zone for the Rydberg `CZ`s, instead of fixed couplers.

<p align="center"><img src="surface3_adder2_d3_neutral_atom.gif" width="560" alt="neutral-atom movement implementing the 2-bit adder's d=3 surface-code lattice surgery"></p>

*The atoms sit in Qian Xu's zones — **MEMORY** (the 5 d=3 patches = 65 data atoms, shown as 5
patch-rows), **ANCILLA** (the 12 merge ancillae, `N_𝒜`), **FACTORY** (the 4 `|C̄CZ̄⟩` magic atoms — one
per Toffoli, *used* here), **RES**ervoir — and are shuttled up into the **ENTANGLING** zone for the
Rydberg `CZ`s. The magenta banner shows the **FormalRV SysCall** each ZAC op realizes.*

## Pipeline

```
FormalRV verified 2-bit Cuccaro adder        cuccaro_n_bit_adder_full 2 0  (5 logical qubits)
  └─ scripts/EmitAdder2Example.lean ──────►  adder2_ppm.txt   (12 joint-Z measurements + 4 magic-T)
       └─ gen_adder2_d3_qasm.py ──────────►  surface3_adder2_d3.qasm   (5 × [[13,1,3]] patches;
                                              each PPM merge = ancilla coupled to the Z̄ boundary
                                              {0,3,6} of each patch; 81 atoms, 88 CX)
            └─ run_zac_surgery.py ────────►  ZAC compile + atom-movement GIF
```

## Architecture — Qian Xu zone taxonomy ([`surface3_surgery_arch.json`](surface3_surgery_arch.json))

| Zone | Role | Here |
|---|---|---|
| **Memory** | logical data patches | 65 atoms = **5 × `[[13,1,3]]`** surface-code patches (5 patch-rows) |
| **Operation Ancilla** (`N_𝒜`) | mediating merge ancillae | 12 atoms (one per joint-`Z` measurement) |
| **Factory** | `\|C̄CZ̄⟩` magic-state factory | **4 atoms — USED** (one `\|C̄CZ̄⟩` per Toffoli; the adder is non-Clifford) |
| **Reservoir** | spare | idle trap sites |
| **Entangling (processor)** | Rydberg `CZ` fires here | the merges + the magic injections |

All zones have physical trap sites in the one storage array, separated into column bands; the
entangling zone sits above (atoms shuttle up for `CZ`).

## Compiled resource (ZAC verifier passes) — `python run_zac_surgery.py all`

| Metric | Value |
|---|---:|
| logical qubits / surface-code patches | 5 |
| physical atoms | **81** (65 data + 12 merge ancillae + 4 magic) |
| entangling `CZ` | **88** |
| Rydberg stages (max parallel `CZ`) | 39 (≤ 6) |
| ZAIR atom-movement instructions | **219** |
| schedule runtime | 25 830 µs (≈ 26 ms) |
| ZAC gate-scheduling + placement verification | ✓ pass |

## Do FormalRV's system invariants hold on neutral atoms? — YES

[`NeutralAtomInvariants.lean`](NeutralAtomInvariants.lean) (`native_decide`) proves the verified
schedule satisfies every strict system invariant under neutral-atom capacities (`max_gate2q_active`
set to the platform's Rydberg parallelism, vs the superconducting single-laser `1`).

## Reproduce

```bash
lake env lean --run scripts/EmitAdder2Example.lean              # adder -> PPM
cd Example/neutral_atom
python gen_adder2_d3_qasm.py                                    # 5 d=3 patches + merges -> QASM
python run_zac_surgery.py all                                   # full adder surgery + resources
python run_zac_surgery.py 8                                     # GIF (first merges)
lake env lean --run NeutralAtomInvariants.lean                  # invariants on neutral atoms
```

## Honest scope

- **5 d=3 patches.** Each logical qubit is a verified `[[13,1,3]]` surface code (13 data atoms). The
  building-block single merge (`surface3_xx_merge`, the full merged-code syndrome) is in
  `surface3_xx_merge.stim`; here each of the adder's 12 merges is realized as the **joint-`Z̄`
  measurement** (an ancilla coupled to the patches' `Z̄`-boundary `{0,3,6}`) — the lattice-surgery
  readout. Per-patch syndrome maintenance between merges is separate.
- **ZAC routes the circuit**; the surface-code + lattice-surgery structure is in the input we emit
  from the verified adder. ZAC verifies the *movement* schedule (no collisions, valid placement).
- **Layers/units.** FormalRV is logical (cycles); ZAC is physical (26 ms, transport-dominated).
  Same operations, different abstraction — see the GIF banner for the SysCall↔movement map.
- **FormalRV proves *what* the adder does + that the invariants hold; ZAC shows *how* a
  neutral-atom machine does it.**
