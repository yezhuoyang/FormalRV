# FULL end-to-end logical 2-bit adder — verified → d=3 lattice surgery → system schedule → NEUTRAL ATOMS

The complete pipeline for **one** circuit, the 2-bit Cuccaro adder, with every layer present and
checked — no placeholders:

1. **Logical adder computes `a+b`** — proven (Lean), and *re-checked for the realization by simulation*.
2. **d=3 surface-code lattice surgery** — every gate is a real merged-code merge / real `|C̄CZ̄⟩`
   magic injection.
3. **Detailed system schedule** — 192 SysCalls, machine-checked to fit the architecture.
4. **Neutral-atom compile (ZAC)** — the whole thing as atom movements, ZAC-verified, with a GIF.

<p align="center"><img src="surface3_adder2_d3_neutral_atom.gif" width="560" alt="neutral-atom atoms implementing the full d=3 surface-code lattice-surgery 2-bit adder"></p>

*Zones (Qian Xu taxonomy): **MEMORY** = the 5 `[[13,1,3]]` data patches; **ANCILLA** = the reused
surgery/syndrome pool (`N_𝒜`); **FACTORY** = the 3 `|C̄CZ̄⟩` magic atoms; **RES**ervoir. Atoms shuttle
into the **ENTANGLING** zone for the Rydberg `CZ`s (the merges + magic injections). Banner = the
FormalRV SysCall each ZAC op realizes.*

---

## 1 · The logical adder actually computes `a+b` — a Lean theorem + an independent simulation re-check

| What is established | How |
|---|---|
| WHAT the **logical circuit** computes (`a+b`) | `cuccaro_n_bit_adder_full_correct` (Lean theorem) |
| the **measurement-based realization** also computes `a+b` on all tested inputs/branches | [`logical_adder/verify_mb_adder.py`](logical_adder/verify_mb_adder.py) — NumPy statevector **simulation** (python-vs-python) |

`python logical_adder/verify_mb_adder.py` builds the adder out of **real measurement-based gadgets**
and checks it:

```
[1] |CCZ> magic injection == CCZ ... OK            # real |C̄CZ̄⟩ = CCZ|+++>, gate teleportation
[2] lattice-surgery CNOT == CX ... OK              # joint M_ZZ + M_XX merges + Pauli feed-forward
[3] measurement-based adder == ideal adder (32 inputs x 30 random branches): mismatches: 0
    => FULL LOGICAL ADDER VERIFIED
[4] semantic check: computes a+b (mod 4): a+b correct for all 16 (a,b) pairs: YES
```

This is what makes it a *real* adder, and closes the gaps the earlier draft had — the **4 Toffolis
are genuinely performed** (real `|C̄CZ̄⟩` magic consumed by gate teleportation), the computation is
**measurement-driven with outcome-conditioned Pauli/Clifford feed-forward**, and "computes `a+b`" is
shown **for the realization** (over many random measurement branches), not just inherited from the
abstract proof. Note the scope: this is a NumPy statevector **simulation** that re-checks the
measurement-based realization against an *ideal* Cuccaro adder — both built in Python — so it is an
independent re-check, **not** a comparison against the Lean object and not itself a Lean proof. The
Lean theorem (separately) proves WHAT the adder computes; the simulation shows the realization
matches it on all 32 inputs × 30 branches tested.

## 2 · d=3 surface-code lattice surgery — the FULL merged-code syndrome per gate

Each of the 5 logical qubits is a `[[13,1,3]]` surface code (`surfaceHGP 3`, verified;
`scripts/DumpSurface3.lean`). [`gen_adder2_d3_full_qasm.py`](gen_adder2_d3_full_qasm.py) lowers the
adder's PPM to the **complete merged-code syndrome circuit** for every gate:

- each joint-`Z` measurement → the verified `surface3_zz_merge` (88 CX) / `surface3_zzz_merge`
  (131 CX) full syndrome (`scripts/EmitSurgeryStim.lean`), remapped onto the 5 shared patches;
- each Toffoli → a **real `|C̄CZ̄⟩`** prepared on 3 magic atoms (`= CCZ|+++>`) and injected into its
  3 data patches.

→ `surface3_adder2_d3_full.qasm`: **107 atoms** (65 data + 39 reused ancillae + 3 magic), **1240 CZ**
+ 4 real magic injections.

## 3 · Detailed system schedule — `Example/Adder2EndToEnd.lean`

`lake env lean --run Example/Adder2EndToEnd.lean`:

```
System schedule:  SysCalls=192  Gate2q merges=72  wall-clock=192µs
✓ VERIFIED  schedule fits this architecture          (theorem schedule_fits)
✓ VERIFIED  wall-clock LOWER BOUND ≥ 72µs            (gate2q capacity bound)
```

The 192 SysCalls (`FRESHANC / GATE2Q / MEAS / DECODE / PFU / MAGIC`) are scheduled onto the
Data/Ancilla/Factory/Routing zones with explicit µs intervals and **machine-checked** to satisfy
every strict invariant (operation-capacity, feedback-after-decode, slot-capacity, ancilla-freshness).
(`schedule_fits` is proved `by native_decide` — an arithmetic-tier decidable machine check, not an
axiom-clean semantic theorem. The 12 surgery blocks are count-matched replicas of one verified
representative merge gadget via `merge_blocks_match_ppm`, also `native_decide`.)

## 4 · Neutral-atom compile (ZAC) — `python run_zac_surgery.py all`

| Metric | Value |
|---|---:|
| logical qubits / patches | 5 |
| physical atoms | **107** (65 data + 39 reused ancillae + 3 `\|C̄CZ̄⟩` magic) |
| entangling `CZ` (full merged-code syndromes + magic) | **1240** |
| Rydberg stages (runtime ZAC output) | ~95 |
| ZAIR atom-movement instructions | ~1892 |
| schedule runtime | ~318 881 µs (≈ 319 ms) |
| ZAC gate-scheduling + placement verification | pass (external ZAC verifier) |

The atom/`CZ` counts (**107**, **1240**) are static properties of `surface3_adder2_d3_full.qasm` and
its `.roles.json`. The Rydberg-stage count (~95), ZAIR instruction count (~1892), runtime (~318 881 µs)
and the "verification pass" are **runtime outputs of `run_zac_surgery.py` driving the external ZAC
tool** (UCLA-VAST) — they are *not* stored in the repo's data files and *not* Lean-proven; rerunning
ZAC reproduces them. The per-stage parallelism ZAC actually achieves and the conservative parallelism
cap used by the Lean proof are **different quantities**: `NeutralAtomInvariants.lean` justifies a
conservative `max_gate2q_active = 12` ("up to 12 parallel CZ per Rydberg stage") and the ZAC run may
report a different (looser) figure.

Plus [`NeutralAtomInvariants.lean`](NeutralAtomInvariants.lean): the FormalRV system invariants are
re-checked via `native_decide` under neutral-atom (Rydberg-parallel) capacities (`max_gate2q_active = 12`).
This is an arithmetic-tier decidable machine check (kernel-trusted Boolean evaluation), **not** an
axiom-clean semantic theorem.

## Reproduce the whole thing

```bash
python Example/neutral_atom/logical_adder/verify_mb_adder.py   # 1: adder really computes a+b
lake env lean --run scripts/EmitSurgeryStim.lean              # zz/zzz full merge templates
lake env lean --run scripts/EmitAdder2Example.lean            # adder -> PPM
lake env lean --run Example/Adder2EndToEnd.lean               # 3: system schedule (schedule_fits)
cd Example/neutral_atom
python gen_adder2_d3_full_qasm.py                             # 2: d=3 full merges + real magic
python run_zac_surgery.py all                                 # 4: neutral-atom compile + resources
python run_zac_surgery.py 6                                   # 4: the GIF
```

## Honest scope

- **Magic states** are assumed distilled (the Factory zone provides `|C̄CZ̄⟩`); we prepare a genuine
  `|C̄CZ̄⟩` (`CCZ|+++>`) and inject it — we do not simulate the distillation factory itself.
- **Measurements + decoding + Pauli-frame feed-forward run on the classical controller.** ZAC routes
  the *unitary* atom-movements (it skips measurement); a real neutral-atom machine measures in the
  readout zone and applies corrections between rounds. The feed-forward is verified to be correct in
  layer 1; ZAC realizes the gate-movement layer.
- **Ancillae + magic are reused** across gates (measured + reset between; the reset is controller-side
  SPAM ZAC doesn't route), giving the realistic ~107-atom footprint instead of fresh-per-gate.
- **FormalRV proves *what* the adder does + that the schedule fits; the simulation proves the
  realization computes `a+b`; ZAC shows *how* a neutral-atom machine moves the atoms to do it.**
