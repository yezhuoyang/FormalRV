# Measured Gidney Adder

The **measured** Gidney ripple-carry adder family is the `n`-Toffoli-per-add adder that Cain–Xu 2026 / Gidney 2018 actually charge — half the `2n` of a reversible adder. It computes the FAITHFUL sum `(a + b) % 2^bits` on the target register, but releases the carry ancillas by **measurement-based AND-uncompute** (Gidney's "temporary AND", arXiv:1709.06648) instead of a second reversible Toffoli sweep. The reverse pass is therefore **Toffoli-free**, so the adder's cost collapses to its forward sweep's `n` Toffoli. A controlled variant gates the addend under a control (`ctrl ? (a+b) : b`) at `2n` Toffoli — Cain–Xu's E3 → E4 jump. Import `FormalRV.Arithmetic.MeasuredAdder` to get the whole verified family (defs + value correctness + Toffoli counts).

This adder is built as a `FormalRV.Shor.MeasUncompute.EGate` — the measurement-augmented IR where `mz q` resets qubit `q` to `|0⟩` (the Boolean image of an X-basis measure + classical fixup, justified at the density layer by `MeasuredANDUncompute.measANDUncompute_perfect`).

## The spine — where everything lives
| Aspect | File | Headline theorem |
|---|---|---|
| Defs + frame/congruence base | `MeasuredAdderDef` | `gidneyAdderMeasured`, `gidneyAdderMeasuredControlled`, `gidneyMeasFullReverse`, `ctrlMaskRead`, `gidneyMeasFullReverse_rt`/`_carry_clear`, `EGate.applyNat_congr_lt`, `gidneyAdderMeasured_boundedBy` |
| Value (uncontrolled) | `MeasuredAdderCorrectness` | `gidneyAdderMeasured_correct` (target = `(a+b).testBit i`, carries cleared), `gidneyAdderMeasured_target_val` (= `(a+b) % 2^(n+2)`) |
| Value (controlled) | `MeasuredAdderCorrectness` | `gidneyAdderMeasuredControlled_correct` (target = `(ctrl?a+b:b).testBit i`), `gidneyAdderMeasuredControlled_target_val` |
| Count (uncontrolled) | `MeasuredAdderResource` | `toffoli_gidneyAdderMeasured` (= `n+2`), `gidneyAdderMeasured_halves` (= HALF the reversible adder) |
| Count (controlled) | `MeasuredAdderResource` | `toffoli_gidneyAdderMeasuredControlled` (= `2·(n+2)`), `gidneyAdderMeasuredControlled_doubles` (= DOUBLE the uncontrolled) |
| Example | `Example.lean` | `#eval` Toffoli counts + `EGate.applyNat` runs decoding the faithful sum `(a+b) % 16` |

The full theorem names are unchanged from the pre-refactor monolith — namespace is still `FormalRV.Arithmetic.MeasuredAdder`; the two old files `GidneyMeasured.lean` / `GidneyMeasuredControlled.lean` were split into Def/Correctness/Resource with **identical statements and proofs, just relocated**.

## What the circuit is

Layout: the interleaved Gidney layout `read[i] = 3i`, `target[i] = 3i+1`, `carry[i] = 3i+2`. The uncontrolled measured adder `gidneyAdderMeasured (n+2) q_start` is three stages composed in sequence:

1. **Forward carry sweep** `gidney_adder_forward_faithful_full (n+2)` — a CCX cascade that computes the ripple carry chain into the carry ancillas. This is the **only Toffoli-bearing stage**: `n+2` CCX.
2. **Final-CX sum stamp** `gidney_final_cx_cascade (n+2)` — T-free CNOTs `read[i] ⊕ target[i]`.
3. **Measured reverse** `gidneyMeasFullReverse (n+2)` — the reversible reverse cascade with **each per-step carry AND-uncompute `CCX(read i, target i, carry i)` replaced by a measurement `mz(carry i)`**, keeping every CX. Toffoli count `0`.

The reverse sweep's CXs are genuinely load-bearing for the sum (a tempting `forward ; final_cx ; mz(carries)` shortcut does NOT compute `a+b` — machine-checked false at `n=2, a=b=1`), so they are kept; only the carry-uncompute CCX becomes a measurement. Because each measured step equals the unitary step then clearing its own carry, and no later (lower-index) step reads that carry, forcing it to `false` is invisible to every read/target output (`gidneyMeasFullReverse_rt`). So the target is the same faithful `(a+b) % 2^bits` as the reversible adder, while the carries are all released (`gidneyMeasFullReverse_carry_clear`).

The **controlled** adder `gidneyAdderMeasuredControlled (n+2) q_start ctrl` prepends a controlled core `ctrlMaskRead ctrl (n+2)` — `n+2` Toffolis `CCX(ctrl, srcA_idx ctrl i, read_idx i)` that gate the addend `a` (held in a high source register) into the read register under `ctrl` — then reuses `gidneyAdderMeasured` verbatim. The control cannot be measured away (it entangles the addend with the rest of the computation), so it adds a genuine `n` Toffoli on top: `2n` total.

## Circuit diagram

ASCII (the adder is an `EGate` *with measurement*, so a unitary OpenQASM render cannot express the `mz` reset channel — see `diagrams/README.md`). Width `n+2 = 4` (`n = 2`), interleaved `read/target/carry`:

```
            ┌────────── FORWARD (n+2 CCX, the ONLY Toffolis) ──────────┐  ┌─ final CX ─┐  ┌──────── MEASURED REVERSE (0 Toffoli) ────────┐

 read[0] ───●───────────────────────────────────────────────────────────────●─────────────────────────────────────────────────────
 target[0]──┼──●────────────────────────────────────────────────────────────⊕─────────────────────────────────────────────────────
 carry[0] ──⊕──⊕──●──────────────────────── … carry chain … ────────────────────────────────────────────●───────●──╫(mz)═══ |0⟩
            CCX   │                                                                                       │CX      │CX  reset
 read[1] ─────────●──────────────────────────────────────────────────────────●──────────────────────────⊕────────┼─────────────────
 target[1]────────┼──●───────────────────────────────────────────────────────⊕───────────────────────────────────⊕────────────────
 carry[1] ────────⊕──⊕──●────────────────── … ──────────────────────────●──────────────────────●──────────╫(mz)═══════════ |0⟩
                  CCX                                                    │CX(carry0→carry1)      │
   ⋮                                                                     (chain CXs in reverse)  (each step ends in mz(carry i),
                                                                                                  NOT a CCX uncompute)
```

Per step the rule is: forward writes carry `i` with a `CCX(read i, target i, carry i)`; the reverse undoes the propagation CXs (kept) and, instead of a second `CCX(read i, target i, carry i)` to uncompute carry `i`, **measures it**: `mz(carry i)` resets it to `|0⟩` for free. That single substitution — `CCX → mz`, per carry — is the whole of Gidney's measurement trick, and it is exactly what turns the `2n`-Toffoli reversible adder into this `n`-Toffoli measured one.

Reproduce the counts and the value runs: `lake env lean FormalRV/Arithmetic/MeasuredAdder/Example.lean`.

## Correctness (the theorems to audit)
- Uncontrolled: `gidneyAdderMeasured_correct` — `target[i] = (a+b).testBit i` and `carry[i] = false` for every `i < n+2`; decoded form `gidneyAdderMeasured_target_val = (a+b) % 2^(n+2)`. The target value is **reused verbatim** from the reversible adder's proven correctness (`gidney_adder_full_faithful_no_measurement_target_correct`) via `gidneyMeasFullReverse_rt`; no arithmetic is re-proved.
- Controlled: `gidneyAdderMeasuredControlled_correct` — `target[i] = (if cval=1 then a+b else b).testBit i`, carries cleared; decoded `gidneyAdderMeasuredControlled_target_val = (if cval=1 then a+b else b) % 2^(n+2)`. Proved by an index-congruence (`EGate.applyNat_congr_lt`) that swaps the masked state for the literal `adder_input_F (n+2) (if cval=1 then a else 0) b` on the adder block (the measured adder only touches indices `< adder_n_qubits`, `gidneyAdderMeasured_boundedBy`), then reuses `gidneyAdderMeasured_correct`.

## Resource (the count theorems)
- `toffoli_gidneyAdderMeasured (n q_start) = n + 2` — final-CX and measured reverse are Toffoli-free (`tcount_gidneyMeasFullReverse = 0`), so the cost is the forward sweep's `n+2`.
- `gidneyAdderMeasured_halves` — `= tcount (gidney_adder_full_faithful_no_measurement (n+2)) / 7 / 2`, i.e. exactly HALF the reversible adder.
- `toffoli_gidneyAdderMeasuredControlled (n q_start ctrl) = 2·(n+2)` — controlled core `n+2` + reused measured add `n+2`.
- `gidneyAdderMeasuredControlled_doubles` — `= 2 · toffoli_gidneyAdderMeasured`, the verified E3 → E4 factor-2.

| adder (width n+2 = 4, n = 2) | Toffoli |
|---|---|
| reversible Gidney `gidney_adder_full_faithful_no_measurement` | 8 |
| **measured `gidneyAdderMeasured`** | **4** (HALF) |
| **controlled `gidneyAdderMeasuredControlled`** | **8** (= 2·4) |

## Honest scope
- The `mz`-as-reset Boolean model is the value-level image of Gidney's X-basis measure + classical phase fixup; the amplitude-layer justification that this reset IS the perfect AND-uncompute on the computed family is `FormalRV.Shor.MeasuredANDUncompute.measANDUncompute_perfect` (cited, not re-proved here).
- `q_start` is carried for API parity with the windowed-adder convention; this adder is hardwired to the base-0 interleaved layout, so `q_start` does not shift indices.
- The controlled adder requires the control register placed ABOVE the adder block (`adder_n_qubits (n+2) ≤ ctrl`); that disjointness is what powers the congruence reuse.
- Kernel-clean: no `sorry`, no `native_decide`, no added axioms. The headline theorems use only `[propext, Classical.choice, Quot.sound]` (the pure bit-value theorems are `[propext, Quot.sound]`).

## For auditors
`import FormalRV.Arithmetic.MeasuredAdder` — the umbrella pulls the whole verified family. For Cain–Xu 2026: `toffoli_gidneyAdderMeasured` = the E3 `n`-Toffoli adder (value `gidneyAdderMeasured_correct`), `toffoli_gidneyAdderMeasuredControlled` = the E4 `2n`-Toffoli controlled adder (value `gidneyAdderMeasuredControlled_correct`), and `gidneyAdderMeasuredControlled_doubles` = the E3 → E4 factor-2, all on objects that genuinely compute `a + b`.
