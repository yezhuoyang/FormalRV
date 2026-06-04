# Handoff — Windowed → Shor connection (COMPLETE)

**Branch:** `feat/windowed-shor`  •  **Worktree:** `C:/Users/yezhu/Documents/FormalRV-windowed`
**Key file:** `FormalRV/Shor/WindowedShorConnection.lean`
**Build:** `lake build FormalRV.Shor.WindowedShorConnection`  (**green**, 8348 jobs)

## Status — DONE, fully unconditional, kernel-clean `[propext, Classical.choice, Quot.sound]`

The windowed (Pipeline C) modular multiplier now reaches the headline Shor bound with
**no remaining circuit obligations**:

```
theorem windowed_shor_correct
    (a r N m bits anc ainv0 : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N) (hN1 : 1 < N)
    (hN : N ≤ 2^bits) (hN2 : 2*N ≤ 2^bits) (h_anc : 2*bits + 11 ≤ anc)
    (h_inv0 : a * ainv0 % N = 1) (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc (windowedModMulFamily …).family
      ≥ κ / (Nat.log2 N : ℝ)^4
```
Only standard Shor sizing/setting hypotheses + the base modular inverse `a·ainv0%N = 1`
(from `Order_modinv_correct`) + `anc ≥ 2·bits+11` (so the `3·bits+11` SQIR-Cuccaro workspace
fits).  Verified axiom-clean via `lean_verify` (no `sorryAx`, no custom axioms) — the clean
axiom set of `windowed_shor_correct` certifies the entire dependency chain.

### What was proven (this connection)
- **`h_tw`** — `swapTargetWindows` (target↔windows SWAP cascade, = Gidney `fig:multiply` SWAP) +
  `swapTargetWindows_apply` + `swapTargetWindows_h_tw`.  Supporting: `_preserves_disjoint`,
  `_read_t0/_t1/_b0/_b1`, `windowed2Input_at_window_disjoint`, `cuccaro_base_false`.
- **`windowedInplaceModMulGate_roundTrip`** — unconditional `|x⟩|0⟩ ↦ |(c·x)%N⟩|0⟩`
  (discharges `h_tw` + `h_unload` = `windowed_unload_concrete`).
- **Well-typedness** — `swapTargetWindows_wellTyped`, `windowedSwapLoadAdapter_wellTyped`
  (swap cascades via `qubit_swap_wellTyped`); `toyWindow2SelectedAddGate_wellTyped`,
  `windowed2SelectedAddGate_wellTyped`, `windowedSelectedAdd_wellTyped_concrete` (the
  selected-add, via `ControlledModAdd.clean_wellTyped` lifted by `Gate.WellTyped.mono` —
  control `0 < 2`, `0 ≠ flagPos=1`, `tableValue_lt_N`); `windowedInplaceModMulGate_wellTyped`.
- **Family + headline** — `windowedModMulFamily` (mmi via the MCP bridge + the round-trip;
  per-power inverse `ainv0^(2^i)%N` with `mul_pow_mod_one`), `windowed_shor_correct`.

### Notes for callers
- `ainv0` is obtained from a period `r` via `Order_modinv_correct` (`a·(modinv a N)%N = 1`),
  and `1 < N`, `2·N ≤ 2^bits` from the relaxed setting + `VerifiedCircuitSizing` (see §6
  WLOG lemmas `exists_even_bits_setting_sizing`).
- `anc ≥ 2·bits+11` is the binding ancilla constraint (SQIR-Cuccaro workspace `3·bits+11`).

## Gidney validation
Gidney, *Windowed quantum arithmetic* (arXiv:1905.07682), `fig:multiply`: the final SWAP is
exactly `swapTargetWindows` / `h_tw`.  Construction matches the paper.

## Git note
Nothing committed this session (commit only when asked).  Migration commit `804ef80` also
sits on `feat/ldpc-ppm-correctness`; do **not** rewrite that shared branch.
