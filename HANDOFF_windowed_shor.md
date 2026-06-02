# Handoff — Windowed → Shor connection (only `h_tw` remains)

**Branch:** `feat/windowed-shor`  •  **Worktree:** `C:/Users/yezhu/Documents/FormalRV-windowed`
**Key file:** `FormalRV/Shor/WindowedShorConnection.lean`
**Build:** `lake build FormalRV.Shor.WindowedShorConnection`
**Tooling:** start the Claude session **in this worktree dir** so `lean-lsp` roots here (live goal-states). Confirm the `lean-lsp` MCP is enabled for this project.

## Goal
Connect the windowed (Pipeline C) modular multiplier to the headline
`Shor_correct_verified_no_modmult_axioms` bound `≥ κ / (log₂ N)^4`.
The arithmetic Shor headline currently rides on the SQIR-faithful
(Pipeline B) multiplier; this connects the *windowed* one.

## Status — all kernel-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`
- ✅ `shor_correct_of_encodeRoundTrip`: `EncodeRoundTripModMul → VerifiedModMulFamily → headline`.
- ✅ `windowedForwardGate_apply`: the windowed apex at a concrete layout (~20 hyps via `omega`).
- ✅ `windowedInplaceModMul_roundTrip`: full 5-stage in-place gate, proven **conditional on two hyps `h_tw` and `h_unload`**; reuses `sqir_modmult_inverse_clear_arith` for the `−k⁻¹` cancellation.
- ✅ `h_unload` **fully closed** (`windowed_unload_concrete`) via the loader-involution chain:
  `qubit_swap_involutive`, `qubit_swap_update_comm`, `qubit_swap_comm`,
  `windowedSwapLoadAdapter_update_frame`, `_comm_swap`, `_involutive`.
- ✅ Gap-2 (even-`bits` parity) WLOG: `exists_even_bits_setting_sizing` + monotonicity lemmas.
- ⏳ **REMAINING: `h_tw`** (target↔windows swap), then ~40 lines of family packaging.

## `h_tw` — design is fully worked out (just implement)

Target statement (the open hypothesis of `windowedInplaceModMul_roundTrip`):
```
∀ acc w, acc < 2^bits → w < 2^bits →
  Gate.applyNat tw
      (windowed2Input acc (wb0Idx bits) (wb1Idx bits)
        (windowed2_b0_of_x w) (windowed2_b1_of_x w) (wnumWin bits))
    = windowed2Input w (wb0Idx bits) (wb1Idx bits)
        (windowed2_b0_of_x acc) (windowed2_b1_of_x acc) (wnumWin bits)
```

Encoding facts (`Part24` `windowed2Input` + `FormalRV.BQAlgo.cuccaro_input_F_at_b`):
- `windowed2Input acc … 0 = cuccaro_input_F 2 false 0 acc`; window bits layered on top.
- `acc` bit `j` is at Cuccaro **b-position `2j+3`** (`q_start=2`, `q_start+2j+1`). The `a`-register (even positions `2j+4`) is all 0; flags at positions `0,1,2`.
- window value `w`: `wb0Idx k = 2·bits+3+2k` holds `w.testBit (2k)`; `wb1Idx k = 2·bits+4+2k` holds `w.testBit (2k+1)`.
- b-positions `{2j+3 : j<bits}` (max `2·bits+1`) are **disjoint** from window positions (min `2·bits+3`) ⟹ the swap is a **clean disjoint-swap cascade** (same shape as the involution lemmas).

Gate to define:
```
swapTargetWindows (bits : Nat) : Gate :=     -- cascade over k < bits/2 (= wnumWin bits)
    qubit_swap (4*k+3) (wb0Idx bits k)        -- acc bit 2k   ↔  w bit 2k   (4k+3 = 2·(2k)+3)
  ; qubit_swap (4*k+5) (wb1Idx bits k)        -- acc bit 2k+1 ↔  w bit 2k+1 (4k+5 = 2·(2k+1)+3)
```
After applying to `windowed2Input acc (windows = b0_of_x w, b1_of_x w)`:
- each b-position `2j+3` receives `w.testBit j` ⟹ target value becomes `w`;
- `wb0Idx k`/`wb1Idx k` receive `acc.testBit 2k`/`acc.testBit (2k+1)` = `windowed2_b0_of_x acc k`/`windowed2_b1_of_x acc k` ⟹ windows hold `acc`;
- flags / `a`-register / above-layout all preserved.
⟹ output `= windowed2Input w (windows = b0_of_x acc, b1_of_x acc)` = the `h_tw` RHS. ∎

Proof reuses the toolkit **already in this file / repo**: `qubit_swap_correct`,
`FormalRV.Framework.update_eq`/`update_neq`, `cuccaro_input_F_at_b`,
`windowed2Input_read_b0`/`_read_b1`, and the disjoint-frame + cascade-induction
pattern from `windowedSwapLoadAdapter_involutive`. Estimate ~100–150 lines, mechanical.

**Then:** instantiate `windowedInplaceModMul_roundTrip` at the concrete `swapTargetWindows`
(discharge its `h_tw` via the new lemma, `h_unload` via `windowed_unload_concrete`), package as
a `VerifiedModMulFamily` (gate keyed by `a^(2^i)`, inverse `ainv^(2^i) % N`; the per-power inverse
`(a^(2^i)·(ainv^(2^i)%N))%N = 1` follows from `mul_pow_mod_one` in MCPBridge) → headline bound.

## Gidney validation
Gidney, *Windowed quantum arithmetic* (arXiv:1905.07682), `fig:multiply` (`main.tex:530–544`):
`|x⟩|0⟩ —[+a·k mod N]→ |x⟩|kx⟩ —[+b·(−k⁻¹) mod N]→ |0⟩|kx⟩ —[SWAP]→ |kx⟩|0⟩`.
The final **SWAP is exactly `swapTargetWindows`/`h_tw`** — the construction matches the paper.

## Namespaces (post-refactor)
`FormalRV.BQAlgo.WindowedShorConnection` (the connection lemmas) • `VerifiedShor.Windowed`
(windowed defs/apex) • `FormalRV.BQAlgo` (MCP bridges, Cuccaro, `sqir_modmult_inverse_clear_arith`)
• `FormalRV.SQIRPort` (`MultiplyCircuitProperty`, `probability_of_success`, `κ`).

## Git note
The migration commit `804ef80` also sits on `feat/ldpc-ppm-correctness` (buried under another
agent's commit). Do **not** rewrite that shared branch; clean up only when it is quiescent.
