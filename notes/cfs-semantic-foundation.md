# CFS semantic foundation (Gidney 2025 arithmetic engine)

Created 2026-06-03 under John's directive **"full semantic proof before resource proof"**.
Paper source: `C:\Users\yezhu\Documents\resourceFormal\Gidney1million\main.tex` (arXiv:2505.15917);
formulas cited from §"Approximate Residue Arithmetic", lines 195–414.

The Gidney-2025 corpus entry (`FormalRV/Corpus/Gidney2025.lean`) is arithmetic-tally verification
of the paper's resource numbers. Those numbers are only meaningful if the algorithm computes
`g^e mod N`. The arithmetic engine is the **Chevignard–Fouque–Schrottenloher approximate residue
arithmetic**. Its core is proved bottom-up in `FormalRV/Shor/CFS/` — six modules, each
`#verify_clean` (axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`, no custom axiom):

| # | file | headline | content |
|---|---|---|---|
| 1 | `ResidueArith.lean` | `residue_modexp_exact_of_lt` | residue modexp EXACT: `(∏ Mₖ^{eₖ}) % L % N = g^e mod N` when `L ≥ N^m` (eq:bound-L, no wraparound). |
| 2 | `ResidueNumberSystem.lean` | `rns_faithful`, `modEq_prod_of_forall` | RNS over prime set `P` (`∏P = L`) is FAITHFUL = CRT injectivity (List + Fin forms). |
| 3 | `Reconstruction.lean` | `reconstruction`, `residue_modexp_via_crt` | EXACT CRT reconstruction `(∑ⱼ rⱼ uⱼ) % L = V % L` (eq:comp_v, `uⱼ mod pᵢ = δᵢⱼ`); full chain `…% L % N = g^e mod N`. Proof: per-prime ZMod + layer 2. |
| 4 | `TruncationBound.lean` | `sum_truncBits_error_double` | approximate reconstruction (`|P|·ℓ` terms truncated to `f` bits) deviates `< |P|·ℓ·2^{-f}` (eq:modevbound). Via `Int.sub_one_lt_floor` + general Finset bound. |
| 5 | `ModularDeviation.lean` | `modDev_triangle`, `modDev_chain` | paper's `Δ_N` metric (line 299): pseudometric, `=0 ↔ ≡ mod N`, ACCUMULATES LINEARLY over an op chain (line 311). `modDev_triangle` needs only `{propext, Quot.sound}`. |
| 6 | `Assumptions.lean` | `Assumption1` (def, NOT asserted) | the one genuine conjecture (line 346): a prime set with `∏P ≥ N^m` and `Δ_N(∏P) < 2^{-f}` exists. Stated as a `Prop`; `assumption1_deviation_meaning` bridges the cleared-denominator form to `Δ_N(L)<2^{-f}` in ℚ. |

Umbrella + status table + honest-gap list: `FormalRV/Shor/CFS.lean`. Wired into `FormalRV/Shor.lean`.

## Correction logged
Earlier (first pass) I listed "exact fractional-CRT identity" as an open gap. **Wrong** — the paper's
reconstruction (eq:comp_v) is the EXACT INTEGER CRT dot product, now proved (`reconstruction`,
layer 3). Approximation enters only at truncation (layer 4), not in the reconstruction identity.

## Honest remaining semantic gaps (do NOT fake)
- Bridge layer-4's real-valued `∑truncated−∑exact < |P|·ℓ·2^{-f}` to layer-5's integer `Δ_N` metric
  over the paper's exact `(N≫t)` truncation model — fuse into one `Δ_N(V−Ṽ≪t) ≤ |P|·ℓ·2^{-f}`.
- Constructing the explicit CRT basis `uⱼ=(L/pⱼ)·MultInv_{pⱼ}(L/pⱼ)` (now a hypothesis via `uⱼ mod pᵢ=δᵢⱼ`).
- deviation → "good shot" probability → Ekerå–Håstad post-processing → success probability.
- Quantum-circuit semantics of the reversible residue multiplications.
- `Assumption1` stays a documented conjecture (encoded as a `Prop`, never proved).
