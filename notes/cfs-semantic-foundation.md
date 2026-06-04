# CFS semantic foundation (Gidney 2025 arithmetic engine)

Created 2026-06-03 under John's directive **"full semantic proof before resource proof"**.

The Gidney-2025 corpus entry (`FormalRV/Corpus/Gidney2025.lean`) is arithmetic-tally verification
of the paper's resource numbers. Those numbers are only meaningful if the algorithm computes
`g^e mod N`. The arithmetic engine is the **Chevignard–Fouque–Schrottenloher approximate residue
arithmetic**. Its core is now proved bottom-up in `FormalRV/Shor/CFS/` — three layers, each
`#verify_clean` (axioms: `propext, Classical.choice, Quot.sound`; no `sorry`, no custom axiom):

| layer | file | headline | content |
|---|---|---|---|
| 1 | `CFS/ResidueArith.lean` | `residue_modexp_exact_of_lt` | residue modexp EXACT: `(∏ M_k^{e_k}) % L % N = g^e mod N` when `L ≥ N^m` (no wraparound). Proof: `modexpProd_modEq` (≡ `g^(e mod 2^m)` by induction) + `modexpProd_lt_pow` (product `< N^m`) + `residue_no_wraparound`. |
| 2 | `CFS/ResidueNumberSystem.lean` | `rns_faithful`, `rns_recover` | RNS over prime set `P` (`∏P = L`) is FAITHFUL = CRT injectivity. Proof: `modEq_list_prod_of_forall` (inductive CRT via `Nat.modEq_and_modEq_iff_modEq_mul`) + `coprime_list_prod`. |
| 3 | `CFS/TruncationBound.lean` | `sum_truncBits_error` | approximate reconstruction (each term truncated to `f` bits) deviates `< |P|·2^{-f}` (the `2^{-f}` of eq:modevbound). Proof: `truncBits_err_lt` (single-term `< 2^{-f}` via `Int.sub_one_lt_floor`) + `Finset.sum_lt_sum_of_nonempty`. |

Umbrella + status table + honest-gap list: `FormalRV/Shor/CFS.lean`. Wired into `FormalRV/Shor.lean`.

## Honest remaining semantic gaps (do NOT fake)
- Exact fractional-CRT identity `V/L = ∑_j a_j y_j / p_j (mod 1)` (needs inverses `y_j = (L/p_j)⁻¹ mod p_j`) — would tie layer-3's abstract terms to the actual reconstruction.
- The `ℓ` bit-width factor in the full paper bound `Δ_N ≤ |P|·ℓ·2^{-f}`.
- deviation → "good shot" probability → Ekerå–Håstad post-processing → success probability.
- Quantum-circuit semantics of the reversible residue multiplications.
- Assumption 1 (a prime set `P` with `∏P ≥ N^m` and small modular deviation exists) = genuine conjecture / honest axiom; never asserted.

## Note: no paper source in repo
`Corpus/Gidney2025.lean` cites `main.tex:NNNN` line numbers from the earlier session's checkout;
the `.tex` source is **not** present in `FormalRV/`. The CFS layers above formalize the standard,
unambiguous CFS mathematics (not paper-line-specific notation), so they are correct regardless.
Re-fetch arXiv:2505.15917 source to close the `ℓ`-factor / fractional-CRT gaps precisely.
