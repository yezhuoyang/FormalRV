# CFS semantic foundation (Gidney 2025 arithmetic engine)

Created 2026-06-03 under John's directive **"full semantic proof before resource proof"**, then
deepened to close the documented gaps (`/goal`).  Paper source:
`C:\Users\yezhu\Documents\resourceFormal\Gidney1million\main.tex` (arXiv:2505.15917); formulas cited
from §"Approximate Residue Arithmetic" (l.195–414) and §"Approximate Period Finding" (l.432+).

The **Chevignard–Fouque–Schrottenloher approximate residue arithmetic** (Gidney 2025's engine) is
proved bottom-up in `FormalRV/Shor/CFS/` — 10 modules, every theorem `#verify_clean`
(axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`, `native_decide`, or custom axiom):

| # | file | headline | content |
|---|---|---|---|
| 1 | `ResidueArith` | `residue_modexp_exact_of_lt` | residue modexp EXACT: `(∏ Mₖ^{eₖ})%L%N = g^e mod N` when `L≥N^m`. |
| 2 | `ResidueNumberSystem` | `rns_faithful`, `modEq_prod_of_forall` | RNS over prime set `P` (`∏P=L`) FAITHFUL = CRT injectivity. |
| 3 | `Reconstruction` | `reconstruction`, `residue_modexp_via_crt` | EXACT CRT reconstruction `(∑ⱼ rⱼ uⱼ)%L = V%L` (eq:comp_v); full chain `…%L%N = g^e mod N`. |
| 3′| `CRTBasis` | `crtBasis`, `crtBasis_delta`, `reconstruction_explicit` | **CONSTRUCTS** `uⱼ=(L/pⱼ)·invₚⱼ(L/pⱼ)`, proves `uⱼ mod pᵢ=δᵢⱼ` → reconstruction with NO basis hypothesis. (closes gap 2) |
| 4 | `TruncationBound` | `sum_truncBits_error_double` | real-valued truncation: `|P|·ℓ` terms deviate `< |P|·ℓ·2^{-f}`. |
| 5 | `ModularDeviation` | `modDev_triangle`, `modDev_chain` | paper's `Δ_N` metric: pseudometric, `=0↔≡`, accumulates linearly. |
| 4+5 | `TruncatedAccumulation` | `modDev_truncAcc`, `modDev_truncAcc_normalized` | **FUSION**: integer trunc `(x≫t)≪t`, `A` ops deviate `≤A·2^t`; normalized `Δ_N/N ≤ |P|·ℓ·2^{-f}` (eq:modevbound) when `2^{t+f}≤N`. Via `modDev` translation invariance. (closes gap 1) |
| 6 | `ApproxPeriodFinding` | `modexp_periodic`, `approx_periodic`, `window_overlap_card`, `infidelity_ratio_bound` | modexp is periodic; deviation `≤ε` ⟹ APPROX PERIODIC `≤2ε` (eq:438); + infidelity combinatorial core (overlap `=W−d`, `d/W≤ε/S`). (gap 3 classical core) |
| 7 | `ResidueCircuit` | `residueAccumulate_step`, `residueAccumulate_eq` | each controlled-mult step IS the verified modmult `r↦Mₖ·r mod pⱼ`; `m`-step composition `= modexpProd % pⱼ`. (gap 4 classical core) |
| — | `Assumptions` | `Assumption1` | the one CONJECTURE (l.346), a `Prop`, never asserted. (gap 5) |

Umbrella + status table + honest-gap list: `FormalRV/Shor/CFS.lean`. Wired into `FormalRV/Shor.lean`.

## Gap status (the `/goal` list)
- **Gap 1 (fuse layer 4↔5)** — CLOSED. `modDev_truncAcc` / `modDev_truncAcc_normalized` give the
  integer-model `Δ_N(V−Ṽ≪t) ≤ |P|·ℓ·2^{-f}` (eq:modevbound). Key new fact: `modDev` translation invariance.
- **Gap 2 (explicit uⱼ basis)** — CLOSED. `crtBasis` constructed from modular inverses; `crtBasis_delta`
  proves `uⱼ mod pᵢ=δᵢⱼ`; `reconstruction_explicit` removes the basis hypothesis.
- **Gap 3 (deviation→success)** — classical core CLOSED: `approx_periodic` (the periodicity premise)
  + infidelity counting core. REMAINING (quantum): amplitude identity `|⟨ψ₁|ψ̃₁⟩|=|A∩B|/W`, QPE on the
  ideal state, Ekerå–Håstad — connect to `FormalRV.SQIRPort.probability_of_success`.
- **Gap 4 (circuit semantics)** — classical core CLOSED: per-register action `residueAccumulate_eq`,
  each step = verified `sqir_modmult_inplace_shifted_correct`. REMAINING: full multi-register `Gate`-IR
  assembly + UNITARY (superposition) faithfulness.
- **Gap 5 (Assumption1)** — DONE by design: encoded as a `Prop` (`Assumptions.Assumption1`), never asserted.

The arithmetic/classical chain is closed end-to-end (per-step modmult → product → faithful RNS →
exact CRT reconstruction w/ constructed basis → bounded `Δ_N` truncation → approximate periodicity).
The residue is purely QUANTUM (state overlap amplitudes, QPE on approximately-periodic masked states)
and the number-theoretic Assumption 1 conjecture.
