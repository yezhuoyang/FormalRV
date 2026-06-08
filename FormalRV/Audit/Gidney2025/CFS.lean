/-
  FormalRV.Audit.Gidney2025.CFS — SEMANTIC foundation of the Chevignard–Fouque–Schrottenloher approximate-
  residue-arithmetic factoring algorithm (the arithmetic engine of Gidney 2025, arXiv:2505.15917).

  ## Why this exists ("semantic proof BEFORE resource proof", John 2026-06-03)

  The Gidney-2025 corpus entry (`FormalRV.Audit.Gidney2025`, tallies in `…SystemZones`) records the paper's resource numbers.
  Those numbers are only meaningful if the underlying algorithm actually computes `g^e mod N`.  This
  directory proves the arithmetic core of that algorithm, bottom-up, each layer `#verify_clean`
  (axiom-clean, no `sorry`).  Formulas are cited against `Gidney1million/main.tex` §"Approximate
  Residue Arithmetic" (lines 195–414):

  | # | file | result | meaning |
  |---|---|---|---|
  | 1 | `CFS.ResidueArith`        | `residue_modexp_exact_of_lt` | residue modexp is EXACT: `(∏ Mₖ^{eₖ}) % L % N = g^e mod N` when `L ≥ N^m` (no wraparound; eq:bound-L). |
  | 2 | `CFS.ResidueNumberSystem` | `rns_faithful`, `modEq_prod_of_forall` | the residue-number-system over the prime set `P` (`∏P = L`) is FAITHFUL (CRT injectivity): the residue vector determines `V mod L`. |
  | 3 | `CFS.Reconstruction`      | `reconstruction`, `residue_modexp_via_crt` | the EXACT CRT reconstruction `(∑ⱼ rⱼ uⱼ) % L = V % L` (paper eq:comp_v, with `uⱼ mod pᵢ = δᵢⱼ`), and the full chain `(∑ⱼ rⱼ uⱼ) % L % N = g^e mod N`. |
  | 3′| `CFS.CRTBasis`           | `crtBasis`, `crtBasis_delta`, `reconstruction_explicit` | CONSTRUCTS `uⱼ = (L/pⱼ)·MultInv_{pⱼ}(L/pⱼ)` and proves `uⱼ mod pᵢ = δᵢⱼ`, so reconstruction holds with NO basis hypothesis (only `pᵢ` prime + pairwise coprime). |
  | 4 | `CFS.TruncationBound`     | `sum_truncBits_error_double` | the APPROXIMATE reconstruction (each of the `|P|·ℓ` terms truncated to `f` bits) deviates by `< |P|·ℓ · 2^{-f}` (real-valued model). |
  | 5 | `CFS.ModularDeviation`    | `modDev_triangle`, `modDev_chain` | the paper's deviation metric `Δ_N` (line 299) is a pseudometric whose value is `0 ↔ ≡ mod N`, and it ACCUMULATES LINEARLY over a chain of operations (line 311). |
  | 4+5| `CFS.TruncatedAccumulation` | `modDev_truncAcc`, `modDev_truncAcc_normalized` | the FUSION: the paper's integer truncation `(x≫t)≪t` over `A=|P|·ℓ` ops deviates by `≤ A·2^t`, i.e. `Δ_N/N ≤ |P|·ℓ·2^{-f}` (eq:modevbound) when `2^{t+f}≤N`. Uses `modDev` translation invariance. |
  | 6 | `CFS.ApproxPeriodFinding` | `modexp_periodic`, `approx_periodic` | the exact modexp `g^x mod N` is periodic; with a pointwise deviation `≤ ε`, the approximation is APPROXIMATELY PERIODIC: `Δ_N(f̃(x+yP)−f̃(x)) ≤ 2ε` (paper eq:438) — the classical entry point of period finding. |
  | 7 | `CFS.ResidueCircuit`     | `residueAccumulate_step`, `residueAccumulate_eq` | CLASSICAL SEMANTICS of the controlled residue multiplications: each step IS the verified modmult `r↦M_k·r mod p_j` (or identity), and the `m`-step composition computes `modexpProd % p_j`. |
  | 8 | `CFS.EkeraHastad`        | `ekera_hastad_exponent`, `ekera_hastad_recovery` | CLASSICAL post-processing: `g^{N−1} ≡ g^{p+q−2}` (so `d = p+q−2`), and from `d`,`N` the factors solve `p·(d−p+2)=N` / the quadratic `X²−(d+2)X+N`. |
  | — | `CFS.Assumptions`        | `Assumption1` | the one genuine CONJECTURE (line 346), stated as a `Prop`, never asserted. |

  Together: carry the modexp product componentwise in the residue domain over `P` (layer 2) via the
  verified per-step modmults (layer 7), reconstruct `V mod L` exactly with the constructed CRT basis
  and reduce mod `N` to get `g^e mod N` (layers 1+3+3′), at a cost made cheap by truncating the
  reconstruction with a deviation proven `≤ |P|·ℓ·2^{-f}` in the paper's integer `Δ_N` metric (layers
  4+5 fused), which makes the approximation APPROXIMATELY PERIODIC (layer 6) so period finding applies.

  ## HONEST remaining semantic gaps (documented, NOT faked)

  The arithmetic/classical chain is now CLOSED end to end: verified per-step modmult (7) → residue
  product (1) → faithful RNS (2) → exact CRT reconstruction with constructed basis (3,3′) → bounded
  truncation deviation in `Δ_N` (4,5) → approximate periodicity (6).  What remains is QUANTUM /
  number-theoretic and is each its own effort:

  - The **quantum success half** of "deviation → success".  Closed (classical/combinatorial):
    `approx_periodic`; the full masked-state infidelity argument eq:max-infidelity (`unifSuper_inner`
    amplitude identity, `window_overlap_card`, `masked_fidelity`, `infidelity_ratio_bound`,
    `global_fidelity_ge` lift); and the Ekerå–Håstad post-processing (`EkeraHastad`: `d = p+q−2` and
    factor recovery from the quadratic).  Remaining (irreducibly QUANTUM): that the QPE shots recover
    the discrete log `d` with high probability — the quantum period-finding success on the ideal
    state, connecting to `FormalRV.SQIRPort.probability_of_success` (the ported exact analysis).
  - The full multi-register **`Gate`-IR assembly** and its UNITARY (superposition) faithfulness;
    layer 7 proves one register's classical action and identifies each step with the verified modmult.
  - **Assumption 1** (main.tex line 346): a prime set `P` with `∏P ≥ N^m` and `Δ_N(∏P) < 2^{-f}`
    exists / is findable in `O(2^f·poly)` time.  Encoded as `CFS.Assumptions.Assumption1` (a `Prop`),
    NEVER asserted — the paper's own conjecture stays a conjecture.
-/
import FormalRV.Audit.Gidney2025.CFS.ResidueArith
import FormalRV.Audit.Gidney2025.CFS.ResidueNumberSystem
import FormalRV.Audit.Gidney2025.CFS.Reconstruction
import FormalRV.Audit.Gidney2025.CFS.CRTBasis
import FormalRV.Audit.Gidney2025.CFS.TruncationBound
import FormalRV.Audit.Gidney2025.CFS.ModularDeviation
import FormalRV.Audit.Gidney2025.CFS.TruncatedAccumulation
import FormalRV.Audit.Gidney2025.CFS.ApproxPeriodFinding
import FormalRV.Audit.Gidney2025.CFS.ResidueCircuit
import FormalRV.Audit.Gidney2025.CFS.EkeraHastad
import FormalRV.Audit.Gidney2025.CFS.Assumptions
