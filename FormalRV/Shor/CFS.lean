/-
  FormalRV.Shor.CFS — SEMANTIC foundation of the Chevignard–Fouque–Schrottenloher approximate-
  residue-arithmetic factoring algorithm (the arithmetic engine of Gidney 2025, arXiv:2505.15917).

  ## Why this exists ("semantic proof BEFORE resource proof", John 2026-06-03)

  The Gidney-2025 corpus entry (`FormalRV.Corpus.Gidney2025`) tallies the paper's resource numbers.
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
  | — | `CFS.Assumptions`        | `Assumption1` | the one genuine CONJECTURE (line 346), stated as a `Prop`, never asserted. |

  Together: carry the modexp product componentwise in the residue domain over `P` (layer 2),
  reconstruct `V mod L` exactly with the constructed CRT basis and reduce mod `N` to get `g^e mod N`
  (layers 1+3+3′), at a cost made cheap by truncating the reconstruction with a deviation that is
  proven `≤ |P|·ℓ·2^{-f}` in the paper's own integer `Δ_N` metric (layers 4+5 fused).

  ## HONEST remaining semantic gaps (documented, NOT faked)

  - The chain `Δ_N(V − Ṽ≪t) ≤ |P|·ℓ·2^{-f}` (now proved, `TruncatedAccumulation`) → "good shot"
    probability → Ekerå–Håstad post-processing → success probability.  This links the deviation bound
    to `FormalRV.SQIRPort`'s `probability_of_success`.
  - The quantum-circuit semantics of the reversible residue multiplications (a `Gate`-IR construction
    of the controlled modular multiplications, with a correctness proof à la the SQIR modmult port).
  - **Assumption 1** (main.tex line 346): a prime set `P` with `∏P ≥ N^m` and `Δ_N(∏P) < 2^{-f}`
    exists / is findable in `O(2^f·poly)` time.  Encoded as `CFS.Assumptions.Assumption1` (a `Prop`),
    NEVER asserted — the paper's own conjecture stays a conjecture.
-/
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Shor.CFS.Reconstruction
import FormalRV.Shor.CFS.CRTBasis
import FormalRV.Shor.CFS.TruncationBound
import FormalRV.Shor.CFS.ModularDeviation
import FormalRV.Shor.CFS.TruncatedAccumulation
import FormalRV.Shor.CFS.Assumptions
