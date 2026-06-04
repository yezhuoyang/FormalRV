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
  | 4 | `CFS.TruncationBound`     | `sum_truncBits_error_double` | the APPROXIMATE reconstruction (each of the `|P|·ℓ` terms truncated to `f` bits) deviates by `< |P|·ℓ · 2^{-f}` (eq:modevbound — the `ℓ` is the residue bit-width, `|P|` the prime count). |
  | 5 | `CFS.ModularDeviation`    | `modDev_triangle`, `modDev_chain` | the paper's deviation metric `Δ_N` (line 299) is a pseudometric whose value is `0 ↔ ≡ mod N`, and it ACCUMULATES LINEARLY over a chain of operations (line 311). |

  Together: carry the modexp product componentwise in the residue domain over `P` (layer 2),
  reconstruct `V mod L` exactly and reduce mod `N` to get `g^e mod N` (layers 1+3), at a cost made
  cheap by truncating the reconstruction with a deviation that is proven small (layer 4) in a metric
  that is proven to accumulate only linearly (layer 5).

  ## HONEST remaining semantic gaps (documented, NOT faked)

  - The explicit CRT basis `uⱼ = (L/pⱼ)·MultInv_{pⱼ}(L/pⱼ)` is taken via its defining property
    `uⱼ mod pᵢ = δᵢⱼ` (a hypothesis of `reconstruction`); constructing it from modular inverses is
    classical precomputation.  (Was mislabelled "fractional CRT" — it is the EXACT integer CRT, now
    proved in layer 3.)
  - The bridge from the real-valued truncation bound (layer 4) to the integer `Δ_N` metric
    (layer 5): layer 4 bounds `∑ truncated − ∑ exact < |P|·ℓ·2^{-f}` in ℝ; layer 5 supplies the
    metric and its linear accumulation.  Fusing them into a single `Δ_N(V − Ṽ≪t) ≤ |P|·ℓ·2^{-f}`
    statement over the paper's exact `(N ≫ t)` integer truncation model is the next step.
  - The chain deviation → "good shot" probability → Ekerå–Håstad post-processing → success.
  - The quantum-circuit semantics of the reversible residue multiplications.
  - **Assumption 1** (main.tex line 346): a prime set `P` with `∏P ≥ N^m` and `Δ_N(∏P) < 2^{-f}`
    exists / is findable in `O(2^f·poly)` time.  This is the paper's own CONJECTURE — a genuine
    axiom, never asserted in these files.
-/
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Shor.CFS.Reconstruction
import FormalRV.Shor.CFS.TruncationBound
import FormalRV.Shor.CFS.ModularDeviation
import FormalRV.Shor.CFS.Assumptions
