/-
  FormalRV.Shor.CFS — SEMANTIC foundation of the Chevignard–Fouque–Schrottenloher approximate-
  residue-arithmetic factoring algorithm (the arithmetic engine of Gidney 2025, arXiv:2505.15917).

  ## Why this exists ("semantic proof BEFORE resource proof", John 2026-06-03)

  The Gidney-2025 corpus entry (`FormalRV.Corpus.Gidney2025`) tallies the paper's resource numbers.
  Those numbers are only meaningful if the underlying algorithm actually computes `g^e mod N`.  This
  directory proves the arithmetic core of that algorithm, bottom-up, each layer `#verify_clean`
  (axiom-clean, no `sorry`):

  | layer | file | result | meaning |
  |---|---|---|---|
  | 1 | `CFS.ResidueArith`        | `residue_modexp_exact_of_lt` | residue modexp is EXACT: `(∏ M_k^{e_k}) % L % N = g^e mod N` when `L ≥ N^m` (no wraparound) |
  | 2 | `CFS.ResidueNumberSystem` | `rns_faithful` / `rns_recover` | the residue-number-system representation over the prime set `P` (`∏P = L`) is FAITHFUL (CRT injectivity): the residue vector determines `V mod L` |
  | 3 | `CFS.TruncationBound`     | `sum_truncBits_error` | the APPROXIMATE reconstruction (each fractional term truncated to `f` bits) deviates from the exact value by `< |P|·2^{-f}` (the `2^{-f}` scaling of eq:modevbound) |

  Together: carry the modexp product componentwise in the residue domain over `P` (layer 2),
  reconstruct `V mod L` and reduce mod `N` to get `g^e mod N` exactly (layer 1), at a cost made cheap
  by truncating the reconstruction with a controlled, proven deviation (layer 3).

  ## HONEST remaining semantic gaps (documented, NOT faked)

  - The exact fractional-CRT identity `V/L = ∑_j a_j y_j / p_j (mod 1)` that layer 3's terms
    truncate (needs the modular inverses `y_j = (L/p_j)⁻¹ mod p_j`).
  - The bit-width factor `ℓ` in the paper's full bound `Δ_N ≤ |P|·ℓ·2^{-f}`.
  - The chain deviation → "good shot" probability → Ekerå–Håstad post-processing → success.
  - The quantum-circuit semantics of the reversible residue multiplications.
  - Assumption 1 (a prime set `P` with `∏P ≥ N^m` and small modular deviation EXISTS) is a genuine
    CONJECTURE — an honest axiom, never asserted in these files.
-/
import FormalRV.Shor.CFS.ResidueArith
import FormalRV.Shor.CFS.ResidueNumberSystem
import FormalRV.Shor.CFS.TruncationBound
