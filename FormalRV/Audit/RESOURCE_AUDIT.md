# Resource-Equation Audit — reported vs verified, with gaps

Cross-paper consolidation of the **logical-level** resource audit (T / Toffoli / CNOT /
logical qubits / depth / deviation). Each row is a paper *equation or quantity*, the
paper's value, the **verified FormalRV object**, the audit result, and the gap.

**The project rule.** A count difference between us and a paper is a finding *about the
paper* **only if we faithfully implement the same gadget**. Reversible-vs-measured,
single-pass-vs-word-sliced, no-top-carry-shave, etc. are **our** modeling artifacts, not
paper errors. Below, `FAITHFUL` = our verified gadget matches the paper's count (on a
value-correct circuit); `OURS +k` = we over-count by `k` because our gadget is less
optimal (not a paper error); `PAPER ERROR` = the paper's own equation is internally wrong.

---

## ⚠️ Genuine paper arithmetic errors

**MACHINE-CHECKED** (a `decide`/`native_decide` refutation on named paper-claim constants — the only
`✅`-grade announceable errors):

| Paper | Equation | Paper says | Correct | How found |
|---|---|---|---|---|
| **Cain–Xu 2026** | E10 `τ_Toff` (RSA, space-eff) | `0.5·25 + 0.5·71 ≈ 43 τ_s` | **`= 48 τ_s`** (11.6% low) | `decide`-refuted, `PaperClaims.lean` (`example`, "The E10 refutation") |

**PROSE OBSERVATIONS** (un-formalized — NOT machine-checked; a reader should treat these as
narrative findings, not `decide`-grade proofs):

| Paper | Equation | Paper says | Correct | How found |
|---|---|---|---|---|
| **Cain–Xu 2026** | E7/E9 lookup split | `⌈q_w/(k_p−3)⌉` (prose) **vs** `⌈q_w/(k_p−1)⌉` (Eq E9) | `k_p−3` (geometry) | self-contradiction — **prose only, no `decide`** |
| **GE2021** | l.712 per-lookup term | `2^{g_exp+g_pad}` | **`2^{g_exp+g_mul}=2^10`** | typo; our model uses the fix — **prose only** |
| **Gidney 2025** | — | (none in the verified simple form) | | |
| **Pinnacle** | — | (none) | | |

---

## GE2021 (1905.09749) — windowed modexp + Zalka coset + oblivious runway

| Quantity / equation | Paper | Verified object | Result | Gap |
|---|---|---|---|---|
| `perLookupToffoli` | `2n + n·g_pad/g_sep + 2^{g+g}` | `toffoli_babbushLookupAddAt = (2^w−1)+2·bits` | STRUCTURAL | runway term `n·g_pad/g_sep` unmodeled (+86/lookup) + lookup +1 |
| Cuccaro add | `2n` | `tcount_cuccaro… = 14n = 2n` | **FAITHFUL** | — |
| single lookup | `2^{g+g}` | `toffoli_unaryQROMAt = 2^w−1` | OFF +1 | paper rounds the root AND up |
| `LookupAdditionCount` | `(2n·n_e)/(g_e·g_m)·(g_s+1)/g_s` | `lookupAdditionCount = 41/512·n·n_e = 503808` | **FAITHFUL** | leading form exact |
| `ToffoliCount` | `503808·5206 = 2.62e9` | circuit `modExpAt = 2,578,993,152` | MODEL | gap `43,831,296 = 503808·(1+86)` |
| Table-1 ceiling | `2.7e9` | ≥ formula 2.62e9 & circuit 2.58e9 | sound ceiling | +2.94% over formula |
| logical qubits | `6189` / `6200` | circuit `6162` (+27 coset, +11 abstract) | MODEL | +27 / +38 |
| `TotalDeviation` | `≈10⁻⁷` | `41/536870912 ≈ 7.64e-8` | ROUNDING | ours tighter |
| meas. depth | `500n²+n²lgn` | `≈371n²+0.72n²lgn` | bound holds | abstract over-states |

---

## Cain–Xu 2026 (2603.28627) — qLDPC; imports Gidney/Babbush arithmetic

Faithful re-audit: `Audit/CainXu2026/L2_ArithmeticFaithful.lean` (on the verified **measured** gadgets).

| Equation | Paper | Verified object | Result | Gap |
|---|---|---|---|---|
| E3 adder | `25 q_A τ_s`; `n` Toffoli | `toffoli_gidneyAdderMeasured = n` (value `a+b`) | **FAITHFUL** | — |
| E4 ctrl-adder | `30 q_A τ_s`; `2n` Toffoli | `toffoli_gidneyAdderMeasuredControlled = 2n` | **FAITHFUL** | exactly 2× (`_doubles`) |
| E9 lookup | `2^q_a` Toffoli; `~71 τ_s` | `toffoli_unaryQROMAt = 2^q_a−1` | FAITHFUL +1 | paper rounds root AND |
| E10 `τ_Toff` | `≈43 τ_s` | `0.5·25+0.5·71 = 48` | **PAPER ERROR** | 11.6% low |
| E7/E9 split | `k_p−3` vs `k_p−1` | — | **PAPER ERROR** | self-contradiction |
| E11 (RSA bal.) | `≈10 τ_s` | `0.5·13+0.5·7 = 10` | MATCH | — |

*The earlier "factor-2" (adder, lookup) was **ours** (reversible vs measured) — now closed.*

---

## Pinnacle (2602.11457) — qLDPC; logical arithmetic = Gidney 2025

`Audit/Pinnacle/L2_Arithmetic.lean` (CFS engine) + `ParallelReduction.lean` + `L2_ArithmeticFaithful.lean`.

| Equation | Paper | Verified object | Result | Gap |
|---|---|---|---|---|
| Addition | `g2025_add = n−1` | `toffoli_gidneyAdderMeasured = n` | OURS +1 | top carry we don't shave |
| Lookup | `2^w−w−1` | `toffoli_unaryQROMAt = 2^w−1` | OURS +w | cascade fold we don't do |
| **Parallel reduction (Eq.20)** | binary tree = serial sum | `parallelReduction_eq_serial` | **PROVEN** | — (Pinnacle-specific) |
| `T = 4·Toffoli` | CCZ-magic | compare via `toffoliCount` | CONVENTION | gate model (ours 7-T) |
| Phaseup | `√(2^w)` SELECT-SWAP | `SplitPhaseFixup` (partial) | PARTIAL | shared Gidney 2025 |
| `ρ≥200` threshold | for `w₁=6` | needs `ρ≥160` at `w₁=8` | wrinkle | parameter carryover |

---

## Gidney 2025 (2505.15917) — CFS approximate-residue arithmetic (NOT windowed modexp)

`Shor/CFS/` (11 modules) verifies the **simple residue form** end-to-end. The
**optimized** algorithm (whose `6.5e9`-Toffoli / `<1M`-qubit numbers are the headline)
needs three gadgets we don't yet have.

| Piece | Paper | Verified object | Result | Gap |
|---|---|---|---|---|
| RNS modexp (no wrap) | residue product | `residue_modexp_exact_of_lt` | **VERIFIED** | — |
| RNS faithfulness | CRT injective | `rns_faithful` | **VERIFIED** | — |
| CRT reconstruction | `Σ r_j u_j` | `reconstruction_explicit` | **VERIFIED** | — |
| Truncation deviation | `\|P\|·ℓ·2^{-f}` | `modDev_truncAcc_normalized` | **VERIFIED** | — |
| Approx. periodicity | `Δ_N ≤ 2ε` | `approx_periodic` | **VERIFIED** | — |
| Ekerå–Håstad recovery | `d = p+q−2` | `ekera_hastad_recovery` | **VERIFIED** | — |
| **dlog reduction** | `S_p = Σ D_{p,k}·e_k → V_p = g_p^{S_p} mod p` | `dlog_reduction_eq_residueAccumulate` (`CFS/DiscreteLogReduction.lean`) | ◑ VALUE-level CLOSED | the optimized arithmetic's defining step is proven EQUAL to the verified residue accumulate at the Nat/ZMod value level; CIRCUIT-level (a single Gate of the addition form with its own count) still ⬜ GAP |
| **PHASEUP** | Berry `√(2^w)` amplitude negation | **MISSING** | ⬜ GAP | unmodeled (shared w/ Pinnacle) |
| **2.5n modular adder** | subtract-with-underflow + lookup fixup | have the wrong 5× construction | ⬜ GAP | mechanism + cost mismatch |
| `6.5e9` Toffoli total | grid-scan output | not derived from per-gadget × iterations | ⬜ GAP | needs the 3 above |

**The verification status of Gidney 2025:** the *logical residue semantics* is proven
(the simple algorithm is end-to-end axiom-clean). The *optimized* algorithm — the one the
paper actually costs — is blocked on the three gadgets above, in priority order:
1. **discrete-log reduction** (highest leverage; pure `Nat`/`ZMod`, bridges optimized→verified semantics),
2. **PHASEUP** (a new `Arithmetic/` primitive),
3. **the 2.5n modular adder** (now plausibly buildable from the verified measured adder + a lookup fixup).
