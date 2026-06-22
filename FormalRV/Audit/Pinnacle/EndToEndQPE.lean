/-
  Audit · webster-2026 "The Pinnacle Architecture" (arXiv:2602.11457) · END-TO-END QPE / ORDER-FINDING
  ════════════════════════════════════════════════════════════════════════════
  The directive: a Shor-paper audit is NOT arithmetic counting — it is the FULL end-to-end
  order-finding/QPE circuit's logical content, carrying BOTH semantic correctness AND a rigorous
  resource count on the SAME arithmetic object.  This file delivers that for Pinnacle.

  Pinnacle's logical algorithm IS Gidney-2025 = Ekerå–Håstad short discrete log + Chevignard residue
  (RNS) modular arithmetic.  The verified vehicle is the CFS engine's CONCRETE residue circuit
  `residueFold` (|P| base-disjoint per-prime in-place windowed modular-multiplier chains) — this is
  the RNS MODULAR-EXPONENTIATION the QPE period-finds; the surrounding QPE wrap (Hadamard init +
  controlled-power structure + inverse-QFT + measurement) is Clifford+small, contributes ZERO Toffoli,
  and is NOT part of this object.  We compose:

    (1),(2),(4)  CIRCUIT-DERIVED SEMANTIC + FACTORING SPINE (`cfs_correctness_capstone`, sharing
             `g,N,d,p,q` with the `residueFold` run):
             (1) `residueFold` on the clean encoded `globalInput`, read out + CRT-reconstructed with
                 `crtBasis`, reduced mod `N`, computes exactly `g^e mod N`;
             (2) the recovered short dlog `d = p+q-2` is the dlog of `g^{N-1}` in the SAME group;
             (4) the factors fall out of `(d, N)`.
    (3)      CARRIED-WITNESS SUCCESS BOUND (NOT circuit-derived): single-run dlog recovery succeeds
             with prob `≥ ekeraGoodFactor·ekeraBalancedFactor` (Ekerå 2023 Thm 1).  This is a TRUE
             bound on the carried abstract `EkeraDLPSuccess` witness `S` — `S` is NOT tied by a binder
             to `residueFold`/`(g,N,e,d)`; the spine→success link is the unbuilt QPE measurement law
             (see QUANTUM SEAM below).  So the chain "circuit → dlog" is circuit-derived, but
             "→ success" rests on the carried witness, not on this gate.
    (5)      RESOURCE, on the SAME gate (`residueFold_toffoli`): the assembled RNS-MODEXP Toffoli count
             `= numP · (m · numWin · (16·w·2^w + 16·bits))`, counted by the tree-walk counter on the
             actual `Gate` — not a paper literal.  (Toffoli-only: the QFT⁻¹/QPE Cliffords add none.)
    (6)      PINNACLE'S OWN ALGORITHM-LEVEL NOVELTY (`parallelReduction_eq_serial`, paper Eq.20): the
             ρ-way binary-tree parallel accumulator reduction equals the serial accumulation.  This is
             an ABSTRACT accumulator identity (over free `s,chunk,ρ`), NOT a property of `residueFold`;
             it certifies the scheduling generalisation is value-invariant.

  ── HONEST SEAMS the composition forces (the structural points the paper glosses) ──
  • COST MODEL: conjunct (5) is the count of the CFS *reversible* windowed multiplier
    (`16·w·2^w + 16·bits` Toffoli per window-pass).  Pinnacle/Gidney use *measured* (Gidney) adders,
    which HALVE the per-adder Toffoli count (`Arithmetic.MeasuredAdder.gidneyAdderMeasured_halves`);
    the paper-faithful per-subroutine MEASURED counts (Table V addition/lookup) are anchored, with
    their honest our-side over-counts, in `L2_ArithmeticFaithful` (`pinnacle_addition_toffoli`,
    `pinnacle_lookup_toffoli`).  So (5) is an EXACT-for-construction count on the verified SEMANTIC
    object and a faithful UPPER bound on the measured target — the two are value-equal circuits with
    different cost models, a seam the paper conflates by citing Gidney's measured counts for an
    abstractly-specified RNS modexp.
  • QUANTUM SEAM: conjunct (3) is a TRUE proven bound on the abstract `EkeraDLPSuccess` witness; the
    spine→success link (this circuit's measurement statistics ⇒ that witness) is the carried QPE
    measurement law (the same seam standard Shor carries).  Made load-bearing on Assumption 1 in the
    `_under_rns_modulus` variant below.
  • DEVIATION: the parallel schedule's per-register *approximate* (truncated) accumulator is provably
    EQUAL to the serial truncated accumulator (`parApprAcc_eq_serial` — truncation commutes with adding
    `2^t`-multiples), so the verified serial deviation bound transfers verbatim
    (`parallelSchedule_apprAcc_modDev`); see `ParallelReduction`.
-/
import FormalRV.Shor.CFS.Capstone
import FormalRV.Shor.CFS.ResidueFold
import FormalRV.Audit.Pinnacle.ParallelReduction

namespace FormalRV.Audit.Pinnacle

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.CFS
open FormalRV.Shor.WindowedCircuit
open FormalRV.Audit.Pinnacle.ParallelReduction

/-- **PINNACLE END-TO-END QPE / ORDER-FINDING CAPSTONE.**  ONE composed object (`residueFold`) carries
    the full Pinnacle logical algorithm: the RNS modular-exponentiation the QPE period-finds is
    SEMANTICALLY correct on the actual `Gate` (computes `g^e mod N` → short dlog → success → factors),
    the assembled whole-circuit Toffoli count is proven on the SAME gate, and Pinnacle's parallel
    binary-tree reduction (its only new logical-algorithm content) is value-invariant (Eq.20).

    Carried (genuine preconditions, none the conclusion): the per-prime residue contract `hPok`, the
    coprimality `hco` + product bound `hL` (the constructible half of Assumption 1), and the
    `EkeraDLPSuccess` quantum witness `S`.  See `cfs_correctness_capstone`. -/
theorem pinnacle_modexp_endToEnd
    (P : Nat → Nat) (ainvss : Nat → Nat → Nat) (numP w bits numWin g N e m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hL : N ^ m ≤ ∏ i : Fin numP, P i.val)
    (S : EkeraDLPSuccess)
    (p q d : Nat) (hd : d = p + q - 2) (hNpq : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q])
    (s : Nat → Nat) (chunk ρ : Nat) :
    -- (1) ARITHMETIC: the concrete `residueFold` circuit computes `g^e mod N` (CRT-reconstructed)
    ((∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
      = g ^ e % N)
    -- (2) DLOG LINK
    ∧ (g ^ d ≡ g ^ (N - 1) [MOD N])
    -- (3) SUCCESS (carried quantum seam)
    ∧ (ekeraGoodFactor S.τ * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb)
    -- (4) RECOVERY
    ∧ (p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p)
    -- (5) RESOURCE: the assembled RNS-MODEXP Toffoli count on the SAME `residueFold` gate
    --     (Toffoli-only; the QFT⁻¹/QPE wrap is Clifford and adds none)
    ∧ (toffoliCount (residueFold P ainvss numP w bits numWin g N e m)
        = numP * (m * numWin * (16 * w * 2 ^ w + 16 * bits)))
    -- (6) PINNACLE PARALLELISM (ABSTRACT identity, not on the gate): the ρ-way binary-tree
    --     reduction = serial accumulation (Eq.20) — the scheduling generalisation is value-invariant
    ∧ (parAcc s chunk ρ = exactAcc s (ρ * chunk)) := by
  obtain ⟨h1, h2, h3, h4⟩ := cfs_correctness_capstone P ainvss numP w bits numWin g N e m
    hw hbits hPok hN hm he hco hL S p q d hd hNpq hp hq hphi
  exact ⟨h1, h2, h3, h4, residueFold_toffoli P ainvss numP w bits numWin g N e m,
    parallelReduction_eq_serial s chunk ρ⟩

end FormalRV.Audit.Pinnacle
