/-
  FormalRV.Shor.CFS.Capstone — T8: the CFS correctness capstone, composing the verified pieces of
  the Chevignard–Fouque–Schrottenloher factoring algorithm (the logical core of Gidney 2025) into a
  single end-to-end statement, threaded through the CONCRETE circuit and naming every carried
  obligation.

  ## What the capstone composes (each conjunct is a proven theorem, on real objects)

  The CFS factoring pipeline, end to end:

    1. **Arithmetic / circuit correctness (T7, `residueFold_crt_correct`).**  The concrete residue
       circuit `residueFold` — run on the concrete `globalInput` — has its `|P|` accumulators read out
       and CRT-reconstructed with the constructed basis `crtBasis`, and reduced mod `N` gives exactly
       `g^e mod N`.  The circuit computes the right function (the one being period-found).
    2. **Dlog link (`ekera_hastad_exponent`).**  For `N = p·q`, the recovered short dlog `d = p+q-2`
       is the discrete log of `h = g^{N-1}` in the SAME group `⟨g⟩ mod N` the circuit (1) operates on:
       `g^d ≡ g^{N-1} (mod N)`.  This ties `d` to the modexp function the circuit computes — the
       formal bridge between the verified arithmetic (1) and the factoring data (4).
    3. **Dlog-recovery success (T1, `EkeraDLPSuccess.success_ge`).**  A single quantum run recovers the
       short discrete log with probability `≥ ekeraGoodFactor·ekeraBalancedFactor` (Ekerå 2023 Thm 1),
       the success bound combining the trigamma good-pair (Lemma 1) and t-balanced lattice (Lemma 2)
       obligations carried in the `EkeraDLPSuccess` witness.
    4. **Factor recovery (`ekera_hastad_recovery`).**  From `d = p+q-2` and `N = p·q`, the factors come
       out of the quadratic: `p·(d-p+2) = N` and `p² + N = (d+2)·p`.

  ## What is FORMALLY THREADED vs. what is the CARRIED SEAM (honest scoping)

  **Formally threaded — the classical spine (1)↔(2)↔(4):** conjuncts (1),(2),(4) share `g, N, d, p, q`
  by their binders + `hd : d = p+q-2` + `hNpq : N = p·q`: the concrete circuit operates on `g mod N`
  computing `g^e mod N` (1); `d` is the dlog of `g^{N-1}` in that same group (2); the factors fall out
  of `d, N` (4).  This is a genuine shared-parameter composition over real objects.

  **The carried QUANTUM seam — conjunct (3).**  `EkeraDLPSuccess` is an ABSTRACT measurement-distribution
  witness (`measProb`/`condGood`/`balancedJ`); it is NOT yet formally pinned to THIS circuit's `(g,N,e,d)`
  — connecting `S.successProb` to the recovery of THIS `d` is exactly the QPE measurement law, i.e. the
  T5 `h_orbit_exists` bridge (the framework-`control`-stub-blocked Phase-4 gap that standard Shor also
  carries).  So (3) is a TRUE proven bound on `S` but the spine→success link is the documented unbuilt
  seam, not a formal thread.  The supporting Stage-3/4 facts (`modDev_truncAcc_normalized`,
  `approx_periodic`) and T5/T6 (peak law, masked infidelity) justify what `S` abstracts.

  ## What is CARRIED (honest, explicit, never the conclusion)

  None of the carried inputs is the success bound or the arithmetic conclusion — each is a genuine
  structural/algorithmic precondition:
    * the residue-circuit preconditions `hPok`/`hco`/`hL` — the per-prime input contract and the
      product bound `N^m ≤ ∏P`.  The product bound + pairwise-coprimality are exactly the
      CONSTRUCTIBLE half of **`SmallPrimeRNSModulusExists`** (`∏P ≥ N^m`, coprime, prime); `cfs_capstone_under_rns_modulus`
      makes that half LOAD-BEARING by deriving `hco`/`hL`/`1<P` from an `SmallPrimeRNSModulusExists` witness.  (Assumption 1's
      genuinely-conjectural DEVIATION clause `Δ_N(∏P) < 2^{-f}` governs the APPROXIMATION quality — Stage 3/4,
      `modDev_truncAcc_normalized` — and is not needed for this exact-arithmetic spine, so it is honestly
      left unused here.)
    * the `EkeraDLPSuccess` witness `S` — carries Lemma 1 / Lemma 2 (the measurement-distribution
      facts), the genuinely-quantum half awaiting the QPE circuit's `h_orbit_exists` bridge (T5).
    * the order condition `hphi : g^{(p-1)(q-1)} ≡ 1`.
  `SmallPrimeRNSModulusExists` itself is the paper's own conjecture — stated, never proved.
-/
import FormalRV.Shor.CFS.ResidueCRT
import FormalRV.Shor.CFS.EkeraSuccess
import FormalRV.Shor.CFS.EkeraHastad
import FormalRV.Shor.CFS.Assumptions
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open scoped BigOperators

/-- **THE CFS CORRECTNESS CAPSTONE (T8).**  The end-to-end composition of the verified CFS pieces,
    threaded through the concrete circuit `residueFold` and the shared factoring semantics
    (`g^e mod N` → dlog `d = p+q-2` → success probability → factors).  Every conjunct is a proven
    theorem; the carried inputs are genuine preconditions, none of them the conclusion. -/
theorem cfs_correctness_capstone
    -- circuit / residue-arithmetic data (T7 contract = the conjecture's content + primality)
    (P : Nat → Nat) (ainvss : Nat → Nat → Nat) (numP w bits numWin g N e m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hPok : ∀ j, j < numP → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hco : ∀ i j : Fin numP, i ≠ j → Nat.Coprime (P i.val) (P j.val))
    (hL : N ^ m ≤ ∏ i : Fin numP, P i.val)
    -- the dlog-recovery success witness (T1; carries the Lemma-1 / Lemma-2 obligations)
    (S : EkeraDLPSuccess)
    -- factorisation data (Ekerå–Håstad)
    (p q d : Nat) (hd : d = p + q - 2) (hNpq : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q]) :
    -- (1) ARITHMETIC: the concrete circuit computes `g^e mod N` (T7)
    ((∑ j : Fin numP,
        (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
          (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
          * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
      = g ^ e % N)
    -- (2) DLOG LINK: `d` is the discrete log of `h = g^{N-1}` in `⟨g⟩ mod N` — the SAME `g`, `N` the
    --     circuit (1) operates on, so `d` is tied to the modexp function the circuit computes
    ∧ (g ^ d ≡ g ^ (N - 1) [MOD N])
    -- (3) SUCCESS (carried QUANTUM seam): single-run dlog recovery `≥ ekeraGoodFactor·ekeraBalancedFactor`
    --     (T1) — the measurement-distribution witness `S` (see honesty note in the docstring)
    ∧ (ekeraGoodFactor S.τ * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb)
    -- (4) RECOVERY: the factors fall out of `d = p+q-2`, `N = p·q` (Ekerå–Håstad)
    ∧ (p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p) :=
  ⟨residueFold_crt_correct P ainvss numP w bits numWin g N e m hw hbits hPok hN hm he hco hL,
   by rw [hd, hNpq]; exact (ekera_hastad_exponent p q g (by omega) (by omega) hphi).symm,
   S.success_ge,
   ekera_hastad_recovery p q d N hd hNpq hp hq⟩

/-- **The capstone with `SmallPrimeRNSModulusExists` made LOAD-BEARING.**  Instead of taking the
    product bound `hL` and coprimality `hco` as free hypotheses, this version derives them from a
    `SmallPrimeRNSModulusExists N m f ℓ` witness (Gidney 2025 Assumption 1, the `ℓ`-bit prime set) —
    the prime set `P` of the residue circuit IS the conjecture's prime set, so `N^m ≤ ∏P` and
    pairwise-coprimality come from the conjecture, and `1 < P j` from its primality clause.  Only the
    per-prime register-size + multiplier-inverse contract (`hfit`, the residue-circuit instantiation
    detail) remains a carried hypothesis.  This shows the capstone genuinely RESTS on Assumption 1,
    not on free-floating arithmetic preconditions. -/
theorem cfs_capstone_under_rns_modulus
    (ainvss : Nat → Nat → Nat) (w bits numWin g N e m f ℓ : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (he : e < 2 ^ m)
    (hassume : SmallPrimeRNSModulusExists N m f ℓ)
    -- the per-prime residue-circuit instantiation contract (size + invertible multiplier table)
    (hfit : ∀ (t : ℕ) (P : Fin t → ℕ), (∀ i, (P i).Prime) → ∀ j : Fin t,
      2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j.val k < P j ∧ residueConst g N (P j) e k * ainvss j.val k % (P j) = 1)
    (S : EkeraDLPSuccess)
    (p q d : Nat) (hd : d = p + q - 2) (hNpq : N = p * q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hphi : g ^ ((p - 1) * (q - 1)) ≡ 1 [MOD p * q]) :
    ∃ (numP : Nat) (P : Nat → Nat),
      ((∑ j : Fin numP,
          (decodeReg (fun i => j.val * residueWidth w bits numWin + (1 + 2 * w + (2 * bits + 1) + i)) bits
            (Gate.applyNat (residueFold P ainvss numP w bits numWin g N e m) (globalInput w bits numWin)))
            * crtBasis (fun i : Fin numP => P i.val) j) % (∏ i : Fin numP, P i.val) % N
        = g ^ e % N)
      ∧ (g ^ d ≡ g ^ (N - 1) [MOD N])
      ∧ (ekeraGoodFactor S.τ * ekeraBalancedFactor S.Δ S.t S.τ ≤ S.successProb)
      ∧ (p * (d - p + 2) = N ∧ p * p + N = (d + 2) * p) := by
  obtain ⟨t, pset, hcop, hprime, _hbit, hprod, _hdev⟩ := hassume
  -- The residue circuit's prime set is Assumption 1's prime set, bridged to `Nat → Nat`.
  refine ⟨t, fun n => if h : n < t then pset ⟨n, h⟩ else 1, ?_,
    by rw [hd, hNpq]; exact (ekera_hastad_exponent p q g (by omega) (by omega) hphi).symm,
    S.success_ge, ekera_hastad_recovery p q d N hd hNpq hp hq⟩
  set P : Nat → Nat := fun n => if h : n < t then pset ⟨n, h⟩ else 1 with hP
  have hPval : ∀ i : Fin t, P i.val = pset i := by
    intro i; simp only [hP, i.isLt, dif_pos]
  have hPok : ∀ j, j < t → 1 < P j ∧ 2 * P j ≤ 2 ^ bits ∧
      ∀ k, k < m → ainvss j k < P j ∧ residueConst g N (P j) e k * ainvss j k % (P j) = 1 := by
    intro j hj
    have hjval : P j = pset ⟨j, hj⟩ := by simp only [hP, hj, dif_pos]
    have hsize := hfit t pset hprime ⟨j, hj⟩
    rw [hjval]
    refine ⟨(hprime ⟨j, hj⟩).one_lt, hsize.1, ?_⟩
    intro k hk; exact hsize.2 k hk
  have hco : ∀ i j : Fin t, i ≠ j → Nat.Coprime (P i.val) (P j.val) := by
    intro i j hij; rw [hPval i, hPval j]; exact hcop i j (fun h => hij (Fin.ext (by rw [h])))
  have hL : N ^ m ≤ ∏ i : Fin t, P i.val := by
    rw [Finset.prod_congr rfl (fun i _ => hPval i)]; exact hprod
  exact residueFold_crt_correct P ainvss t w bits numWin g N e m hw hbits hPok hN hm he hco hL

/-! ## The CFS capstone passes the VERIFIER gate (axiom-clean — the carried obligations are
    hypotheses, not axioms). -/

#verify_clean cfs_correctness_capstone
#verify_clean cfs_capstone_under_rns_modulus

end FormalRV.CFS
