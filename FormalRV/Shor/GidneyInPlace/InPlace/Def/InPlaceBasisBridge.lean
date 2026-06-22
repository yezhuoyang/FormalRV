/-
  FormalRV.Shor.GidneyInPlace.InPlaceBasisBridge
  ──────────────────────────────────────────────────
  BRICK 8 of the two-register in-place coset-multiplier DYNAMICS transport: the
  OFF-BAD ⇒ BASIS-HYPOTHESES bridge — the last delicate step before the coset sum.

  `gidneyTwoRegInPlace_coset_basis_good_branch` (the per-branch basis correctness)
  consumes three hypotheses about the RAW running sums:
    Σ1 := ∑ j<numWin, TfamK    j (window w x j)            -- pass-1 raw sum
    P1 := Σ1 % 2^bits                                       -- pass-1 register value
    Σ2 := ∑ k'<numWin, TfamKinv k' (window w P1 k')         -- pass-2 raw sum
    • hP1       : Σ1 % 2^bits = (k·x) % N                    -- pass-1 register canonical
    • hS2N      : Σ2 % N      = (kInv·P1) % N                -- pass-2 mod-N identity
    • hS2nowrap : Σ2 % 2^bits = Σ2 % N                       -- pass-2 NO-WRAP
  This file proves them from explicit NO-OVERFLOW hypotheses.

  ════════════════════════════════════════════════════════════════════════════
  THE TRAP (the whole point of this brick).  `hS2nowrap : Σ2 % 2^bits = Σ2 % N`.
  With `Σ2 < 2^bits` the LHS is just `Σ2` — but `Σ2 % N ≤ Σ2`, with EQUALITY only when
  `Σ2 < N`.  So `Σ2 < 2^bits` ALONE does NOT give `hS2nowrap`; you need CANONICALITY
  BELOW N (`Σ2 < N`).  `nowrap_of_lt_N` makes this explicit: it requires `S < N`, not
  `S < 2^bits`.  Likewise `hP1` requires `Σ1 < N`.  `hS2N` is the only UNCONDITIONAL
  one (the mod-N identity, reused from Brick 6's `endpoint_residue_modN`).

  WHICH "off-bad" is this?  The VALUE-LEVEL no-overflow `Σ < N` (the running sum stays
  canonical, `q = 0` wraps) — i.e. off the OVERFLOW bad set `{Σ ≥ N}`.  This is a
  DIFFERENT notion from the cosetState symmetric-difference band
  (`cosetState_windowedMul_embed_off`), which ABSORBS wraps `q ≥ 1` via the coset
  window.  Consequently the basis route (`good_branch`) covers ONLY the no-overflow
  (`q = 0`) branches; the general wrapping case is the COSET route (Bricks 4-7).  Since
  `Σ2 = runningSum` of `numWin` addends each `< N`, `Σ2 < numWin·N`, so `Σ2 < N` is a
  genuinely strong (small-`numWin`/no-wrap) condition — flagged, not papered over.

  Contents:
   • `nowrap_of_lt_N` — the canonicality bridge `S < N → S % 2^bits = S % N`
     (REQUIRES `S < N`; documents why `S < 2^bits` is insufficient).
   • `offBad_implies_basis_hyps` — `hP1 ∧ hS2N ∧ hS2nowrap`, from the no-overflow
     hypotheses `Σ1 < N`, `Σ2 < N` (plus the canonical table families + fits).
   • `good_branch_of_nowrap` — feeds those into `good_branch`: off-overflow ⇒ the full
     per-branch basis correctness (`a` clears, `b ← (k·x)%N`, scratch restored).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceEndpoint
import FormalRV.Shor.GidneyInPlace.InPlace.Def.GidneyTwoRegInPlace

namespace FormalRV.Shor.GidneyInPlace.InPlaceBasisBridge

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.GidneyInPlace.InPlaceEndpoint (endpoint_residue_modN)
open FormalRV.Shor.GidneyInPlace.ProductAddArith (RelocStepInv)
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  (gidneyTwoRegInPlaceCosetMul basisFinal0 gidneyTwoRegInPlace_coset_basis_good_branch)

/-! ## §1. The canonicality bridge (REQUIRES `S < N`, not merely `S < 2^bits`). -/

/-- **Canonicality bridge.**  `S % 2^bits = S % N` PROVIDED `S < N` (and `N ≤ 2^bits`):
    then `S % 2^bits = S` (since `S < N ≤ 2^bits`) and `S % N = S` (since `S < N`), so
    both equal `S`.

    ⚠️ The hypothesis is `S < N`, NOT `S < 2^bits`.  `S < 2^bits` alone gives only
    `S % 2^bits = S`; it does NOT give `S % 2^bits = S % N` unless `S` is already
    canonical below `N` (`S % N = S`, i.e. `S < N`).  This is the literal-register
    vs mod-`N` distinction the whole brick turns on. -/
theorem nowrap_of_lt_N (S N bits : Nat) (hSN : S < N) (hN2 : N ≤ 2 ^ bits) :
    S % 2 ^ bits = S % N := by
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hSN hN2), Nat.mod_eq_of_lt hSN]

/-! ## §2. Off-overflow ⇒ the three basis hypotheses. -/

/-- **The off-bad ⇒ basis-hypotheses bridge.**  Under the canonical table families and
    the NO-OVERFLOW conditions `Σ1 < N` (pass-1) and `Σ2 < N` (pass-2), the three
    hypotheses `good_branch` consumes hold:
      • `hP1` — from `Σ1 < N` + the pass-1 mod-N identity (`Σ1 ≡ (k·x) [MOD N]`);
      • `hS2N` — UNCONDITIONAL (Brick 6's `endpoint_residue_modN`);
      • `hS2nowrap` — from `Σ2 < N` via `nowrap_of_lt_N` (CANONICALITY BELOW N, not
        `Σ2 < 2^bits`).
    `hxFit`/`hP1Fit` are the windowing fits the mod-N identities need. -/
theorem offBad_implies_basis_hyps (w bits numWin N k kInv x : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hN : 0 < N) (hN2 : N ≤ 2 ^ bits)
    (hxFit : x < (2 ^ w) ^ numWin)
    (hP1Fit : (k * x) % N < (2 ^ w) ^ numWin)
    (hS1lt : (∑ j ∈ Finset.range numWin, TfamK j (window w x j)) < N)
    (hS2lt : (∑ k' ∈ Finset.range numWin, TfamKinv k' (window w
        ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits) k')) < N) :
    ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits = (k * x) % N)
    ∧ ((∑ k' ∈ Finset.range numWin, TfamKinv k' (window w
          ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits) k')) % N
        = (kInv * ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits)) % N)
    ∧ ((∑ k' ∈ Finset.range numWin, TfamKinv k' (window w
          ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits) k')) % 2 ^ bits
        = (∑ k' ∈ Finset.range numWin, TfamKinv k' (window w
          ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits) k')) % N) := by
  -- pass-1 mod-N identity (Brick 6), unconditional
  have hS1modN : (∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % N = (k * x) % N := by
    have h := endpoint_residue_modN k N w numWin x 0 TfamK hTfamK hN hxFit
    simpa using h
  -- hP1: Σ1 < N makes the register value canonical
  have hP1 : (∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits = (k * x) % N := by
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hS1lt hN2), ← hS1modN, Nat.mod_eq_of_lt hS1lt]
  -- the pass-2 input register value is canonical and fits the window bound
  have hP1Fit' : (∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits < (2 ^ w) ^ numWin := by
    rw [hP1]; exact hP1Fit
  refine ⟨hP1, ?_, ?_⟩
  · -- hS2N: unconditional mod-N identity (Brick 6)
    have h := endpoint_residue_modN kInv N w numWin
      ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits) 0 TfamKinv hTfamKinv hN hP1Fit'
    simpa using h
  · -- hS2nowrap: Σ2 < N (canonicality below N) — NOT from Σ2 < 2^bits
    exact nowrap_of_lt_N _ N bits hS2lt hN2

/-! ## §3. Off-overflow ⇒ the full per-branch basis correctness. -/

/-- **Off-overflow good branch.**  Feeding the §2 hypotheses into
    `gidneyTwoRegInPlace_coset_basis_good_branch`: on a no-overflow branch (`Σ1 < N`,
    `Σ2 < N`, canonical tables, `kInv·k ≡ 1`, `x < N`), the in-place gate maps the
    basis input to `basisFinal0` — register `a` clears, register `b` receives `(k·x)%N`,
    scratch restored.  This is the basis route's coverage: the NO-OVERFLOW branches
    only (the wrapping case is the coset route, Bricks 4-7). -/
theorem good_branch_of_nowrap (w bits numWin N k kInv x : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (g : Nat → Bool)
    (hg : RelocStepInv w bits numWin x (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) 0 g)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hN : 0 < N) (hN2 : N ≤ 2 ^ bits) (hxN : x < N)
    (hxFit : x < (2 ^ w) ^ numWin) (hP1Fit : (k * x) % N < (2 ^ w) ^ numWin)
    (hkkinv : (kInv * k) % N = 1 % N)
    (hS1lt : (∑ j ∈ Finset.range numWin, TfamK j (window w x j)) < N)
    (hS2lt : (∑ k' ∈ Finset.range numWin, TfamKinv k' (window w
        ((∑ j ∈ Finset.range numWin, TfamK j (window w x j)) % 2 ^ bits) k')) < N) :
    Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g
        = basisFinal0 w bits TfamK numWin g
    ∧ decodeReg (fun i => 1 + 2 * w + i) bits
        (Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g) = 0
    ∧ decodeReg (fun i => 1 + 2 * w + bits + i) bits
        (Gate.applyNat (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin) g)
        = (k * x) % N := by
  obtain ⟨hP1, hS2N, hS2nowrap⟩ := offBad_implies_basis_hyps w bits numWin N k kInv x
    TfamK TfamKinv hTfamK hTfamKinv hN hN2 hxFit hP1Fit hS1lt hS2lt
  exact gidneyTwoRegInPlace_coset_basis_good_branch w bits numWin N k kInv x TfamK TfamKinv
    hw hbits g hg hxN hP1 hS2N hS2nowrap hkkinv

end FormalRV.Shor.GidneyInPlace.InPlaceBasisBridge
