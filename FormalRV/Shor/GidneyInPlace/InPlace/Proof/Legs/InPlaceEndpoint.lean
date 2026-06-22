/-
  FormalRV.Shor.GidneyInPlace.InPlaceEndpoint
  ───────────────────────────────────────────────
  BRICK 6 of the two-register in-place coset-multiplier DYNAMICS transport: the
  product-add ENDPOINT off-bad — the FIRST place `% N` enters.

  Bricks 4-5 proved the register-arithmetic fold endpoint (the eGid branch value
  `(z + ∑ k<numWin, Tfam k (window w y k)) % 2^bits`).  Brick 6 interprets that endpoint
  as a coset RESIDUE: under the CANONICAL table family `Tfam k addr = tableValue K N w k
  addr`, the endpoint represents the residue `z + K·y mod N`, and — off the forward wrap
  band — its coset STATE agrees with the canonical residue's coset state.

  Strictly LOCAL (per directive): NOT the full coset-state / norm theorem.  The literal
  register-value identity is kept SEPARATE from the residue identity, and the off-bad
  agreement REUSES `CosetFoldWindowed.cosetState_windowedMul_embed_off` (not a new hand
  proof).  No reverse leg, no norm bound.

  Contents:
   • `runningSum_eq_sum` — `runningSum cs n = ∑ k ∈ Finset.range n, cs k` (the recursion
     ↔ Finset.sum bridge).
   • `canonicalSum_eq_runningSum` — LITERAL register value: under the canonical table
     family, `∑ k<numWin, Tfam k (window w y k) = runningSum (cosetWindowConst K N w y)
     numWin`.  (Table-family equality stated EXPLICITLY via `hTfam`.)
   • `endpoint_residue_modN` — RESIDUE (general `z`, UNCONDITIONAL `mod N`):
     `(z + ∑ …) % N = (z + K·y) % N`.  This is "represents the same residue mod N".
   • `endpoint_embed_off` — OFF-BAD coset-state agreement (fresh accumulator `z=0`),
     reusing `cosetState_windowedMul_embed_off`: ∃ a wrap band `B : Finset (Fin (2^bits))`
     (RAW branch indices) off which `cosetState (∑ …) = cosetState ((K·y) % N)`, with
     Born mass ≤ numWin/2^cm each side.
   • `pass1_endpoint_embed_off` (`K=k`, `y=a`, residue `(k·a) % N`) and
     `pass2_endpoint_embed_off` (`K=kInv`, `y=(k·x) % N`, residue `x` via `revCanonical_eq`)
     — the two passes' fresh-accumulator forward endpoints.

  AUDIT (per directive).  Table-family equality explicit (`hTfam`).  Literal value
  (`canonicalSum_eq_runningSum`) SEPARATE from residue (`endpoint_residue_modN`).
  Off-bad `B` is a `Finset (Fin (2^bits))` over RAW branch indices, NOT decoded residues.
  Reuses `cosetState_windowedMul_embed_off`.  No reverse leg, no norm bound.  The
  `z=x`-in-the-gate pass-2 framing (reverse leg) and the cosetState SUM are deferred.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Proof.CosetFoldWindowed
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Branch.InPlaceBadSet

namespace FormalRV.Shor.GidneyInPlace.InPlaceEndpoint

open FormalRV.SQIRPort
open FormalRV.Shor.WindowedArith (window tableValue)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState)
open FormalRV.Shor.GidneyInPlace.CosetMul (runningSum)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst idealAcc_cosetWindowConst)
open FormalRV.Shor.GidneyInPlace.CosetFoldWindowed (cosetState_windowedMul_embed_off idealAcc_modEq_runningSum)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)
open FormalRV.Shor.GidneyInPlace.InPlaceBadSet (revCanonical_eq)

/-! ## §1. The recursion ↔ Finset.sum bridge. -/

/-- `runningSum cs n = ∑ k ∈ Finset.range n, cs k` (the recursive accumulator IS the
    finite sum). -/
theorem runningSum_eq_sum (cs : Nat → Nat) (n : Nat) :
    runningSum cs n = ∑ k ∈ Finset.range n, cs k := by
  induction n with
  | zero => rfl
  | succ m ih =>
      show runningSum cs m + cs m = ∑ k ∈ Finset.range (m + 1), cs k
      rw [Finset.sum_range_succ, ih]

/-! ## §2. The literal register-value identity (table-family bridge). -/

/-- **LITERAL register value.**  Under the canonical table family `Tfam k addr =
    tableValue K N w k addr`, the eGid fold endpoint sum is exactly the coset
    `runningSum`.  No `mod N`, no coset state — purely the table-family substitution. -/
theorem canonicalSum_eq_runningSum (K N w numWin y : Nat) (Tfam : Nat → Nat → Nat)
    (hTfam : ∀ k addr, Tfam k addr = tableValue K N w k addr) :
    ∑ k ∈ Finset.range numWin, Tfam k (window w y k)
      = runningSum (cosetWindowConst K N w y) numWin := by
  rw [runningSum_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hTfam k (window w y k)]
  rfl

/-! ## §3. The residue identity (general `z`, unconditional `mod N`). -/

/-- **RESIDUE (general `z`).**  Under the canonical table family, the endpoint value
    represents the residue `z + K·y mod N`: `(z + ∑ …) % N = (z + K·y) % N`.
    UNCONDITIONAL — holds for ANY `z` (no off-bad needed at the residue level; the
    wrap band only matters for the coset-state agreement in §4). -/
theorem endpoint_residue_modN (K N w numWin y z : Nat) (Tfam : Nat → Nat → Nat)
    (hTfam : ∀ k addr, Tfam k addr = tableValue K N w k addr)
    (hN : 0 < N) (hy : y < (2 ^ w) ^ numWin) :
    (z + ∑ k ∈ Finset.range numWin, Tfam k (window w y k)) % N = (z + K * y) % N := by
  rw [canonicalSum_eq_runningSum K N w numWin y Tfam hTfam]
  have hrs : runningSum (cosetWindowConst K N w y) numWin % N = (K * y) % N := by
    rw [← idealAcc_modEq_runningSum N (cosetWindowConst K N w y) numWin,
        idealAcc_cosetWindowConst K N w numWin y hN hy]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hN)
  rw [Nat.add_mod z (runningSum (cosetWindowConst K N w y) numWin) N, hrs, ← Nat.add_mod]

/-! ## §4. The off-bad coset-state agreement (fresh accumulator `z=0`). -/

/-- **OFF-BAD endpoint (fresh accumulator).**  Under the canonical table family, the
    fresh-accumulator endpoint coset state `cosetState (∑ k<numWin, Tfam k (window w y k))`
    agrees with the canonical residue coset state `cosetState ((K·y) % N)` off a wrap band
    `B : Finset (Fin (2^bits))` (RAW branch indices), with Born mass ≤ numWin/2^cm each
    side.  This is `cosetState_windowedMul_embed_off` with the table-family substitution
    (§2) — NOT a new hand proof. -/
theorem endpoint_embed_off (bits N cm K w numWin y : Nat) (Tfam : Nat → Nat → Nat)
    (hTfam : ∀ k addr, Tfam k addr = tableValue K N w k addr)
    (hN : 0 < N) (hy : y < (2 ^ w) ^ numWin) :
    ∃ B : Finset (Fin (2 ^ bits)),
      (∀ i, i ∉ B →
        cosetState (2 ^ bits) N cm (∑ k ∈ Finset.range numWin, Tfam k (window w y k)) i 0
          = cosetState (2 ^ bits) N cm ((K * y) % N) i 0)
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm
          (∑ k ∈ Finset.range numWin, Tfam k (window w y k))) B ≤ (numWin : ℝ) / 2 ^ cm
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm ((K * y) % N)) B ≤ (numWin : ℝ) / 2 ^ cm := by
  rw [canonicalSum_eq_runningSum K N w numWin y Tfam hTfam]
  exact cosetState_windowedMul_embed_off (2 ^ bits) N cm K w numWin y hN hy

/-! ## §5. The two passes' fresh-accumulator forward endpoints. -/

/-- Pass 1 (`b += a·k`, fresh `b`): the forward endpoint represents residue `(k·a) % N`,
    off the wrap band. -/
theorem pass1_endpoint_embed_off (bits N cm k w numWin a : Nat) (Tfam : Nat → Nat → Nat)
    (hTfam : ∀ j addr, Tfam j addr = tableValue k N w j addr)
    (hN : 0 < N) (ha : a < (2 ^ w) ^ numWin) :
    ∃ B : Finset (Fin (2 ^ bits)),
      (∀ i, i ∉ B →
        cosetState (2 ^ bits) N cm (∑ j ∈ Finset.range numWin, Tfam j (window w a j)) i 0
          = cosetState (2 ^ bits) N cm ((k * a) % N) i 0)
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm
          (∑ j ∈ Finset.range numWin, Tfam j (window w a j))) B ≤ (numWin : ℝ) / 2 ^ cm
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm ((k * a) % N)) B ≤ (numWin : ℝ) / 2 ^ cm :=
  endpoint_embed_off bits N cm k w numWin a Tfam hTfam hN ha

/-- Pass 2 (`a += b·kInv`, fresh forward leg at the chained input `b = (k·x) % N`): the
    forward endpoint represents residue `x` (via `revCanonical_eq`, using `kInv·k ≡ 1
    [MOD N]` and `x < N`), off the wrap band. -/
theorem pass2_endpoint_embed_off (bits N cm k kInv w numWin x : Nat) (Tfam : Nat → Nat → Nat)
    (hTfam : ∀ j addr, Tfam j addr = tableValue kInv N w j addr)
    (hN : 0 < N) (hxN : x < N) (hkkinv : (kInv * k) % N = 1 % N)
    (hkxFit : (k * x) % N < (2 ^ w) ^ numWin) :
    ∃ B : Finset (Fin (2 ^ bits)),
      (∀ i, i ∉ B →
        cosetState (2 ^ bits) N cm
            (∑ j ∈ Finset.range numWin, Tfam j (window w ((k * x) % N) j)) i 0
          = cosetState (2 ^ bits) N cm x i 0)
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm
          (∑ j ∈ Finset.range numWin, Tfam j (window w ((k * x) % N) j))) B ≤ (numWin : ℝ) / 2 ^ cm
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm x) B ≤ (numWin : ℝ) / 2 ^ cm := by
  have hrev : (kInv * ((k * x) % N)) % N = x := revCanonical_eq N k kInv x hxN hkkinv
  have h := endpoint_embed_off bits N cm kInv w numWin ((k * x) % N) Tfam hTfam hN hkxFit
  rw [hrev] at h
  exact h

end FormalRV.Shor.GidneyInPlace.InPlaceEndpoint
