/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetNormBound
  ───────────────────────────────────────────────────
  CAPSTONE of Architecture B: the whole two-register Gidney in-place
  coset-multiplier norm bound, assembled from the two FORWARD legs
  (`InPlaceLeg1` / `InPlaceLeg2`) through the triangle + unitary-invariance
  backbone (`InPlaceNormBound.gidneyTwoRegInPlace_coset_norm_bound_of_legs`):

      normSqDist (uc_eval(gidneyTwoRegInPlaceCosetMul) · cosetInputVec x 0)
                 (cosetInputVec 0 ((k·x)%N))
        ≤ 4·numWin/2^cm.

  • Leg 1 (`gidneyTwoRegInPlace_leg1_deviation`) supplies `hleg1` verbatim
    (pass-1 forward windowed multiply on the b-register, multiplier `k`).
  • Leg 2 (`gidneyTwoRegInPlace_leg2_deviation`) supplies `hleg2` up to the
    symmetry of `normSqDist` (`normSqDist_comm`): the backbone wants
    `normSqDist M1 (U_p2·target)`, the leg proves `normSqDist (U_p2·target) M1`.
  • The two well-typed obligations are discharged by
    `gidneyProductAdd_pass1_wellTyped` / `_pass2_wellTyped`
    (`cosetDim w bits` is defeq `2+2w+3·bits`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Legs.InPlaceLeg2
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Mass.InPlaceNormBound

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetNormBound

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (normSqDist)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.CosetMul (runningSum)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.GidneyTwoRegInPlace
  (pass1 pass2 gidneyTwoRegInPlaceCosetMul)
open FormalRV.Shor.GidneyInPlace.ProductAddWrapper
  (gidneyProductAddTOf gidneyProductAdd_pass1_wellTyped gidneyProductAdd_pass2_wellTyped)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound
  (cosetInputVec gidneyTwoRegInPlace_coset_norm_bound_of_legs)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg1 (gidneyTwoRegInPlace_leg1_deviation)
open FormalRV.Shor.GidneyInPlace.InPlaceLeg2 (gidneyTwoRegInPlace_leg2_deviation)

/-- `normSqDist` is symmetric: it is the Born-`L¹` distance
    `∑ᵢ |‖s₁ i‖² − ‖s₂ i‖²|`, and `|a − b| = |b − a|`. -/
theorem normSqDist_comm {dim : Nat} (s₁ s₂ : QState dim) :
    normSqDist s₁ s₂ = normSqDist s₂ s₁ := by
  unfold normSqDist
  exact Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)

/-!
## DESIGN NOTE — FROZEN (2026-06-17)

`gidneyTwoRegInPlace_coset_norm_bound` below is the **two-register LOCAL** deviation
theorem.  It is frozen GREEN after a 4-dimension adversarial audit (statement fidelity,
the constant, assumption necessity / non-vacuity, axiom soundness): every dimension
upheld, zero overturned claims, axioms = `{propext, Classical.choice, Quot.sound}` only
(transitive `#print axioms`, no `sorry`/`native_decide` on the dependency path).

**What it says (physical reading).**  On the two data blocks
`a @ [1+2w, 1+2w+bits)` and `b @ [1+2w+bits, 1+2w+2·bits)`:

      a = cosetState x ,  b = cosetState 0
        ── gidneyTwoRegInPlaceCosetMul ──▶
      a = cosetState 0 ,  b = cosetState ((k·x) mod N)

with Born-`L¹` (`normSqDist`) deviation `≤ 4·numWin/2^cm`.  The **b-block is the OUTPUT**
(it holds `k·x mod N`); the **a-block is the CLEARED in-place ancilla** (uncomputed to the
residue-0 coset, NOT the zero vector / register index 0).  The gate is the genuine
composite `Gate.seq pass1 (Gate.reverse pass2)` (pass1 `b += k·a`; reverse-pass2 clears a).

**The constant is exact** — `4 = 2 (non-expansive step per add) × 2 (legs)`, `numWin` adds,
denominator `2^cm` threaded unchanged engine → leg → backbone → `ring` (no `field_simp`/
`ring_nf`/denominator rescaling).  The two table families are pinned to canonical
`tableValue` by `hTfamK`/`hTfamKinv` — NOT free oracles.  Non-vacuous: concrete witnesses
satisfy all hypotheses simultaneously.

**NEXT PHASE IS PACKAGING, NOT NEW ARITHMETIC.**  The remaining work toward the
single-register contract `inplaceReducedLookupCosetMul_shift` is purely structural:
(1) the register-iso lift to the contiguous/logical layout, (2) the logical output
convention, (3) the D6 factor-2 Born-mass roll-up (`numWin := 2·numWin` at instantiation).
Do not re-derive the deviation bound.

**WARNING for any "single-register" wrapper.**  This theorem is irreducibly two-register.
A wrapper that presents it as a single-register oracle MUST keep explicit that *physical
`b` is the output block holding `k·x mod N`* and *physical `a` is cleared ancilla* — never
silently swap or hide the two-register structure.
-/

/-- **Architecture-B capstone.**  The faithful two-register Gidney in-place
    coset multiplier `pass1 ; reverse pass2`, applied to the clean two-register
    coset input `|coset_x⟩_a ⊗ |coset_0⟩_b`, deviates from the intended output
    `|coset_0⟩_a ⊗ |coset_{kx}⟩_b` by at most `4·numWin/2^cm` in Born-`L¹`
    distance — the sum of the two forward windowed-multiply deviations
    (each `≤ numWin·(2/2^cm)`), via the triangle inequality and the fact that
    `uc_eval(reverse pass2)` is a `normSqDist`-isometry. -/
theorem gidneyTwoRegInPlace_coset_norm_bound
    (w bits numWin N cm k kInv x : Nat) (TfamK TfamKinv : Nat → Nat → Nat)
    (hTfamK : ∀ j addr, TfamK j addr = tableValue k N w j addr)
    (hTfamKinv : ∀ j addr, TfamKinv j addr = tableValue kInv N w j addr)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N) (hxN : x < N)
    (hkInv : (kInv * k) % N = 1 % N)
    (hfit_engine : N + 2 ^ cm * N ≤ 2 ^ bits)
    (hfitAllK : ∀ ja : Fin (2 ^ bits),
      runningSum (cosetWindowConst k N w ja.val) numWin + (2 ^ cm - 1) * N < 2 ^ bits)
    (hfitAllKinv : ∀ jb : Fin (2 ^ bits),
      runningSum (cosetWindowConst kInv N w jb.val) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (gidneyTwoRegInPlaceCosetMul w bits TfamK TfamKinv numWin))
          * cosetInputVec w bits N cm x 0)
        (cosetInputVec w bits N cm 0 ((k * x) % N))
      ≤ 4 * (numWin : ℝ) / 2 ^ cm := by
  -- well-typedness of the two forward passes (`cosetDim` is defeq `2+2w+3·bits`)
  have hwt1 : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamK (1 + 2 * w + bits) (1 + 2 * w + 2 * bits) (1 + 2 * w) numWin) :=
    gidneyProductAdd_pass1_wellTyped w bits TfamK numWin hw hbits
  have hwt2 : Gate.WellTyped (cosetDim w bits)
      (gidneyProductAddTOf w bits TfamKinv (1 + 2 * w) (1 + 2 * w + 2 * bits) (1 + 2 * w + bits) numWin) :=
    gidneyProductAdd_pass2_wellTyped w bits TfamKinv numWin hw hbits
  -- Leg 1 = `hleg1` (pass-1 forward leg) verbatim
  have hleg1 := gidneyTwoRegInPlace_leg1_deviation w bits numWin N cm k x TfamK
    hTfamK hw hbits hN hxN hfit_engine hfitAllK hwt1
  -- Leg 2 (pass-2 forward leg), then flip the arguments for the backbone's `hleg2`
  have hleg2 := gidneyTwoRegInPlace_leg2_deviation w bits numWin N cm k kInv x TfamKinv
    hTfamKinv hw hbits hN hxN hkInv hfit_engine hfitAllKinv hwt2
  rw [normSqDist_comm] at hleg2
  -- backbone: triangle + isometry of `uc_eval(reverse pass2)` ⇒ `≤ 2·L`
  have hmain := gidneyTwoRegInPlace_coset_norm_bound_of_legs
    w bits numWin N cm k x TfamK TfamKinv hw hbits ((numWin : ℝ) * (2 / 2 ^ cm))
    hleg1 hleg2
  -- `2·(numWin·(2/2^cm)) = 4·numWin/2^cm`
  have harith : 2 * ((numWin : ℝ) * (2 / 2 ^ cm)) = 4 * (numWin : ℝ) / 2 ^ cm := by
    ring
  linarith [hmain, harith.le, harith.ge]

end FormalRV.Shor.GidneyInPlace.InPlaceCosetNormBound
