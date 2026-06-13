/-
  FormalRV.Shor.RunwayWindowed.RunwayNoOverflow — M2: DISCHARGING the per-step
  runway no-overflow `hno` from a deterministic per-segment padding condition.
  ════════════════════════════════════════════════════════════════════════════

  The fold's `hno` (per window `t`, per segment `m`:
  `segReg m (acc_t) + digit_m(word_t) < 2^(gSep+1)`) is NOT unconditionally true —
  it is exactly the no-wrap event whose failure probability is the runway
  deviation (`RunwayAdderMultiAdd` §0: "the gap-2 wrap/deviation bound is precisely
  the probability that this no-overflow condition fails").  Concretely it CAN fail:
  a segment's 1-bit runway absorbs ONE carry, so over many distinct-word adds a
  segment's digit-sum can saturate its `(gSep+1)`-bit register and wrap.

  But `hno` IS a THEOREM under a clean, static, deterministic padding hypothesis:
  each segment's TOTAL accumulated digit-sum fits its register,

      segPadded :  ∀ m < k, Σ_{t<numWin} digit_m(word_t) < 2^(gSep+1).

  This file proves `segPadded → hno`, turning the free per-state hypothesis into a
  consequence of a checkable inequality — the genuine "prove it, don't assume it".
  The engine is the per-segment value chain
      segReg m (acc_t) = (Σ_{i<t} digit_m(word_i)) mod 2^(gSep+1)
  (each window's segment add is a mod-`2^(gSep+1)` advance, `runwayAddK_step_segReg`,
  transported through the base-shift `runwayAddKAt_downshift`), under which
  `segPadded` makes the mod a no-op and `hno` immediate.

  HONEST REGIME NOTE: at full Shor parameters with this 1-bit-per-segment runway,
  `segPadded` forces small `numWin` (each `digit_m < 2^gSep`, so `numWin` of them
  fit `2^(gSep+1)` only for `numWin ≤ 2`); the paper instead WIDENS the runway
  (`g_pad ≳ log₂ numWin` bits/segment) — which is the same `segPadded` with a
  wider register — or pays the `7.64e-8` deviation.  This theorem is the exact
  deterministic boundary.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.RunwayWindowed.RunwayFold

namespace FormalRV.Shor.RunwayWindowed.RunwayNoOverflow

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.RunwayWindowed.RunwayLayout
  (runwayAddKAt runwayAddendIdx runwayWindowStep runwayWindowedMul)
open FormalRV.Shor.RunwayWindowed.RunwayShift (runwayAddKAt_downshift)
open FormalRV.Shor.RunwayWindowed.RunwayFold
  (runwayFoldGate runwayWindowedMul_value_ready runwayWindowedMul_residue)
open FormalRV.Shor.RunwayWindowed.RunwayMulCorrect
  (yBaseR RunwayReady runway_lookup_writes_word windowIO_frame segOffset_ne_runwayAddendIdx
   copyWindow_fixes_above runwayAddendIdx_gt_two_w runwayAddendIdx_inj windowWrite_IterReady
   runwayWindowStep_preserves_ready)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderFunctional
  (segReg segStride segBase runwayAddK)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderContiguous (contiguousDecode)
open FormalRV.Arithmetic.ObliviousRunwayAdder.RunwayAdderMultiAdd (IterReady runwayAddK_step_segReg)
open FormalRV.Shor.WindowedCircuit
  (copyWindow lookupReadAt encodeReg copyWindow_frame
   lookupReadAt_selects_word lookupReadAt_frame decodeReg_eq_mod_of_testBit)

/-- **The per-segment window-step value (unconditional, mod form).**  One window
    step advances segment `m`'s `(gSep+1)`-bit register by the word's `m`-th
    `gSep`-bit digit, MOD `2^(gSep+1)`:
        segReg m (acc') = (segReg m (acc) + digit_m(word_j)) mod 2^(gSep+1).
    The cleanup stages frame the augend, so the value lands at the add
    (`runwayAddK_step_segReg`, via the base-shift downshift); the lookup-write
    deposits `digit_m` into segment `m`'s addend. -/
theorem runwayWindowStep_segReg (w gSep a N k numWin y j m : Nat) (g : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hj : j < numWin) (hm : m < k)
    (hctrl : g ulookup_ctrl_idx = true)
    (haddr_clean : ∀ i, i < w → g (ulookup_address_idx i) = false)
    (hand_clean : ∀ i, i < w → g (ulookup_and_idx i) = false)
    (haddend_clean : ∀ i, i < k * gSep → g (runwayAddendIdx gSep (1 + 2 * w) i) = false)
    (hy : ∀ i, i < w → g (yBaseR w gSep k + j * w + i)
        = encodeReg (yBaseR w gSep k) (numWin * w) y (yBaseR w gSep k + j * w + i))
    (hready : IterReady gSep k (fun q => g (q + (1 + 2 * w)))) :
    segReg gSep m
        (fun q => Gate.applyNat
          (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) j) g (q + (1 + 2 * w)))
      = (segReg gSep m (fun q => g (q + (1 + 2 * w)))
          + ((a * (2 ^ w) ^ j * WindowedArith.window w y j) % N / 2 ^ (m * gSep)) % 2 ^ gSep)
        % 2 ^ (gSep + 1) := by
  simp only [runwayWindowStep, FormalRV.Shor.RunwayWindowed.RunwayLayout.runwayLookupAdd,
    Gate.applyNat_seq]
  set T : Nat → Nat := fun v => (a * (2 ^ w) ^ j * v) % N with hT
  set word : Nat := (a * (2 ^ w) ^ j * WindowedArith.window w y j) % N with hword
  set g1 := Gate.applyNat (copyWindow w (yBaseR w gSep k) j) g with hg1
  set g2 := Gate.applyNat (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T) g1
    with hg2
  set g3 := Gate.applyNat (runwayAddKAt gSep (1 + 2 * w) k) g2 with hg3
  -- the addend bits of g2 encode the residue word (reuse the lookup-write lemma).
  have hbits : ∀ m' i', m' < k → i' < gSep →
      g2 (cuccaroAdder.addendIdx (segBase gSep m') i' + (1 + 2 * w)) = word.testBit (m' * gSep + i') := by
    intro m' i' hm' hi'
    have hlt : m' * gSep + i' < k * gSep := by
      have h1 : (m' + 1) * gSep ≤ k * gSep := Nat.mul_le_mul_right _ (by omega)
      have h2 : (m' + 1) * gSep = m' * gSep + gSep := by ring
      omega
    have hd : (m' * gSep + i') / gSep = m' := by
      rw [Nat.add_comm (m' * gSep) i', Nat.add_mul_div_right i' m' hgSep,
          Nat.div_eq_of_lt hi', Nat.zero_add]
    have hmod : (m' * gSep + i') % gSep = i' := by
      rw [Nat.add_comm (m' * gSep) i', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
    have hidx : cuccaroAdder.addendIdx (segBase gSep m') i' + (1 + 2 * w)
        = runwayAddendIdx gSep (1 + 2 * w) (m' * gSep + i') := by
      unfold runwayAddendIdx
      rw [hd, hmod]
      show segBase gSep m' + 2 * i' + 2 + (1 + 2 * w)
        = 1 + 2 * w + segBase gSep m' + 2 * i' + 2
      omega
    rw [hidx, hg2, hg1]
    exact runway_lookup_writes_word w gSep a N k numWin y j g hw hgSep hj hctrl
      haddr_clean hand_clean haddend_clean hy (m' * gSep + i') hlt
  -- segment m's addend register on (down g2) reassembles to digit_m.
  have haddend_chunk : decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep
        (fun q => g2 (q + (1 + 2 * w)))
      = (word / 2 ^ (m * gSep)) % 2 ^ gSep := by
    refine decodeReg_eq_mod_of_testBit (cuccaroAdder.addendIdx (segBase gSep m)) gSep
      (word / 2 ^ (m * gSep)) (fun q => g2 (q + (1 + 2 * w))) (fun i' hi' => ?_)
    show g2 (cuccaroAdder.addendIdx (segBase gSep m) i' + (1 + 2 * w))
      = (word / 2 ^ (m * gSep)).testBit i'
    rw [hbits m i' hm hi', Nat.testBit_div_two_pow, Nat.add_comm i' (m * gSep)]
  -- IterReady on (down g2).
  have hready_g2 : IterReady gSep k (fun q => g2 (q + (1 + 2 * w))) :=
    windowWrite_IterReady w gSep a N k numWin y j g hgSep hready
  -- augend frame: (down g2) agrees with (down g) on segment m's augend bits.
  have haugend_g : ∀ i', i' < gSep + 1 →
      g2 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
        = g (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) := by
    intro i' hi'
    rw [hg2, hg1]
    exact windowIO_frame w gSep k (yBaseR w gSep k) j T g
      (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) (by omega)
      (fun I _ => segOffset_ne_runwayAddendIdx gSep (1 + 2 * w) m (2 * i' + 1) _ I hgSep
        (by omega) (fun t ht => by omega)
        (by show segBase gSep m + 2 * i' + 1 + (1 + 2 * w)
              = 1 + 2 * w + segBase gSep m + (2 * i' + 1); omega))
  -- g4 (unwrite) frames the augend; g5 (uncopy) frames the augend.
  have haugend_g3_g5 : ∀ i', i' < gSep + 1 →
      Gate.applyNat (copyWindow w (yBaseR w gSep k) j)
          (Gate.applyNat (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T) g3)
          (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
        = g3 (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) := by
    intro i' hi'
    rw [copyWindow_fixes_above w (yBaseR w gSep k) j _
          (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w)) (by omega),
        lookupReadAt_frame w (k * gSep) T (runwayAddendIdx gSep (1 + 2 * w)) g3
          (fun I _ => runwayAddendIdx_gt_two_w gSep w I)
          (cuccaroAdder.augendIdx (segBase gSep m) i' + (1 + 2 * w))
          (fun I _ => segOffset_ne_runwayAddendIdx gSep (1 + 2 * w) m (2 * i' + 1) _ I hgSep
            (by omega) (fun t ht => by omega)
            (by show segBase gSep m + 2 * i' + 1 + (1 + 2 * w)
                  = 1 + 2 * w + segBase gSep m + (2 * i' + 1); omega))]
  -- segReg m (down g5) = segReg m (down g3)  [cleanup frames the augend]
  have h54 : segReg gSep m
        (fun q => Gate.applyNat (copyWindow w (yBaseR w gSep k) j)
          (Gate.applyNat (lookupReadAt w (runwayAddendIdx gSep (1 + 2 * w)) (k * gSep) T) g3)
          (q + (1 + 2 * w)))
      = segReg gSep m (fun q => g3 (q + (1 + 2 * w))) := by
    unfold segReg
    exact decodeReg_ext (cuccaroAdder.augendIdx (segBase gSep m)) (gSep + 1) _ _
      (fun i' hi' => haugend_g3_g5 i' hi')
  -- segReg m (down g3) = (segReg m (down g2) + addend_m) mod 2^(gSep+1)  [the add]
  have h32 : segReg gSep m (fun q => g3 (q + (1 + 2 * w)))
      = (segReg gSep m (fun q => g2 (q + (1 + 2 * w)))
          + decodeReg (cuccaroAdder.addendIdx (segBase gSep m)) gSep (fun q => g2 (q + (1 + 2 * w))))
        % 2 ^ (gSep + 1) := by
    rw [hg3]
    rw [show (fun q => Gate.applyNat (runwayAddKAt gSep (1 + 2 * w) k) g2 (q + (1 + 2 * w)))
          = Gate.applyNat (runwayAddK gSep k) (fun q => g2 (q + (1 + 2 * w))) from
          runwayAddKAt_downshift gSep (1 + 2 * w) k g2]
    exact runwayAddK_step_segReg gSep k (fun q => g2 (q + (1 + 2 * w))) hready_g2 m hm
  -- segReg m (down g2) = segReg m (down g)  [lookup-write∘copy frames the augend]
  have h2g : segReg gSep m (fun q => g2 (q + (1 + 2 * w)))
      = segReg gSep m (fun q => g (q + (1 + 2 * w))) := by
    unfold segReg
    exact decodeReg_ext (cuccaroAdder.augendIdx (segBase gSep m)) (gSep + 1) _ _
      (fun i' hi' => haugend_g i' hi')
  rw [h54, h32, h2g, haddend_chunk]

/-! ## The fold's per-segment value (mod form) + the deterministic discharge. -/

/-- **The fold's per-segment register value.**  After `t` windows, segment `m`'s
    register holds the accumulated digit-sum MOD `2^(gSep+1)`:
        segReg m (acc_t) = (Σ_{i<t} digit_m(word_i)) mod 2^(gSep+1).
    By induction, threading `RunwayReady` (so the per-segment step applies) and the
    mod algebra `(a%M + b)%M = (a+b)%M`. -/
theorem runwayFold_segReg (w gSep a N k numWin y : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hr0 : RunwayReady w gSep k numWin y g0)
    (hseg0 : ∀ m, m < k → segReg gSep m (fun q => g0 (q + (1 + 2 * w))) = 0) :
    ∀ t, t ≤ numWin →
      RunwayReady w gSep k numWin y (Gate.applyNat (runwayFoldGate w gSep a N k t) g0)
      ∧ ∀ m, m < k →
          segReg gSep m
              (fun q => Gate.applyNat (runwayFoldGate w gSep a N k t) g0 (q + (1 + 2 * w)))
            = ((Finset.range t).sum
                (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N / 2 ^ (m * gSep))
                  % 2 ^ gSep)) % 2 ^ (gSep + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨hr0, fun m hm => ?_⟩
    rw [Finset.sum_range_zero, Nat.zero_mod]
    show segReg gSep m (fun q => g0 (q + (1 + 2 * w))) = 0
    exact hseg0 m hm
  | succ n ih =>
    intro hn1
    obtain ⟨hr_n, hseg_n⟩ := ih (by omega)
    have hstep_eq : Gate.applyNat (runwayFoldGate w gSep a N k (n + 1)) g0
        = Gate.applyNat (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) n)
            (Gate.applyNat (runwayFoldGate w gSep a N k n) g0) := by
      show Gate.applyNat (Gate.seq (runwayFoldGate w gSep a N k n)
        (runwayWindowStep w gSep a N k (1 + 2 * w) (yBaseR w gSep k) n)) g0 = _
      rw [Gate.applyNat_seq]
    obtain ⟨hctrl, haddr, hand, haddend, hyfull, hready⟩ := hr_n
    have hy : ∀ i, i < w →
        Gate.applyNat (runwayFoldGate w gSep a N k n) g0 (yBaseR w gSep k + n * w + i)
          = encodeReg (yBaseR w gSep k) (numWin * w) y (yBaseR w gSep k + n * w + i) := by
      intro i hi
      have hjw : n * w + i < numWin * w := by
        calc n * w + i < n * w + w := by omega
          _ = (n + 1) * w := by ring
          _ ≤ numWin * w := Nat.mul_le_mul_right w (by omega)
      have h := hyfull (n * w + i) hjw
      rwa [show yBaseR w gSep k + (n * w + i) = yBaseR w gSep k + n * w + i from by omega] at h
    refine ⟨?_, fun m hm => ?_⟩
    · rw [hstep_eq]
      exact runwayWindowStep_preserves_ready w gSep a N k numWin y n _ hw hgSep hk (by omega)
        ⟨hctrl, haddr, hand, haddend, hyfull, hready⟩
    · rw [hstep_eq, runwayWindowStep_segReg w gSep a N k numWin y n m _ hw hgSep (by omega) hm
            hctrl haddr hand haddend hy hready,
          hseg_n m hm, Finset.sum_range_succ, Nat.mod_add_mod]

/-- **The deterministic per-segment padding condition.**  Each segment's TOTAL
    accumulated `gSep`-bit digit-sum fits its `(gSep+1)`-bit register.  Static and
    checkable from `a, N, w, y, k, numWin` — no per-state quantifier. -/
def segPadded (w gSep a N k numWin y : Nat) : Prop :=
  ∀ m, m < k →
    (Finset.range numWin).sum
        (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N / 2 ^ (m * gSep)) % 2 ^ gSep)
      < 2 ^ (gSep + 1)

/-- **THE DISCHARGE — `segPadded → hno`.**  Under the deterministic per-segment
    padding, the fold's per-step no-overflow holds for ALL windows: the mod in
    `runwayFold_segReg` is a no-op (each prefix digit-sum `< 2^(gSep+1)`), so
    `segReg m (acc_t) = Σ_{i<t} digit_m(i)`, and `+ digit_m(t) = Σ_{i≤t} ≤
    Σ_{<numWin} < 2^(gSep+1)`.  This is the per-state `hno` of `runwayFold`,
    PROVEN rather than assumed. -/
theorem hno_of_segPadded (w gSep a N k numWin y : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hr0 : RunwayReady w gSep k numWin y g0)
    (hseg0 : ∀ m, m < k → segReg gSep m (fun q => g0 (q + (1 + 2 * w))) = 0)
    (hpad : segPadded w gSep a N k numWin y) :
    ∀ t, t < numWin → ∀ m, m < k →
      segReg gSep m (fun q => Gate.applyNat (runwayFoldGate w gSep a N k t) g0 (q + (1 + 2 * w)))
        + ((a * (2 ^ w) ^ t * WindowedArith.window w y t) % N / 2 ^ (m * gSep)) % 2 ^ gSep
        < 2 ^ (gSep + 1) := by
  intro t ht m hm
  have hseg := (runwayFold_segReg w gSep a N k numWin y g0 hw hgSep hk hr0 hseg0 t (by omega)).2 m hm
  have hpadm := hpad m hm
  have hsub_t : Finset.range t ⊆ Finset.range numWin :=
    fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_of_lt ht))
  have hsub_t1 : Finset.range (t + 1) ⊆ Finset.range numWin :=
    fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
  -- prefix sum over range t ≤ full sum over range numWin
  have hsubt : (Finset.range t).sum
      (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N / 2 ^ (m * gSep)) % 2 ^ gSep)
      < 2 ^ (gSep + 1) :=
    lt_of_le_of_lt (Finset.sum_le_sum_of_subset hsub_t) hpadm
  rw [hseg, Nat.mod_eq_of_lt hsubt,
      show (Finset.range t).sum
            (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N / 2 ^ (m * gSep)) % 2 ^ gSep)
          + ((a * (2 ^ w) ^ t * WindowedArith.window w y t) % N / 2 ^ (m * gSep)) % 2 ^ gSep
        = (Finset.range (t + 1)).sum
            (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N / 2 ^ (m * gSep)) % 2 ^ gSep)
        from (Finset.sum_range_succ _ t).symm]
  exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset hsub_t1) hpadm

/-- A clean accumulator (every segment register zero) decodes to `0`. -/
theorem contiguousDecode_eq_zero (gSep : Nat) (f : Nat → Bool) :
    ∀ (k : Nat), (∀ m, m < k → segReg gSep m f = 0) → contiguousDecode gSep k f = 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
      intro hz
      show contiguousDecode gSep m f + segReg gSep m f * 2 ^ (m * gSep) = 0
      simp [ih (fun m' hm' => hz m' (by omega)), hz m (Nat.lt_succ_self m)]

/-! ## The payoff — `runwayWindowedMul` correctness with NO free `hno`. -/

/-- **The fold value + `RunwayReady`, UNCONDITIONAL under `segPadded`.**  The free
    per-state `hno` of `runwayWindowedMul_value_ready` is discharged by
    `hno_of_segPadded`; the clean-accumulator `hacc0` is derived from `hseg0`. -/
theorem runwayWindowedMul_value_ready_of_segPadded (w gSep a N k numWin y : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k)
    (hr0 : RunwayReady w gSep k numWin y g0)
    (hseg0 : ∀ m, m < k → segReg gSep m (fun q => g0 (q + (1 + 2 * w))) = 0)
    (hpad : segPadded w gSep a N k numWin y) :
    RunwayReady w gSep k numWin y
        (Gate.applyNat (runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) numWin) g0)
      ∧ contiguousDecode gSep k
          (fun q => Gate.applyNat
            (runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) numWin) g0 (q + (1 + 2 * w)))
        = (Finset.range numWin).sum
            (fun i => ((a * (2 ^ w) ^ i * WindowedArith.window w y i) % N) % 2 ^ (k * gSep)) :=
  runwayWindowedMul_value_ready w gSep a N k numWin y g0 hw hgSep hk hr0
    (contiguousDecode_eq_zero gSep (fun q => g0 (q + (1 + 2 * w))) k hseg0)
    (hno_of_segPadded w gSep a N k numWin y g0 hw hgSep hk hr0 hseg0 hpad)

/-- **The coset residue, UNCONDITIONAL under `segPadded` (+ `N ≤ 2^(k·gSep)`).**
    `runwayWindowedMul` computes `(a·y) mod N` in the coset representation with NO
    free no-overflow hypothesis — the per-step runway no-overflow is now a THEOREM,
    `hno_of_segPadded`, derived from the static padding `segPadded`. -/
theorem runwayWindowedMul_residue_of_segPadded (w gSep a N k numWin y : Nat) (g0 : Nat → Bool)
    (hw : 0 < w) (hgSep : 0 < gSep) (hk : 0 < k) (hN : 0 < N)
    (hNsize : N ≤ 2 ^ (k * gSep)) (hybnd : y < (2 ^ w) ^ numWin)
    (hr0 : RunwayReady w gSep k numWin y g0)
    (hseg0 : ∀ m, m < k → segReg gSep m (fun q => g0 (q + (1 + 2 * w))) = 0)
    (hpad : segPadded w gSep a N k numWin y) :
    contiguousDecode gSep k
        (fun q => Gate.applyNat
          (runwayWindowedMul w gSep a N k (1 + 2 * w) (yBaseR w gSep k) numWin) g0 (q + (1 + 2 * w)))
        % N
      = (a * y) % N :=
  runwayWindowedMul_residue w gSep a N k numWin y g0 hw hgSep hk hN hNsize hybnd hr0
    (contiguousDecode_eq_zero gSep (fun q => g0 (q + (1 + 2 * w))) k hseg0)
    (hno_of_segPadded w gSep a N k numWin y g0 hw hgSep hk hr0 hseg0 hpad)

end FormalRV.Shor.RunwayWindowed.RunwayNoOverflow
