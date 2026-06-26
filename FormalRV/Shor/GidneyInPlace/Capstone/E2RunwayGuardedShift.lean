/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayGuardedShift — the COMPRESSED guarded-shift
  gate, fitting `cosetDim`, by SHARING the divider/multiply low region.
  ════════════════════════════════════════════════════════════════════════════

  GOAL.  Realize the guarded shift
      data band value  z + j·N   ↦   (c·z)%N + j·N   =  guardedShift (2^bits) N c (z + j·N)
  at the COMPRESSED dimension `cgsDim bits cm := 3*bits + 5 + cm`, which is
  `≤ cosetDim w bits = 2 + 2w + 3·bits` exactly when `cm ≤ 2w - 3` (with `2 ≤ w`).

  The gain over a DISJOINT placement of the divider and multiply (which would cost
  `gsDim = (2bits+2+cm) + dim'` ≈ `4bits+5+cm`) is that here the
  divider and the multiply SHARE the low region `[0, 3bits+5)`; only the `cm` quotient
  wires are parked just ABOVE the multiply footprint.

  LAYOUT (window size 1 for the internal multiply, `numWin' = bits`).
    Multiply (`windowedModNMulGate 1 bits N bits c cinv`) footprint = `3bits+5`:
      • ctrl qubit       : wire `0`  (`ulookup_ctrl_idx`),
      • Cuccaro block    : `[3, 2bits+4)` (carry-in `3`, acc `2i+4`, addend `2i+5`),
      • y-register       : `[2bits+4, 3bits+4)`  (value bit `i` at `2bits+4+i`),
      • multiply flag    : wire `3bits+4`.
    Divider (`divModN bits cm N`) at base 0, dim `dimDiv = 2bits+2+cm`:
      • data band (value)  : wire `2i+1`,   carry-in wire `0`, read band `2i+2`,
      • divider flag       : wire `2bits+1`, quotient band `[2bits+2, 2bits+2+cm)`.
    Parked quotient: wires `[3bits+5, 3bits+5+cm)` (just above the multiply footprint).

  PIPELINE (symmetric, so the tail is the inverse of the head and the final
  `reverse divModN` cancels):

      divModN ; moveQuot ; adapter ; X 0 ; mul ; X 0 ; adapter ; moveQuot ; reverse divModN

    1. `divModN`   : data `{2i+1}=z.testBit i`, quotient `{2bits+2+k}=j.testBit k`, clean.
    2. `moveQuot`  : swap quotient `{2bits+2+k} ↔ {3bits+5+k}` (parks it above mul).
    3. `adapter`   : swap residue `{2i+1} ↔ y-register {2bits+4+i}` (z into y-reg).
    4. `X 0`       : set the multiply control qubit.
    5. `mul`       : y-register `z ↦ (c·z)%N` (the whole low region is, ON `[0,3bits+5)`,
                     exactly `mulInputOf cuccaroAdder 1 bits bits z`; the parked quotient
                     lives ABOVE the footprint and is handled by `applyNat_congr_lt`
                     + the WellTyped frame).
    6–8. inverse of 4,3,2 : `(c·z)%N` back to `{2i+1}`, quotient back to `{2bits+2+k}`.
    9. `reverse divModN` : recombine to `encDiv bits ((c·z)%N + j·N)` via reverse-cancel.

  DELIVERABLE (`cgsGate_decode`):  on the support
    (`z<N`, `j<2^cm`, `cm≤bits`, `2^cm·N≤2^bits`, `2N≤2^bits`, `cinv<N`, `c·cinv%N=1`):
      • whole output state EQUALS `encDiv bits ((c·z)%N + j·N)`  (data + transient + quotient),
      • data-band decode = `(c·z)%N + j·N = guardedShift …`,
      • `Gate.WellTyped (cgsDim bits cm) (cgsGate …)`,
    plus `cgsDim bits cm ≤ cosetDim w bits` from `cm ≤ 2w-3` (`2 ≤ w`).

  Kernel-clean target: no `sorry`, no `native_decide`; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace
import FormalRV.Shor.WindowedModNShor
import FormalRV.Arithmetic.GateShift
import FormalRV.Shor.GidneyInPlace.Gate.Def.GatePerm
import FormalRV.Shor.WindowedCosetFamily

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayGuardedShift

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Arithmetic (applyNat_congr_lt)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
open FormalRV.Shor.GidneyInPlace.GatePerm (applyNat_frame reverse_wellTyped)
open FormalRV.Shor.GidneyInPlace.GateReversible (Gate.reverse applyNat_reverse_cancel)
open FormalRV.BQAlgo.WindowedModNShor (swapCascade swapCascade_apply swapCascade_wellTyped
  windowedModNMulGate_wellTyped)
open FormalRV.Shor.WindowedCircuit (mulInputOf mulInputOf_ctrl mulInputOf_low
  mulInputOf_eq_encodeReg encodeReg encodeReg_at encodeReg_high
  ModNMulReady windowedModNMulGate windowedModNMulGate_correct modNMulReady_mulInputOf)
open FormalRV.Shor.WindowedCosetFamily (cosetDim)
open FormalRV.Shor.GidneyInPlace.RunwayShiftPerm (guardedShift guarded_on_support)

/-! ## §0. Dimension constants and the `cgsDim ≤ cosetDim` arithmetic. -/

/-- The compressed total dimension: shared low region (`3bits+5`) + the `cm` parked
    quotient wires. -/
def cgsDim (bits cm : Nat) : Nat := 3 * bits + 5 + cm

/-- The internal multiply's footprint (window size 1, `numWin' = bits`):
    `1 + 2·1 + (2bits+1) + bits·1 + 1 = 3bits+5`.  Equals the shared low region. -/
def mulFoot (bits : Nat) : Nat := 3 * bits + 5

theorem mulFoot_eq (bits : Nat) :
    mulFoot bits = 1 + 2 * 1 + (2 * bits + 1) + bits * 1 + 1 := by
  unfold mulFoot; ring

/-- **`cgsDim ≤ cosetDim`** from `cm ≤ 2w − 3` (and `2 ≤ w`, needed so the Nat
    subtraction is faithful).  This is the arithmetic the next milestone needs to
    place the compressed gate inside the coset register. -/
theorem cgsDim_le_cosetDim (w bits cm : Nat) (hw : 2 ≤ w) (hcm : cm ≤ 2 * w - 3) :
    cgsDim bits cm ≤ cosetDim w bits := by
  unfold cgsDim cosetDim
  omega

/-! ## §1. Layout wire maps and the three swap adapters. -/

/-- Multiply control qubit (`ulookup_ctrl_idx = 0`). -/
def ctrlIdx : Nat := 0

/-- The multiply's y-register base wire: `1 + 2·1 + cuccaroAdder.span bits = 2bits+4`. -/
def yBase (bits : Nat) : Nat := 2 * bits + 4

/-- Divider data wire `i` (interleaved Cuccaro target register). -/
def uDiv (i : Nat) : Nat := 2 * i + 1

/-- Multiply y-register wire `i` (contiguous, LSB-first). -/
def vY (bits i : Nat) : Nat := yBase bits + i

/-- Divider quotient wire `k` (`qBase bits + k = 2bits+2+k`). -/
def uQ (bits k : Nat) : Nat := qBase bits + k

/-- Parked quotient wire `k` (just above the multiply footprint). -/
def vQ (bits k : Nat) : Nat := mulFoot bits + k

/-- ADAPTER moving the residue `z` from the divider data band into the y-register. -/
def adapter (bits : Nat) : Gate := swapCascade uDiv (vY bits) bits

/-- ADAPTER parking the quotient just above the multiply footprint. -/
def moveQuot (bits cm : Nat) : Gate := swapCascade (uQ bits) (vQ bits) cm

/-- The internal residue multiply (window 1, `numWin' = bits`). -/
def mul (bits N c cinv : Nat) : Gate := windowedModNMulGate 1 bits N bits c cinv

/-- **THE COMPRESSED GUARDED-SHIFT GATE.** -/
def cgsGate (bits cm N c cinv : Nat) : Gate :=
  Gate.seq (divModN bits cm N)
    (Gate.seq (moveQuot bits cm)
      (Gate.seq (adapter bits)
        (Gate.seq (Gate.X ctrlIdx)
          (Gate.seq (mul bits N c cinv)
            (Gate.seq (Gate.X ctrlIdx)
              (Gate.seq (adapter bits)
                (Gate.seq (moveQuot bits cm)
                  (Gate.reverse (divModN bits cm N)))))))))

/-! ## §2. WellTyped for the whole gate. -/

theorem divModN_wellTyped_cgs (bits cm N : Nat) (hbits : 1 ≤ bits) (hcm : cm ≤ bits) :
    Gate.WellTyped (cgsDim bits cm) (divModN bits cm N) :=
  wellTyped_mono (divModN bits cm N) (dimDiv bits cm) (cgsDim bits cm)
    (by unfold cgsDim dimDiv; omega) (divModN_wellTyped bits cm N hbits hcm)

theorem mul_wellTyped_cgs (bits cm N c cinv : Nat) :
    Gate.WellTyped (cgsDim bits cm) (mul bits N c cinv) := by
  unfold mul
  exact windowedModNMulGate_wellTyped 1 bits N bits c cinv (cgsDim bits cm)
    (by norm_num) (by omega) (by unfold cgsDim; omega)

theorem adapter_wellTyped_cgs (bits cm : Nat) (hbits : 1 ≤ bits) :
    Gate.WellTyped (cgsDim bits cm) (adapter bits) := by
  unfold adapter
  apply swapCascade_wellTyped uDiv (vY bits) bits (cgsDim bits cm)
    (by unfold cgsDim; omega)
  intro i hi
  refine ⟨?_, ?_, ?_⟩
  · show 2 * i + 1 < cgsDim bits cm; unfold cgsDim; omega
  · show yBase bits + i < cgsDim bits cm; unfold cgsDim yBase; omega
  · show 2 * i + 1 ≠ yBase bits + i; unfold yBase; omega

theorem moveQuot_wellTyped_cgs (bits cm : Nat) (hbits : 1 ≤ bits) (hcm : cm ≤ bits) :
    Gate.WellTyped (cgsDim bits cm) (moveQuot bits cm) := by
  unfold moveQuot
  apply swapCascade_wellTyped (uQ bits) (vQ bits) cm (cgsDim bits cm)
    (by unfold cgsDim; omega)
  intro k hk
  refine ⟨?_, ?_, ?_⟩
  · show qBase bits + k < cgsDim bits cm; unfold cgsDim qBase; omega
  · show vQ bits k < cgsDim bits cm; unfold cgsDim vQ mulFoot; omega
  · show qBase bits + k ≠ vQ bits k; unfold qBase vQ mulFoot; omega

theorem cgsGate_wellTyped (bits cm N c cinv : Nat) (hbits : 1 ≤ bits) (hcm : cm ≤ bits) :
    Gate.WellTyped (cgsDim bits cm) (cgsGate bits cm N c cinv) := by
  have hdiv := divModN_wellTyped_cgs bits cm N hbits hcm
  have hmq := moveQuot_wellTyped_cgs bits cm hbits hcm
  have hadp := adapter_wellTyped_cgs bits cm hbits
  have hmul := mul_wellTyped_cgs bits cm N c cinv
  have hx : Gate.WellTyped (cgsDim bits cm) (Gate.X ctrlIdx) := by
    show ctrlIdx < cgsDim bits cm; unfold ctrlIdx cgsDim; omega
  refine ⟨hdiv, hmq, hadp, hx, hmul, hx, hadp, hmq, ?_⟩
  exact reverse_wellTyped (divModN bits cm N) (cgsDim bits cm) hdiv

/-! ## §3. Post-divider state (S1). -/

/-- The state after `divModN` on the clean input `encDiv bits v`, `v = z + j·N`:
    data band (`uDiv i = 2i+1`) = `z.testBit i`; quotient wire `qBase+k` = `j.testBit k`;
    carry/read/flag clean; and EVERY wire `≥ dimDiv` is clean. -/
theorem divider_state (bits cm N z j : Nat)
    (hbits : 1 ≤ bits) (hN : 0 < N) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) (hj : j < 2 ^ cm) :
    let g := Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N))
    (∀ i, i < bits → g (uDiv i) = z.testBit i)
    ∧ (∀ k, k < cm → g (uQ bits k) = j.testBit k)
    ∧ g 0 = false
    ∧ g (flagW bits) = false
    ∧ (∀ i, i < bits → g (0 + 2 * i + 2) = false)
    ∧ (∀ p, dimDiv bits cm ≤ p → g p = false) := by
  intro g
  have hbud' : N * 2 ^ cm ≤ 2 ^ bits := by rw [Nat.mul_comm]; exact hbudget
  have hv_lt : z + j * N < N * 2 ^ cm := by
    calc z + j * N < N + j * N := by omega
      _ = (j + 1) * N := by ring
      _ ≤ 2 ^ cm * N := Nat.mul_le_mul_right _ (by omega)
      _ = N * 2 ^ cm := by ring
  obtain ⟨hd_tgt, hd_quot, hd_cin, hd_flag, hd_read⟩ :=
    divModN_decode_gen cm bits N (z + j * N) (encDiv bits (z + j * N))
      (encDiv_DivState bits cm N (z + j * N) hv_lt hbud' hcm hN)
  obtain ⟨hjdiv, hzmod⟩ := divModN_arith N z j hN hz
  refine ⟨?_, ?_, hd_cin, hd_flag, hd_read, ?_⟩
  · intro i hi
    show Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (uDiv i) = z.testBit i
    have huv : uDiv i = 0 + 2 * i + 1 := by unfold uDiv; ring
    rw [huv, hd_tgt i hi]
    show ((z + j * N) % N).testBit i = z.testBit i
    rw [hzmod]
  · intro k hk
    show Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (uQ bits k) = j.testBit k
    show Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (qBase bits + k) = j.testBit k
    rw [hd_quot k hk]
    show ((z + j * N) / N).testBit k = j.testBit k
    rw [hjdiv]
  · intro p hp
    have hfr := FormalRV.Shor.GidneyInPlace.GatePerm.applyNat_frame (divModN bits cm N)
      (dimDiv bits cm) (divModN_wellTyped bits cm N hbits hcm) (encDiv bits (z + j * N)) p hp
    show Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) p = false
    rw [hfr]
    unfold encDiv
    rw [if_neg (by unfold dimDiv at hp; omega)]
    rw [if_neg (by unfold dimDiv at hp; intro hc; omega)]

/-! ## §4. Swap injectivity / disjointness and the adapter / moveQuot actions. -/

theorem vY_inj (bits : Nat) :
    ∀ i k, i < bits → k < bits → i ≠ k → vY bits i ≠ vY bits k := by
  intro i k _ _ h; unfold vY yBase; omega

theorem uDiv_ne_vY (bits : Nat) :
    ∀ i k, i < bits → k < bits → uDiv i ≠ vY bits k := by
  intro i k hi hk; unfold uDiv vY yBase; omega

theorem uQ_inj (bits : Nat) :
    ∀ i k, i < bits → k < bits → i ≠ k → uQ bits i ≠ uQ bits k := by
  intro i k _ _ h; unfold uQ qBase; omega

theorem vQ_inj (bits : Nat) :
    ∀ i k, i < bits → k < bits → i ≠ k → vQ bits i ≠ vQ bits k := by
  intro i k _ _ h; unfold vQ mulFoot; omega

theorem uQ_ne_vQ (bits cm : Nat) (hcm : cm ≤ bits) :
    ∀ i k, i < cm → k < cm → uQ bits i ≠ vQ bits k := by
  intro i k hi hk; unfold uQ vQ qBase mulFoot; omega

/-- One application of the adapter: divider data wire `uDiv i` ← old `vY i`,
    y-register wire `vY i` ← old `uDiv i`, everything else fixed. -/
theorem adapter_apply (bits : Nat) (g : Nat → Bool) :
    (∀ i, i < bits → Gate.applyNat (adapter bits) g (uDiv i) = g (vY bits i))
    ∧ (∀ i, i < bits → Gate.applyNat (adapter bits) g (vY bits i) = g (uDiv i))
    ∧ (∀ p, (∀ i, i < bits → p ≠ uDiv i ∧ p ≠ vY bits i) →
        Gate.applyNat (adapter bits) g p = g p) := by
  unfold adapter
  exact swapCascade_apply uDiv (vY bits) bits g
    (fun i k _ _ h => by unfold uDiv; omega) (vY_inj bits) (uDiv_ne_vY bits)

/-- One application of moveQuot: quotient wire `uQ k` ← old `vQ k`,
    parked wire `vQ k` ← old `uQ k`, everything else fixed. -/
theorem moveQuot_apply (bits cm : Nat) (hcm : cm ≤ bits) (g : Nat → Bool) :
    (∀ k, k < cm → Gate.applyNat (moveQuot bits cm) g (uQ bits k) = g (vQ bits k))
    ∧ (∀ k, k < cm → Gate.applyNat (moveQuot bits cm) g (vQ bits k) = g (uQ bits k))
    ∧ (∀ p, (∀ k, k < cm → p ≠ uQ bits k ∧ p ≠ vQ bits k) →
        Gate.applyNat (moveQuot bits cm) g p = g p) := by
  unfold moveQuot
  exact swapCascade_apply (uQ bits) (vQ bits) cm g
    (fun i k hi hk h => uQ_inj bits i k (by omega) (by omega) h)
    (fun i k hi hk h => vQ_inj bits i k (by omega) (by omega) h)
    (uQ_ne_vQ bits cm hcm)

/-! ## §5. The residue-multiply leg (footprint-local, parked quotient framed). -/

/-- The y-register footprint value of `mulInputOf cuccaroAdder 1 bits bits x`:
    bit `i` (at wire `vY bits i = 2bits+4+i`) reads `x.testBit i`. -/
theorem mulInputOf_vY (bits x i : Nat) (hi : i < bits) :
    mulInputOf cuccaroAdder 1 bits bits x (vY bits i) = x.testBit i := by
  have hp : vY bits i ≠ ulookup_ctrl_idx := by
    unfold vY yBase ulookup_ctrl_idx; omega
  rw [mulInputOf_eq_encodeReg cuccaroAdder 1 bits bits x (vY bits i) hp]
  show encodeReg (1 + 2 * 1 + cuccaroAdder.span bits) (bits * 1) x (vY bits i) = x.testBit i
  have hspan : (1 + 2 * 1 + cuccaroAdder.span bits) = yBase bits := by
    show 1 + 2 * 1 + (2 * bits + 1) = yBase bits
    unfold yBase; ring
  rw [hspan]
  show encodeReg (yBase bits) (bits * 1) x (yBase bits + i) = x.testBit i
  exact encodeReg_at (yBase bits) (bits * 1) x i (by omega)

/-- `mulInputOf` at the ctrl wire 0 reads `true`. -/
theorem mulInputOf_ctrl0 (bits x : Nat) :
    mulInputOf cuccaroAdder 1 bits bits x 0 = true := by
  have : (0 : Nat) = ulookup_ctrl_idx := by unfold ulookup_ctrl_idx; rfl
  rw [this]; exact mulInputOf_ctrl cuccaroAdder 1 bits bits x

/-- `mulInputOf` is `false` at every footprint position that is neither the ctrl
    wire `0` nor a y-register wire `vY i`.  (Below yBase ⇒ `mulInputOf_low`; the
    flag wire `3bits+4` is above the y-register ⇒ `encodeReg_high`.) -/
theorem mulInputOf_foot_clean (bits x p : Nat) (hp : p < mulFoot bits)
    (hp0 : p ≠ 0) (hpy : ∀ i, i < bits → p ≠ vY bits i) :
    mulInputOf cuccaroAdder 1 bits bits x p = false := by
  have hpc : p ≠ ulookup_ctrl_idx := by unfold ulookup_ctrl_idx; omega
  by_cases hlow : p < yBase bits
  · rw [mulInputOf_low cuccaroAdder 1 bits bits x p hpc
        (by show p < 1 + 2 * 1 + cuccaroAdder.span bits
            show p < 1 + 2 * 1 + (2 * bits + 1); unfold yBase at hlow; omega)]
  · -- p ≥ yBase: either in y-register (excluded by hpy) or above it.
    have habove : yBase bits + bits ≤ p := by
      by_contra hcon
      push_neg at hcon
      exact hpy (p - yBase bits) (by simp only [yBase] at hlow hcon ⊢; omega)
        (by simp only [vY, yBase] at hlow hcon ⊢; omega)
    rw [mulInputOf_eq_encodeReg cuccaroAdder 1 bits bits x p hpc]
    show encodeReg (1 + 2 * 1 + cuccaroAdder.span bits) (bits * 1) x p = false
    have hspan : (1 + 2 * 1 + cuccaroAdder.span bits) = yBase bits := by
      show 1 + 2 * 1 + (2 * bits + 1) = yBase bits; unfold yBase; ring
    rw [hspan]
    exact encodeReg_high (yBase bits) (bits * 1) x p (by omega)

/-- **The residue-multiply leg.**  Given a state `s` agreeing with
    `mulInputOf cuccaroAdder 1 bits bits z` on the whole multiply footprint
    `[0, mulFoot bits)`, the multiply:
      • sends the y-register `vY i` to `((c·z)%N).testBit i`,
      • leaves the footprint state equal to `mulInputOf … ((c·z)%N)` (so the rest of
        the footprint is clean / ctrl-set, just like the input shape),
      • FIXES every wire `≥ mulFoot bits` (the parked quotient and above). -/
theorem mul_leg (bits N c cinv z : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hz : z < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1)
    (s : Nat → Bool)
    (hfoot : ∀ p, p < mulFoot bits → s p = mulInputOf cuccaroAdder 1 bits bits z p) :
    let g := Gate.applyNat (mul bits N c cinv) s
    (∀ i, i < bits → g (vY bits i) = ((c * z) % N).testBit i)
    ∧ (∀ p, p < mulFoot bits → g p = mulInputOf cuccaroAdder 1 bits bits ((c * z) % N) p)
    ∧ (∀ p, mulFoot bits ≤ p → g p = s p) := by
  intro g
  -- the multiply is WellTyped at its footprint.
  have hmwt : Gate.WellTyped (mulFoot bits) (windowedModNMulGate 1 bits N bits c cinv) := by
    rw [mulFoot_eq]
    exact windowedModNMulGate_wellTyped 1 bits N bits c cinv _ (by norm_num) (by omega) (by omega)
  -- ModNMulReady on the clean encoded input mulInputOf.
  have hready : ModNMulReady 1 bits bits z (mulInputOf cuccaroAdder 1 bits bits z) :=
    modNMulReady_mulInputOf 1 bits bits z
  -- the multiply output on mulInputOf is ModNMulReady at (c*z)%N.
  have hout := windowedModNMulGate_correct 1 bits N bits c cinv z (by norm_num) (by omega)
    hN_pos hN2 hz hcinv hinv (mulInputOf cuccaroAdder 1 bits bits z) hready
  -- the frame condition of ModNMulReady gives the y-register values + footprint shape.
  obtain ⟨hF, hD, hC, hG, hV⟩ := hout
  -- transfer the multiply action from s to mulInputOf on the footprint (input locality).
  have hagree : ∀ q, q < mulFoot bits →
      Gate.applyNat (windowedModNMulGate 1 bits N bits c cinv) s q
        = Gate.applyNat (windowedModNMulGate 1 bits N bits c cinv)
            (mulInputOf cuccaroAdder 1 bits bits z) q :=
    fun q hq => applyNat_congr_lt (mulFoot bits) _ hmwt s
      (mulInputOf cuccaroAdder 1 bits bits z) hfoot q hq
  refine ⟨?_, ?_, ?_⟩
  · -- y-register values.
    intro i hi
    show Gate.applyNat (mul bits N c cinv) s (vY bits i) = ((c * z) % N).testBit i
    unfold mul
    rw [hagree (vY bits i) (by unfold vY yBase mulFoot; omega)]
    -- read the ModNMulReady frame at vY i (off the Cuccaro block, ≠ flag).
    have hpb : ¬ inBlock (1 + 2 * 1) (2 * bits + 1) (vY bits i) := by
      unfold inBlock vY yBase; omega
    have hpf : vY bits i ≠ 1 + 2 * 1 + (2 * bits + 1) + bits * 1 := by
      unfold vY yBase; omega
    rw [hF (vY bits i) hpb hpf]
    exact mulInputOf_vY bits ((c * z) % N) i hi
  · -- footprint shape = mulInputOf ((c*z)%N).
    intro p hp
    show Gate.applyNat (mul bits N c cinv) s p = mulInputOf cuccaroAdder 1 bits bits ((c * z) % N) p
    unfold mul
    rw [hagree p hp]
    -- classify p within the footprint.
    by_cases hpb : inBlock (1 + 2 * 1) (2 * bits + 1) p
    · -- p in the Cuccaro block: clean (carry / acc / addend), and mulInputOf is false there.
      -- mulInputOf at a Cuccaro-block position (3 ≤ p < 2bits+4): below yBase, ≠ ctrl ⇒ false.
      have hpc : p ≠ ulookup_ctrl_idx := by
        unfold inBlock at hpb; unfold ulookup_ctrl_idx; omega
      have hlow : mulInputOf cuccaroAdder 1 bits bits ((c * z) % N) p = false := by
        rw [mulInputOf_low cuccaroAdder 1 bits bits ((c * z) % N) p hpc
              (by show p < 1 + 2 * 1 + cuccaroAdder.span bits
                  show p < 1 + 2 * 1 + (2 * bits + 1); unfold inBlock at hpb; omega)]
      rw [hlow]
      -- the output value at a Cuccaro-block position is clean (carry / acc / addend).
      unfold inBlock at hpb
      -- p = 3 (carry), or p = 2i+4 (acc, hD/hV reversed), or p = 2i+5 (addend)
      rcases Nat.lt_or_ge p (1 + 2 * 1) with h | h
      · omega
      · -- p ∈ [3, 2bits+4): is it carry (3), acc (2i+4) or addend (2i+5)?
        by_cases hc3 : p = 1 + 2 * 1
        · rw [hc3]; exact hC
        · -- p ≥ 4.  Even ⇒ acc (1+2+2i+1 = 2i+4 ⇒ p-4 even... acc is 1+2w+2i+1);
          -- odd ⇒ addend (1+2w+2i+2).
          by_cases hpar : p % 2 = 0
          · -- p even, p ≥ 4: addend wire 1+2·1+2i+2 = 2i+6? No: acc = 1+2+2i+1=2i+4 (even);
            -- addend = 1+2+2i+2 = 2i+5 (odd).  So even ⇒ acc.
            have hi' : (p - 4) / 2 < bits := by omega
            have hpeq : p = 1 + 2 * 1 + 2 * ((p - 4) / 2) + 1 := by omega
            rw [hpeq]; exact hV ((p - 4) / 2) hi'
          · -- p odd, p ≥ 5: addend.
            have hi' : (p - 5) / 2 < bits := by omega
            have hpeq : p = 1 + 2 * 1 + 2 * ((p - 5) / 2) + 2 := by omega
            rw [hpeq]; exact hD ((p - 5) / 2) hi'
    · -- p off the Cuccaro block: is it the flag, or a frame position?
      by_cases hpf : p = 1 + 2 * 1 + (2 * bits + 1) + bits * 1
      · -- flag wire (= 3bits+4): clean by hG; mulInputOf there is encodeReg above y-reg = false.
        rw [hpf, hG]
        have hpc : (1 + 2 * 1 + (2 * bits + 1) + bits * 1 : Nat)
            ≠ ulookup_ctrl_idx := by
          unfold ulookup_ctrl_idx; omega
        rw [mulInputOf_eq_encodeReg cuccaroAdder 1 bits bits ((c * z) % N) _ hpc]
        symm
        show encodeReg (1 + 2 * 1 + cuccaroAdder.span bits) (bits * 1) ((c * z) % N)
            (1 + 2 * 1 + (2 * bits + 1) + bits * 1) = false
        have hspan : (1 + 2 * 1 + cuccaroAdder.span bits) = 1 + 2 * 1 + (2 * bits + 1) := by
          show 1 + 2 * 1 + (2 * bits + 1) = 1 + 2 * 1 + (2 * bits + 1); rfl
        rw [hspan]
        exact encodeReg_high _ _ _ _ (by omega)
      · exact hF p hpb hpf
  · -- frame above the footprint.
    intro p hp
    show Gate.applyNat (mul bits N c cinv) s p = s p
    unfold mul
    exact applyNat_frame (windowedModNMulGate 1 bits N bits c cinv) (mulFoot bits) hmwt s p hp

/-! ## §6. The head state S4 (post moveQuot ; adapter ; X 0), footprint + frame. -/

/-- The head state `S4 = X0 (adapter (moveQuot (divModN (encDiv (z+jN)))))`:
    on the footprint `[0, mulFoot)` it is `mulInputOf cuccaroAdder 1 bits bits z`
    (ctrl set, residue `z` in the y-register, everything else clean); the parked
    quotient `vQ k = mulFoot+k` holds `j.testBit k`; and every other wire `≥ mulFoot`
    is clean. -/
theorem head_state (bits cm N z j : Nat)
    (hbits : 1 ≤ bits) (hN : 0 < N) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits) (hz : z < N) (hj : j < 2 ^ cm) :
    let S4 := Gate.applyNat (Gate.X ctrlIdx)
                (Gate.applyNat (adapter bits)
                  (Gate.applyNat (moveQuot bits cm)
                    (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)))))
    (∀ p, p < mulFoot bits → S4 p = mulInputOf cuccaroAdder 1 bits bits z p)
    ∧ (∀ k, k < cm → S4 (vQ bits k) = j.testBit k)
    ∧ (∀ p, mulFoot bits + cm ≤ p → S4 p = false) := by
  intro S4
  obtain ⟨hS1_data, hS1_quot, hS1_cin, hS1_flag, hS1_read, hS1_high⟩ :=
    divider_state bits cm N z j hbits hN hcm hbudget hz hj
  set S1 := Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) with hS1def
  obtain ⟨hMQ_u, hMQ_v, hMQ_fr⟩ := moveQuot_apply bits cm hcm S1
  set S2 := Gate.applyNat (moveQuot bits cm) S1 with hS2def
  obtain ⟨hA_u, hA_v, hA_fr⟩ := adapter_apply bits S2
  set S3 := Gate.applyNat (adapter bits) S2 with hS3def
  -- S4 = X 0 S3.
  have hS4_apply : ∀ p, S4 p = if p = ctrlIdx then !S3 ctrlIdx else S3 p := by
    intro p
    show Gate.applyNat (Gate.X ctrlIdx) S3 p = _
    rw [Gate.applyNat_X, update_apply]
  -- helper: S2 at a position outside the moveQuot zones = S1.
  have hS2_fr : ∀ p, (∀ k, k < cm → p ≠ uQ bits k ∧ p ≠ vQ bits k) → S2 p = S1 p := hMQ_fr
  -- S2 of a y-register-or-above position is clean (false) unless it's a parked quotient.
  -- First: S2 cleanliness facts we need.
  refine ⟨?_, ?_, ?_⟩
  · -- footprint agreement.
    intro p hp
    rw [hS4_apply p]
    by_cases hp0 : p = ctrlIdx
    · -- ctrl wire: S4 0 = !S3 0 = !false = true = mulInputOf 0.
      rw [hp0, if_pos rfl]
      -- S3 0 = adapter frame at 0 = S2 0 = moveQuot frame at 0 = S1 0 = false.
      have h30 : S3 ctrlIdx = false := by
        rw [hA_fr ctrlIdx (fun i hi => ⟨by simp only [ctrlIdx, uDiv]; omega,
              by simp only [ctrlIdx, vY, yBase]; omega⟩)]
        rw [hS2_fr ctrlIdx (fun k hk => ⟨by simp only [ctrlIdx, uQ, qBase]; omega,
              by simp only [ctrlIdx, vQ, mulFoot]; omega⟩)]
        show S1 0 = false; exact hS1_cin
      rw [h30]
      show (true : Bool) = mulInputOf cuccaroAdder 1 bits bits z 0
      rw [mulInputOf_ctrl0]
    · rw [if_neg hp0]
      have hp0' : p ≠ 0 := by simp only [ctrlIdx] at hp0; exact hp0
      by_cases hpy : ∃ i, i < bits ∧ p = vY bits i
      · -- y-register: S3 (vY i) = S2 (uDiv i) = S1 (uDiv i) = z.testBit i = mulInputOf (vY i).
        obtain ⟨i, hi, rfl⟩ := hpy
        rw [hA_v i hi]
        rw [hS2_fr (uDiv i) (fun k hk => ⟨by simp only [uDiv, uQ, qBase]; omega,
              by simp only [uDiv, vQ, mulFoot]; omega⟩)]
        rw [hS1_data i hi]
        symm; exact mulInputOf_vY bits z i hi
      · -- other footprint positions: clean (= false = mulInputOf).
        push_neg at hpy
        rw [mulInputOf_foot_clean bits z p hp hp0' (fun i hi => hpy i hi)]
        -- S3 p = ? .  p ≠ ctrl, p ≠ vY i, p < mulFoot.
        by_cases hpu : ∃ i, i < bits ∧ p = uDiv i
        · -- p = uDiv i (odd ≤ 2bits-1): S3 (uDiv i) = S2 (vY i) = false.
          obtain ⟨i, hi, rfl⟩ := hpu
          rw [hA_u i hi]
          -- S2 (vY i): vY i = 2bits+4+i.  Either it's a parked-quotient source uQ k, or framed.
          by_cases hvq : ∃ k, k < cm ∧ vY bits i = uQ bits k
          · obtain ⟨k, hk, hvk⟩ := hvq
            rw [hvk, hMQ_u k hk]
            -- S1 (vQ k) = false (vQ k ≥ mulFoot ≥ dimDiv).
            exact hS1_high (vQ bits k) (by simp only [vQ, mulFoot, dimDiv]; omega)
          · push_neg at hvq
            rw [hS2_fr (vY bits i) (fun k hk => ⟨fun h => hvq k hk h, by
                  simp only [vY, vQ, yBase, mulFoot]; omega⟩)]
            -- S1 (vY i): vY i = 2bits+4+i ≥ dimDiv (since it's not a uQ k below dimDiv).
            -- vY i ≥ dimDiv = 2bits+2+cm iff i ≥ cm-2; the i < cm-2 case is a uQ k (excluded).
            exact hS1_high (vY bits i) (by
              -- show dimDiv ≤ vY i.  If vY i < dimDiv then vY i = uQ (vY i - qBase), contradiction.
              by_contra hcon
              push_neg at hcon
              simp only [vY, yBase, qBase, dimDiv] at hcon
              exact hvq (vY bits i - qBase bits)
                (by simp only [vY, yBase, qBase]; omega)
                (by simp only [uQ, vY, yBase, qBase]; omega))
        · -- p not ctrl, not vY, not uDiv, p < mulFoot: a divider read/flag/quotient-region wire.
          push_neg at hpu
          rw [hA_fr p (fun i hi => ⟨fun h => hpu i hi h, fun h => hpy i hi h⟩)]
          -- S2 p: is p a parked-quotient source uQ k?
          by_cases hpq : ∃ k, k < cm ∧ p = uQ bits k
          · obtain ⟨k, hk, rfl⟩ := hpq
            rw [hMQ_u k hk]
            exact hS1_high (vQ bits k) (by simp only [vQ, mulFoot, dimDiv]; omega)
          · push_neg at hpq
            simp only [mulFoot] at hp
            rw [hS2_fr p (fun k hk => ⟨fun h => hpq k hk h, by
                  simp only [vQ, mulFoot]; omega⟩)]
            -- S1 p where p < mulFoot, p ≠ 0, p ≠ uDiv i, p ≠ uQ k.
            -- Classify: p ≥ dimDiv ⇒ high clean; else carry/read/flag/quotient.
            by_cases hpd : dimDiv bits cm ≤ p
            · exact hS1_high p hpd
            · push_neg at hpd
              simp only [dimDiv] at hpd
              -- p < dimDiv, p ≠ 0, p ≠ uDiv i (odd data), p ≠ uQ k (quotient).
              -- So p = even read wire {2i+2} or the flag {2bits+1}.
              by_cases hpfl : p = flagW bits
              · rw [hpfl]; exact hS1_flag
              · simp only [flagW] at hpfl
                have hpne_u : ∀ i, i < bits → p ≠ 2 * i + 1 := by
                  intro i hi h; exact hpu i hi (by show p = uDiv i; unfold uDiv; exact h)
                have hpne_q : ∀ k, k < cm → p ≠ 2 * bits + 2 + k := by
                  intro k hk h; exact hpq k hk (by show p = uQ bits k; unfold uQ qBase; exact h)
                -- p even read wire 2i+2 with i<bits.
                have hp_le : p ≤ 2 * bits := by
                  by_contra hgt
                  push_neg at hgt
                  exact hpne_q (p - (2 * bits + 2)) (by omega) (by omega)
                have hpeven : p % 2 = 0 := by
                  by_contra hodd
                  exact hpne_u ((p - 1) / 2) (by omega) (by omega)
                have hpread : ∃ i, i < bits ∧ p = 0 + 2 * i + 2 :=
                  ⟨(p - 2) / 2, by omega, by omega⟩
                obtain ⟨i, hi, rfl⟩ := hpread
                exact hS1_read i hi
  · -- parked quotient values.
    intro k hk
    rw [hS4_apply (vQ bits k)]
    rw [if_neg (by simp only [vQ, ctrlIdx, mulFoot]; omega)]
    -- S3 (vQ k) = adapter frame (vQ k not uDiv/vY) = S2 (vQ k) = S1 (uQ k) = j.testBit k.
    rw [hA_fr (vQ bits k) (fun i hi => ⟨by simp only [vQ, uDiv, mulFoot]; omega,
          by simp only [vQ, vY, yBase, mulFoot]; omega⟩)]
    rw [hMQ_v k hk]
    exact hS1_quot k hk
  · -- everything ≥ mulFoot+cm is clean.
    intro p hp
    simp only [mulFoot] at hp
    rw [hS4_apply p]
    rw [if_neg (by simp only [ctrlIdx]; omega)]
    rw [hA_fr p (fun i hi => ⟨by simp only [uDiv]; omega,
          by simp only [vY, yBase]; omega⟩)]
    rw [hS2_fr p (fun k hk => ⟨by simp only [uQ, qBase]; omega,
          by simp only [vQ, mulFoot]; omega⟩)]
    exact hS1_high p (by simp only [dimDiv]; omega)

/-! ## §7. Involutions of the swap adapters and the control flip. -/

/-- A `swapCascade` (with the injectivity/disjointness hypotheses) is self-inverse
    as a state transform. -/
theorem swapCascade_involution (u v : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (hu_inj : ∀ i k, i < n → k < n → i ≠ k → u i ≠ u k)
    (hv_inj : ∀ i k, i < n → k < n → i ≠ k → v i ≠ v k)
    (huv : ∀ i k, i < n → k < n → u i ≠ v k) :
    Gate.applyNat (swapCascade u v n) (Gate.applyNat (swapCascade u v n) f) = f := by
  obtain ⟨h1u, h1v, h1fr⟩ := swapCascade_apply u v n f hu_inj hv_inj huv
  obtain ⟨h2u, h2v, h2fr⟩ :=
    swapCascade_apply u v n (Gate.applyNat (swapCascade u v n) f) hu_inj hv_inj huv
  funext p
  by_cases hpu : ∃ i, i < n ∧ p = u i
  · obtain ⟨i, hi, rfl⟩ := hpu
    rw [h2u i hi, h1v i hi]
  · by_cases hpv : ∃ i, i < n ∧ p = v i
    · obtain ⟨i, hi, rfl⟩ := hpv
      rw [h2v i hi, h1u i hi]
    · push_neg at hpu hpv
      rw [h2fr p (fun i hi => ⟨fun h => hpu i hi h, fun h => hpv i hi h⟩),
          h1fr p (fun i hi => ⟨fun h => hpu i hi h, fun h => hpv i hi h⟩)]

theorem adapter_involution (bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (adapter bits) (Gate.applyNat (adapter bits) f) = f := by
  unfold adapter
  exact swapCascade_involution uDiv (vY bits) bits f
    (fun i k _ _ h => by unfold uDiv; omega) (vY_inj bits) (uDiv_ne_vY bits)

theorem moveQuot_involution (bits cm : Nat) (hcm : cm ≤ bits) (f : Nat → Bool) :
    Gate.applyNat (moveQuot bits cm) (Gate.applyNat (moveQuot bits cm) f) = f := by
  unfold moveQuot
  exact swapCascade_involution (uQ bits) (vQ bits) cm f
    (fun i k hi hk h => uQ_inj bits i k (by omega) (by omega) h)
    (fun i k hi hk h => vQ_inj bits i k (by omega) (by omega) h)
    (uQ_ne_vQ bits cm hcm)

theorem X0_involution (f : Nat → Bool) :
    Gate.applyNat (Gate.X ctrlIdx) (Gate.applyNat (Gate.X ctrlIdx) f) = f :=
  FormalRV.Shor.GidneyInPlace.GateReversible.applyNat_X_involution ctrlIdx f

/-! ## §8. Stage-mid full-state equality: `S8 = divModN (encDiv w)`. -/

/-- The state after the SIX middle stages
    `moveQuot ∘ adapter ∘ X0 ∘ mul ∘ X0 ∘ adapter ∘ moveQuot` applied to
    `divModN (encDiv (z+jN))` EQUALS the divider applied to the clean encoding of
    `w = (c·z)%N + j·N`, on EVERY wire.  The bridge for the final reverse-cancel.

    Strategy: the post-`mul` state `S5` equals `R4 := X0(adapter(moveQuot R))` (the
    head-half applied to the target `R = divModN (encDiv w)`), shown by full-state
    equality from `head_state` (for residue `z` AND residue `(c·z)%N`) + `mul_leg`.
    The back-half is then the inverse of the head-half: `X0`, `adapter`, `moveQuot`
    are each involutions, applied in reverse order, so `back(R4) = R`. -/
theorem stage_mid_eq (bits cm N c cinv z j : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (hz : z < N) (hj : j < 2 ^ cm) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    Gate.applyNat (moveQuot bits cm)
        (Gate.applyNat (adapter bits)
          (Gate.applyNat (Gate.X ctrlIdx)
            (Gate.applyNat (mul bits N c cinv)
              (Gate.applyNat (Gate.X ctrlIdx)
                (Gate.applyNat (adapter bits)
                  (Gate.applyNat (moveQuot bits cm)
                    (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)))))))))
      = Gate.applyNat (divModN bits cm N) (encDiv bits ((c * z) % N + j * N)) := by
  have hczN : (c * z) % N < N := Nat.mod_lt _ hN_pos
  obtain ⟨hS4_foot, hS4_quot, hS4_high⟩ :=
    head_state bits cm N z j hbits hN_pos hcm hbudget hz hj
  set S4 := Gate.applyNat (Gate.X ctrlIdx)
              (Gate.applyNat (adapter bits)
                (Gate.applyNat (moveQuot bits cm)
                  (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N))))) with hS4def
  obtain ⟨hS5_y, hS5_foot, hS5_high⟩ :=
    mul_leg bits N c cinv z hbits hN_pos hN2 hz hcinv hinv S4 hS4_foot
  set S5 := Gate.applyNat (mul bits N c cinv) S4 with hS5def
  obtain ⟨hR4_foot, hR4_quot, hR4_high⟩ :=
    head_state bits cm N ((c * z) % N) j hbits hN_pos hcm hbudget hczN hj
  set R := Gate.applyNat (divModN bits cm N) (encDiv bits ((c * z) % N + j * N)) with hRdef
  set R4 := Gate.applyNat (Gate.X ctrlIdx)
              (Gate.applyNat (adapter bits)
                (Gate.applyNat (moveQuot bits cm) R)) with hR4def
  -- Step 1: S5 = R4 (full-state equality).
  have hS5_eq_R4 : S5 = R4 := by
    funext p
    by_cases hpm : p < mulFoot bits
    · rw [hS5_foot p hpm, hR4_foot p hpm]
    · push_neg at hpm
      by_cases hpvq : ∃ k, k < cm ∧ p = vQ bits k
      · obtain ⟨k, hk, rfl⟩ := hpvq
        rw [hS5_high (vQ bits k) (by simp only [vQ]; omega), hS4_quot k hk, hR4_quot k hk]
      · push_neg at hpvq
        by_cases hpc : mulFoot bits + cm ≤ p
        · rw [hS5_high p hpm, hS4_high p hpc, hR4_high p hpc]
        · push_neg at hpc
          exact absurd (show p = vQ bits (p - mulFoot bits) by simp only [vQ]; omega)
            (hpvq (p - mulFoot bits) (by simp only [mulFoot] at hpm hpc ⊢; omega))
  -- Step 2: back-half (moveQuot ∘ adapter ∘ X0) of R4 = R, by involutions.
  show Gate.applyNat (moveQuot bits cm)
      (Gate.applyNat (adapter bits) (Gate.applyNat (Gate.X ctrlIdx) S5)) = R
  rw [hS5_eq_R4]
  have hx : Gate.applyNat (Gate.X ctrlIdx) R4
      = Gate.applyNat (adapter bits) (Gate.applyNat (moveQuot bits cm) R) := by
    rw [hR4def]; exact X0_involution _
  rw [hx, adapter_involution bits (Gate.applyNat (moveQuot bits cm) R)]
  exact moveQuot_involution bits cm hcm R

/-! ## §9. HEADLINE: the compressed guarded-shift-gate decode. -/

/-- `w = (c·z)%N + j·N < 2^bits` on the support. -/
theorem result_lt (bits cm N c z j : Nat) (hN_pos : 0 < N)
    (hj : j < 2 ^ cm) (hbudget : 2 ^ cm * N ≤ 2 ^ bits) :
    (c * z) % N + j * N < 2 ^ bits := by
  have hczN : (c * z) % N < N := Nat.mod_lt _ hN_pos
  calc (c * z) % N + j * N < N + j * N := by omega
    _ = (j + 1) * N := by ring
    _ ≤ 2 ^ cm * N := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 ^ bits := hbudget

/-- **THE COMPRESSED GUARDED-SHIFT GATE DECODE, fully assembled and kernel-clean.**
    On the support `v = z + j·N` (`z < N`, `j < 2^cm`, `cm ≤ bits`, budget
    `2^cm·N ≤ 2^bits`, `2N ≤ 2^bits`, `c·cinv ≡ 1 [N]`, `cinv < N`), running
    `cgsGate` on the clean input `encDiv bits v`:
      • the WHOLE output state EQUALS `encDiv bits ((c·z)%N + j·N)` — data band decodes
        to `(c·z)%N + j·N`, and ALL transient/quotient wires are restored clean,
      • the data-band value is `guardedShift (2^bits) N c (z + j·N)`,
      • the gate is WellTyped at the COMPRESSED dimension `cgsDim bits cm`. -/
theorem cgsGate_decode
    (bits cm N c cinv z j : Nat)
    (hbits : 1 ≤ bits) (hN : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (hz : z < N) (hj : j < 2 ^ cm) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    Gate.applyNat (cgsGate bits cm N c cinv) (encDiv bits (z + j * N))
        = encDiv bits ((c * z) % N + j * N)
    ∧ cuccaro_target_val bits 0
        (Gate.applyNat (cgsGate bits cm N c cinv) (encDiv bits (z + j * N)))
        = (c * z) % N + j * N
    ∧ guardedShift (2 ^ bits) N c (z + j * N) = (c * z) % N + j * N
    ∧ Gate.WellTyped (cgsDim bits cm) (cgsGate bits cm N c cinv) := by
  have hN_pos : 0 < N := by omega
  have hw_lt : (c * z) % N + j * N < 2 ^ bits := result_lt bits cm N c z j hN_pos hj hbudget
  have hdiv_wt : Gate.WellTyped (dimDiv bits cm) (divModN bits cm N) :=
    divModN_wellTyped bits cm N hbits hcm
  have hstate : Gate.applyNat (cgsGate bits cm N c cinv) (encDiv bits (z + j * N))
      = encDiv bits ((c * z) % N + j * N) := by
    unfold cgsGate
    simp only [Gate.applyNat_seq]
    rw [show Gate.applyNat (Gate.reverse (divModN bits cm N))
          (Gate.applyNat (moveQuot bits cm)
            (Gate.applyNat (adapter bits)
              (Gate.applyNat (Gate.X ctrlIdx)
                (Gate.applyNat (mul bits N c cinv)
                  (Gate.applyNat (Gate.X ctrlIdx)
                    (Gate.applyNat (adapter bits)
                      (Gate.applyNat (moveQuot bits cm)
                        (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N))))))))))
        = Gate.applyNat (Gate.reverse (divModN bits cm N))
            (Gate.applyNat (divModN bits cm N) (encDiv bits ((c * z) % N + j * N)))
        from by rw [stage_mid_eq bits cm N c cinv z j hbits hN_pos hN2 hcm hbudget hz hj hcinv hinv]]
    exact applyNat_reverse_cancel (divModN bits cm N) (dimDiv bits cm) hdiv_wt
      (encDiv bits ((c * z) % N + j * N))
  refine ⟨hstate, ?_, ?_, ?_⟩
  · rw [hstate]
    exact cuccaro_target_val_encDiv bits ((c * z) % N + j * N) hw_lt
  · exact guarded_on_support (2 ^ bits) N cm c z j hN_pos hz hj hbudget
  · exact cgsGate_wellTyped bits cm N c cinv hbits hcm

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayGuardedShift
