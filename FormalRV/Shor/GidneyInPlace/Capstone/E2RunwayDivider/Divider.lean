/- E2RunwayDivider — Â§4-4b full divider gate + wellTyped.  Part of the `E2RunwayDivider` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.Setup

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (compareConstXor_state_general condSub_state_general)


/-! ## §4. The full divider gate (cm-step long division).

  We process `k = cm−1, …, 0`.  Step `k` runs `divStep` on the width-`(bits − k)`
  window at base `q_start + 2·k` (so it subtracts `N·2^k` when the running top
  exceeds it), writing quotient bit `k` to `qBase bits + k`.  The single flag wire
  `flagPos := 2·bits+1` is reused across steps (it is returned clean by each step).
-/

/-- The shared flag wire (one fresh qubit above the data/read block). -/
def flagW (bits : Nat) : Nat := 2 * bits + 1

/-- Step `k` of the divider: `divStep` on the top `bits − k` bits, quotient → wire
    `qBase bits + k`. -/
def divStepAt (bits N k : Nat) : Gate :=
  divStep (bits - k) (2 * k) N (flagW bits) (qBase bits + k)

/-- The full divider, by descending recursion on the number of steps `cm`:
    process the TOP bit `k = cm−1` first (`divStepAt bits N (cm−1)`), then the
    `cm−1`-step divider on the remaining lower bits.  So
    `divModN bits (cm+1) N = Gate.seq (divStepAt bits N cm) (divModN bits cm N)`. -/
def divModN (bits : Nat) : Nat → Nat → Gate
  | 0,      _ => Gate.I
  | cm + 1, N => Gate.seq (divStepAt bits N cm) (divModN bits cm N)

/-! ## §4b. WellTyped for the full divider. -/

/-- Each divider step is well-typed at `dimDiv bits cm`, provided `1 ≤ bits` and
    `k < cm ≤ bits` (so every window `[2k, 2k+2(bits−k)+1)` and quotient wire fits). -/
theorem divStepAt_wellTyped (bits cm N k : Nat)
    (_hbits : 1 ≤ bits) (hk : k < cm) (hcm : cm ≤ bits) :
    Gate.WellTyped (dimDiv bits cm) (divStepAt bits N k) := by
  unfold divStepAt
  have hkb : k ≤ bits := by omega
  -- workspace of the window: 2k + 2*(bits−k) + 1 = 2*bits + 1 ≤ dimDiv
  have h_ws : 2 * k + 2 * (bits - k) + 1 ≤ dimDiv bits cm := by
    unfold dimDiv; omega
  have h_flag : flagW bits < dimDiv bits cm := by unfold flagW dimDiv; omega
  have h_qbit : qBase bits + k < dimDiv bits cm := by unfold qBase dimDiv; omega
  apply divStep_wellTyped (bits - k) (2 * k) N (flagW bits) (qBase bits + k)
    (dimDiv bits cm) h_ws h_flag h_qbit
  · intro i hi; unfold flagW; omega
  · unfold flagW; omega
  · unfold qBase flagW; omega

/-- Monotonicity of well-typedness in the dimension (a gate WellTyped at `d` is
    WellTyped at any `d' ≥ d`). -/
theorem wellTyped_mono : ∀ (g : Gate) (d d' : Nat), d ≤ d' →
    Gate.WellTyped d g → Gate.WellTyped d' g := by
  intro g
  induction g with
  | I => intro d d' hd h; exact lt_of_lt_of_le h hd
  | X q => intro d d' hd h; exact lt_of_lt_of_le h hd
  | CX a b => intro d d' hd h; exact ⟨lt_of_lt_of_le h.1 hd, lt_of_lt_of_le h.2.1 hd, h.2.2⟩
  | CCX a b c => intro d d' hd h
                 exact ⟨lt_of_lt_of_le h.1 hd, lt_of_lt_of_le h.2.1 hd,
                        lt_of_lt_of_le h.2.2.1 hd, h.2.2.2⟩
  | seq g₁ g₂ ih₁ ih₂ => intro d d' hd h; exact ⟨ih₁ d d' hd h.1, ih₂ d d' hd h.2⟩

/-- **The full divider is well-typed** at `dimDiv bits cm` (for `1 ≤ bits`,
    `cm ≤ bits`).  By recursion on `cm`; each step is `divStepAt_wellTyped`,
    monotone-lifted from `dimDiv bits cm'` to `dimDiv bits cm`. -/
theorem divModN_wellTyped (bits cm N : Nat)
    (hbits : 1 ≤ bits) (hcm : cm ≤ bits) :
    Gate.WellTyped (dimDiv bits cm) (divModN bits cm N) := by
  induction cm with
  | zero => show 0 < dimDiv bits 0; unfold dimDiv; omega
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · -- top step at k, well-typed at dimDiv bits (k+1)
      exact divStepAt_wellTyped bits (k + 1) N k hbits (by omega) hcm
    · -- the k-step divider, lifted from dimDiv bits k to dimDiv bits (k+1)
      exact wellTyped_mono (divModN bits k N) (dimDiv bits k) (dimDiv bits (k + 1))
        (by unfold dimDiv; omega) (ih (by omega))


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
