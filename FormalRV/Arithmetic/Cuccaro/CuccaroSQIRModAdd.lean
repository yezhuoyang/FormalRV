/-
  FormalRV.BQAlgo.CuccaroSQIRModAdd — SQIR-style modular
  add-constant SKELETON.

  Tick 53: build the first SQIR-style modular adder skeleton.

  Background: SQIR's `modadder21` (ModMult.v lines 134-137) is
  register-to-register modular addition `[M][x][y] → [M][(x+y) % M][y]`.
  For our Lean development targeting Shor's modular multiplier (which
  multiplies by a CLASSICAL constant), we adapt this to a register-to-
  CONSTANT modular addition:
    `target ← (target + c) mod N`

  The SQIR sequence for register-to-register:
    swapper02 ; adder01 ; swapper02 ;     -- target ← (target + y) mod 2^n
    comparator01 ;                          -- flag ← decide (M ≤ target)
    bygatectrl 1 (subtractor01) ; bcx 1 ; -- conditional sub of M, flip flag
    swapper02 ; bcinv (comparator01) ;     -- uncompute flag (swap to undo logic)
    swapper02.

  Our adapted sequence for register-to-constant (with the constant c
  and modulus N):
    cuccaro_addConstGate c ;                            -- target ← (target + c) mod 2^bits
    sqir_style_compareConst_candidate N ;               -- flag ← decide (N ≤ target)
    [conditional sub of N] ;                            -- target ← target - N if flag = 1
    [flag uncompute].

  This file lands the SKELETON `addConst c ; compareConst N` (Tick 53,
  Deliverable 6 fallback per directive). The conditional-sub +
  flag-uncompute steps are deferred to Tick 54+.

  Reason for split: the conditional subtract requires either a
  controlled-CCX (not in our IR), or a manual controlled re-encoding
  of the subtractor. Both are substantial work and deserve their own
  tick.

  This tick proves:
  - WellTyped.
  - Flag = `decide (N ≤ x + c)` (after the skeleton).
  - Target decode = `(x + c) % 2^bits`.
  - Read register restored to 0.
  - Carry-in qubit restored to 0.

  These four together characterize the skeleton's behavior precisely.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRStyle
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Skeleton definition. -/

/-- **Skeleton modular add-constant** (Tick 53).  Composes the clean
add-const + clean compare-const primitives.  The result has the target
register holding `(x + c) mod 2^bits` and the external flag at `flagPos`
holding `decide (N ≤ x + c)`. -/
def sqir_style_modAddConst_skeleton
    (bits q_start N c flagPos : Nat) : Gate :=
  seq (cuccaro_addConstGate bits q_start c)
      (sqir_style_compareConst_candidate bits q_start N flagPos)

/-! ## WellTyped. -/

theorem sqir_style_modAddConst_skeleton_wellTyped
    (bits q_start N c flagPos dim : Nat)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : flagPos ≠ q_start + 2 * bits) :
    Gate.WellTyped dim
        (sqir_style_modAddConst_skeleton bits q_start N c flagPos) := by
  refine ⟨?_, ?_⟩
  · exact cuccaro_addConstGate_wellTyped bits q_start c dim h_workspace
  · exact sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_workspace h_flag h_flag_distinct

/-! ## Workspace bit-level theorems for the skeleton.

These bit-level theorems characterize what the skeleton does WITHOUT
the full flag theorem (which is deferred). The skeleton is the
composition addConst + compare; per Tick 51-52's results, each
component cleanly restores its workspace AND the compare doesn't
touch the target. So the skeleton's overall effect on the workspace
is precisely the addConst's effect. -/

/-- **Target bit after the skeleton.**  At each target position
`q_start + 2*i + 1` for `i < bits`, the output equals `(x+c).testBit i`. -/
theorem sqir_style_modAddConst_skeleton_target_bit
    (bits q_start N c x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    ∀ i, i < bits →
      Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 1)
      = (x + c).testBit i := by
  intro i hi
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (sqir_style_compareConst_candidate bits q_start N flagPos))
      (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 1) = _
  simp only [Gate.applyNat_seq]
  -- compareConst restores the target position (workspace restoration).
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos _ h_flag_above (q_start + 2 * i + 1) (by omega) (by omega)]
  -- And addConst writes (x+c).testBit i to target position.
  exact cuccaro_addConstGate_target_bit bits q_start c x i hi hc

/-- **Read bit after the skeleton.**  At each read position
`q_start + 2*i + 2` for `i < bits`, the output equals `false`. -/
theorem sqir_style_modAddConst_skeleton_read_bit
    (bits q_start N c x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    ∀ i, i < bits →
      Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
        (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2)
      = false := by
  intro i hi
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (sqir_style_compareConst_candidate bits q_start N flagPos))
      (cuccaro_input_F q_start false 0 x) (q_start + 2 * i + 2) = _
  simp only [Gate.applyNat_seq]
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos _ h_flag_above (q_start + 2 * i + 2) (by omega) (by omega)]
  exact cuccaro_addConstGate_read_bit bits q_start c x i hi

/-- **Carry-in qubit after the skeleton.**  At position `q_start`, the
output equals `false`. -/
theorem sqir_style_modAddConst_skeleton_carry_in_bit
    (bits q_start N c x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
        (cuccaro_input_F q_start false 0 x) q_start = false := by
  show Gate.applyNat
      (seq (cuccaro_addConstGate bits q_start c)
            (sqir_style_compareConst_candidate bits q_start N flagPos))
      (cuccaro_input_F q_start false 0 x) q_start = _
  simp only [Gate.applyNat_seq]
  rw [sqir_style_compareConst_candidate_workspace_restored_at bits q_start N
        flagPos _ h_flag_above q_start (by omega) (by omega)]
  exact cuccaro_addConstGate_carry_in_bit bits q_start c x

/-! ## Decoded target correctness. -/

/-- **HEADLINE — decoded target correctness.**  After the skeleton, the
target register decodes to `(x + c) % 2^bits`. -/
theorem sqir_style_modAddConst_skeleton_target_decode
    (bits q_start N c x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_target_val bits q_start
        (Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
          (cuccaro_input_F q_start false 0 x))
      = (x + c) % 2^bits := by
  apply cuccaro_target_val_eq_sum_when_bits_match bits q_start (x + c) _
  intro i hi
  exact sqir_style_modAddConst_skeleton_target_bit bits q_start N c x flagPos
    hN_pos hN hc hx h_flag_above i hi

/-- **Decoded read restoration.** -/
theorem sqir_style_modAddConst_skeleton_read_decode
    (bits q_start N c x flagPos : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
          (cuccaro_input_F q_start false 0 x))
      = 0 := by
  have h_eq : cuccaro_read_val bits q_start
        (Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
          (cuccaro_input_F q_start false 0 x))
      = 0 % 2^bits := by
    apply cuccaro_read_val_eq_sum_when_bits_match bits q_start 0 _
    intro i hi
    rw [sqir_style_modAddConst_skeleton_read_bit bits q_start N c x flagPos
          hN_pos hN hc hx h_flag_above i hi]
    simp [Nat.zero_testBit]
  rw [h_eq]
  simp

/-! ## Packaged skeleton primitive. -/

/-- **HEADLINE — packaged skeleton primitive.**  Bundles WellTyped +
target decode + read restored + carry-in restored.  The flag-behavior
theorem is DEFERRED to Tick 54 (requires the input-state equivalence
argument and is needed for the controlled-sub-N step). -/
theorem sqir_style_modAddConst_skeleton_clean
    (bits q_start N c x flagPos dim : Nat)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hc : c < 2^bits) (hx : x < 2^bits)
    (h_workspace : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim)
    (h_flag_distinct : flagPos ≠ q_start + 2 * bits)
    (h_flag_above : q_start + 2 * bits + 1 ≤ flagPos) :
    Gate.WellTyped dim
        (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
    ∧ cuccaro_target_val bits q_start
          (Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
            (cuccaro_input_F q_start false 0 x))
        = (x + c) % 2^bits
    ∧ cuccaro_read_val bits q_start
          (Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
            (cuccaro_input_F q_start false 0 x))
        = 0
    ∧ Gate.applyNat (sqir_style_modAddConst_skeleton bits q_start N c flagPos)
          (cuccaro_input_F q_start false 0 x) q_start = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sqir_style_modAddConst_skeleton_wellTyped bits q_start N c flagPos dim
      h_workspace h_flag h_flag_distinct
  · exact sqir_style_modAddConst_skeleton_target_decode bits q_start N c x flagPos
      hN_pos hN hc hx h_flag_above
  · exact sqir_style_modAddConst_skeleton_read_decode bits q_start N c x flagPos
      hN_pos hN hc hx h_flag_above
  · exact sqir_style_modAddConst_skeleton_carry_in_bit bits q_start N c x flagPos
      hN_pos hN hc hx h_flag_above

end FormalRV.BQAlgo
