import FormalRV.Arithmetic.SQIRModMult
import FormalRV.Shor.VerifiedShor.MultiplierStepInterface

namespace VerifiedShor
namespace MultiplierStep
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open FormalRV.Framework (Gate update)




/-! ### Level-2 layout structure

`MultiplierStepLayout` adds multiplier-register-specific positions
and the install machinery to a base `ControlledModAddLayout`.  It is
data-level only; semantic theorems are stated as wrapper aliases on
specific instances rather than bundled fields. -/
structure MultiplierStepLayout where
  /-- The underlying Level-1 controlled-mod-add layout. -/
  base             : ControlledModAdd.ControlledModAddLayout
  /-- Position of multiplier bit `j` (controls the j-th add step). -/
  multControlIdx   : (bits j : Nat) → Nat
  /-- Position of accumulator bit `i` (the target register). -/
  targetBitIdx     : (bits i : Nat) → Nat
  /-- Multiplier input encoder combining the accumulator and the
  multiplier bits. -/
  multInputEncode  : (bits m acc : Nat) → Nat → Bool
  /-- Install-then-skip-j helper: install the first `num_bits` of
  multiplier `m` into the state-function while skipping bit `j`. -/
  installStepInput : (bits m j num_bits : Nat) → (Nat → Bool) → (Nat → Bool)

/-! ### SQIR/Cuccaro multiplier-step layout instance -/
def sqirCuccaroLayout : MultiplierStepLayout where
  base             := ControlledModAdd.sqirCuccaroLayout
  multControlIdx   := sqir_mult_control_idx
  targetBitIdx     := fun _ i => sqir_target_idx i
  multInputEncode  := sqir_mult_input_F
  installStepInput := install_mult_bits_skip_j

/-! ### Public aliases for position / disjointness facts -/

theorem sqirCuccaro_controlIdx_allowed (bits j : Nat) :
    sqir_mult_control_idx bits j < 2
      ∨ 2 + 2 * bits + 1 ≤ sqir_mult_control_idx bits j :=
  sqir_mult_control_idx_outside_modadd_workspace_form bits j

theorem sqirCuccaro_controlIdx_ne_flag (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 1 :=
  sqir_mult_control_idx_ne_flag bits j

theorem sqirCuccaro_controlIdx_ne_topCarry (bits j : Nat) :
    sqir_mult_control_idx bits j ≠ 2 + 2 * bits :=
  sqir_mult_control_idx_ne_top_carry bits j

theorem sqirCuccaro_controlIdx_lt_dim
    (bits j : Nat) (hj : j < bits) :
    sqir_mult_control_idx bits j < sqir_modmult_rev_anc bits :=
  sqir_mult_control_idx_lt_sqir_dim bits j hj

theorem sqirCuccaro_controlIdx_injective
    (bits j j' : Nat)
    (h : sqir_mult_control_idx bits j = sqir_mult_control_idx bits j') :
    j = j' :=
  sqir_mult_control_idx_injective bits j j' h

theorem sqirCuccaro_targetBitIdx_eq (i : Nat) :
    sqir_target_idx i = 2 + 2 * i + 1 := rfl

/-! ### Public aliases for input-encoding facts -/

theorem sqirCuccaro_input_targetDecode
    (bits m acc : Nat) (hacc : acc < 2 ^ bits) :
    cuccaro_target_val bits 2 (sqir_mult_input_F bits m acc) = acc :=
  sqir_mult_input_target_decode bits m acc hacc

theorem sqirCuccaro_input_readDecode (bits m acc : Nat) :
    cuccaro_read_val bits 2 (sqir_mult_input_F bits m acc) = 0 :=
  sqir_mult_input_read_decode bits m acc

theorem sqirCuccaro_input_flagFalse (bits m acc : Nat) :
    sqir_mult_input_F bits m acc 1 = false :=
  sqir_mult_input_flag_1_false bits m acc

theorem sqirCuccaro_input_topCarryFalse
    (bits m acc : Nat) (hbits : 1 ≤ bits) :
    sqir_mult_input_F bits m acc (2 + 2 * bits) = false :=
  sqir_mult_input_top_carry_false bits m acc hbits

theorem sqirCuccaro_input_controlBit
    (bits m acc j : Nat) (hj : j < bits) :
    sqir_mult_input_F bits m acc (sqir_mult_control_idx bits j) = m.testBit j :=
  sqir_mult_input_control_bit bits m acc j hj

/-! ### Public aliases for install / commutation bridge facts -/

open FormalRV.Framework in
theorem sqirCuccaro_input_eq_install_with_j
    (bits m acc j : Nat) (hj : j < bits) (hacc : acc < 2 ^ bits) :
    sqir_mult_input_F bits m acc
      = install_mult_bits_skip_j bits m j bits
          (update (cuccaro_input_F 2 false 0 acc)
            (sqir_mult_control_idx bits j) (m.testBit j)) :=
  sqir_mult_input_F_eq_install_with_j bits m acc j hj hacc

theorem sqirCuccaro_targetDecode_through_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    cuccaro_target_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_target_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) :=
  cuccaro_target_val_through_install_mult bits m j N c num_bits f

theorem sqirCuccaro_controlledModAdd_commute_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f)
      = install_mult_bits_skip_j bits m j num_bits
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) :=
  sqir_style_controlledModAddConst_gate_commute_install bits m j N c num_bits f

/-! Three additional through-install aliases consumed by the
workspace wrapper theorem (Phase R6c). -/

theorem sqirCuccaro_readDecode_through_install
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    cuccaro_read_val bits 2
        (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1)
          (install_mult_bits_skip_j bits m j num_bits f))
      = cuccaro_read_val bits 2
          (Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
            (sqir_mult_control_idx bits j) 1) f) :=
  cuccaro_read_val_through_install_mult bits m j N c num_bits f

theorem sqirCuccaro_applyNat_through_install_at_workspace
    (bits m j N c num_bits q : Nat) (f : Nat → Bool)
    (hq_ws : q < 2 + 2 * bits + 1) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) q
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f q :=
  applyNat_modmult_through_install_at_workspace bits m j N c num_bits q f hq_ws

theorem sqirCuccaro_applyNat_through_install_at_j
    (bits m j N c num_bits : Nat) (f : Nat → Bool) :
    Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1)
      (install_mult_bits_skip_j bits m j num_bits f) (sqir_mult_control_idx bits j)
      = Gate.applyNat (sqir_style_controlledModAddConst_gate bits 2 N c
        (sqir_mult_control_idx bits j) 1) f (sqir_mult_control_idx bits j) :=
  applyNat_modmult_through_install_at_j bits m j N c num_bits f

/-- The k-th multiplier bit (with `k ≠ j`) is set to `m.testBit k`
after running the install. -/
theorem sqirCuccaro_install_at_mult_k_eq
    (bits m j num_bits k : Nat) (f : Nat → Bool)
    (h_k_lt : k < num_bits) (h_k_ne_j : k ≠ j) :
    install_mult_bits_skip_j bits m j num_bits f (sqir_mult_control_idx bits k)
      = m.testBit k :=
  install_mult_bits_skip_j_at_mult_k_eq bits m j num_bits k f h_k_lt h_k_ne_j

/-! ### Fine-grained per-position aliases (Phase R5b' for R6f-real)

These 5 aliases expose per-position facts that the 6-conjunct
`ControlledModAddImpl.clean` bundle does NOT cover.  Together with
R6b/R6c/R6e, they unlock a real interface-routed proof of the
one-step state equality (`sqir_modmult_step_state_eq`).

The clean bundle is value-level (target/read/topCarry/flag/control);
these aliases are bit/position-level.  They are interface exposure
aliases (option 1 of loop rules) — pure wrappers around existing
SQIR lemmas. -/

theorem sqirCuccaro_step_flag0_false
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hj : j < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) 0 = false :=
  sqir_modmult_step_flag0_false bits N a j m acc hbits hj

theorem sqirCuccaro_step_above_layout_false
    (bits N a j m acc q : Nat) (hbits : 1 ≤ bits) (hj : j < bits)
    (hq : q ≥ 2 + 2 * bits + 1 + bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) q = false :=
  sqir_modmult_step_above_layout_false bits N a j m acc q hbits hj hq

theorem sqirCuccaro_step_carryIn_restored
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) 2 = false :=
  sqir_modmult_step_carry_in_restored bits N a j m acc hbits hN_pos hN hN2 hj hacc

theorem sqirCuccaro_step_targetBit_extracted
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) (2 + 2 * i + 1)
      = (if m.testBit j then (acc + (a * 2^j) % N) % N else acc).testBit i :=
  sqir_modmult_step_target_bit bits N a j m acc i hbits hN_pos hN hN2 hj hacc hi

theorem sqirCuccaro_step_readBit_zero
    (bits N a j m acc i : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) (hi : i < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc) (2 + 2 * i + 2) = false :=
  sqir_modmult_step_read_bit bits N a j m acc i hbits hN_pos hN hN2 hj hacc hi

/-! ### Smoke theorems

These demonstrate that the Level-2 layout connects sensibly to the
Level-1 layout: the SQIR multiplier control positions land in the
Level-1 `controlAllowed` region, and the SQIR multiplier input
decodes the accumulator through the Level-1 `targetDecode`. -/

theorem sqirCuccaro_controlIdx_controlAllowed (bits j : Nat) :
    ControlledModAdd.sqirCuccaroLayout.controlAllowed bits
      (sqir_mult_control_idx bits j) :=
  sqir_mult_control_idx_outside_modadd_workspace_form bits j

theorem sqirCuccaro_multInput_targetDecode
    (bits m acc : Nat) (hacc : acc < 2 ^ bits) :
    ControlledModAdd.sqirCuccaroLayout.targetDecode bits
      (sqir_mult_input_F bits m acc) = acc :=
  sqir_mult_input_target_decode bits m acc hacc

/-! ### First proof-chain theorem via interfaces (Phase R6b)

`sqirCuccaro_step_targetDecode_via_interface` proves the same fact as
the existing `sqir_modmult_step_target_decode` (`SQIRModMult.lean:501`),
but states it through the new layout stack and proves it through the
R5b/R5c aliases — no direct call to
`sqir_style_controlledModAddConst_gate_clean`.

The proof mirrors the original 4-step skeleton:
1. `hacc_lt : acc < 2^bits` (Mathlib `Nat.lt_of_lt_of_le`).
2. Convert `multInputEncode` to install form via
   `sqirCuccaro_input_eq_install_with_j` (R5c alias).
3. Push `targetDecode` through `installStepInput` via
   `sqirCuccaro_targetDecode_through_install` (R5c alias).
4. Close with the Level-1 `ControlledModAdd.clean_targetDecode`
   projection applied to `ControlledModAdd.sqirCuccaroImpl`.

The original `sqir_modmult_step_target_decode` is NOT changed. -/
theorem sqirCuccaro_step_targetDecode_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    ControlledModAdd.sqirCuccaroLayout.targetDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc))
      = if m.testBit j then (acc + (a * 2^j) % N) % N else acc := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  have h_ctrl_allowed := sqirCuccaro_controlIdx_controlAllowed bits j
  have h_ctrl_ne_flag := sqirCuccaro_controlIdx_ne_flag bits j
  have h_ctrl_lt := sqirCuccaro_controlIdx_lt_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  -- Step 1: convert layout-form projections to their SQIR-form
  -- counterparts (all four are definitional through `sqirCuccaroLayout`
  -- and `sqirCuccaroImpl`).  This exposes the SQIR identifiers that the
  -- R5c aliases are stated in.
  show cuccaro_target_val bits 2
        (Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
            (sqir_mult_control_idx bits j) 1)
          (sqir_mult_input_F bits m acc))
      = if m.testBit j then (acc + (a * 2^j) % N) % N else acc
  -- Step 2: install form for the multiplier input encoder (R5c alias).
  rw [sqirCuccaro_input_eq_install_with_j bits m acc j hj hacc_lt]
  -- Step 3: push targetDecode through install (R5c alias).
  rw [sqirCuccaro_targetDecode_through_install bits m j N ((a * 2^j) % N) bits]
  -- Step 4: apply Level-1 clean-targetDecode projection on the SQIR instance.
  exact ControlledModAdd.clean_targetDecode ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt

/-- Comparison theorem: the interface-form target decode equals the
SQIR-form target decode used by `sqir_modmult_step_target_decode`.
Both terms reduce to the same SQIR-level expression via definitional
unfolding through the layout projections, so this is `rfl`. -/
theorem sqirCuccaro_step_targetDecode_matches_old
    (bits N a j m acc : Nat) :
    ControlledModAdd.sqirCuccaroLayout.targetDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc))
      = cuccaro_target_val bits 2
          (Gate.applyNat (sqir_modmult_step_gate bits N a j)
            (sqir_mult_input_F bits m acc)) := rfl

/-! ### Workspace wrapper theorem via interfaces (Phase R6c)

`sqirCuccaro_step_workspace_via_interface` proves the same 4-conjunct
workspace fact as `sqir_modmult_step_workspace` (`SQIRModMult.lean:631`)
but stated through the new layout stack and proved through the
R5b/R5c aliases.

The proof mirrors the original skeleton:
1. `hacc_lt : acc < 2^bits` (Mathlib `Nat.lt_of_lt_of_le`).
2. `show` converts the layout-form goal to its SQIR-form counterpart
   (same def-equality trick as R6b).
3. Convert `multInputEncode` to install form via
   `sqirCuccaro_input_eq_install_with_j`.
4. For each of the 4 conjuncts, use the corresponding R5b
   `clean_*` projection (`clean_readZero`, `clean_topCarryFalse`,
   `clean_flagFalse`, `clean_controlPreserved`) on
   `ControlledModAdd.sqirCuccaroImpl`, then bridge through the
   corresponding R5c `_through_install_*` alias.

No direct call to `sqir_style_controlledModAddConst_gate_clean`. -/
theorem sqirCuccaro_step_workspace_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    ControlledModAdd.sqirCuccaroLayout.readDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)) = 0
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.topCarryPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.flagPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (sqirCuccaroLayout.multControlIdx bits j) = m.testBit j := by
  have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
  have h_ctrl_allowed := sqirCuccaro_controlIdx_controlAllowed bits j
  have h_ctrl_ne_flag := sqirCuccaro_controlIdx_ne_flag bits j
  have h_ctrl_lt := sqirCuccaro_controlIdx_lt_dim bits j hj
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  -- Step 1: def-unfold layout projections to SQIR-form.
  show cuccaro_read_val bits 2
        (Gate.applyNat
          (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
            (sqir_mult_control_idx bits j) 1)
          (sqir_mult_input_F bits m acc)) = 0
      ∧ Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
              (sqir_mult_control_idx bits j) 1)
            (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
      ∧ Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
              (sqir_mult_control_idx bits j) 1)
            (sqir_mult_input_F bits m acc) 1 = false
      ∧ Gate.applyNat
            (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
              (sqir_mult_control_idx bits j) 1)
            (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits j)
          = m.testBit j
  -- Step 2: install form for the multiplier input encoder.
  rw [sqirCuccaro_input_eq_install_with_j bits m acc j hj hacc_lt]
  -- Step 3: extract the 4 needed clean conjuncts from the R5b
  -- projections applied to `sqirCuccaroImpl`, on the "after F_j update"
  -- starting state.
  have h_rd := ControlledModAdd.clean_readZero ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  have h_tc := ControlledModAdd.clean_topCarryFalse ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  have h_fl := ControlledModAdd.clean_flagFalse ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  have h_ctrl := ControlledModAdd.clean_controlPreserved ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) acc (sqir_mult_control_idx bits j) (m.testBit j)
    hbits hN_pos hN hN2 hc_pos hacc h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sqirCuccaro_readDecode_through_install bits m j N ((a * 2^j) % N) bits]
    exact h_rd
  · rw [sqirCuccaro_applyNat_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          (2 + 2 * bits) _ (by omega)]
    exact h_tc
  · rw [sqirCuccaro_applyNat_through_install_at_workspace bits m j N ((a * 2^j) % N) bits
          1 _ (by omega)]
    exact h_fl
  · rw [sqirCuccaro_applyNat_through_install_at_j bits m j N ((a * 2^j) % N) bits]
    exact h_ctrl

/-- Comparison theorem: the interface-form workspace conjunction equals
the SQIR-form workspace conjunction used by `sqir_modmult_step_workspace`.
Both terms reduce to the same SQIR-level expression via definitional
unfolding through the layout projections, so this is `rfl`. -/
theorem sqirCuccaro_step_workspace_matches_old
    (bits N a j m acc : Nat) :
    (ControlledModAdd.sqirCuccaroLayout.readDecode bits
        (Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)) = 0
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.topCarryPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (ControlledModAdd.sqirCuccaroLayout.flagPos bits) = false
    ∧ Gate.applyNat
          (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
            (sqirCuccaroLayout.multControlIdx bits j))
          (sqirCuccaroLayout.multInputEncode bits m acc)
          (sqirCuccaroLayout.multControlIdx bits j) = m.testBit j)
    =
    (cuccaro_read_val bits 2
        (Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc)) = 0
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) 1 = false
    ∧ Gate.applyNat (sqir_modmult_step_gate bits N a j)
          (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits j) = m.testBit j) := rfl

/-! ### Step gate well-typedness via interfaces (Phase R6d)

`sqirCuccaro_step_gate_wellTyped_via_interface` proves the same
well-typedness fact as `sqir_modmult_step_gate_wellTyped`
(`SQIRModMult.lean:1329`) but stated through the new layout stack
and proved via `ControlledModAdd.clean_wellTyped` on
`ControlledModAdd.sqirCuccaroImpl`.

The original proof uses the same trick: pass `x := 0` (and
`hx := hN_pos`) to the `clean` bundle, since well-typedness does
not depend on the data value `x`.

No direct call to `sqir_style_controlledModAddConst_gate_clean`. -/
theorem sqirCuccaro_step_gate_wellTyped_via_interface
    (bits N a j : Nat) (hbits : 1 ≤ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits) (hj : j < bits) :
    Gate.WellTyped
      (ControlledModAdd.sqirCuccaroLayout.ancillaWidth bits)
      (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
        (sqirCuccaroLayout.multControlIdx bits j)) := by
  have hc_pos : (a * 2 ^ j) % N < N := Nat.mod_lt _ hN_pos
  have h_ctrl_allowed := sqirCuccaro_controlIdx_controlAllowed bits j
  have h_ctrl_ne_flag := sqirCuccaro_controlIdx_ne_flag bits j
  have h_ctrl_lt := sqirCuccaro_controlIdx_lt_dim bits j hj
  -- Apply Level-1 clean-wellTyped projection on the SQIR instance.
  -- (Use x := 0, hx := hN_pos since wellTyped doesn't depend on x.)
  exact ControlledModAdd.clean_wellTyped ControlledModAdd.sqirCuccaroImpl
    bits N ((a * 2^j) % N) 0 (sqir_mult_control_idx bits j) false
    hbits hN_pos hN hN2 hc_pos hN_pos h_ctrl_allowed h_ctrl_ne_flag h_ctrl_lt

/-- Comparison theorem: the interface-form well-typedness equals the
SQIR-form well-typedness used by `sqir_modmult_step_gate_wellTyped`.
Both terms reduce to the same SQIR-level expression via definitional
unfolding through the layout projections, so this is `rfl`. -/
theorem sqirCuccaro_step_gate_wellTyped_matches_old
    (bits N a j : Nat) :
    Gate.WellTyped
        (ControlledModAdd.sqirCuccaroLayout.ancillaWidth bits)
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
      = Gate.WellTyped (sqir_modmult_rev_anc bits)
          (sqir_modmult_step_gate bits N a j) := rfl

/-! ### Preserves-all-control-bits via interfaces (Phase R6e)

`sqirCuccaro_step_preserves_all_control_bits_via_interface` proves the
across-bit preservation fact: after the step gate runs, EVERY
multiplier control bit `k < bits` is preserved as `m.testBit k`
(not just the `k = j` one).

The original `sqir_modmult_step_preserves_all_control_bits`
(`SQIRModMult.lean:774`) splits on `k = j` vs `k ≠ j`:
- `k = j`: the j-th conjunct of `sqir_modmult_step_workspace` —
  reusable via R6c `sqirCuccaro_step_workspace_via_interface`.
- `k ≠ j`: gate commutes through the install, then the install at
  position `controlIdx_k` is `m.testBit k` — needs R5c
  `sqirCuccaro_controlledModAdd_commute_install` and the new
  `sqirCuccaro_install_at_mult_k_eq` alias.

No direct call to `sqir_style_controlledModAddConst_gate_clean`. -/
theorem sqirCuccaro_step_preserves_all_control_bits_via_interface
    (bits N a m acc j k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hj : j < bits) (hk : k < bits) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
        (sqirCuccaroLayout.multControlIdx bits k) = m.testBit k := by
  by_cases h_kj : k = j
  · -- k = j case: use the workspace bundle's control-preservation conjunct
    -- (= conjunct #4 of R6c sqirCuccaro_step_workspace_via_interface).
    subst h_kj
    have ⟨_, _, _, h_ctrl⟩ :=
      sqirCuccaro_step_workspace_via_interface bits N a k m acc
        hbits hN_pos hN hN2 hk hacc
    exact h_ctrl
  · -- k ≠ j case: gate commutes through install; install at controlIdx_k
    -- delivers m.testBit k.
    have hacc_lt : acc < 2 ^ bits := Nat.lt_of_lt_of_le hacc hN
    show Gate.applyNat
        (sqir_style_controlledModAddConst_gate bits 2 N ((a * 2^j) % N)
          (sqir_mult_control_idx bits j) 1)
        (sqir_mult_input_F bits m acc)
        (sqir_mult_control_idx bits k) = m.testBit k
    rw [sqirCuccaro_input_eq_install_with_j bits m acc j hj hacc_lt]
    rw [sqirCuccaro_controlledModAdd_commute_install bits m j N ((a * 2^j) % N) bits _]
    exact sqirCuccaro_install_at_mult_k_eq bits m j bits k _ hk h_kj

/-- Comparison theorem: rfl-equivalence of the interface-form and
SQIR-form preserves-all-control-bits conclusion. -/
theorem sqirCuccaro_step_preserves_all_control_bits_matches_old
    (bits N a m acc j k : Nat) :
    (Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
        (sqirCuccaroLayout.multControlIdx bits k) = m.testBit k)
    = (Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc) (sqir_mult_control_idx bits k)
        = m.testBit k) := rfl

/-! ### Full one-step state equality (Phase R6f — fallback wrapper)

`sqirCuccaro_step_state_eq_via_interface` states the full one-step
state equality through the layout stack.

**Honesty note**: the proof here is a **fallback wrapper** (option 3
in the loop instructions).  It calls the original
`sqir_modmult_step_state_eq` (`SQIRModMult.lean:1156`) directly,
because the original `funext q` proof depends on per-position lemmas
(`sqir_modmult_step_above_layout_false`, `_flag0_false`,
`_carry_in_restored`, `_target_bit`, `_read_bit`) that are NOT
exposed by the 6-conjunct `ControlledModAddImpl.clean` bundle.

Routing through interface requires either:
1. enriching the clean bundle with per-position conjuncts (a deeper
   refactor reserved as R5b'), OR
2. adding 3 supplementary per-position aliases
   (`sqirCuccaro_flag0_false`, `_carry_in_restored`, `_above_layout_false`)
   and replaying the case-split funext proof.

For R6f we land a fallback wrapper so the **statement** uses
interface fields; later phases (R5b' or a dedicated R6f') may close
the proof via interface.  The original theorem is not changed and
is not weakened. -/
theorem sqirCuccaro_step_state_eq_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) :=
  sqir_modmult_step_state_eq bits N a j m acc hbits hN_pos hN hN2 hj hacc

/-- Comparison theorem: the interface-form state equality equals the
SQIR-form state equality by `rfl`. -/
theorem sqirCuccaro_step_state_eq_matches_old
    (bits N a j m acc : Nat) :
    (Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc))
    = (Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc)) := rfl

/-! ### Real-via-interface state equality (R6f-real)

The R5b' aliases + R6c workspace + R6e preserves-all-control-bits +
the per-position decoder facts on `sqir_mult_input_F` give all the
ingredients needed to prove `sqir_modmult_step_state_eq` through
interface aliases, NOT through `sqir_modmult_step_state_eq` or
`sqir_style_controlledModAddConst_gate_clean` directly.

Proof engineering: the aliases are stated in layout-form
(`sqirCuccaroLayout.multInputEncode`, etc.), but the funext-style
state-equality proof needs SQIR-form sub-goals.  We bridge with
**type-ascribed `have`**: `have h_sqir : <SQIR-form> := <alias-call>`
elaborates by def-eq (layout-form = SQIR-form), and then `rw [h_sqir]`
matches the SQIR-form pattern in the goal.

Strategy (per loop instructions):
* Stage 1: prove a SQIR-form helper using type-ascribed aliases.
* Stage 2: derive the layout-form theorem by `exact` (def-eq). -/

theorem sqirCuccaro_step_state_eq_real_sqir_form
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) := by
  funext q
  set acc' := if m.testBit j then (acc + (a * 2^j) % N) % N else acc with hacc'_def
  have hacc'_lt_N : acc' < N := by
    rw [hacc'_def]
    by_cases h : m.testBit j
    · rw [if_pos h]; exact Nat.mod_lt _ hN_pos
    · rw [if_neg h]; exact hacc
  have hacc'_lt : acc' < 2^bits := Nat.lt_of_lt_of_le hacc'_lt_N hN
  -- Case split on q.
  by_cases hq_above : q ≥ 2 + 2 * bits + 1 + bits
  · -- Above layout.
    have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                  (sqir_mult_input_F bits m acc) q = false :=
      sqirCuccaro_step_above_layout_false bits N a j m acc q hbits hj hq_above
    rw [h_lhs]
    -- RHS = false (above layout).
    unfold sqir_mult_input_F
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1)]
    rw [if_neg (by omega : ¬ q < 2 + 2 * bits + 1 + bits)]
  · push_neg at hq_above
    by_cases hq_in_mult : q ≥ 2 + 2 * bits + 1
    · -- Multiplier register.
      set k := q - (2 + 2 * bits + 1) with hk_def
      have hk_lt : k < bits := by omega
      have hq_eq : q = sqir_mult_control_idx bits k := by
        unfold sqir_mult_control_idx; omega
      rw [hq_eq]
      have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                    (sqir_mult_input_F bits m acc)
                    (sqir_mult_control_idx bits k) = m.testBit k :=
        sqirCuccaro_step_preserves_all_control_bits_via_interface
          bits N a m acc j k hbits hN_pos hN hN2 hacc hj hk_lt
      rw [h_lhs]
      exact (sqir_mult_input_control_bit bits m acc' k hk_lt).symm
    · push_neg at hq_in_mult
      -- Workspace q < 2 + 2*bits + 1.
      by_cases hq_0 : q = 0
      · subst hq_0
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) 0 = false :=
          sqirCuccaro_step_flag0_false bits N a j m acc hbits hj
        rw [h_lhs]
        exact (sqir_mult_input_flag_0_false bits m acc').symm
      by_cases hq_1 : q = 1
      · subst hq_1
        have h_workspace := sqirCuccaro_step_workspace_via_interface
          bits N a j m acc hbits hN_pos hN hN2 hj hacc
        -- workspace.2.2.1 is conj #3 = flag at position 1 = false.
        have h_fl : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) 1 = false :=
          h_workspace.2.2.1
        rw [h_fl]
        exact (sqir_mult_input_flag_1_false bits m acc').symm
      by_cases hq_2 : q = 2
      · subst hq_2
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) 2 = false :=
          sqirCuccaro_step_carryIn_restored bits N a j m acc
            hbits hN_pos hN hN2 hj hacc
        rw [h_lhs]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 : Nat) < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_c_in 2 false 0 acc').symm
      by_cases hq_top : q = 2 + 2 * bits
      · subst hq_top
        have h_workspace := sqirCuccaro_step_workspace_via_interface
          bits N a j m acc hbits hN_pos hN hN2 hj hacc
        -- workspace.2.1 is conj #2 = top carry = false.
        have h_tc : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) (2 + 2 * bits) = false :=
          h_workspace.2.1
        rw [h_tc]
        have h_eq : (2 + 2 * bits : Nat) = 2 + 2 * (bits - 1) + 2 := by omega
        unfold sqir_mult_input_F
        rw [if_pos (by omega : (2 + 2 * bits : Nat) < 2 + 2 * bits + 1)]
        rw [h_eq, cuccaro_input_F_at_a 2 (bits - 1) false 0 acc']
        exact (Nat.zero_testBit _).symm
      -- q ∈ [3, 2*bits + 1].  Parity dispatch.
      by_cases h_q_odd : q % 2 = 1
      · -- Target bit: q = 2 + 2*i + 1.
        have hi_lt : (q - 3) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 3) / 2) + 1 := by omega
        rw [hq_eq]
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) (2 + 2 * ((q - 3) / 2) + 1)
                    = acc'.testBit ((q - 3) / 2) := by
          have := sqirCuccaro_step_targetBit_extracted bits N a j m acc
            ((q - 3) / 2) hbits hN_pos hN hN2 hj hacc hi_lt
          -- The alias is layout-form; type-ascribe to SQIR-form via def-eq.
          exact this
        rw [h_lhs]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 3) / 2) + 1 < 2 + 2 * bits + 1)]
        exact (cuccaro_input_F_at_b 2 ((q - 3) / 2) false 0 acc').symm
      · -- Read bit: q = 2 + 2*i + 2.
        have hi_lt : (q - 4) / 2 < bits := by omega
        have hq_eq : q = 2 + 2 * ((q - 4) / 2) + 2 := by omega
        rw [hq_eq]
        have h_lhs : Gate.applyNat (sqir_modmult_step_gate bits N a j)
                      (sqir_mult_input_F bits m acc) (2 + 2 * ((q - 4) / 2) + 2)
                    = false :=
          sqirCuccaro_step_readBit_zero bits N a j m acc ((q - 4) / 2)
            hbits hN_pos hN hN2 hj hacc hi_lt
        rw [h_lhs]
        unfold sqir_mult_input_F
        rw [if_pos (by omega : 2 + 2 * ((q - 4) / 2) + 2 < 2 + 2 * bits + 1)]
        rw [cuccaro_input_F_at_a 2 ((q - 4) / 2) false 0 acc']
        exact (Nat.zero_testBit _).symm

/-- **R6f-real**: the layout-form state-equality theorem.  Derived from
`sqirCuccaro_step_state_eq_real_sqir_form` by `exact` (def-eq through
layout-projection unfolding). -/
theorem sqirCuccaro_step_state_eq_real_via_interface
    (bits N a j m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hj : j < bits) (hacc : acc < N) :
    Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc) :=
  sqirCuccaro_step_state_eq_real_sqir_form bits N a j m acc
    hbits hN_pos hN hN2 hj hacc

/-- Comparison theorem: the real-via-interface and the R6f fallback
theorem have the same conclusion (rfl). -/
theorem sqirCuccaro_step_state_eq_real_matches_fallback
    (bits N a j m acc : Nat) :
    (Gate.applyNat
        (ControlledModAdd.sqirCuccaroImpl.gate bits N ((a * 2^j) % N)
          (sqirCuccaroLayout.multControlIdx bits j))
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc))
    = (Gate.applyNat (sqir_modmult_step_gate bits N a j)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m
          (if m.testBit j then (acc + (a * 2^j) % N) % N else acc)) := rfl

/-! ### Prefix/const-gate chain via interface (Phase R6g — fallback)

These theorems lift the one-step state equality (R6f) to the full
constant-multiplier prefix.  Like R6f, these are **fallback wrappers**:
statement uses interface fields, proof calls the existing SQIR
theorems.  Future R6g' can replay the induction once R5b' enriches
the clean bundle to support a real R6f proof. -/

theorem sqirCuccaro_prefix_state_eq_from_via_interface
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (sqir_modmult_acc_spec_from N a m acc k) :=
  sqir_modmult_prefix_state_eq_from bits N a m acc k hbits hN_pos hN hN2 hacc hk

theorem sqirCuccaro_const_gate_state_eq_from_via_interface
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m ((acc + a * m) % N) :=
  sqir_modmult_const_gate_state_eq_from bits N a m acc hbits hN_pos hN hN2 hacc hm

/-! ### Prefix/const-gate chain — real interface routing (Phase R6g-real)

These theorems promote the R6g fallback wrappers to genuine interface
proofs by replaying the original prefix induction (and the trivial
const-gate composition) with `sqirCuccaro_step_state_eq_real_sqir_form`
(R6f-real) replacing `sqir_modmult_step_state_eq`.

* `_real_sqir_form` variants: SQIR-form helpers whose proof bodies
  replay the original inductions.
* `_real_via_interface` variants: layout-form wrappers, one-line
  `exact` from the SQIR-form helpers (def-eq).

Neither calls `sqir_modmult_step_state_eq`,
`sqir_modmult_prefix_state_eq_from`,
`sqir_modmult_const_gate_state_eq_from`, or
`sqir_style_controlledModAddConst_gate_clean`. -/

theorem sqirCuccaro_prefix_state_eq_from_real_sqir_form
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k)
        (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m (sqir_modmult_acc_spec_from N a m acc k) := by
  induction k with
  | zero =>
    rw [sqir_modmult_prefix_gate, Gate.applyNat_I, sqir_modmult_acc_spec_from_zero]
  | succ n ih =>
    have hn_le : n ≤ bits := by omega
    have hn_lt : n < bits := by omega
    rw [sqir_modmult_prefix_gate_succ_eq, Gate.applyNat_seq]
    rw [ih hn_le]
    have hacc_lt_N : sqir_modmult_acc_spec_from N a m acc n < N :=
      sqir_modmult_acc_spec_from_lt N a m acc n hN_pos hacc
    rw [sqirCuccaro_step_state_eq_real_sqir_form bits N a n m
          (sqir_modmult_acc_spec_from N a m acc n)
          hbits hN_pos hN hN2 hn_lt hacc_lt_N]
    rfl

theorem sqirCuccaro_prefix_state_eq_from_real_via_interface
    (bits N a m acc k : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hk : k ≤ bits) :
    Gate.applyNat (sqir_modmult_prefix_gate bits N a k)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m
          (sqir_modmult_acc_spec_from N a m acc k) :=
  sqirCuccaro_prefix_state_eq_from_real_sqir_form bits N a m acc k
    hbits hN_pos hN hN2 hacc hk

theorem sqirCuccaro_const_gate_state_eq_from_real_sqir_form
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a) (sqir_mult_input_F bits m acc)
      = sqir_mult_input_F bits m ((acc + a * m) % N) := by
  unfold sqir_modmult_const_gate
  rw [sqirCuccaro_prefix_state_eq_from_real_sqir_form bits N a m acc bits
        hbits hN_pos hN hN2 hacc (le_refl _)]
  rw [sqir_modmult_acc_spec_from_eq_add_mul_mod bits N a m acc hN_pos hacc hm]

theorem sqirCuccaro_const_gate_state_eq_from_real_via_interface
    (bits N a m acc : Nat) (hbits : 1 ≤ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2^bits) (hN2 : 2 * N ≤ 2^bits)
    (hacc : acc < N) (hm : m < 2^bits) :
    Gate.applyNat (sqir_modmult_const_gate bits N a)
        (sqirCuccaroLayout.multInputEncode bits m acc)
      = sqirCuccaroLayout.multInputEncode bits m ((acc + a * m) % N) :=
  sqirCuccaro_const_gate_state_eq_from_real_sqir_form bits N a m acc
    hbits hN_pos hN hN2 hacc hm

end MultiplierStep
end VerifiedShor
