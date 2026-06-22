/-
  FormalRV.Shor.GidneyInPlace.ReducedLookupEgate — e_gate (reusable named product equiv) + one-pass branchOfE coset action.
-/
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Proof.ReducedLookupStepAction
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Proof.CosetDeviationE
import FormalRV.Arithmetic.Windowed.WindowedInPlace

namespace FormalRV.Shor.GidneyInPlace.ReducedLookupEgate

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (tableValue window)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.ReducedLookupStepAction
open FormalRV.Shor.GidneyInPlace.GatePerm
open FormalRV.Shor.GidneyInPlace.CuccaroGatePerm (gateToPerm_funboolNat)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState permState shiftState shiftState_cosetState)
open FormalRV.Shor.GidneyInPlace.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE)

/-! ## PART A — the reusable named product equiv `e_gate`.

The DATA factor is the accumulator value `z` (little-endian: `z.val.testBit i` at
augend position `augendIdx (1+2w) i = 2+2w+2i`).  The CONTROL factor enumerates the
COMPLEMENT positions (carry/address/ancilla, addends, y-register) via `compIdx`. -/

/-- The complement-position enumerator: a bijection `[0, cosetDim-bits) → (non-augend
    positions of [0, cosetDim))`.  Three regions: the low carry/address/ancilla zone,
    the (odd) addend positions, and the y-register zone. -/
def compIdx (w bits : Nat) (j : Nat) : Nat :=
  if j < 2 + 2 * w then j
  else if j < 2 + 2 * w + bits then 3 + 2 * w + 2 * (j - (2 + 2 * w))
  else 2 + 2 * w + 2 * bits + (j - (2 + 2 * w + bits))

/-- `compIdx` is bounded by `cosetDim` on `[0, cosetDim-bits)`. -/
theorem compIdx_lt (w bits j : Nat) (hj : j < cosetDim w bits - bits) :
    compIdx w bits j < cosetDim w bits := by
  unfold compIdx cosetDim at *
  split <;> [skip; split] <;> omega

/-- `compIdx` is injective (its piecewise branch conditions are on the input). -/
theorem compIdx_inj (w bits i j : Nat) (_hi : i < cosetDim w bits - bits)
    (_hj : j < cosetDim w bits - bits) (h : compIdx w bits i = compIdx w bits j) : i = j := by
  unfold compIdx cosetDim at *
  split_ifs at h <;> omega

/-- `compIdx` images avoid the augend positions. -/
theorem compIdx_ne_augend (w bits j i : Nat) (_hj : j < cosetDim w bits - bits) (hi : i < bits) :
    compIdx w bits j ≠ cuccaroAdder.augendIdx (1 + 2 * w) i := by
  have haug : cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := rfl
  rw [haug]
  unfold compIdx cosetDim at *
  split_ifs <;> omega

/-- **Coverage.**  Every position `< cosetDim` is EITHER an augend position (for a
    unique `i < bits`) OR a complement position (for a unique `j < cosetDim-bits`). -/
theorem cover (w bits p : Nat) (hp : p < cosetDim w bits) :
    (∃ i, i < bits ∧ p = cuccaroAdder.augendIdx (1 + 2 * w) i)
      ∨ (∃ j, j < cosetDim w bits - bits ∧ p = compIdx w bits j) := by
  have haug : ∀ i, cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := fun _ => rfl
  unfold cosetDim at *
  unfold compIdx
  -- carry/address/ancilla zone
  by_cases h0 : p < 2 + 2 * w
  · right; exact ⟨p, by omega, by rw [if_pos h0]⟩
  -- adder block [2+2w, 2+2w+2bits): augend (even) vs addend (odd)
  by_cases hblk : p < 2 + 2 * w + 2 * bits
  · by_cases hpar : (p - (2 + 2 * w)) % 2 = 0
    · -- augend: p = 1+2w+2i+1 with i = (p-(2+2w))/2
      left
      refine ⟨(p - (2 + 2 * w)) / 2, by omega, ?_⟩
      rw [haug]; omega
    · -- addend: complement, region 1
      right
      refine ⟨2 + 2 * w + (p - (2 + 2 * w)) / 2, by omega, ?_⟩
      rw [if_neg (by omega), if_pos (by omega)]
      omega
  -- y-register zone [2+2w+2bits, cosetDim): complement, region 2
  · right
    refine ⟨2 + 2 * w + bits + (p - (2 + 2 * w + 2 * bits)), by omega, ?_⟩
    rw [if_neg (by omega), if_neg (by omega)]
    omega

/-! ### The assembled bit-function and the named equiv. -/

/-- Assemble a `cosetDim`-bit function from a control value `x` (written at the
    complement positions) and a data value `z` (written at the augend positions,
    little-endian: bit `i` at `augendIdx (1+2w) i`). -/
def assembleE (w bits : Nat) (x z : Nat) : Nat → Bool :=
  writeReg (cuccaroAdder.augendIdx (1 + 2 * w)) bits z
    (writeReg (compIdx w bits) (cosetDim w bits - bits) x (fun _ => false))

/-- At an augend position, `assembleE` reads bit `i` of the data value `z`. -/
theorem assembleE_augend (w bits x z i : Nat) (hi : i < bits) :
    assembleE w bits x z (cuccaroAdder.augendIdx (1 + 2 * w) i) = z.testBit i := by
  unfold assembleE
  exact writeReg_at _ bits z _
    (fun a b ha hb h => cuccaroAdder_augendIdx_inj (1 + 2 * w) a b h) i hi

/-- At a complement position, `assembleE` reads bit `j` of the control value `x`. -/
theorem assembleE_comp (w bits x z j : Nat) (hj : j < cosetDim w bits - bits) :
    assembleE w bits x z (compIdx w bits j) = x.testBit j := by
  unfold assembleE
  rw [writeReg_frame _ bits z _ _
        (fun i hi => compIdx_ne_augend w bits j i hj hi)]
  exact writeReg_at _ (cosetDim w bits - bits) x _
    (fun a b ha hb h => compIdx_inj w bits a b ha hb h) j hj

/-- `bits ≤ cosetDim w bits`, so the data factor exponent splits off. -/
theorem bits_le_cosetDim (w bits : Nat) : bits ≤ cosetDim w bits := by
  unfold cosetDim; omega

/-- `(cosetDim - bits) + bits = cosetDim`. -/
theorem comp_add_bits (w bits : Nat) : (cosetDim w bits - bits) + bits = cosetDim w bits := by
  unfold cosetDim; omega

/-- **`assembleE` is injective in the value pair** (over the relevant value ranges),
    on `[0, cosetDim)`: recover `z` at augend positions, `x` at complement positions. -/
theorem assembleE_inj (w bits x z x' z' : Nat)
    (hx : x < 2 ^ (cosetDim w bits - bits)) (hx' : x' < 2 ^ (cosetDim w bits - bits))
    (hz : z < 2 ^ bits) (hz' : z' < 2 ^ bits)
    (h : (fun p : Fin (cosetDim w bits) => assembleE w bits x z p.val)
       = (fun p : Fin (cosetDim w bits) => assembleE w bits x' z' p.val)) :
    x = x' ∧ z = z' := by
  have key : ∀ p, p < cosetDim w bits → assembleE w bits x z p = assembleE w bits x' z' p :=
    fun p hp => congrFun h ⟨p, hp⟩
  refine ⟨Nat.eq_of_testBit_eq (fun j => ?_), Nat.eq_of_testBit_eq (fun i => ?_)⟩
  · -- compare bit j of x vs x'
    by_cases hj : j < cosetDim w bits - bits
    · have := key (compIdx w bits j) (compIdx_lt w bits j hj)
      rw [assembleE_comp w bits x z j hj, assembleE_comp w bits x' z' j hj] at this
      exact this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by omega) (by omega)))]
  · -- compare bit i of z vs z'
    by_cases hi : i < bits
    · have := key (cuccaroAdder.augendIdx (1 + 2 * w) i)
        (by have : cuccaroAdder.augendIdx (1 + 2 * w) i = 1 + 2 * w + 2 * i + 1 := rfl
            unfold cosetDim; omega)
      rw [assembleE_augend w bits x z i hi, assembleE_augend w bits x' z' i hi] at this
      exact this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hz' (Nat.pow_le_pow_right (by omega) (by omega)))]

/-- The forward map of `e_gate`: `(x, z) ↦ funboolNat (assembleE x.val z.val)`. -/
noncomputable def eFun (w bits : Nat) :
    Fin (2 ^ (cosetDim w bits - bits)) × Fin (2 ^ bits) → Fin (2 ^ cosetDim w bits) :=
  fun p => funboolNat (cosetDim w bits) (fun i => assembleE w bits p.1.val p.2.val i.val)

theorem eFun_injective (w bits : Nat) : Function.Injective (eFun w bits) := by
  rintro ⟨x, z⟩ ⟨x', z'⟩ h
  unfold eFun at h
  have hassemble := funboolNat_injective (cosetDim w bits) h
  obtain ⟨hxx, hzz⟩ := assembleE_inj w bits x.val z.val x'.val z'.val
    x.isLt x'.isLt z.isLt z'.isLt hassemble
  exact Prod.ext (Fin.ext hxx) (Fin.ext hzz)

theorem eFun_bijective (w bits : Nat) : Function.Bijective (eFun w bits) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨eFun_injective w bits, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      ← pow_add, comp_add_bits]

/-- **PART A — the reusable named product equiv `e_gate`.**  Factors the cuccaro
    coset-multiplier register `Fin (2^cosetDim)` into control `Fin (2^(cosetDim-bits))`
    × data `Fin (2^bits)`, with the data slice carrying the accumulator VALUE. -/
noncomputable def e_gate (w bits _numWin : Nat) :
    Fin (2 ^ (cosetDim w bits - bits)) × Fin (2 ^ bits) ≃ Fin (2 ^ cosetDim w bits) :=
  Equiv.ofBijective (eFun w bits) (eFun_bijective w bits)

/-! ### The control value `xCtrl` and the defining property `e_gate_apply`. -/

/-- The control value encoding "multiplier register = `y`, ctrl bit = 1, clean
    ancilla": the complement-register decode of the clean multiplier input. -/
noncomputable def xCtrl (w bits numWin y : Nat) : Fin (2 ^ (cosetDim w bits - bits)) :=
  ⟨decodeReg (compIdx w bits) (cosetDim w bits - bits)
      (mulInputOf cuccaroAdder w bits numWin y),
   decodeReg_lt_two_pow _ _ _⟩

/-- `xCtrl`'s bits ARE the multiplier input at the complement positions. -/
theorem xCtrl_testBit (w bits numWin y j : Nat) (hj : j < cosetDim w bits - bits) :
    (xCtrl w bits numWin y).val.testBit j
      = mulInputOf cuccaroAdder w bits numWin y (compIdx w bits j) :=
  decodeReg_testBit (compIdx w bits) (cosetDim w bits - bits) _ j hj

/-- `assembleE` of the clean control value at data `z` IS the accumulator input
    `mulInputAccOf` on `[0, cosetDim)`. -/
theorem assembleE_xCtrl (w bits numWin z y p : Nat) (hp : p < cosetDim w bits) :
    assembleE w bits (xCtrl w bits numWin y).val z p
      = mulInputAccOf cuccaroAdder w bits numWin z y p := by
  unfold mulInputAccOf
  rcases cover w bits p hp with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · -- augend position: both write bit i of z
    rw [assembleE_augend w bits _ z i hi,
        writeReg_at _ bits z _
          (fun a b ha hb h => cuccaroAdder_augendIdx_inj (1 + 2 * w) a b h) i hi]
  · -- complement position: both read mulInputOf y
    rw [assembleE_comp w bits _ z j hj, xCtrl_testBit w bits numWin y j hj,
        writeReg_frame _ bits z _ _ (fun i hi => compIdx_ne_augend w bits j i hj hi)]

/-- **PART A DEFINING PROPERTY.**  `e_gate` sends the clean control value `xCtrl y`
    paired with accumulator value `z` to the funbool index of `mulInputAccOf z y` —
    exactly the basis index the per-step action `reducedWindowStep_uc_eval` produces. -/
theorem e_gate_apply (w bits numWin z y : Nat) (hz : z < 2 ^ bits) :
    e_gate w bits numWin (xCtrl w bits numWin y, ⟨z, hz⟩)
      = funboolNat (cosetDim w bits)
          (fun p => mulInputAccOf cuccaroAdder w bits numWin z y p.val) := by
  unfold e_gate
  rw [Equiv.ofBijective_apply]
  unfold eFun
  congr 1
  funext p
  exact assembleE_xCtrl w bits numWin z y p.val p.isLt

/-! ## PART B — `cosetInput` and the `branchOfE` projection facts. -/

/-- The whole-register coset input: the coset state `cosetState (2^bits) N cm k`
    placed in the control branch `xCtrl y` (and zero in every other control branch),
    laid out through `e_gate`. -/
noncomputable def cosetInput (w bits numWin N cm k y : Nat) :
    QState (2 ^ cosetDim w bits) :=
  fun idx _ =>
    if ((e_gate w bits numWin).symm idx).1 = xCtrl w bits numWin y
    then cosetState (2 ^ bits) N cm k ((e_gate w bits numWin).symm idx).2 0
    else 0

/-- **PART B (active branch).**  In the active control branch `xCtrl y`, the
    `branchOfE` data substate of `cosetInput` is exactly the coset state. -/
theorem branchOfE_cosetInput_active (w bits numWin N cm k y : Nat) :
    branchOfE (e_gate w bits numWin) (cosetInput w bits numWin N cm k y)
        (xCtrl w bits numWin y)
      = cosetState (2 ^ bits) N cm k := by
  funext z hz
  have h0 : hz = 0 := Subsingleton.elim hz 0
  subst h0
  show cosetInput w bits numWin N cm k y (e_gate w bits numWin (xCtrl w bits numWin y, z)) 0
    = cosetState (2 ^ bits) N cm k z 0
  unfold cosetInput
  rw [Equiv.symm_apply_apply]
  rw [if_pos rfl]

/-- **PART B (inactive branch).**  Off the active control branch, the `branchOfE`
    data substate of `cosetInput` is identically zero. -/
theorem branchOfE_cosetInput_zero (w bits numWin N cm k y : Nat)
    (x : Fin (2 ^ (cosetDim w bits - bits))) (hx : x ≠ xCtrl w bits numWin y) :
    branchOfE (e_gate w bits numWin) (cosetInput w bits numWin N cm k y) x
      = fun _ _ => 0 := by
  funext z hz
  show cosetInput w bits numWin N cm k y (e_gate w bits numWin (x, z)) 0 = 0
  unfold cosetInput
  rw [Equiv.symm_apply_apply]
  rw [if_neg hx]

/-! ## PART C — the one-pass `branchOfE` coset action. -/

/-- The reduced window step's well-typedness at its own coset dimension. -/
theorem stepWellTyped (w bits N a numWin j : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin) :
    Gate.WellTyped (cosetDim w bits)
      (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j) :=
  reducedWindowStepOf_cuccaro_wellTyped w bits N a numWin j (cosetDim w bits)
    hw hbits hj (by unfold cosetDim; omega)

/-- **The per-step basis permutation through `e_gate`.**  In the active control branch
    `xCtrl y`, the gate's basis permutation `gateToPerm step` advances the data value
    by `c = tableValue a N w j (window w y j)` mod `2^bits`. -/
theorem step_perm_through_e_gate (w bits N a numWin z y j : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin)
    (hz : z < 2 ^ bits) (hz2 : (z + tableValue a N w j (window w y j)) % 2 ^ bits < 2 ^ bits) :
    gateToPerm (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j) (cosetDim w bits)
        (stepWellTyped w bits N a numWin j hw hbits hj)
        (e_gate w bits numWin (xCtrl w bits numWin y, ⟨z, hz⟩))
      = e_gate w bits numWin (xCtrl w bits numWin y,
          ⟨(z + tableValue a N w j (window w y j)) % 2 ^ bits, hz2⟩) := by
  rw [e_gate_apply w bits numWin z y hz,
      e_gate_apply w bits numWin ((z + tableValue a N w j (window w y j)) % 2 ^ bits) y hz2,
      gateToPerm_funboolNat]
  congr 1
  funext i
  show Gate.applyNat (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
        (1 + 2 * w + cuccaroAdder.span bits) j)
        (extendBool (cosetDim w bits)
          (fun i => mulInputAccOf cuccaroAdder w bits numWin z y i.val)) i.val
    = mulInputAccOf cuccaroAdder w bits numWin
        ((z + tableValue a N w j (window w y j)) % 2 ^ bits) y i.val
  rw [extendBool_mulInputAccOf w bits N a numWin z y hbits,
      reducedWindowStep_applyNat w bits N a numWin z y j hw hbits hj]

open FormalRV.Shor.GidneyInPlace.ApproxOp (wrapShiftState wrapShiftState_cosetState)

/-- **PART C — THE ONE-PASS COSET ACTION.**  In the active control branch `xCtrl y`,
    one literal `uc_eval` reduced window step `j`, applied to the coset input
    `cosetInput k`, advances the coset data state by the canonical window addend
    `c = tableValue a N w j (window w y j)` — i.e. it realizes `cosetState k → cosetState (k+c)`,
    EXACTLY (under the no-wrap window fit).  This is one `actualAcc`/`wrapActualAcc` step
    in the `branchOfE` language, ready to feed the fold + `cosetOutOfPlace_hfwd_E`. -/
theorem reducedWindowStep_branchOfE (w bits N a numWin k y j cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin) (hN : 0 < N)
    (hc : tableValue a N w j (window w y j) < 2 ^ bits)
    (hfit : k + tableValue a N w j (window w y j) + (2 ^ cm - 1) * N < 2 ^ bits) :
    branchOfE (e_gate w bits numWin)
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
              (1 + 2 * w + cuccaroAdder.span bits) j))
          * (id (cosetInput w bits numWin N cm k y) :
              Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
        (xCtrl w bits numWin y)
      = cosetState (2 ^ bits) N cm (k + tableValue a N w j (window w y j)) := by
  set c := tableValue a N w j (window w y j) with hcdef
  -- Reduce the gate to the basis permutation σ.symm.
  rw [uc_eval_eq_permState _ (cosetDim w bits)
        (stepWellTyped w bits N a numWin j hw hbits hj)]
  set σ := gateToPerm (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
      (1 + 2 * w + cuccaroAdder.span bits) j) (cosetDim w bits)
      (stepWellTyped w bits N a numWin j hw hbits hj) with hσ
  -- It suffices to identify the branch data state with the wrapping shift of cosetState k.
  rw [← wrapShiftState_cosetState (2 ^ bits) N cm k c hN hfit]
  funext z' hz'
  have h0 : hz' = 0 := Subsingleton.elim hz' 0
  subst h0
  -- LHS = cosetInput (σ.symm (e (xCtrl y, z'))) 0.
  show cosetInput w bits numWin N cm k y
      (σ.symm (e_gate w bits numWin (xCtrl w bits numWin y, z'))) 0
    = wrapShiftState (2 ^ bits) c (cosetState (2 ^ bits) N cm k) z' 0
  -- The data preimage value `z = (z' + (2^bits − c)) mod 2^bits`.
  set z : Nat := (z'.val + (2 ^ bits - c)) % 2 ^ bits with hzdef
  have hzlt : z < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
  have hzc : (z + c) % 2 ^ bits = z'.val := by
    rw [hzdef, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        show z'.val + (2 ^ bits - c) + c = z'.val + 2 ^ bits by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt z'.isLt]
  -- The key permutation fact: σ (e (xCtrl y, ⟨z⟩)) = e (xCtrl y, z').
  have hperm : σ (e_gate w bits numWin (xCtrl w bits numWin y, ⟨z, hzlt⟩))
      = e_gate w bits numWin (xCtrl w bits numWin y, z') := by
    rw [hσ, step_perm_through_e_gate w bits N a numWin z y j hw hbits hj hzlt
          (hzc ▸ z'.isLt)]
    exact congrArg _ (Prod.ext rfl (Fin.ext hzc))
  -- Hence σ.symm (e (xCtrl y, z')) = e (xCtrl y, ⟨z⟩).
  have hsymm : σ.symm (e_gate w bits numWin (xCtrl w bits numWin y, z'))
      = e_gate w bits numWin (xCtrl w bits numWin y, ⟨z, hzlt⟩) := by
    rw [← hperm, Equiv.symm_apply_apply]
  rw [hsymm]
  -- Evaluate cosetInput at e (xCtrl y, ⟨z⟩): control matches, data = ⟨z⟩.
  unfold cosetInput
  rw [Equiv.symm_apply_apply, if_pos rfl]
  -- RHS: wrapShiftState picks index ⟨(z' + (2^bits−c))%2^bits⟩ = ⟨z⟩.
  show cosetState (2 ^ bits) N cm k ⟨z, hzlt⟩ 0
    = cosetState (2 ^ bits) N cm k _ 0
  congr 1

end FormalRV.Shor.GidneyInPlace.ReducedLookupEgate