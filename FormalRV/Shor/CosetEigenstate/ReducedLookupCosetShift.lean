/-
  FormalRV.Shor.CosetEigenstate.ReducedLookupCosetShift — FOLD the one-pass coset action
  across all window passes, discharge `cosetOutOfPlace_hfwd_E.hfac_act` for the concrete
  reduced-lookup gate, and state the multiplier-local cosetState-shift deliverable.
-/
import FormalRV.Shor.CosetEigenstate.ReducedLookupEgate
import FormalRV.Shor.CosetEigenstate.CosetDeviationE
import FormalRV.Shor.CosetEigenstate.CosetFoldWindowed

namespace FormalRV.Shor.CosetEigenstate.ReducedLookupCosetShift

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.WindowedArith (tableValue window)
open FormalRV.Shor.CosetEigenstate.ReducedLookupCosetGate
open FormalRV.Shor.CosetEigenstate.ReducedLookupEgate
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)
open FormalRV.Shor.CosetEigenstate.GatePerm (gateToPerm)
open FormalRV.Shor.CosetEigenstate.UCEvalBridge (uc_eval_eq_permState)
open FormalRV.Shor.CosetEigenstate.BranchFactor (branchOfE)
open FormalRV.Shor.CosetEigenstate.CosetMul
  (actualAcc runningSum actualAcc_eq_cosetState_runningSum)
open FormalRV.Shor.CosetEigenstate.CosetTableSum (cosetWindowConst cosetWindowConst_lt)
open FormalRV.Shor.CosetEigenstate.CosetDeviationE (cosetOutOfPlace_hfwd_E)
open FormalRV.Shor.CosetEigenstate.CosetFoldWindowed (cosetState_windowedMul_embed_off)
open FormalRV.Shor.CosetBornWeight (bornWeightOn)

/-! ## PART 1 — STATE-LEVEL one-pass. -/

/-- **PART 1 — STATE-LEVEL one-pass coset action.**  One literal `uc_eval` reduced
    window step `j`, applied to the whole-register coset input `cosetInput m`, advances
    the accumulator value to `m + c` (`c = tableValue a N w j (window w y j)`), exactly,
    AS A WHOLE-REGISTER STATE EQUALITY (every control branch tracked). -/
theorem reducedWindowStep_cosetInput (w bits N a numWin m y j cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hj : j < numWin) (hN : 0 < N)
    (hc : tableValue a N w j (window w y j) < 2 ^ bits)
    (hfit : m + tableValue a N w j (window w y j) + (2 ^ cm - 1) * N < 2 ^ bits) :
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
          (1 + 2 * w + cuccaroAdder.span bits) j))
      * (id (cosetInput w bits numWin N cm m y) :
          Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
      = cosetInput w bits numWin N cm (m + tableValue a N w j (window w y j)) y := by
  set c := tableValue a N w j (window w y j) with hcdef
  rw [uc_eval_eq_permState _ (cosetDim w bits)
        (stepWellTyped w bits N a numWin j hw hbits hj)]
  set σ := gateToPerm (reducedWindowStepOf cuccaroAdder w bits N a bits (1 + 2 * w)
      (1 + 2 * w + cuccaroAdder.span bits) j) (cosetDim w bits)
      (stepWellTyped w bits N a numWin j hw hbits hj) with hσ
  funext idx z
  have h0 : z = 0 := Subsingleton.elim z 0
  subst h0
  -- LHS = cosetInput m (σ.symm idx) 0.  RHS = cosetInput (m+c) idx 0.
  show cosetInput w bits numWin N cm m y (σ.symm idx) 0
    = cosetInput w bits numWin N cm (m + c) y idx 0
  -- Classify idx by its control branch.
  by_cases hctrl : ((e_gate w bits numWin).symm idx).1 = xCtrl w bits numWin y
  · -- Active branch: idx = e (xCtrl y, z') with z' the data value.
    set z' := ((e_gate w bits numWin).symm idx).2 with hz'def
    have hidx : idx = e_gate w bits numWin (xCtrl w bits numWin y, z') := by
      rw [hz'def, ← hctrl, Prod.mk.eta, Equiv.apply_symm_apply]
    -- The data preimage value: z = (z'.val + (2^bits - c)) % 2^bits.
    set zz : Nat := (z'.val + (2 ^ bits - c)) % 2 ^ bits with hzzdef
    have hzzlt : zz < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
    have hzzc : (zz + c) % 2 ^ bits = z'.val := by
      rw [hzzdef, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show z'.val + (2 ^ bits - c) + c = z'.val + 2 ^ bits by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt z'.isLt]
    -- σ (e (xCtrl y, ⟨zz⟩)) = e (xCtrl y, z').
    have hperm : σ (e_gate w bits numWin (xCtrl w bits numWin y, ⟨zz, hzzlt⟩))
        = e_gate w bits numWin (xCtrl w bits numWin y, z') := by
      rw [hσ, step_perm_through_e_gate w bits N a numWin zz y j hw hbits hj hzzlt
            (hzzc ▸ z'.isLt)]
      exact congrArg _ (Prod.ext rfl (Fin.ext hzzc))
    have hsymm : σ.symm idx = e_gate w bits numWin (xCtrl w bits numWin y, ⟨zz, hzzlt⟩) := by
      rw [hidx, ← hperm, Equiv.symm_apply_apply]
    -- LHS: cosetInput m at e (xCtrl y, ⟨zz⟩): control matches, data = ⟨zz⟩.
    rw [hsymm]
    unfold cosetInput
    rw [Equiv.symm_apply_apply, if_pos rfl, hidx, Equiv.symm_apply_apply, if_pos rfl]
    -- Both sides are cosetState evaluations; RHS data z', LHS data ⟨zz⟩.
    -- Use the wrap shift: cosetState m at ⟨zz⟩ = wrapShiftState c (cosetState m) at z' = cosetState (m+c) at z'.
    have hkey : cosetState (2 ^ bits) N cm m ⟨zz, hzzlt⟩ 0
        = cosetState (2 ^ bits) N cm (m + c) z' 0 := by
      have hws := ApproxOp.wrapShiftState_cosetState (2 ^ bits) N cm m c hN hfit
      have := congrFun (congrFun hws z') 0
      -- wrapShiftState c (cosetState m) z' 0 = cosetState m at ⟨(z'+(2^bits-c))%2^bits⟩ 0
      rw [show ApproxOp.wrapShiftState (2 ^ bits) c (cosetState (2 ^ bits) N cm m) z' 0
            = cosetState (2 ^ bits) N cm m ⟨zz, hzzlt⟩ 0 by
            unfold ApproxOp.wrapShiftState; rfl] at this
      rw [this]
    exact hkey
  · -- Inactive branch: both sides 0.
    -- RHS: cosetInput (m+c) idx 0 = 0 since idx control ≠ xCtrl y.
    have hrhs : cosetInput w bits numWin N cm (m + c) y idx 0 = 0 := by
      unfold cosetInput; rw [if_neg hctrl]
    -- LHS: cosetInput m (σ.symm idx) 0 = 0; show σ.symm idx control ≠ xCtrl y.
    have hlhs : cosetInput w bits numWin N cm m y (σ.symm idx) 0 = 0 := by
      unfold cosetInput
      by_cases hc2 : ((e_gate w bits numWin).symm (σ.symm idx)).1 = xCtrl w bits numWin y
      · -- σ.symm idx = e (xCtrl y, w'); then idx = σ (that) is in the active branch — contradiction.
        exfalso
        set w' := ((e_gate w bits numWin).symm (σ.symm idx)).2 with hw'def
        have hpre : σ.symm idx = e_gate w bits numWin (xCtrl w bits numWin y, w') := by
          rw [hw'def, ← hc2, Prod.mk.eta, Equiv.apply_symm_apply]
        have hidx2 : idx = σ (e_gate w bits numWin (xCtrl w bits numWin y, w')) := by
          rw [← hpre, Equiv.apply_symm_apply]
        have hstep : σ (e_gate w bits numWin (xCtrl w bits numWin y, w'))
            = e_gate w bits numWin (xCtrl w bits numWin y,
                ⟨(w'.val + c) % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩) := by
          rw [hσ]
          have := step_perm_through_e_gate w bits N a numWin w'.val y j hw hbits hj w'.isLt
                    (Nat.mod_lt _ (Nat.two_pow_pos bits))
          rw [show (⟨w'.val, w'.isLt⟩ : Fin (2 ^ bits)) = w' from rfl] at this
          exact this
        apply hctrl
        rw [hidx2, hstep, Equiv.symm_apply_apply]
      · rw [if_neg hc2]
    rw [hlhs, hrhs]

/-! ## PART 2 — THE FOLD. -/

/-- `runningSum` is monotone in its upper bound. -/
theorem runningSum_le_mono (cs : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    runningSum cs a ≤ runningSum cs b := by
  induction b with
  | zero =>
      have : a = 0 := Nat.le_zero.mp hab
      subst this
      exact le_refl _
  | succ k ih =>
      rcases Nat.lt_or_ge a (k + 1) with h | h
      · have hak : a ≤ k := by omega
        calc runningSum cs a ≤ runningSum cs k := ih hak
          _ ≤ runningSum cs k + cs k := Nat.le_add_right _ _
          _ = runningSum cs (k + 1) := rfl
      · have hak1 : a = k + 1 := by omega
        subst hak1
        exact le_refl _

/-- The fold split for `reducedWindowedMulOf`: peel the last window step. -/
theorem reducedWindowedMulOf_succ (w bits N a q yBase n : Nat) :
    reducedWindowedMulOf cuccaroAdder w bits N a bits q yBase (n + 1)
      = Gate.seq (reducedWindowedMulOf cuccaroAdder w bits N a bits q yBase n)
          (reducedWindowStepOf cuccaroAdder w bits N a bits q yBase n) := by
  unfold reducedWindowedMulOf
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

/-- **PART 2 (generalized fold).**  For every prefix length `n ≤ numWin`, the
    `reducedWindowedMulOf … n` (the first `n` window passes) sends the fresh coset input
    to `cosetState` at the running sum of the first `n` window addends — exactly, as a
    whole-register state equality.  `numWin`/`bits` are the GLOBAL parameters so each
    per-step `j < n ≤ numWin` is well-typed and `step_perm_through_e_gate`-eligible. -/
theorem reducedWindowedMul_cosetInput_aux (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    ∀ n, n ≤ numWin →
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (reducedWindowedMulOf cuccaroAdder w bits N a bits (1 + 2 * w)
          (1 + 2 * w + cuccaroAdder.span bits) n))
      * (id (cosetInput w bits numWin N cm 0 y) :
          Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
      = cosetInput w bits numWin N cm
          (runningSum (cosetWindowConst a N w y) n) y := by
  intro n
  induction n with
  | zero =>
      intro _
      show (Framework.uc_eval (Gate.toUCom (cosetDim w bits) Gate.I)
          * (id (cosetInput w bits numWin N cm 0 y) :
              Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
        = cosetInput w bits numWin N cm (runningSum (cosetWindowConst a N w y) 0) y
      rw [Gate.toUCom_I,
          uc_eval_ID_eq_one (show 0 < cosetDim w bits by unfold cosetDim; omega),
          Matrix.one_mul]
      rfl
  | succ k ih =>
      intro hk
      have hkle : k ≤ numWin := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      have hkwin : k < numWin := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      -- per-step addend c_k.
      set ck := tableValue a N w k (window w y k) with hckdef
      have hck_eq : cosetWindowConst a N w y k = ck := rfl
      -- runningSum at k+1 = runningSum k + ck.
      have hrs_succ : runningSum (cosetWindowConst a N w y) (k + 1)
          = runningSum (cosetWindowConst a N w y) k + ck := by
        show runningSum (cosetWindowConst a N w y) k + cosetWindowConst a N w y k = _
        rw [hck_eq]
      -- the per-step fit: runningSum k + ck + (2^cm-1)*N < 2^bits.
      have hmono : runningSum (cosetWindowConst a N w y) (k + 1)
          ≤ runningSum (cosetWindowConst a N w y) numWin :=
        runningSum_le_mono _ hk
      have hfit_k : runningSum (cosetWindowConst a N w y) k + ck + (2 ^ cm - 1) * N < 2 ^ bits := by
        rw [← hrs_succ]; omega
      -- hc_k : ck < 2^bits.
      have hc_k : ck < 2 ^ bits := by omega
      -- fold split.
      rw [reducedWindowedMulOf_succ, Gate.toUCom_seq, uc_eval_seq_mul, ih hkle,
          ← (show (id (cosetInput w bits numWin N cm
                  (runningSum (cosetWindowConst a N w y) k) y) :
                Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ)
              = cosetInput w bits numWin N cm
                  (runningSum (cosetWindowConst a N w y) k) y from rfl),
          reducedWindowStep_cosetInput w bits N a numWin
            (runningSum (cosetWindowConst a N w y) k) y k cm hw hbits hkwin hN hc_k hfit_k]
      rw [hrs_succ]

/-- **PART 2 — THE FOLD across all window passes.**  The full reduced-lookup coset
    multiplier circuit, applied to the FRESH coset input `cosetInput 0`, advances the
    accumulator value to the un-reduced running sum of all window addends, exactly, as a
    whole-register state equality. -/
theorem reducedWindowedMul_cosetInput (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
      * (id (cosetInput w bits numWin N cm 0 y) :
          Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
      = cosetInput w bits numWin N cm
          (runningSum (cosetWindowConst a N w y) numWin) y := by
  -- cosetModMulCircuitOf is DEFEQ reducedWindowedMulOf at the standard layout.
  show (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (reducedWindowedMulOf cuccaroAdder w bits N a bits (1 + 2 * w)
          (1 + 2 * w + cuccaroAdder.span bits) numWin))
      * (id (cosetInput w bits numWin N cm 0 y) :
          Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
      = cosetInput w bits numWin N cm
          (runningSum (cosetWindowConst a N w y) numWin) y
  exact reducedWindowedMul_cosetInput_aux w bits N a numWin y cm hw hbits hN hfitAll
    numWin (le_refl _)

/-! ## PART 3 — hfac_act DISCHARGE + the deviation. -/

/-- **PART 3 — THE DEVIATION OF THE CONCRETE REDUCED-LOOKUP GATE.**  The literal
    reduced-lookup windowed coset multiplier `cosetModMulCircuitOf cuccaroAdder`, applied
    to the fresh coset input `cosetInput 0` (multiplier `y`, accumulator at value `0`), is
    within `numWin·(2/2^cm)` (Born-L1, `normSqDist`) of the IDEAL coset output
    `cosetInput ((a·y) mod N)`.  This DISCHARGES `cosetOutOfPlace_hfwd_E.hfac_act` for the
    literal gate: the active singleton branch `{xCtrl y}` runs the coset fold
    `actualAcc … (cosetWindowConst a N w y)` (= PART 2 + `actualAcc_eq_cosetState_runningSum`),
    while the ideal is `cosetState ((a·y) mod N)`. -/
theorem reducedLookupWindowedMul_deviation (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hy : y < (2 ^ w) ^ numWin) (hfit_engine : N + 2 ^ cm * N ≤ 2 ^ bits)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
          * (id (cosetInput w bits numWin N cm 0 y) :
              Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
        (cosetInput w bits numWin N cm ((a * y) % N) y)
      ≤ (numWin : ℝ) * (2 / 2 ^ cm) := by
  -- The active control branch is the singleton {xCtrl y}; weight β ≡ 1; input value y.
  refine cosetOutOfPlace_hfwd_E (e_gate w bits numWin)
    (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
        (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
      * (id (cosetInput w bits numWin N cm 0 y) :
          Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
    (cosetInput w bits numWin N cm ((a * y) % N) y)
    {xCtrl w bits numWin y} (fun _ => 1)
    a N cm w numWin (fun _ => y) hN ?_ hfit_engine ?_ ?_ ?_ ?_
  · -- hxval: y < (2^w)^numWin for the active branch.
    intro b _; exact hy
  · -- hzero: off the singleton, both branches are 0.
    intro b hb
    have hbne : b ≠ xCtrl w bits numWin y := by
      intro h; exact hb (Finset.mem_singleton.mpr h)
    rw [reducedWindowedMul_cosetInput w bits N a numWin y cm hw hbits hN hfitAll]
    rw [branchOfE_cosetInput_zero w bits numWin N cm
          (runningSum (cosetWindowConst a N w y) numWin) y b hbne,
        branchOfE_cosetInput_zero w bits numWin N cm ((a * y) % N) y b hbne]
  · -- hfac_act: the active branch runs the coset fold of the window constants.
    intro b hb
    have hbeq : b = xCtrl w bits numWin y := Finset.mem_singleton.mp hb
    subst hbeq
    rw [reducedWindowedMul_cosetInput w bits N a numWin y cm hw hbits hN hfitAll,
        branchOfE_cosetInput_active]
    funext i z
    rw [actualAcc_eq_cosetState_runningSum (2 ^ bits) N cm 0
          (cosetWindowConst a N w y) hN numWin]
    show cosetState (2 ^ bits) N cm (runningSum (cosetWindowConst a N w y) numWin) i z
      = (1 : ℂ) * cosetState (2 ^ bits) N cm (0 + runningSum (cosetWindowConst a N w y) numWin) i z
    rw [one_mul, Nat.zero_add]
  · -- hfac_idl: the ideal branch is cosetState ((a·y) mod N).
    intro b hb
    have hbeq : b = xCtrl w bits numWin y := Finset.mem_singleton.mp hb
    subst hbeq
    rw [branchOfE_cosetInput_active]
    funext i z
    rw [one_mul]
  · -- hweight: ∑ over {xCtrl y} of normSq 1 = 1 ≤ 1.
    rw [Finset.sum_singleton]
    simp

/-! ## PART 4 — the named deliverable. -/

/-- **PART 4 — THE MULTIPLIER-LOCAL COSET-STATE-SHIFT DELIVERABLE.**  The concrete
    reduced-lookup windowed coset multiplier gate (`cosetModMulCircuitOf cuccaroAdder`)
    sends the fresh coset input (accumulator value `0`, multiplier register `y`) to the
    ideal coset output `cosetInput ((a·y) mod N)` — i.e. it realizes the coset-state shift
    `cosetState(0) → cosetState((a·y) mod N)` in the active multiplier branch — with total
    Born-L1 deviation `≤ numWin·(2/2^cm)` off the accumulated wrap/bad set.  This is the
    multiplier-local discharge of `cosetOutOfPlace_hfwd_E.hfac_act` for the LITERAL gate;
    it is `reducedLookupWindowedMul_deviation`, named as the deliverable. -/
theorem reducedLookupWindowedMul_cosetState_shift (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hy : y < (2 ^ w) ^ numWin) (hfit_engine : N + 2 ^ cm * N ≤ 2 ^ bits)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    normSqDist
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
          * (id (cosetInput w bits numWin N cm 0 y) :
              Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
        (cosetInput w bits numWin N cm ((a * y) % N) y)
      ≤ (numWin : ℝ) * (2 / 2 ^ cm) :=
  reducedLookupWindowedMul_deviation w bits N a numWin y cm hw hbits hN hy hfit_engine hfitAll

/-! ## PART 5 — the trusted local oracle in the engine's `EmbedAgreeOff` language.

The deviation form (`reducedLookupWindowedMul_cosetState_shift`) is what the Shor-level
engine consumes through `normSqDist`; but the `EmbedAgreeOff`-based engine
(`embedAgreeOff_oracle_step`, `cosetOutOfPlace_hfwd_E`) consumes an EXACT off-bad
agreement plus a Born-mass bound.  This restates the multiplier-local result in exactly
that off-bad form (on the gate's own `e_gate` factorization): the gate output, read on the
active control branch `xCtrl y`, agrees with the ideal `cosetState ((a·y) mod N)` off a bad
set `B` whose Born mass is `≤ numWin/2^cm` on each side.  This is the trusted-local-oracle
endpoint; the Shor-level assembly transports it through the controlled-oracle / `jointIdx`
register lift (the genuine remaining construction, NOT yet done). -/
theorem reducedLookupWindowedMul_embedAgreeOff_local (w bits N a numWin y cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN : 0 < N)
    (hy : y < (2 ^ w) ^ numWin)
    (hfitAll : runningSum (cosetWindowConst a N w y) numWin + (2 ^ cm - 1) * N < 2 ^ bits) :
    ∃ B : Finset (Fin (2 ^ bits)),
      (∀ z, z ∉ B →
        branchOfE (e_gate w bits numWin)
            (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
                (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
              * (id (cosetInput w bits numWin N cm 0 y) :
                  Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
            (xCtrl w bits numWin y) z 0
          = cosetState (2 ^ bits) N cm ((a * y) % N) z 0)
      ∧ bornWeightOn
          (cosetState (2 ^ bits) N cm (runningSum (cosetWindowConst a N w y) numWin)) B
          ≤ (numWin : ℝ) / 2 ^ cm
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm ((a * y) % N)) B ≤ (numWin : ℝ) / 2 ^ cm := by
  obtain ⟨B, hagree, hb1, hb2⟩ :=
    cosetState_windowedMul_embed_off (2 ^ bits) N cm a w numWin y hN hy
  refine ⟨B, ?_, hb1, hb2⟩
  intro z hzB
  have hbr : branchOfE (e_gate w bits numWin)
        (Framework.uc_eval (Gate.toUCom (cosetDim w bits)
            (cosetModMulCircuitOf cuccaroAdder w bits N a numWin))
          * (id (cosetInput w bits numWin N cm 0 y) :
              Matrix (Fin (2 ^ cosetDim w bits)) (Fin 1) ℂ))
        (xCtrl w bits numWin y)
      = cosetState (2 ^ bits) N cm (runningSum (cosetWindowConst a N w y) numWin) := by
    rw [reducedWindowedMul_cosetInput w bits N a numWin y cm hw hbits hN hfitAll]
    exact branchOfE_cosetInput_active w bits numWin N cm
      (runningSum (cosetWindowConst a N w y) numWin) y
  rw [congrFun (congrFun hbr z) 0]
  exact hagree z hzB

end FormalRV.Shor.CosetEigenstate.ReducedLookupCosetShift