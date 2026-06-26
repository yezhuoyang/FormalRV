/-
  FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepClose — closing gap-3 (2b)+(2c).
  ════════════════════════════════════════════════════════════════════════════
  Scratch module assembling the literal `E2runwayInit` from the prep circuit.

  DELIVERED, kernel-clean (axioms ⊆ {propext, Classical.choice, Quot.sound}; no
  `sorry`, no `native_decide`):

   §B.1  `interior_npar_H` — the GENERAL interior-block npar_H lemma (the genuinely
         hard, reusable (2b) core).  Placing `npar_H cm` on the INTERIOR block
         `[b, b+cm)` of a register split `lo ⊗ (zeros_cm ⊗ hi)` produces the uniform
         superposition on the middle block, framing `lo` and `hi`.  Lifts the
         framework's LEADING-block `npar_H_kron_zeros_eq_uniform_sum` onto an interior
         block via `uc_eval_map_qubits_shift_kron_vec` + the leading form.

   §C    The (2c) KRON → `E2runwayInit` reconciliation — FULLY proved:
         `kronDim_eq`, `cast_jointIdx_eq_combine_runway`, and the headline
         `kron_E2runwayInit` (the dimension-cast of `(1/√2^m ∑|x⟩) ⊗ cosetInputVec 1 0`
         IS the literal `E2runwayInit`), via the `jointEquiv`/`E2shor_dim_eq`
         factorization and `E2runwayInit_acts`.

   §D    The headline `uc_eval_E2runwayInitPrep_eq_E2runwayInit` — FULLY proved
         MODULO the single open (2b) input `hInteriorH` (the interior-H source spec).
         Composes RunwayPrepFull's conditional headline with (2c)'s `kron_E2runwayInit`.

  STILL OPEN (the remaining (2b) piece): a concrete `runwayDataH` circuit together
  with `runwayDataH_spec : uc_eval (runwayDataH …) * basis0 = doublyHWindowSource …`.
  Feeding that into §D (with `runwayDataH_wellTyped`) yields the UNCONDITIONAL literal
  headline.  See the §D doc-comment for the precise remaining goal.  The `interior_npar_H`
  core (§B.1) is the structural workhorse for that spec; the obstruction is purely the
  entry-wise match of the resulting nested-kron uniform-double-sum against `genTwoReg`'s
  `decodeReg`/`scratchClean` indicator form (a coordinate-bridge problem, not a new
  circuit-semantics fact).
-/
import FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull
import FormalRV.Shor.GidneyInPlace.Ideal.Def.E2CosetSuccess

namespace FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepClose

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore (basis0)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull
open FormalRV.Framework (kron_vec kron_zeros)
open FormalRV.Framework.BaseUCom (npar_H npar_H_well_typed)
open FormalRV.QFT.TwoRegisterQFT (uc_eval_map_qubits_shift_kron_vec)
open FormalRV.SQIRPort (npar_H_kron_zeros_eq_uniform_sum)
open FormalRV.SQIRPort (QState QState.cast)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx sum_jointIdx_eq)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc cosetWork_dim_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceNormBound (cosetInputVec)
open FormalRV.Shor.GidneyInPlace.BranchFactor (jointEquiv jointEquiv_apply)
open FormalRV.Shor.GidneyInPlace.InPlaceTwoRegEmbedHmarg (E2shor_dim_eq)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess (E2runwayInit E2runwayInit_acts)
open scoped Classical

/-! ## §B.1. The GENERAL interior-block npar_H lemma.

Placing `npar_H cm` on the INTERIOR `cm`-wire block `[b, b+cm)` of a register split as
`lo ⊗ (zeros_cm ⊗ hi)` produces the uniform superposition on the middle block, framing
`lo` (low wires `[0,b)`) and `hi` (high wires `[b+cm, b+cm+hi)`).  This is the genuine
"interior npar_H" piece (2b): the framework's `npar_H_kron_zeros_eq_uniform_sum` puts H on
a LEADING block; we lift it onto an interior block by `uc_eval_map_qubits_shift_kron_vec`
(which frames the low `lo` factor) and then apply the leading form to the `zeros_cm ⊗ hi`
sub-register. -/
theorem interior_npar_H (b cm hi : Nat) (hcm : 0 < cm)
    (lo : Matrix (Fin (2 ^ b)) (Fin 1) ℂ) (hiv : Matrix (Fin (2 ^ hi)) (Fin 1) ℂ) :
    Framework.uc_eval
        (map_qubits (fun q => b + q) (npar_H cm : Framework.BaseUCom (cm + hi))
          : Framework.BaseUCom (b + (cm + hi)))
        * kron_vec lo (kron_vec (kron_zeros cm) hiv)
      = kron_vec lo
          (((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
            ∑ x : Fin (2 ^ cm),
            kron_vec (FormalRV.Framework.basis_vector (2 ^ cm) x.val) hiv) := by
  rw [uc_eval_map_qubits_shift_kron_vec (npar_H cm : Framework.BaseUCom (cm + hi))
        (npar_H_well_typed cm (Nat.le_add_right cm hi) (by omega)) lo
        (kron_vec (kron_zeros cm) hiv),
      npar_H_kron_zeros_eq_uniform_sum hcm hiv]

/-! ## §C. (2c) KRON → `E2runwayInit`.

`E2runwayInit m w bits N cm` is the `jointEquiv`/`shorDvd` factorization of the
phase-uniform ⊗ data-factor tensor, living in `QState (2^m·2^bits·2^(cosetAnc w bits))`.
The kron form `(1/√2^m ∑_x|x⟩) ⊗ cosetInputVec 1 0` produced by (2a)+(2b) lives in
`Fin (2^(m + cosetDim w bits))`.  We reconcile the two through the dimension cast
`2^(m + cosetDim w bits) = 2^m·2^bits·2^(cosetAnc w bits)` (composing `cosetWork_dim_eq`,
`cosetDim w bits = bits + cosetAnc w bits`, with the `pow_add`/`mul_assoc` split). -/

/-- The dimension equality bridging the kron register `m + cosetDim w bits` and the
    `E2runwayInit` register `2^m·2^bits·2^(cosetAnc w bits)`. -/
theorem kronDim_eq (m w bits : Nat) :
    2 ^ (m + cosetDim w bits) = 2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits) := by
  rw [← cosetWork_dim_eq w bits, pow_add, pow_add, mul_assoc]

/-- The `jointIdx`↔`kron_vec_combine` index bridge for the runway register: after casting
    back to `Fin (2^(m + cosetDim w bits))`, `jointIdx x y` IS `kron_vec_combine x` of the
    work index `y` (cast to `Fin (2^(cosetDim w bits))`).  Both have val `x·2^(cosetDim) + y`. -/
theorem cast_jointIdx_eq_combine_runway (m w bits : Nat)
    (x : Fin (2 ^ m)) (y : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m)) :
    (Fin.cast (kronDim_eq m w bits).symm (jointIdx (shorDvd m bits (cosetAnc w bits)) x y)
      : Fin (2 ^ (m + cosetDim w bits)))
      = FormalRV.Framework.kron_vec_combine x (Fin.cast (E2shor_dim_eq m w bits) y) := by
  apply Fin.ext
  show (jointIdx (shorDvd m bits (cosetAnc w bits)) x y).val
      = (FormalRV.Framework.kron_vec_combine x (Fin.cast (E2shor_dim_eq m w bits) y)).val
  show x.val * ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m) + y.val
      = x.val * 2 ^ (cosetDim w bits) + y.val
  have h := E2shor_dim_eq m w bits
  generalize y.val = yv
  rw [h]

/-- **THE KRON → `E2runwayInit` RECONCILIATION (2c).**  The dimension-cast of the
    phase-uniform ⊗ data tensor IS `E2runwayInit`.  Proved entry-wise via the
    `jointEquiv` decomposition: at `i = jointIdx x y`, the cast-kron reads
    `(1/√2^m)·cosetInputVec 1 0` at the work index `y` (cast), matching
    `E2runwayInit_acts`. -/
theorem kron_E2runwayInit (m w bits N cm : Nat) :
    QState.cast (kronDim_eq m w bits)
        (kron_vec
          (((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) •
            ∑ x : Fin (2 ^ m), FormalRV.Framework.basis_vector (2 ^ m) x.val)
          (cosetInputVec w bits N cm 1 0))
      = E2runwayInit m w bits N cm := by
  funext i col
  obtain rfl : col = 0 := Subsingleton.elim col 0
  -- Write i as jointIdx x y via the jointEquiv surjection.
  set p := (jointEquiv (shorDvd m bits (cosetAnc w bits))).symm i with hp
  have hi : i = jointIdx (shorDvd m bits (cosetAnc w bits)) p.1 p.2 := by
    rw [← jointEquiv_apply (shorDvd m bits (cosetAnc w bits)) p.1 p.2, hp]
    simp [Prod.mk.eta, Equiv.apply_symm_apply]
  rw [hi, E2runwayInit_acts m w bits N cm p.1 p.2]
  -- LHS: read the cast-kron at jointIdx x y.
  show QState.cast (kronDim_eq m w bits)
      (kron_vec
        (((1 : ℂ) / Real.sqrt (2 ^ m : ℝ)) •
          ∑ x : Fin (2 ^ m), FormalRV.Framework.basis_vector (2 ^ m) x.val)
        (cosetInputVec w bits N cm 1 0))
      (jointIdx (shorDvd m bits (cosetAnc w bits)) p.1 p.2) 0
    = ((1 : ℂ) / Real.sqrt (2 ^ m : ℝ))
        * cosetInputVec w bits N cm 1 0 (Fin.cast (E2shor_dim_eq m w bits) p.2) 0
  show kron_vec _ _
        (Fin.cast (kronDim_eq m w bits).symm
          (jointIdx (shorDvd m bits (cosetAnc w bits)) p.1 p.2)) 0 = _
  rw [cast_jointIdx_eq_combine_runway m w bits p.1 p.2,
      FormalRV.Framework.kron_vec_apply_combine]
  -- χ at p.1 = (1/√2^m)·(∑ basis)(p.1) = (1/√2^m)·1.
  congr 1
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p.1]
  · rw [FormalRV.Framework.basis_vector_apply_eq _ _ _ _ rfl, mul_one]
  · intro b _ hb
    exact FormalRV.Framework.basis_vector_apply_ne _ _ _ _ (fun h => hb (Fin.ext h.symm))
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## §D. The headline `uc_eval (E2runwayInitPrep …) * basis0 = E2runwayInit`,
    modulo the (2b) interior-H bridge `hInteriorH`.

Combines the RunwayPrepFull conditional headline `uc_eval_E2runwayInitPrep_of_interiorH`
(`uc_eval … * basis0 = kron_vec χ (cosetInputVec 1 0)`) with the (2c) reconciliation
`kron_E2runwayInit` (`QState.cast … (kron_vec χ (cosetInputVec 1 0)) = E2runwayInit`), via
the dimension cast `2^(m + cosetDim w (cm+rest)) = 2^m·2^(cm+rest)·2^(cosetAnc w (cm+rest))`.
The ONLY remaining open input is the (2b) interior-npar_H spec `hInteriorH`. -/

/-- **THE HEADLINE (cast form), modulo (2b).**  GIVEN an interior-H circuit `dataH`
    realizing the (2b) source spec (`basis0 → doublyHWindowSource`), the full prep
    `E2runwayInitPrep` carries `|0…0⟩` to the LITERAL `E2runwayInit` (under the dimension
    cast).  All of (2c) and the assembly are discharged here; only `hInteriorH` is open. -/
theorem uc_eval_E2runwayInitPrep_eq_E2runwayInit
    (m w rest cm N : Nat) (hm : 0 < m) (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (dataH : Framework.BaseUCom (cosetDim w (cm + rest)))
    (hdataH_wt : UCom.WellTyped (cosetDim w (cm + rest)) dataH)
    (hInteriorH : Framework.uc_eval dataH * basis0 (cosetDim w (cm + rest))
      = RunwayPrepFull.doublyHWindowSource w rest cm) :
    QState.cast (kronDim_eq m w (cm + rest))
        (Framework.uc_eval
            (RunwayPrepFull.E2runwayInitPrep m w rest cm N hN h1N hbudget dataH)
          * basis0 (m + cosetDim w (cm + rest)))
      = E2runwayInit m w (cm + rest) N cm := by
  rw [RunwayPrepFull.uc_eval_E2runwayInitPrep_of_interiorH m w rest cm N hm hN h1N hbudget
        dataH hdataH_wt hInteriorH]
  exact kron_E2runwayInit m w (cm + rest) N cm

/-! ## §E. (2b) THE CONCRETE INTERIOR-H CIRCUIT `runwayDataH`.

A concrete instance of the (2b) `dataH` input: `X` on the ctrl wire `0`, then `npar_H cm`
on the a-block H-window `[aBase+rest, aBase+rest+cm)`, then `npar_H cm` on the b-block
H-window `[bBase+rest, bBase+rest+cm)`.  Delivered kernel-clean: the circuit `runwayDataH`,
its well-typedness `runwayDataH_wellTyped`, the leading-wire `X` action `uc_eval_X_zero` /
`uc_eval_X_basis0`, and the `kron_zeros` split helpers.  Its source spec
`runwayDataH_spec` (= the (2b) `hInteriorH` instance) is the single remaining goal — its
precise statement and proof plan are §F. -/

open FormalRV.Framework.BaseUCom (U_X)
open FormalRV.SQIRPort (uc_eval_app1_control_kron_vec pad_u_one_zero_eq)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase scratchClean)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock (genTwoReg winA genTwoReg_funboolNat)

/-- **Offset-shifted `npar` well-typedness (count form).**  For a per-wire gate family
    `g : Nat → BaseUCom src` each of which lands (after the `+off` shift) on an in-range wire,
    `map_qubits (·+off) (npar k g)` is well-typed on `D` qubits, provided `off < D` (the
    `SKIP = ID 0` base case wire `off+0`).  Inducts on the COUNT `k`, keeping the source dim
    `src` fixed, so it applies to `npar_H cm : BaseUCom cm` at `k = cm`. -/
theorem wellTyped_map_qubits_npar_off {src : Nat} (off D k : Nat)
    (g : Nat → Framework.BaseUCom src) (hoff : off < D)
    (hg : ∀ j, j < k → (map_qubits (fun q => off + q) (g j) : Framework.BaseUCom D).WellTyped D) :
    UCom.WellTyped D
      (map_qubits (fun q => off + q)
        (FormalRV.Framework.BaseUCom.npar k g : Framework.BaseUCom src)
        : Framework.BaseUCom D) := by
  induction k with
  | zero =>
      -- npar 0 g = SKIP = app1 U_I 0, mapped to app1 U_I (off+0); needs off < D.
      exact UCom.WellTyped.app1 (show off + 0 < D by omega)
  | succ n ih =>
      -- npar (n+1) g = seq (npar n g) (g n); map distributes over seq.
      exact UCom.WellTyped.seq (ih (fun j hj => hg j (by omega))) (hg n (Nat.lt_succ_self n))

/-- **Offset-shifted `npar_H` well-typedness.**  `map_qubits (·+off) (npar_H cm)` is
    well-typed on `D` qubits whenever `off < D` and `off + cm ≤ D` (every H wire `off + k`,
    `k < cm`).  Holds for ALL `cm` (including `cm = 0`), without needing the source
    `npar_H cm : BaseUCom cm` to be well-typed. -/
theorem wellTyped_map_qubits_npar_H_off (off D cm : Nat)
    (hoff : off < D) (hle : off + cm ≤ D) :
    UCom.WellTyped D
      (map_qubits (fun q => off + q) (npar_H cm : Framework.BaseUCom cm)
        : Framework.BaseUCom D) :=
  wellTyped_map_qubits_npar_off off D cm (fun k => FormalRV.Framework.BaseUCom.H k) hoff
    (fun j hj => UCom.WellTyped.app1 (show off + j < D by omega))

/-- **THE CONCRETE INTERIOR-H CIRCUIT.**  `X` on wire `0` (ctrl), then `npar_H cm` on the
    a-block H-window `[aBase w + rest, aBase w + rest + cm)`, then `npar_H cm` on the b-block
    H-window `[bBase w (cm+rest) + rest, bBase w (cm+rest) + rest + cm)`. -/
noncomputable def runwayDataH (w rest cm : Nat) :
    Framework.BaseUCom (cosetDim w (cm + rest)) :=
  UCom.seq
    (UCom.seq
      (UCom.app1 U_X 0)
      (map_qubits (fun q => aBase w + rest + q)
        (npar_H cm : Framework.BaseUCom cm)))
    (map_qubits (fun q => bBase w (cm + rest) + rest + q)
      (npar_H cm : Framework.BaseUCom cm))

/-- **`runwayDataH_wellTyped`.**  All wires lie below `cosetDim w (cm+rest)`. -/
theorem runwayDataH_wellTyped (w rest cm : Nat) :
    UCom.WellTyped (cosetDim w (cm + rest)) (runwayDataH w rest cm) := by
  refine UCom.WellTyped.seq (UCom.WellTyped.seq ?_ ?_) ?_
  · exact UCom.WellTyped.app1 (show 0 < cosetDim w (cm + rest) by unfold cosetDim; omega)
  · exact wellTyped_map_qubits_npar_H_off (aBase w + rest) (cosetDim w (cm + rest)) cm
      (by unfold aBase cosetDim; omega) (by unfold aBase cosetDim; omega)
  · exact wellTyped_map_qubits_npar_H_off (bBase w (cm + rest) + rest) (cosetDim w (cm + rest)) cm
      (by unfold bBase cosetDim; omega) (by unfold bBase cosetDim; omega)

/-- **X on the leading wire `0`.**  `uc_eval (app1 U_X 0 : BaseUCom 1) * |0⟩ = |1⟩`. -/
theorem uc_eval_X_zero :
    Framework.uc_eval (UCom.app1 U_X 0 : Framework.BaseUCom 1)
        * FormalRV.Framework.basis_vector 2 0
      = FormalRV.Framework.basis_vector 2 1 := by
  show pad_u 1 0 (FormalRV.Framework.rotation Real.pi 0 Real.pi)
      * FormalRV.Framework.basis_vector 2 0 = _
  rw [FormalRV.Framework.rotation_X, pad_u_one_zero_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FormalRV.Framework.σx, FormalRV.Framework.basis_vector_apply, Matrix.mul_apply]

/-- `kron_zeros (a + b) = kron_vec (kron_zeros a) (kron_zeros b)`. -/
theorem kron_zeros_split (a b : Nat) :
    FormalRV.Framework.kron_zeros (a + b)
      = kron_vec (FormalRV.Framework.kron_zeros a) (FormalRV.Framework.kron_zeros b) :=
  RunwayPrepCore.basis0_split a b

/-- `basis0 D = kron_zeros D` (definitional). -/
theorem basis0_eq_kron_zeros (D : Nat) :
    RunwayPrepCore.basis0 D = FormalRV.Framework.kron_zeros D := rfl

/-- **Step 2 (X on the leading ctrl wire).**  `uc_eval (app1 U_X 0) * basis0 D`
    (`D = 1 + d`) = `kron_vec |1⟩ (kron_zeros d)` — the ctrl wire flipped to `1`, the
    rest still `|0…0⟩`. -/
theorem uc_eval_X_basis0 (d : Nat) :
    Framework.uc_eval (UCom.app1 U_X 0 : Framework.BaseUCom (1 + d))
        * RunwayPrepCore.basis0 (1 + d)
      = kron_vec (FormalRV.Framework.basis_vector 2 1) (FormalRV.Framework.kron_zeros d) := by
  rw [basis0_eq_kron_zeros, kron_zeros_split 1 d,
      show (FormalRV.Framework.kron_zeros 1 : Matrix (Fin (2 ^ 1)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector 2 0 from rfl,
      uc_eval_app1_control_kron_vec (m := 1) (anc := d) (n := 0) (by omega) U_X
        (FormalRV.Framework.basis_vector 2 0) (FormalRV.Framework.kron_zeros d),
      uc_eval_X_zero]

/-! ## §F. THE PRECISE REMAINING GOAL (the (2b) `runwayDataH_spec`).

The single open obligation closing gap-3 UNCONDITIONALLY is:

    theorem runwayDataH_spec (w rest cm : Nat) (hcm : 0 < cm) :
        uc_eval (runwayDataH w rest cm) * basis0 (cosetDim w (cm + rest))
          = doublyHWindowSource w rest cm

Given it (plus `runwayDataH_wellTyped`), the UNCONDITIONAL literal headline is the
one-liner

    QState.cast (kronDim_eq m w (cm+rest))
        (uc_eval (E2runwayInitPrep m w rest cm N hN h1N hbudget (runwayDataH w rest cm))
          * basis0 (m + cosetDim w (cm+rest)))
      = E2runwayInit m w (cm+rest) N cm
  := uc_eval_E2runwayInitPrep_eq_E2runwayInit m w rest cm N hm hN h1N hbudget
       (runwayDataH w rest cm) (runwayDataH_wellTyped w rest cm) (runwayDataH_spec w rest cm hcm)

PROOF PLAN for `runwayDataH_spec` (the irreducible coordinate bridge):

  1.  `rw [runwayDataH, uc_eval_seq_mul, uc_eval_seq_mul]`, reducing to
        uc_eval(bH-H) * (uc_eval(aH-H) * (uc_eval(X@0) * basis0 D)).
  2.  X@0 on the LEADING wire: `basis0 D = kron_vec (kron_zeros 1) (kron_zeros (D-1))`
        (`kron_zeros_split`/`basis0_eq_kron_zeros`, with `D = 1 + (D-1)`); then
        `uc_eval_app1_control_kron_vec` (m := 1, n := 0) + `uc_eval_X_zero` gives
        `kron_vec (basis_vector 2 1) (kron_zeros (D-1))`.
  3.  Re-associate to the a-window split `kron_vec loA (kron_vec (kron_zeros cm) hiA)`
        at offset `aH = aBase w + rest` (`kron_zeros_split` to carve the `cm` H-window
        block out of `kron_zeros (D-1)`, `kron_vec_assoc` to move `basis_vector 2 1` and
        the `[1,aH)` zeros into `loA`); apply `interior_npar_H` (offset `aH`) — uniform
        sum on the a-window, framing `loA` and `hiA`.
  4.  Symmetrically at offset `bH = bBase w (cm+rest) + rest` (the a-uniform-sum sits
        inside the framed `loB`; distribute the b-H over the a-sum by linearity —
        `kron_vec_sum_left/right`, `Matrix.mul_sum`); apply `interior_npar_H` (offset `bH`).
  5.  Match the resulting nested-kron uniform-DOUBLE-sum against `doublyHWindowSource`
        ENTRY-WISE: `funext idx`, write `idx = funboolNat f`, evaluate both sides via
        `genTwoReg_funboolNat` (RHS) and iterated `kron_vec_apply` (LHS), reconciling the
        kron division/mod index decomposition (wire 0 = MSB, `fbn_testBit`) with the
        per-block little-endian `decodeReg` and the `scratchClean` predicate.  Reuse the
        single-block sum→indicator reindexing of
        `RunwayPrepCore.uniform_window_sum_eq_cosetState` / `npar_H_sum_over_hWindow`
        twice (one per block), gated by `scratchClean` of the framed (ctrl = 1, all other
        non-block wires = 0) wires.

  Steps 1–4 are mechanical (the `interior_npar_H` core + `kron_vec_assoc` cast plumbing);
  step 5 is the genuine coordinate bridge between the kron layout and the
  `decodeReg`/`scratchClean`/`funboolNat` layout of `genTwoReg`.  The reusable hard core
  (`interior_npar_H`) and the entire downstream (§C/§D) are discharged kernel-clean above;
  this is the one remaining piece. -/

-- Kernel-cleanliness checks (axioms ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms interior_npar_H
#print axioms kron_E2runwayInit
#print axioms cast_jointIdx_eq_combine_runway
#print axioms uc_eval_E2runwayInitPrep_eq_E2runwayInit

end FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepClose
