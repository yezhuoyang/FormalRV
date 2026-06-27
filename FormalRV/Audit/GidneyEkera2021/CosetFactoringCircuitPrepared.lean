/-
  FormalRV.Audit.GidneyEkera2021.CosetFactoringCircuitPrepared — closing audit G1:
  the coset factoring theorem ON the all-zeros input via ONE concrete prep+QPE circuit.
  ════════════════════════════════════════════════════════════════════════════

  Composes two existing kernel-clean results so that the coset success state
  `Shor_final_state_E2coset` is `uc_eval (cosetFullCircuit) · |0…0⟩` — the action of a
  SINGLE concrete `BaseUCom` (state-prep, then the H-free composed QPE circuit) on the
  all-zeros input — rather than a hand-defined runway column.

  INPUTS (both kernel-clean):
  • `CosetFactoring.shor_final_state_E2coset_eq_uc_eval` — the success state IS `uc_eval`
    of the composed QPE circuit applied to the `E2runwayRaw` column.
  • `RunwayPrepDone.uc_eval_E2runwayInitPrep` — `E2runwayInit` IS `uc_eval` of the prep
    circuit `E2runwayInitPrep` applied to `|0…0⟩` (modulo the `kronDim_eq` cast).

  KEY REPARAM.  The prep is for `bits = cm + rest`, so everything is instantiated at
  `bits := cm + rest`.  The composed QPE circuit lives at dimension `m + (bits + cosetAnc w bits)`
  while the prep lives at `m + cosetDim w bits`; these dimensions are PROPOSITIONALLY equal
  (`cosetWork_dim_eq : bits + cosetAnc w bits = cosetDim w bits`) but NOT defeq, so the QPE
  circuit is transported across that equality with `hU ▸ ·` and the matrix action is bridged by
  `uc_eval_dimcast_mul` (`subst`-then-`rfl`).  Both casts (`dim_assoc_eq` and `kronDim_eq`) land
  on the SAME factored target `2^m·2^bits·2^(cosetAnc w bits)` — the native dimension of
  `E2runwayInit` — which is what makes the reconciliation go through.

  DELIVERED.
  (1) `cosetFullCircuit` — the ONE concrete circuit `seq (E2runwayInitPrep …) (composed QPE …)`.
  (2) `Shor_final_state_E2coset_eq_fullCircuit` — the success state IS `uc_eval (cosetFullCircuit) · |0…0⟩`.
  (3) `gidney_inplace_coset_factoring_succeeds_circuit_prepared` — the G1-closing corollary:
      the SAME factoring bound `≥ κ/(log₂N)⁴ − 2m√(8·numWin/2^cm)` AND a nontrivial factor exists,
      AND the success state is now a genuine circuit on `|0…0⟩` (the `_eq_fullCircuit` conjunct).

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.

  HONEST SCOPE.  The NEW content is (2): the input is now a real prep circuit on `|0…0⟩`, not a
  hand-defined column.  The success bound itself is exactly `gidney_inplace_coset_factoring_succeeds`
  at `bits := cm + rest`.  This does NOT close gap-4 (the success bound still rides the exact
  reversible oracle `physRunwayOracle`, not GE2021's measured count-optimal `modExpAt` gate).
-/
import FormalRV.Audit.GidneyEkera2021.CosetFactoringSucceeds
import FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepDone

namespace FormalRV.Audit.GidneyEkera2021.CosetFactoringCircuitPrepared

open scoped BigOperators
open FormalRV.SQIRPort (QState dim_assoc_eq revIndex BasicSetting κ)
open FormalRV.Framework (BaseUCom UCom uc_eval uc_eval_seq_mul)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc cosetWork_dim_eq)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess (E2runwayInit Shor_final_state_E2coset)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore (basis0)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull (E2runwayInitPrep)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepClose (runwayDataH kronDim_eq)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepDone (uc_eval_E2runwayInitPrep)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (physRunwayOracle)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Audit.GidneyEkera2021.CosetFactoring
  (composedQPECircuit E2runwayRaw shor_final_state_E2coset_eq_uc_eval
   factoringSuccessProb_E2coset gidney_inplace_coset_factoring_succeeds)

/-! ## The dimension-transport bridge. -/

/-- **Column reindex along a dimension equality** — the `Fin`-cast column reindex, kept as a bare
    `Matrix` (the `fun i j` form, indexed at the actual column `j`) so matrix products against it
    resolve their `HMul` instance directly and so the transport bridge below is `rfl`. -/
def colReindex {A B : Nat} (h : A = B) (v : Matrix (Fin (2 ^ A)) (Fin 1) ℂ) :
    Matrix (Fin (2 ^ B)) (Fin 1) ℂ :=
  fun i j => v (Fin.cast (congrArg (2 ^ ·) h).symm i) j

/-- `colReindex` IS `QState.cast (congrArg (2^·) h)` (the two only differ in writing the column
    index as `j` vs the literal `0` — equal since `Fin 1` is a subsingleton). -/
theorem colReindex_eq_cast {A B : Nat} (h : A = B) (v : Matrix (Fin (2 ^ A)) (Fin 1) ℂ) :
    colReindex h v = FormalRV.SQIRPort.QState.cast (congrArg (2 ^ ·) h) v := by
  funext i j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  rfl

/-- **`uc_eval` of a dimension-`▸`-transported `BaseUCom`, applied to a column.**  For
    `h : A = B`, transporting a circuit `c : BaseUCom A` to `BaseUCom B` and acting on a
    `2^B`-column `v` equals: reindex `v` to `2^A`, act with `c`, reindex back.  `subst`-then-`rfl`. -/
theorem uc_eval_dimcast_mul {A B : Nat} (h : A = B) (c : BaseUCom A)
    (v : Matrix (Fin (2 ^ B)) (Fin 1) ℂ) :
    uc_eval (h ▸ c) * v
      = colReindex h
          ((uc_eval c * colReindex h.symm v : Matrix (Fin (2 ^ A)) (Fin 1) ℂ)) := by
  subst h
  rfl

/-- **`QState.cast` composition.**  `QState.cast h₂ ∘ QState.cast h₁ = QState.cast (h₁.trans h₂)`
    (all `Fin.cast`s preserve `.val`). -/
theorem qstate_cast_comp {a b c : Nat} (h1 : a = b) (h2 : b = c)
    (v : FormalRV.SQIRPort.QState a) :
    FormalRV.SQIRPort.QState.cast h2 (FormalRV.SQIRPort.QState.cast h1 v)
      = FormalRV.SQIRPort.QState.cast (h1.trans h2) v := by
  subst h1; subst h2; rfl

/-- **`colReindex` of a `QState.cast`** collapses to a single `QState.cast` along the composite
    Nat equality (used to fuse the `kronDim_eq` / `dim_assoc_eq` casts; the two proof terms for the
    same Nat equality are defeq by proof irrelevance). -/
theorem colReindex_cast {a A B : Nat} (h1 : a = 2 ^ A) (h2 : A = B)
    (v : FormalRV.SQIRPort.QState a) :
    colReindex h2 (FormalRV.SQIRPort.QState.cast h1 v : Matrix (Fin (2 ^ A)) (Fin 1) ℂ)
      = FormalRV.SQIRPort.QState.cast (h1.trans (congrArg (2 ^ ·) h2)) v := by
  rw [colReindex_eq_cast, qstate_cast_comp]

/-! ## (1) The one concrete circuit: prep, then composed QPE. -/

/-- **★ (1) THE ONE CONCRETE CIRCUIT ★.**  State-prep (`E2runwayInitPrep`, which carries
    `|0…0⟩` to the runway init) followed by the H-free composed QPE circuit
    (`composedQPECircuit` = `controlled_powers (qpeOracle …) m ; QFTinv m`), as a single
    `BaseUCom (m + cosetDim w (cm+rest))`.  The QPE circuit is natively at dimension
    `m + ((cm+rest) + cosetAnc w (cm+rest))`; it is transported to `m + cosetDim w (cm+rest)`
    across `cosetWork_dim_eq` so the two pieces seq at the SAME dimension. -/
noncomputable def cosetFullCircuit (m w rest cm N numWin : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat)
    (hN : 0 < N) (h1N : 1 < N)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    BaseUCom (m + cosetDim w (cm + rest)) :=
  UCom.seq
    (E2runwayInitPrep m w rest cm N hN h1N hbudget (runwayDataH w rest cm))
    (congrArg (m + ·) (cosetWork_dim_eq w (cm + rest))
      ▸ composedQPECircuit m (cm + rest) (cosetAnc w (cm + rest))
          (physRunwayOracle m w (cm + rest) numWin TfamK TfamKinv))

/-! ## (2) The success state IS a circuit on `|0…0⟩`. -/

/-- **★ (2) THE SUCCESS STATE IS `uc_eval (cosetFullCircuit) · |0…0⟩` ★.**  Composes
    `shor_final_state_E2coset_eq_uc_eval` (success state = composed-QPE on the runway column)
    with `uc_eval_E2runwayInitPrep` (the runway column = prep on `|0…0⟩`), reconciling the
    `dim_assoc_eq` and `kronDim_eq` casts (both land on the factored native dimension of
    `E2runwayInit`) via the transport bridge `uc_eval_dimcast_mul`. -/
theorem Shor_final_state_E2coset_eq_fullCircuit
    (m w rest cm N numWin : Nat)
    (TfamK TfamKinv : Nat → Nat → Nat → Nat)
    (hm : 0 < m) (hN : 0 < N) (h1N : 1 < N) (hcm : 0 < cm)
    (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    Shor_final_state_E2coset m w (cm + rest) N cm
        (physRunwayOracle m w (cm + rest) numWin TfamK TfamKinv)
      = FormalRV.SQIRPort.QState.cast (kronDim_eq m w (cm + rest))
          ((uc_eval (cosetFullCircuit m w rest cm N numWin TfamK TfamKinv hN h1N hbudget)
            * basis0 (m + cosetDim w (cm + rest))
            : Matrix (Fin (2 ^ (m + cosetDim w (cm + rest)))) (Fin 1) ℂ)) := by
  have hdim_pos : 0 < m + ((cm + rest) + cosetAnc w (cm + rest)) := by
    unfold cosetAnc; omega
  -- LHS: the success state IS uc_eval(composedQPE) · E2runwayRaw (up to dim_assoc_eq cast).
  rw [shor_final_state_E2coset_eq_uc_eval m w (cm + rest) N cm hdim_pos
        (physRunwayOracle m w (cm + rest) numWin TfamK TfamKinv)]
  -- RHS: unfold the full circuit and peel the seq.
  rw [cosetFullCircuit, uc_eval_seq_mul]
  -- Apply the dimension-transport bridge to the transported composed-QPE circuit.
  rw [uc_eval_dimcast_mul (congrArg (m + ·) (cosetWork_dim_eq w (cm + rest)))
        (composedQPECircuit m (cm + rest) (cosetAnc w (cm + rest))
          (physRunwayOracle m w (cm + rest) numWin TfamK TfamKinv))
        (uc_eval (E2runwayInitPrep m w rest cm N hN h1N hbudget (runwayDataH w rest cm))
          * basis0 (m + cosetDim w (cm + rest)))]
  -- Step 1: the inner-reindexed `uc_eval prep · basis0` IS the `E2runwayRaw` column.
  have hraw : colReindex (congrArg (m + ·) (cosetWork_dim_eq w (cm + rest))).symm
        (uc_eval (E2runwayInitPrep m w rest cm N hN h1N hbudget (runwayDataH w rest cm))
          * basis0 (m + cosetDim w (cm + rest)))
      = E2runwayRaw m w (cm + rest) N cm := by
    -- `uc_eval prep · basis0 = QState.cast (kronDim_eq).symm E2runwayInit`.
    have hprep : (uc_eval (E2runwayInitPrep m w rest cm N hN h1N hbudget (runwayDataH w rest cm))
          * basis0 (m + cosetDim w (cm + rest))
          : Matrix (Fin (2 ^ (m + cosetDim w (cm + rest)))) (Fin 1) ℂ)
        = FormalRV.SQIRPort.QState.cast (kronDim_eq m w (cm + rest)).symm
            (E2runwayInit m w (cm + rest) N cm) := by
      have h := uc_eval_E2runwayInitPrep m w rest cm N hm hN h1N hcm hbudget
      rw [← h, FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qstate_cast_cast]
    rw [hprep, colReindex_cast]
    -- E2runwayRaw = QState.cast (dim_assoc_eq).symm E2runwayInit (by def); reconcile casts.
    show FormalRV.SQIRPort.QState.cast _ (E2runwayInit m w (cm + rest) N cm)
      = FormalRV.SQIRPort.QState.cast (dim_assoc_eq m (cm + rest) (cosetAnc w (cm + rest))).symm
          (E2runwayInit m w (cm + rest) N cm)
    rfl
  rw [hraw]
  -- Step 2: fuse the outer `kronDim_eq` cast with the `colReindex` into a single cast; the
  -- composite Nat equality is `dim_assoc_eq` (defeq by proof irrelevance).
  rw [colReindex_eq_cast, qstate_cast_comp]

/-! ## (3) The G1-closing corollary. -/

/-- **★ (3) THE G1-CLOSING COROLLARY ★.**  The concrete coset/runway machine against the explicit
    physical oracle `physRunwayOracle` (with the table-value families), instantiated at
    `bits := cm + rest`, outputs a nontrivial FACTOR of `N` with probability
    `≥ κ/(log₂N)⁴ − 2m√(8·numWin/2^cm)`, the factor concretely exists, AND — the NEW content over
    `gidney_inplace_coset_factoring_succeeds` — the success state is now a GENUINE circuit on the
    all-zeros input `|0…0⟩`: `Shor_final_state_E2coset = uc_eval (cosetFullCircuit) · |0…0⟩`
    (the `_eq_fullCircuit` conjunct, via (2)).  The bound itself is exactly
    `gidney_inplace_coset_factoring_succeeds` at `bits := cm + rest`; the only added hypothesis is
    `hcm : 0 < cm` (needed for the state-prep circuit). -/
theorem gidney_inplace_coset_factoring_succeeds_circuit_prepared
    (a r N m w rest cm numWin ainv0 : Nat)
    (hm : 0 < m) (hw2 : 2 ≤ w) (hbits : numWin * w = cm + rest) (hb1 : 1 ≤ cm + rest)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ (cm + rest)) (hMN : 2 ^ cm * N ≤ 2 ^ (cm + rest))
    (h_inv0 : a * ainv0 % N = 1)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m (cm + rest))
    (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)])
    (hcm : 0 < cm) :
    factoringSuccessProb_E2coset a N m w (cm + rest) cm
        (physRunwayOracle m w (cm + rest) numWin
          (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
          (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm)
    ∧ (∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N)
    ∧ Shor_final_state_E2coset m w (cm + rest) N cm
        (physRunwayOracle m w (cm + rest) numWin
          (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
          (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w))
      = FormalRV.SQIRPort.QState.cast (kronDim_eq m w (cm + rest))
          ((uc_eval
              (cosetFullCircuit m w rest cm N numWin
                (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
                (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w)
                (lt_trans Nat.zero_lt_one hN1) hN1 hMN)
            * basis0 (m + cosetDim w (cm + rest))
            : Matrix (Fin (2 ^ (m + cosetDim w (cm + rest)))) (Fin 1) ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (gidney_inplace_coset_factoring_succeeds a r N m w (cm + rest) numWin cm ainv0
      hm hw2 hbits hb1 hN1 hN2 hMN h_inv0 h_basic hr_even hgood).1
  · exact (gidney_inplace_coset_factoring_succeeds a r N m w (cm + rest) numWin cm ainv0
      hm hw2 hbits hb1 hN1 hN2 hMN h_inv0 h_basic hr_even hgood).2
  · exact Shor_final_state_E2coset_eq_fullCircuit m w rest cm N numWin
      (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
      (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w)
      hm (lt_trans Nat.zero_lt_one hN1) hN1 hcm hMN

-- Kernel-cleanliness checks (axioms ⊆ {propext, Classical.choice, Quot.sound};
-- no `sorry`, no `native_decide`).
#print axioms Shor_final_state_E2coset_eq_fullCircuit
#print axioms gidney_inplace_coset_factoring_succeeds_circuit_prepared

end FormalRV.Audit.GidneyEkera2021.CosetFactoringCircuitPrepared
