/-
  FormalRV.Audit.GidneyEkera2021.CosetFactoringSucceeds — the coset/runway machine FACTORS,
  on the concrete physical oracle, as ONE composed circuit. (Audit of arXiv:1905.09749.)
  ════════════════════════════════════════════════════════════════════════════

  Carries the (kernel-clean, fully-unconditional) coset/runway ORDER-FINDING bound
  (`E2RunwayShorFinal.gidney_inplace_coset_shor_succeeds_fully_unconditional`) through to a
  FACTORING theorem on the concrete coset machine `physRunwayOracle`, and identifies the
  success state with a single real syntactic circuit.

  (A) COMPOSED-CIRCUIT IDENTITY (`shor_final_state_E2coset_eq_uc_eval`): `Shor_final_state_E2coset`
      IS `uc_eval` of ONE real `BaseUCom` — the H-free composed QPE circuit `composedQPECircuit`
      (`controlled_powers (qpeOracle …) m ; QFTinv m`) — applied to the `E2runwayInit` column.
  (B) FACTORING ≥ ORDER-FINDING (`factoringSuccessProb_E2coset_ge`): the generic per-outcome
      `r_found ≤ factorIndicator` bound, summed over the coset measurement state.
  (C) THE COSET FACTORING THEOREM (`gidney_inplace_coset_factoring_succeeds`): the concrete
      physical coset machine outputs a nontrivial FACTOR of `N` with probability
      `≥ κ/(log₂N)⁴ − 2·m·√(8·numWin/2^cm)`, and the factor concretely exists.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.

  HONEST SCOPE (what this does NOT yet do): the input `E2runwayInit` is a hand-defined coset-window
  column, not yet shown equal to a state-prep circuit on |0…0⟩ (gap 3); and the success bound rides
  the exact reversible oracle, not GE2021's measured count-optimal `modExpAt` gate (gap 4 — the
  `ModExpAtEncodedMatchesResidue` instance).
-/
import FormalRV.Shor.GidneyInPlace
import FormalRV.NumberTheory.ShorFactoringEndToEnd

namespace FormalRV.Audit.GidneyEkera2021.CosetFactoring

open scoped BigOperators
open FormalRV.SQIRPort
open FormalRV.NumberTheory.ShorFactoring (factorIndicator factorWitnessed
  factorWitnessed_yields_factor r_found_le_factorIndicator pow_modEq_one_int pow_ne_one_int)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess
  (E2runwayInit Shor_final_state_E2coset probability_of_success_E2coset)
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp
  (qpeStageMap qpeStageMap_cast qstate_cast_cast stageProd qpeRaw shorInitM
   stageProd_eq_controlled_powers)
open FormalRV.Shor.GidneyInPlace.OrbitState (orbitState)
open FormalRV.SQIRPort (dim_assoc_eq)

/-! ## (A) The composed-circuit identity. -/

/-- **General telescoping over an arbitrary init.**  Mirrors `orbitState_eq_stageProd`, but
    parametrised by ANY init that is the outer cast of a raw column `raw`.  Folding `j` stages
    of `qpeStageMap` equals a single outer cast of `stageProd j * raw`. -/
theorem orbitState_eq_stageProd_of_cast
    (m n anc : Nat) (f : Nat → BaseUCom (n + anc))
    (raw : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ) :
    ∀ j, orbitState (qpeStageMap m n anc f)
            (QState.cast (dim_assoc_eq m n anc) raw) j
        = QState.cast (dim_assoc_eq m n anc)
            ((stageProd m n anc f j * raw
              : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)) := by
  intro j
  induction j with
  | zero =>
      show QState.cast (dim_assoc_eq m n anc) raw = _
      congr 1
      show raw
          = ((1 : FormalRV.Framework.Square (m + (n + anc))) * raw
              : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)
      rw [Matrix.one_mul]
  | succ j ih =>
      show qpeStageMap m n anc f j
            (orbitState (qpeStageMap m n anc f)
              (QState.cast (dim_assoc_eq m n anc) raw) j) = _
      rw [ih, qpeStageMap_cast m n anc f j]
      congr 1
      show (FormalRV.Framework.uc_eval
              (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom m n anc f j)
            * (stageProd m n anc f j * raw)
              : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)
          = ((FormalRV.Framework.uc_eval
              (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom m n anc f j)
              * stageProd m n anc f j)
              * raw
              : Matrix (Fin (2 ^ (m + (n + anc)))) (Fin 1) ℂ)
      rw [Matrix.mul_assoc]

/-- **The H-free composed QPE circuit** as ONE real `BaseUCom`: the `m` controlled-oracle stages
    (`controlled_powers (qpeOracle …) m`) followed by the inverse QFT (`QFTinv m`).  In this
    convention the column of Hadamards is folded into the init (here `E2runwayInit`), so the
    *circuit* is exactly these two pieces — equivalently `QPE_var_lsb` with its leading `npar_H`
    removed. -/
noncomputable def composedQPECircuit (m n anc : Nat) (f : Nat → BaseUCom (n + anc)) :
    FormalRV.Framework.BaseUCom (m + (n + anc)) :=
  FormalRV.Framework.UCom.seq
    (FormalRV.Framework.BaseUCom.controlled_powers
      (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeOracle m n anc f) m)
    (FormalRV.Framework.BaseUCom.QFTinv m)

/-- **`stageProd (m+1)` IS `uc_eval` of the single composed circuit.**  `stageProd m n anc f (m+1)`
    equals `Framework.uc_eval (composedQPECircuit m n anc f)` — ONE real `BaseUCom`, the H-free QPE
    circuit (the same QFTinv-last / `controlled_powers` structure `shor_final_eq_orbitState` and
    `orbitState_eq_stageProd` expose).  Proof: peel the QFTinv-last stage, match the first `m`
    oracle stages to `controlled_powers`, recognise the product as `uc_eval (seq …)`. -/
theorem stageProd_succ_eq_uc_eval (m n anc : Nat) (f : Nat → BaseUCom (n + anc))
    (hdim_pos : 0 < m + (n + anc)) :
    stageProd m n anc f (m + 1)
      = FormalRV.Framework.uc_eval (composedQPECircuit m n anc f) := by
  -- Peel the last (QFTinv) stage and match the first `m` to `controlled_powers`.
  have hstage_last :
      FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom m n anc f m
        = FormalRV.Framework.BaseUCom.QFTinv m := by
    unfold FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom
    rw [if_neg (Nat.lt_irrefl m)]
  have hstageProd : stageProd m n anc f (m + 1)
      = FormalRV.Framework.uc_eval (FormalRV.Framework.BaseUCom.QFTinv m)
          * FormalRV.Framework.uc_eval
              (FormalRV.Framework.BaseUCom.controlled_powers
                (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeOracle m n anc f) m) := by
    show FormalRV.Framework.uc_eval
          (FormalRV.Shor.GidneyInPlace.QPEStageDecomp.qpeStageUCom m n anc f m)
          * stageProd m n anc f m = _
    rw [hstage_last,
        stageProd_eq_controlled_powers m n anc f hdim_pos m (Nat.le_refl m)]
  rw [hstageProd]
  -- `uc_eval (seq c₁ c₂) = uc_eval c₂ * uc_eval c₁`, so the product IS `uc_eval composedQPECircuit`.
  rfl

/-- **The `E2runwayInit` column in the unitary-acting dimension** `2^(m+(bits+anc))` — the inner
    cast of `E2runwayInit`, typed as a bare `Matrix` so matrix products resolve directly.  This is
    the column the composed QPE circuit acts on. -/
noncomputable def E2runwayRaw (m w bits N cm : Nat) :
    Matrix (Fin (2 ^ (m + (bits + cosetAnc w bits)))) (Fin 1) ℂ :=
  QState.cast (dim_assoc_eq m bits (cosetAnc w bits)).symm (E2runwayInit m w bits N cm)

/-- **★ (A) COMPOSED-CIRCUIT IDENTITY ★.**  The coset success state `Shor_final_state_E2coset`
    IS `uc_eval` of ONE real `BaseUCom` — the composed QPE circuit `composedQPECircuit`
    (the H-free `controlled_powers`-then-`QFTinv` circuit, with H folded into the init) — applied
    to the `E2runwayRaw` column (the `E2runwayInit` column inner-cast into the unitary-acting
    dimension).  Reuses the general telescoping lemma + `stageProd_succ_eq_uc_eval`. -/
theorem shor_final_state_E2coset_eq_uc_eval
    (m w bits N cm : Nat) (hdim_pos : 0 < m + (bits + cosetAnc w bits))
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits)) :
    Shor_final_state_E2coset m w bits N cm f
      = QState.cast (dim_assoc_eq m bits (cosetAnc w bits))
          ((FormalRV.Framework.uc_eval (composedQPECircuit m bits (cosetAnc w bits) f)
            * E2runwayRaw m w bits N cm
            : Matrix (Fin (2 ^ (m + (bits + cosetAnc w bits)))) (Fin 1) ℂ)) := by
  -- Write E2runwayInit as the outer cast of its own inner-cast (round-trip), then telescope.
  have hcast : E2runwayInit m w bits N cm
      = QState.cast (dim_assoc_eq m bits (cosetAnc w bits)) (E2runwayRaw m w bits N cm) := by
    -- `cast h (cast h.symm x) = x` via `qstate_cast_cast` applied with `h := (…).symm`.
    have := qstate_cast_cast (dim_assoc_eq m bits (cosetAnc w bits)).symm
      (E2runwayInit m w bits N cm)
    -- `this : cast (h.symm).symm (cast h.symm x) = x`, and `(h.symm).symm = h`.
    simpa [E2runwayRaw] using this.symm
  -- Unfold the coset final state to the orbit, rewrite the init, telescope.
  show orbitState (qpeStageMap m bits (cosetAnc w bits) f)
        (E2runwayInit m w bits N cm) (m + 1) = _
  rw [hcast,
      orbitState_eq_stageProd_of_cast m bits (cosetAnc w bits) f
        (E2runwayRaw m w bits N cm) (m + 1),
      stageProd_succ_eq_uc_eval m bits (cosetAnc w bits) f hdim_pos]

/-! ## (B) The factoring-success probability on the coset machine. -/

open Classical in
/-- **The coset/runway factoring-success probability** — verbatim analogue of
    `factoringSuccessProb` over the two-register `Shor_final_state_E2coset`. -/
noncomputable def factoringSuccessProb_E2coset (a N m w bits cm : Nat)
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits)) : ℝ :=
  ∑ x ∈ Finset.range (2 ^ m),
    factorIndicator a N (OF_post a N x m) *
      prob_partial_meas (basis_vector (2 ^ m) x) (Shor_final_state_E2coset m w bits N cm f)

/-- **★ (B) FACTORING ≥ ORDER-FINDING on the coset machine ★.**  Generic per-outcome bound
    (`r_found_le_factorIndicator`, oracle-independent) summed with `prob_partial_meas_nonneg` and
    `Finset.sum_le_sum` — mirrors the vanilla proof verbatim over the coset state. -/
theorem factoringSuccessProb_E2coset_ge
    {a r N m w bits cm : Nat}
    (f : Nat → FormalRV.Framework.BaseUCom (bits + cosetAnc w bits))
    (hN : 1 < N) (h_ord : Order a r N) (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    factoringSuccessProb_E2coset a N m w bits cm f
      ≥ probability_of_success_E2coset a r N m w bits cm f := by
  unfold probability_of_success_E2coset factoringSuccessProb_E2coset
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_right
    (r_found_le_factorIndicator hN h_ord hr_even hgood x m)
    (prob_partial_meas_nonneg _ _)

/-! ## (C) The coset factoring theorem. -/

open FormalRV.SQIRPort (revIndex BasicSetting κ)
open FormalRV.Shor.WindowedArith (tableValue)
open FormalRV.Shor.GidneyInPlace.E2PhysicalRealization (physRunwayOracle)

/-- **★ (C) THE COSET FACTORING THEOREM ★.**  Combining (B) with the fully-unconditional
    order-finding capstone: the concrete coset/runway machine against the EXPLICIT physical
    oracle `physRunwayOracle` outputs a nontrivial FACTOR of `N` with probability
    `≥ κ/(log₂N)⁴ − 2m√(8·numWin/2^cm)`, and the factor concretely exists. -/
theorem gidney_inplace_coset_factoring_succeeds
    (a r N m w bits numWin cm ainv0 : Nat)
    (hm : 0 < m) (hw2 : 2 ≤ w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hMN : 2 ^ cm * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (hr_even : Even r)
    (hgood : ¬ (a : ℤ) ^ (r / 2) ≡ -1 [ZMOD (N : ℤ)]) :
    factoringSuccessProb_E2coset a N m w bits cm
        (physRunwayOracle m w bits numWin
          (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
          (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w))
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
          - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm)
    ∧ ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  -- `Order a r N` from `BasicSetting`.
  have h_ord : Order a r N := h_basic.2.1
  obtain ⟨hr_pos, h_arN, h_min⟩ := h_ord
  refine ⟨?_, ?_⟩
  · -- factoring ≥ order-finding ≥ κ/(log₂N)⁴ − dev.
    have hof :
        probability_of_success_E2coset a r N m w bits cm
            (physRunwayOracle m w bits numWin
              (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
              (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w))
          ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
              - 2 * (m : ℝ) * Real.sqrt (8 * (numWin : ℝ) / 2 ^ cm) :=
      FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorFinal.gidney_inplace_coset_shor_succeeds_fully_unconditional
        a r N m w bits numWin cm ainv0 hm hw2 hbits hb1 hN1 hN2 hMN h_inv0 h_basic
    have hge :
        factoringSuccessProb_E2coset a N m w bits cm
            (physRunwayOracle m w bits numWin
              (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
              (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w))
          ≥ probability_of_success_E2coset a r N m w bits cm
            (physRunwayOracle m w bits numWin
              (fun k => tableValue (a ^ (2 ^ (revIndex m k)) % N) N w)
              (fun k => tableValue (ainv0 ^ (2 ^ (revIndex m k)) % N) N w)) :=
      factoringSuccessProb_E2coset_ge _ hN1 ⟨hr_pos, h_arN, h_min⟩ hr_even hgood
    linarith
  · exact factorWitnessed_yields_factor hN1
      ⟨hr_even, hr_pos, pow_modEq_one_int hN1 h_arN, pow_ne_one_int hN1 h_min, hgood⟩

end FormalRV.Audit.GidneyEkera2021.CosetFactoring
