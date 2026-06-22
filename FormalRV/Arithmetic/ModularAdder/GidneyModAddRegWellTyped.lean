/-
  FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped — `EGate.WellTypedAt` for the measured
  Gidney modular adder keystone and its sub-components.

  The repo only ever proved `EGate.boundedBy` for the measured-adder family; `boundedBy` omits the
  CX/CCX index DISTINCTNESS conjuncts, so it does NOT imply `WellTypedAt`.  These lemmas prove
  `WellTypedAt` fresh (distinctness of the 3-per-bit `read/target/carry` indices is omega-provable),
  which the EGate→reversible bridge (`MeasuredEqualsReversibleOnEncoded.eg_wellTyped`) consumes.

  Also introduces `EGate.WellTypedAt.mono` (missing in the repo; mirrors `EGate.boundedBy_mono`).

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.ModularAdder.GidneyModAddReg
import FormalRV.Shor.EGateToUnitaryBridge

namespace FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Arithmetic.MeasuredAdder

/-! ## `EGate.WellTypedAt` monotonicity (new; mirrors `EGate.boundedBy_mono`). -/
theorem EGate.WellTypedAt.mono {dim dim' : Nat} (h_le : dim ≤ dim') :
    ∀ (eg : EGate), EGate.WellTypedAt dim eg → EGate.WellTypedAt dim' eg := by
  intro eg
  induction eg with
  | base g => intro hb; exact Gate.WellTyped.mono hb h_le
  | mz q => intro hq; exact Nat.lt_of_lt_of_le hq h_le
  | seq a b iha ihb => intro hb; exact ⟨iha hb.1, ihb hb.2⟩

/-! ## Per-step (forward sweep). -/
theorem first_step_wt : Gate.WellTyped 5 gidney_adder_bit_step_faithful_first := by
  unfold gidney_adder_bit_step_faithful_first
  simp only [Gate.WellTyped, read_idx, target_idx, carry_idx]
  repeat' apply And.intro
  all_goals omega

theorem interior_step_wt (i : Nat) (hi : 0 < i) :
    Gate.WellTyped (3 * i + 5) (gidney_adder_bit_step_faithful_interior i) := by
  unfold gidney_adder_bit_step_faithful_interior
  simp only [Gate.WellTyped, read_idx, target_idx, carry_idx]
  repeat' apply And.intro
  all_goals omega

theorem last_step_wt (i : Nat) (hi : 0 < i) :
    Gate.WellTyped (3 * i + 3) (gidney_adder_bit_step_faithful_last i) := by
  unfold gidney_adder_bit_step_faithful_last
  simp only [Gate.WellTyped, read_idx, target_idx, carry_idx]
  repeat' apply And.intro
  all_goals omega

theorem forward_with_propagation_wt :
    ∀ k, 0 < k → Gate.WellTyped (3 * k + 2) (gidney_adder_forward_with_propagation k)
  | 0 => by intro h; omega
  | 1 => by intro _; exact Gate.WellTyped.mono first_step_wt (by omega)
  | n + 2 => by
      intro _
      show Gate.WellTyped (3 * (n + 2) + 2)
        (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
                  (gidney_adder_bit_step_faithful_interior (n + 1)))
      refine ⟨Gate.WellTyped.mono (forward_with_propagation_wt (n + 1) (by omega)) (by omega),
              Gate.WellTyped.mono (interior_step_wt (n + 1) (by omega)) (by omega)⟩

theorem gidney_adder_forward_faithful_full_wt (n : Nat) :
    Gate.WellTyped (adder_n_qubits (n + 2)) (gidney_adder_forward_faithful_full (n + 2)) := by
  show Gate.WellTyped (adder_n_qubits (n + 2))
    (Gate.seq (gidney_adder_forward_with_propagation (n + 1))
              (gidney_adder_bit_step_faithful_last (n + 1)))
  unfold adder_n_qubits
  refine ⟨Gate.WellTyped.mono (forward_with_propagation_wt (n + 1) (by omega)) (by omega),
          Gate.WellTyped.mono (last_step_wt (n + 1) (by omega)) (by omega)⟩

theorem final_cx_cascade_wt :
    ∀ k, 0 < k → Gate.WellTyped (3 * k) (gidney_final_cx_cascade k)
  | 0 => by intro h; omega
  | 1 => by
      intro _
      show Gate.WellTyped (3 * 1)
        (Gate.seq (gidney_final_cx_cascade 0) (Gate.CX (read_idx 0) (target_idx 0)))
      refine ⟨?_, ?_⟩
      · show (0:Nat) < 3; omega
      · simp only [Gate.WellTyped, read_idx, target_idx]; refine ⟨?_,?_,?_⟩ <;> omega
  | k + 2 => by
      intro _
      show Gate.WellTyped (3 * (k + 2))
        (Gate.seq (gidney_final_cx_cascade (k + 1)) (Gate.CX (read_idx (k + 1)) (target_idx (k + 1))))
      refine ⟨Gate.WellTyped.mono (final_cx_cascade_wt (k + 1) (by omega)) (by omega), ?_⟩
      simp only [Gate.WellTyped, read_idx, target_idx]
      refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## Measured reverse. -/
theorem measFirstReverse_wt : EGate.WellTypedAt 5 gidneyMeasFirstReverse := by
  unfold gidneyMeasFirstReverse
  simp only [EGate.WellTypedAt, Gate.WellTyped, read_idx, target_idx, carry_idx]
  repeat' apply And.intro
  all_goals omega

theorem measInteriorReverse_wt (i : Nat) (hi : 0 < i) :
    EGate.WellTypedAt (3 * i + 5) (gidneyMeasInteriorReverse i) := by
  unfold gidneyMeasInteriorReverse
  simp only [EGate.WellTypedAt, Gate.WellTyped, read_idx, target_idx, carry_idx]
  repeat' apply And.intro
  all_goals omega

theorem measLastReverse_wt (i : Nat) (hi : 0 < i) :
    EGate.WellTypedAt (3 * i + 3) (gidneyMeasLastReverse i) := by
  unfold gidneyMeasLastReverse
  simp only [EGate.WellTypedAt, Gate.WellTyped, carry_idx]
  repeat' apply And.intro
  all_goals omega

theorem measPropReverse_wt :
    ∀ K, 0 < K → EGate.WellTypedAt (3 * K + 2) (gidneyMeasPropReverse K)
  | 0 => by intro h; omega
  | 1 => by intro _; exact EGate.WellTypedAt.mono (by omega) _ measFirstReverse_wt
  | n + 2 => by
      intro _
      show EGate.WellTypedAt (3 * (n + 2) + 2)
        (EGate.seq (gidneyMeasInteriorReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
      exact ⟨EGate.WellTypedAt.mono (by omega) _ (measInteriorReverse_wt (n + 1) (by omega)),
             EGate.WellTypedAt.mono (by omega) _ (measPropReverse_wt (n + 1) (by omega))⟩

theorem measFullReverse_wt (n : Nat) :
    EGate.WellTypedAt (adder_n_qubits (n + 2)) (gidneyMeasFullReverse (n + 2)) := by
  show EGate.WellTypedAt (adder_n_qubits (n + 2))
    (EGate.seq (gidneyMeasLastReverse (n + 1)) (gidneyMeasPropReverse (n + 1)))
  unfold adder_n_qubits
  exact ⟨EGate.WellTypedAt.mono (by omega) _ (measLastReverse_wt (n + 1) (by omega)),
         EGate.WellTypedAt.mono (by omega) _ (measPropReverse_wt (n + 1) (by omega))⟩

/-! ## The measured adder. -/
theorem gidneyAdderMeasured_wellTypedAt (n q_start dim : Nat)
    (hdim : adder_n_qubits (n + 2) ≤ dim) :
    EGate.WellTypedAt dim (gidneyAdderMeasured (n + 2) q_start) := by
  show EGate.WellTypedAt dim
    (EGate.seq
      (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (n + 2))
                            (gidney_final_cx_cascade (n + 2))))
      (gidneyMeasFullReverse (n + 2)))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Gate.WellTyped.mono (gidney_adder_forward_faithful_full_wt n) hdim
  · refine Gate.WellTyped.mono (final_cx_cascade_wt (n + 2) (by omega)) ?_
    unfold adder_n_qubits at hdim; omega
  · exact EGate.WellTypedAt.mono hdim _ (measFullReverse_wt n)

/-! ## Sub-component WellTyped. -/
open FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup

theorem loadConst_wellTyped (B : Nat) (hB : 0 < B) :
    ∀ (W d : Nat), (∀ k, k < W → read_idx k < B) → Gate.WellTyped B (loadConst W d)
  | 0, _, _ => by show 0 < B; exact hB
  | W + 1, d, h => by
      show Gate.WellTyped B (Gate.seq (loadConst W d)
        (if d.testBit W then Gate.X (read_idx W) else Gate.I))
      refine ⟨loadConst_wellTyped B hB W d (fun k hk => h k (by omega)), ?_⟩
      by_cases hpw : d.testBit W
      · simp only [hpw, if_true]; exact h W (by omega)
      · simp only [hpw, Bool.false_eq_true, if_false]; exact hB

theorem prepareMaskedP_wellTyped (flagIdx B : Nat) (hflag : flagIdx < B) :
    ∀ (W p : Nat), (∀ k, k < W → read_idx k < B) → (∀ k, k < W → flagIdx ≠ read_idx k) →
      Gate.WellTyped B (prepareMaskedP flagIdx W p)
  | 0, _, _, _ => by show 0 < B; omega
  | W + 1, p, h, hne => by
      show Gate.WellTyped B (Gate.seq (prepareMaskedP flagIdx W p)
        (if p.testBit W then Gate.CX flagIdx (read_idx W) else Gate.I))
      refine ⟨prepareMaskedP_wellTyped flagIdx B hflag W p (fun k hk => h k (by omega))
                (fun k hk => hne k (by omega)), ?_⟩
      by_cases hpw : p.testBit W
      · simp only [hpw, if_true]; exact ⟨hflag, h W (by omega), hne W (by omega)⟩
      · simp only [hpw, Bool.false_eq_true, if_false]; show 0 < B; omega

theorem mzList_wellTypedAt (B : Nat) (hB : 0 < B) :
    ∀ (L : List Nat), (∀ x ∈ L, x < B) → EGate.WellTypedAt B (mzList L)
  | [], _ => by show 0 < B; exact hB
  | q :: qs, h => by
      show EGate.WellTypedAt B (EGate.seq (mzList qs) (EGate.mz q))
      exact ⟨mzList_wellTypedAt B hB qs (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))),
             h q (List.mem_cons.mpr (Or.inl rfl))⟩

theorem addConstMeasured_wellTypedAt (n d dim : Nat)
    (hdim : adder_n_qubits (n + 2) ≤ dim) :
    EGate.WellTypedAt dim (addConstMeasured (n + 2) d) := by
  show EGate.WellTypedAt dim
    (EGate.seq
      (EGate.seq (EGate.base (loadConst (n + 2) d)) (gidneyAdderMeasured (n + 2) 0))
      (EGate.base (loadConst (n + 2) d)))
  have hread : ∀ k, k < n + 2 → read_idx k < dim := by
    intro k hk; simp only [read_idx, adder_n_qubits] at *; omega
  have hL : Gate.WellTyped dim (loadConst (n + 2) d) :=
    loadConst_wellTyped dim (by unfold adder_n_qubits at hdim; omega) (n + 2) d hread
  exact ⟨⟨hL, gidneyAdderMeasured_wellTypedAt n 0 dim hdim⟩, hL⟩

theorem conditionalAddP_wellTypedAt (n flagIdx p dim : Nat)
    (hflag : flagIdx < dim) (hdim : adder_n_qubits (n + 2) ≤ dim)
    (hne : ∀ k, k < n + 2 → flagIdx ≠ read_idx k) :
    EGate.WellTypedAt dim (conditionalAddP (n + 2) flagIdx p) := by
  show EGate.WellTypedAt dim
    (EGate.seq
      (EGate.seq (EGate.base (prepareMaskedP flagIdx (n + 2) p)) (gidneyAdderMeasured (n + 2) 0))
      (EGate.base (prepareMaskedP flagIdx (n + 2) p)))
  have hread : ∀ k, k < n + 2 → read_idx k < dim := by
    intro k hk; simp only [read_idx, adder_n_qubits] at *; omega
  have hP : Gate.WellTyped dim (prepareMaskedP flagIdx (n + 2) p) :=
    prepareMaskedP_wellTyped flagIdx dim hflag (n + 2) p hread hne
  exact ⟨⟨hP, gidneyAdderMeasured_wellTypedAt n 0 dim hdim⟩, hP⟩

/-! ## THE keystone WellTyped. -/
open FormalRV.Arithmetic.ModularAdder.GidneyModAddReg

theorem gidneyModAddRegMeasured_wellTypedAt (n p dim : Nat)
    (hdim : adder_n_qubits (n + 2) + 1 ≤ dim) :
    EGate.WellTypedAt dim (gidneyModAddRegMeasured (n + 1) p) := by
  have hflag : adder_n_qubits (n + 2) < dim := by omega
  have hadd : adder_n_qubits (n + 2) ≤ dim := by omega
  have hne : ∀ k, k < n + 2 → adder_n_qubits (n + 2) ≠ read_idx k := by
    intro k hk; simp only [read_idx, adder_n_qubits] at *; omega
  show EGate.WellTypedAt dim (EGate.seq
    (EGate.seq
      (EGate.seq (gidneyAdderMeasured (n + 2) 0) (mzList ((List.range (n + 2)).map read_idx)))
      (EGate.base (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2)))))
    (EGate.seq (conditionalAddP (n + 2) (adder_n_qubits (n + 2)) p)
      (EGate.mz (adder_n_qubits (n + 2)))))
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · exact gidneyAdderMeasured_wellTypedAt n 0 dim hadd
  · refine mzList_wellTypedAt dim (by omega) _ ?_
    intro x hx
    obtain ⟨i, hir, rfl⟩ := List.mem_map.mp hx
    have : i < n + 2 := List.mem_range.mp hir
    simp only [read_idx, adder_n_qubits] at *; omega
  · show Gate.WellTyped dim (Gate.CX (target_idx (n + 1)) (adder_n_qubits (n + 2)))
    refine ⟨?_, hflag, ?_⟩
    · simp only [target_idx, adder_n_qubits] at *; omega
    · simp only [target_idx, adder_n_qubits] at *; omega
  · exact conditionalAddP_wellTypedAt n (adder_n_qubits (n + 2)) p dim hflag hadd hne
  · exact hflag

end FormalRV.Arithmetic.ModularAdder.GidneyModAddRegWellTyped
