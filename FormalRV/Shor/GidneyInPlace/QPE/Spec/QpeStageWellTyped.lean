/-
  FormalRV.Shor.GidneyInPlace.QpeStageWellTyped — hU part 2 (well-typedness) + combine.
  ════════════════════════════════════════════════════════════════════════════

  The QPE stage circuit `qpeStageUCom m n anc f k` is well-typed (every gate index in range,
  pairwise distinct where required), hence — via `UComUnitary.uc_eval_unitary_of_wellTyped` —
  its `uc_eval` is unitary, hence — via `PmDistTelescope.qpeStageMap_pmDist_isom` — the stage map
  is a `pmDist` isometry.  That last fact is EXACTLY the `hisom` hypothesis carried by the
  coset-Shor H4/H5 deviation bounds, so this file DISCHARGES `hisom` outright: `qpeStage_physical_isom`
  carries only `0 < m` and the oracle-family well-typedness `hwt` (= the `hwtP` H4/H5 already hold).

  Plumbing (mostly reusing existing QPE/Core lemmas):
    • `controlled_R_well_typed` — the `app1 R` branch of `control` (5-gate `controlled_R`);
    • `control_well_typed` — `control q c` is well-typed when `c` is and `q` is FRESH in `c`
      (the control qubit distinct from every target — exactly `is_fresh`);
    • `qpeStageUCom_well_typed` — oracle stages (`k < m`) via `control_well_typed` on the
      `+m`-shifted oracle (`wellTyped_map_qubits_shift` + `is_fresh_map_qubits_shift`, so the
      control qubit `k < m` is below all data-register qubits `≥ m`); the QFTinv stage
      (`k ≥ m`) via `QFTinv_well_typed_of_layer_well_typed`.
    • `qpeStage_physical_isom` — the combine = the `hisom` shape.

  The QFTinv stage lives on the FULL register `m+(n+anc)`, but `wellTyped_real_QFTinv_layer` only
  types the layer at dim `= m`.  We lift it via the existing polymorphic-lift bridge
  (`real_QFTinv_layer_map_id_bridge`: the dim-`(m+anc)` layer = `map_qubits id` of the dim-`m` one)
  plus the `map_qubits id` rebase `wellTyped_map_qubits_id` (the `UCom.WellTyped` dim-monotonicity
  the framework lacked) — so `hQFT` is DISCHARGED, not carried.

  Kernel-clean: no `sorry`, no `native_decide`, axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Core.UComUnitary
import FormalRV.Shor.GidneyInPlace.Deviation.Engine.PmDistTelescope
import FormalRV.QPE.PhaseKickback
import FormalRV.QFT.IQFTRecursiveArbitrary

namespace FormalRV.Shor.GidneyInPlace.QpeStageWellTyped

open FormalRV.Framework
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.QPEStageDecomp (qpeStageUCom qpeOracle qpeStageMap)
open FormalRV.Shor.Approx (pmDist qpeStageMap_pmDist_isom)

/-! ## §1. `controlled_R` is well-typed. -/

/-- The `controlled_R q t θ φ λ` decomposition (`Rz q ; Rz t ; CNOT q t ; R t ; CNOT q t ; R t`)
    is well-typed when `q ≠ t` and both are in range. -/
theorem controlled_R_well_typed {dim : Nat} (q t : Nat) (θ φ lam : ℝ)
    (hq : q < dim) (ht : t < dim) (hqt : q ≠ t) :
    UCom.WellTyped dim (BaseUCom.controlled_R q t θ φ lam) := by
  unfold BaseUCom.controlled_R
  refine UCom.WellTyped.seq (BaseUCom.Rz_well_typed _ q hq) ?_
  refine UCom.WellTyped.seq (BaseUCom.Rz_well_typed _ t ht) ?_
  refine UCom.WellTyped.seq (BaseUCom.CNOT_well_typed _ _ hq ht hqt) ?_
  refine UCom.WellTyped.seq (UCom.WellTyped.app1 ht) ?_
  refine UCom.WellTyped.seq (BaseUCom.CNOT_well_typed _ _ hq ht hqt) ?_
  exact UCom.WellTyped.app1 ht

/-! ## §2. `control` preserves well-typedness for a fresh control qubit. -/

/-- **`control q c` is well-typed** when `c` is well-typed and `q` is FRESH in `c` (`is_fresh q c`
    — `q` differs from every gate qubit of `c`) and `q < dim`.  Induction over `c`: `seq`
    distributes; `app1 (R …)` → `controlled_R_well_typed` (`q ≠ t` from `is_fresh`); `app2 CNOT`
    → `CCX_well_typed` (`q ≠ a`, `q ≠ b` from `is_fresh`, `a ≠ b` from `c`'s well-typedness);
    `app3` vacuous (`BaseUnitary 3` empty). -/
theorem control_well_typed {dim : Nat} (q : Nat) (c : FormalRV.Framework.BaseUCom dim)
    (hq : q < dim) :
    BaseUCom.is_fresh q c → UCom.WellTyped dim c → UCom.WellTyped dim (BaseUCom.control q c) := by
  induction c with
  | seq c1 c2 ih1 ih2 =>
    intro hfresh hwt
    obtain ⟨hf1, hf2⟩ := hfresh
    cases hwt with
    | seq h1 h2 => exact UCom.WellTyped.seq (ih1 hf1 h1) (ih2 hf2 h2)
  | app1 u t =>
    intro hfresh hwt
    cases u with
    | R θ φ lam =>
      cases hwt with
      | app1 ht => exact controlled_R_well_typed q t θ φ lam hq ht hfresh
  | app2 u a b =>
    intro hfresh hwt
    cases u with
    | CNOT =>
      cases hwt with
      | app2 ha hb hab =>
        obtain ⟨hqa, hqb⟩ := hfresh
        exact BaseUCom.CCX_well_typed q a b hq ha hb hqa hqb hab
  | app3 u a b c => intro _ _; nomatch u

/-! ## §3. `map_qubits id` lifts well-typedness to a larger register dim. -/

/-- **`map_qubits id` dim-rebase.**  Relabelling every qubit by the identity preserves the gate
    indices, so a circuit well-typed on `dim` qubits is well-typed on any `dim' ≥ dim` after the
    (structure-preserving) `map_qubits id` lift.  This is the `UCom.WellTyped` monotonicity the
    framework lacks (a fixed `c : BaseUCom dim` cannot retype to `BaseUCom dim'`, so the lift must
    go through `map_qubits id`). -/
theorem wellTyped_map_qubits_id {dim dim' : Nat} (hle : dim ≤ dim')
    (c : FormalRV.Framework.BaseUCom dim) :
    UCom.WellTyped dim c → UCom.WellTyped dim' (map_qubits id c) := by
  induction c with
  | seq c1 c2 ih1 ih2 =>
    intro h; cases h with | seq h1 h2 => exact UCom.WellTyped.seq (ih1 h1) (ih2 h2)
  | app1 u n =>
    intro h; cases h with | app1 hn => exact UCom.WellTyped.app1 (Nat.lt_of_lt_of_le hn hle)
  | app2 u a b =>
    intro h
    cases h with
    | app2 ha hb hab =>
      exact UCom.WellTyped.app2 (Nat.lt_of_lt_of_le ha hle) (Nat.lt_of_lt_of_le hb hle) hab
  | app3 u a b c =>
    intro h
    cases h with
    | app3 ha hb hc hab hbc hac =>
      exact UCom.WellTyped.app3 (Nat.lt_of_lt_of_le ha hle) (Nat.lt_of_lt_of_le hb hle)
        (Nat.lt_of_lt_of_le hc hle) hab hbc hac

/-! ## §4. Every QPE stage is well-typed. -/

/-- **The QPE stage circuit is well-typed.**  Oracle stages (`k < m`): `control k` of the
    `+m`-shifted oracle — well-typed by `control_well_typed` since `k < m ≤` every shifted data
    qubit (`is_fresh_map_qubits_shift`) and the shifted oracle is well-typed
    (`wellTyped_map_qubits_shift`).  QFTinv stage (`k ≥ m`): `QFTinv_well_typed_of_layer_well_typed`
    fed by `hQFT`. -/
theorem qpeStageUCom_well_typed (m n anc : Nat) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt : ∀ j, UCom.WellTyped (n + anc) (f j)) (k : Nat) :
    UCom.WellTyped (m + (n + anc)) (qpeStageUCom m n anc f k) := by
  unfold qpeStageUCom
  by_cases hk : k < m
  · rw [if_pos hk]
    refine control_well_typed k (qpeOracle m n anc f k) (by omega) ?_ ?_
    · exact is_fresh_map_qubits_shift (f (revIndex m k)) hk
    · exact wellTyped_map_qubits_shift (f (revIndex m k)) (hwt (revIndex m k))
  · rw [if_neg hk]
    -- QFTinv stage: lift the dim-`m` layer well-typedness to the full register via the
    -- polymorphic-lift bridge (`real_QFTinv_layer` at `m+(n+anc)` = `map_qubits id` of the dim-`m`
    -- one) + the `map_qubits id` rebase.
    refine BaseUCom.QFTinv_well_typed_of_layer_well_typed m ?_
    rw [real_QFTinv_layer_map_id_bridge m (n + anc) m]
    exact wellTyped_map_qubits_id (Nat.le_add_right m (n + anc))
      (BaseUCom.real_QFTinv_layer m) (wellTyped_QFTinv m hm)

/-! ## §4. The combine — the `hisom` discharge. -/

/-- **`hisom` for the physical QPE stage.**  Each stage map of the (well-typed) oracle family `f`
    is a `pmDist` isometry: `qpeStageMap_pmDist_isom` fed by the unitarity
    (`uc_eval_unitary_of_wellTyped`) of the well-typed stage circuit (`qpeStageUCom_well_typed`).
    This is EXACTLY the `hisom` hypothesis the coset-Shor H4/H5 deviation bounds carry (with
    `f := f_runwayPhysical`, `n := bits`, `anc := cosetAnc w bits`). -/
theorem qpeStage_physical_isom (m n anc : Nat) (hm : 0 < m)
    (f : Nat → FormalRV.Framework.BaseUCom (n + anc))
    (hwt : ∀ j, UCom.WellTyped (n + anc) (f j))
    (k : Nat) (a b : QState (2 ^ m * 2 ^ n * 2 ^ anc)) :
    pmDist (qpeStageMap m n anc f k a) (qpeStageMap m n anc f k b) = pmDist a b :=
  qpeStageMap_pmDist_isom m n anc f k
    (uc_eval_unitary_of_wellTyped (qpeStageUCom m n anc f k)
      (qpeStageUCom_well_typed m n anc hm f hwt k)) a b

end FormalRV.Shor.GidneyInPlace.QpeStageWellTyped
