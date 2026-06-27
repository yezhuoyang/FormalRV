/-
  FormalRV.SQIRPort.PhaseKickback

  Block-disjoint commutation + QPE-specific phase-kickback cascade.

  QPE's `QPE_var m anc f` lifts each `f i : BaseUCom anc` to
  `BaseUCom (m + anc)` via `map_qubits (fun q => m + q) (f i)`,
  placing the data-register action at qubit positions [m, m + anc)
  and leaving the control register at [0, m). This file proves:

  - `is_fresh_map_qubits_shift`: control qubits are fresh in lifted circuits.
  - `wellTyped_map_qubits_shift`: lifted circuits remain well-typed on the
    enlarged register.
  - `uc_eval_map_qubits_shift_commutes_pad_u`: matrix-level block-disjoint
    commutation — the key bridge that validates the abstract cascade's
    `h_comm_all` hypothesis for QPE's layout.
  - `uc_eval_controlled_powers_shifted_on_common_eigenstate`: the QPE-
    specific cascade theorem, derived by discharging the abstract cascade
    theorem's hypotheses with the three lemmas above.

  This file imports both `ControlledGates` (for the abstract cascade) and
  `Shor` (for `map_qubits`). The two have no cyclic dependency: Shor.lean
  imports only `Eigenstate` + `TotientLowerBound`, neither of which uses
  the control-stub fix.
-/


-- Re-export shim: split into PhaseKickback/ submodules (same namespace; opens de-duplicated); importers unchanged.
import FormalRV.QPE.PhaseKickback.Part1
import FormalRV.QPE.PhaseKickback.Part2
import FormalRV.QPE.PhaseKickback.Part3
import FormalRV.QPE.PhaseKickback.Part4
import FormalRV.QPE.PhaseKickback.Part5
import FormalRV.QPE.PhaseKickback.Part6
