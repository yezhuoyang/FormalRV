/-
  Audit · cain-xu-2026 · VERIFIER — end-to-end obligation + the anti-cheat gate
  ----------------------------------------------------------------------------
  `#verify_clean` accepts a theorem ONLY if its transitive axioms ⊆
  {propext, Classical.choice, Quot.sound}.  A `sorry` or a stray/native axiom makes the
  BUILD FAIL — so this folder cannot pass by "counting numbers": every theorem asserted
  ✅ below is machine-checked here to be genuinely axiom-clean.

  END-TO-END (resource) for cain-xu: the naive modexp-on-the-real-LP-code construction is
  SEMANTICALLY CORRECT (preserves the code throughout — L3/L4), hence its cost is a genuine
  UPPER BOUND, and a structural LOWER BOUND never exceeds it.  The paper's ~10⁴ qubits / ~1
  week sits BETWEEN these verified bounds; the distance to the upper bound is the paper's
  UNCONSTRUCTED optimisations (see the GAP in README.md) — named, never hidden.
-/
import FormalRV.Audit.CainXu2026.QianxuVerifiedUpperBound
import FormalRV.Audit.CainXu2026.QianxuBounds
import FormalRV.Audit.CainXu2026.QianxuNaiveConstructions
import FormalRV.Verifier

-- ✅ the verified resource UPPER BOUND (naive modexp-on-LP is correct ⇒ its cost bounds the real one):
#verify_clean FormalRV.Audit.CainXu2026.QianxuVerifiedUpperBound.qianxu_verified_upper_bound
-- ✅ SOUNDNESS: the structural lower bounds never exceed the upper bound (qubits; time, all schedules):
#verify_clean FormalRV.Audit.CainXu2026.QianxuBounds.qubit_lower_le_upper
#verify_clean FormalRV.Audit.CainXu2026.QianxuBounds.time_floor_all_schedules
